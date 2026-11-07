module Agda.Compiler.ToForth where

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Main (runAgda)
import Agda.Syntax.Abstract.Name (qnameName)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Treeless
import Agda.Syntax.TopLevelModuleName
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.Substitute (TelV(..))
import Agda.TypeChecking.Telescope (telView)
import Data.Char (isAlphaNum, isDigit)
import Data.List (elemIndex, find, sort)
import qualified Data.List.NonEmpty as NE
import Data.SCargot
import Data.SCargot.Repr
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Control.Monad.IO.Class as IO
import Data.Maybe (catMaybes)
import Numeric.Natural (Natural)
import Paths_agda2forth (getDataFileName)

type FthForm = RichSExpr Text

data NatOp
  = NatAdd
  | NatMonus
  | NatMultiply
  deriving (Eq, Show)

data FormalToken
  = FormalPushLiteral Natural
  | FormalAddWord
  | FormalMonusWord
  | FormalMultiplyWord
  | FormalSwapWord
  | FormalRollWord Natural
  | FormalTrueWord
  | FormalFalseWord
  | FormalIf [FormalToken] [FormalToken]
  deriving (Eq, Show)

data CompiledDefinition = CompiledDefinition
  { compiledName :: QName
  , compiledForm :: FthForm
  , compiledTokens :: [FormalToken]
  }

data NatExpr
  = NatLiteral Natural
  | NatBinary NatOp NatExpr NatExpr
  deriving (Eq, Show)

data BoolExpr
  = BoolLiteral Bool
  | BoolVariable Int
  | BoolConditional BoolExpr BoolExpr BoolExpr
  deriving (Eq, Show)

-- Each path is one possible additive branch. The same live resource must
-- occur exactly once along every path; branch alternatives share a context.
boolExprResourcePaths :: BoolExpr -> [[Int]]
boolExprResourcePaths (BoolLiteral _) = [[]]
boolExprResourcePaths (BoolVariable index) = [[index]]
boolExprResourcePaths (BoolConditional condition whenTrue whenFalse) =
  [ conditionPath ++ branchPath
  | conditionPath <- boolExprResourcePaths condition
  , branchPath <- boolExprResourcePaths whenTrue
  ]
  ++
  [ conditionPath ++ branchPath
  | conditionPath <- boolExprResourcePaths condition
  , branchPath <- boolExprResourcePaths whenFalse
  ]

data NatLinearExpr
  = NatArgument
  | NatLinearLeft NatOp NatLinearExpr NatExpr
  | NatLinearRight NatOp NatExpr NatLinearExpr
  deriving (Eq, Show)

data NatTerm
  = NatClosed NatExpr
  | NatOpen NatLinearExpr
  deriving (Eq, Show)

-- Two-argument primitive functions consume both live arguments exactly once.
-- The source argument order is x then y; the incoming Forth stack is y x.
data NatBinaryLinearExpr
  = NatBinaryArguments NatOp
  | NatBinaryArgumentsExchanged NatOp
  deriving (Eq, Show)

-- A general arithmetic tree over labelled linear resources. Labels are
-- Treeless de Bruijn indices; admission requires each top-level argument
-- label exactly once before any target code is emitted.
data NatResourceExpr
  = NatResourceLiteral Natural
  | NatResourceVariable Int
  | NatResourceBinary NatOp NatResourceExpr NatResourceExpr
  deriving (Eq, Show)

natResourceVariables :: NatResourceExpr -> [Int]
natResourceVariables (NatResourceLiteral _) = []
natResourceVariables (NatResourceVariable index) = [index]
natResourceVariables (NatResourceBinary _ left right) =
  natResourceVariables left ++ natResourceVariables right

decodeNatResourceTerm :: [QName] -> [NatResourceExpr] -> TTerm -> TCM NatResourceExpr
decodeNatResourceTerm callStack environment term = do
  let (headTerm, arguments) = tAppView term
  case headTerm of
    TLit (LitNat n)
      | null arguments && n >= 0 ->
          pure (NatResourceLiteral (fromInteger n))
    TVar index
      | null arguments ->
          case drop index environment of
            expression : _ -> pure expression
            [] -> unsupported ("unbound Treeless Nat resource: " ++ show index)
    TLet bound body
      | null arguments ->
          let uses = natVariableUses 0 body
          in if uses == 0
               then decodeNatResourceTerm callStack environment body
               else do
                 value <- decodeNatResourceTerm callStack environment bound
                 if uses > 1 && not (null (natResourceVariables value))
                   then unsupported "MALLP linearity violation: a let-bound expression capturing live resources is reused"
                   else decodeNatResourceTerm callStack (value : environment) body
    TPrim primitive -> do
      operands <- traverse (decodeNatResourceTerm callStack environment) arguments
      case (primitive, operands) of
        (PAdd, [left, right]) ->
          pure (NatResourceBinary NatAdd left right)
        (PMul, [left, right]) ->
          pure (NatResourceBinary NatMultiply left right)
        (PSub, [_, _]) ->
          unsupported "PSub is signed integer subtraction; Nat monus uses builtin NatMinus"
        _ -> unsupported ("unsupported Nat resource primitive or arity: " ++ show primitive)
    TDef name -> do
      plusName <- getBuiltinName builtinNatPlus
      minusName <- getBuiltinName builtinNatMinus
      case (Just name == plusName, Just name == minusName) of
        (True, _) -> do
          operands <- traverse (decodeNatResourceTerm callStack environment) arguments
          case operands of
            [left, right] -> pure (NatResourceBinary NatAdd left right)
            _ -> unsupported "Agda Nat addition must have exactly two operands"
        (_, True) -> do
          operands <- traverse (decodeNatResourceTerm callStack environment) arguments
          case operands of
            [left, right] -> pure (NatResourceBinary NatMonus left right)
            _ -> unsupported "Agda Nat subtraction must have exactly two operands"
        _ -> inlineNatResourceFunction callStack environment name arguments
    TCoerce inner
      | null arguments -> decodeNatResourceTerm callStack environment inner
    _ -> unsupported ("Treeless term is outside the linear Nat expression core: " ++ show headTerm)

-- Inline acyclic, first-order Nat helpers before resource checking.  This
-- makes nonrecursive PureCake-style calls compositional: every argument is
-- substituted as a resource tree, then the final caller is checked for exact
-- once-only use.  Recursive call graphs require a separate recursor proof.
inlineNatResourceFunction
  :: [QName]
  -> [NatResourceExpr]
  -> QName
  -> [TTerm]
  -> TCM NatResourceExpr
inlineNatResourceFunction callStack environment name arguments
  | name `elem` callStack =
      unsupported ("recursive Nat call requires a certified primitive recursor: " ++ prettyShow name)
  | otherwise = do
      definition <- getConstInfo name
      case theDef definition of
        Function{} -> do
          arity <- natFunctionArity definition
          case arity of
            Just expected | expected == length arguments -> do
              body <- toTreeless EagerEvaluation name
              case body of
                Nothing -> unsupported ("Nat helper has no Treeless body: " ++ prettyShow name)
                Just functionTerm -> do
                  let (actualArity, functionBody) = tLamView functionTerm
                  if actualArity /= expected
                    then unsupported ("Nat helper lambda arity mismatch: " ++ prettyShow name)
                    else pure ()
                  argumentValues <- traverse
                    (decodeNatResourceTerm callStack environment) arguments
                  -- De Bruijn index zero denotes the final source argument.
                  decodeNatResourceTerm (name : callStack)
                    (reverse argumentValues) functionBody
            _ -> unsupported ("called definition is not a first-order Nat function: " ++ prettyShow name)
        _ -> unsupported ("called Treeless definition is not a function: " ++ prettyShow name)

-- Compile a resource tree against current live input order. The active depth
-- counts already-built sibling results above those inputs. ROLL moves one
-- selected resource to the top without copying or discarding it.
formalNatToken :: NatOp -> FormalToken
formalNatToken NatAdd = FormalAddWord
formalNatToken NatMonus = FormalMonusWord
formalNatToken NatMultiply = FormalMultiplyWord

compileNatResourceExpr
  :: Int
  -> [Int]
  -> NatResourceExpr
  -> Either String (FthForm, [FormalToken], [Int])
compileNatResourceExpr _ context (NatResourceLiteral value) =
  Right (renderNatExpr (NatLiteral value), [FormalPushLiteral value], context)
compileNatResourceExpr active context (NatResourceVariable index) =
  case elemIndex index context of
    Nothing -> Left ("MALLP resource is missing, duplicated, or out of scope: " ++ show index)
    Just position ->
      let depth = active + position
          remaining = take position context ++ drop (position + 1) context
      in if depth == 0
           then Right (RSList [], [], remaining)
           else if depth == 1
             then Right (RSAtom "SWAP", [FormalSwapWord], remaining)
             else Right
               ( RSList [RSAtom (T.pack (show depth)), RSAtom "ROLL"]
               , [FormalRollWord (fromIntegral depth)]
               , remaining
               )
compileNatResourceExpr active context (NatResourceBinary operation left right) = do
  (leftCode, leftTokens, afterLeft) <- compileNatResourceExpr active context left
  (rightCode, rightTokens, afterRight) <-
    compileNatResourceExpr (active + 1) afterLeft right
  pure
    ( RSList [leftCode, rightCode, renderNatOp operation]
    , leftTokens ++ rightTokens ++ [formalNatToken operation]
    , afterRight
    )

compileBoolResourceExpr
  :: [Int]
  -> BoolExpr
  -> Either String (FthForm, [FormalToken], [Int])
compileBoolResourceExpr context (BoolLiteral value) =
  let (forth, token) = if value
        then ("TRUE", FormalTrueWord)
        else ("FALSE", FormalFalseWord)
  in Right (RSAtom forth, [token], context)
compileBoolResourceExpr context (BoolVariable index) =
  case elemIndex index context of
    Nothing -> Left ("MALLP Bool resource is missing, duplicated, or out of scope: " ++ show index)
    Just position ->
      let depth = position
          remaining = take position context ++ drop (position + 1) context
      in if depth == 0
           then Right (RSList [], [], remaining)
           else if depth == 1
             then Right (RSAtom "SWAP", [FormalSwapWord], remaining)
             else Right
               ( RSList [RSAtom (T.pack (show depth)), RSAtom "ROLL"]
               , [FormalRollWord (fromIntegral depth)]
               , remaining
               )
compileBoolResourceExpr context (BoolConditional condition whenTrue whenFalse) = do
  (conditionCode, conditionTokens, afterCondition) <-
    compileBoolResourceExpr context condition
  (trueCode, trueTokens, afterTrue) <-
    compileBoolResourceExpr afterCondition whenTrue
  (falseCode, falseTokens, afterFalse) <-
    compileBoolResourceExpr afterCondition whenFalse
  if afterTrue /= afterFalse
    then Left "MALLP additive case branches consume different resource contexts"
    else Right
      ( RSList
          [ conditionCode
          , RSAtom "IF"
          , trueCode
          , RSAtom "ELSE"
          , falseCode
          , RSAtom "THEN"
          ]
      , conditionTokens ++ [FormalIf trueTokens falseTokens]
      , afterTrue
      )

compileBoolResourceFunction
  :: QName
  -> Int
  -> TTerm
  -> TCM (FthForm, [FormalToken])
compileBoolResourceFunction owner arity term = do
  let (actualArity, body) = tLamView term
      expectedResources = [0 .. arity - 1]
  if actualArity /= arity
    then unsupported ("expected " ++ show arity ++ " Bool Treeless lambdas, received " ++ show actualArity)
    else pure ()
  expression <- decodeBoolResourceTerm [owner]
    [BoolVariable index | index <- expectedResources]
    body
  let invalidPaths =
        filter ((/= expectedResources) . sort) (boolExprResourcePaths expression)
  if not (null invalidPaths)
    then unsupported "MALLP linearity violation: every Bool argument must occur exactly once on every additive branch"
    else pure ()
  (code, tokens, remaining) <-
    either unsupported pure (compileBoolResourceExpr expectedResources expression)
  if null remaining
    then pure (code, tokens)
    else unsupported ("MALLP Bool resource leak: unconsumed arguments " ++ show remaining)

compileNatResourceFunction :: QName -> Int -> TTerm -> TCM (FthForm, [FormalToken])
compileNatResourceFunction owner arity term = do
  let (actualArity, body) = tLamView term
  if actualArity /= arity
    then unsupported ("expected " ++ show arity ++ " Treeless lambdas, received " ++ show actualArity)
    else pure ()
  expression <- decodeNatResourceTerm [owner]
    [NatResourceVariable index | index <- [0 .. arity - 1]]
    body
  let actualResources = sort (natResourceVariables expression)
      expectedResources = [0 .. arity - 1]
  if actualResources /= expectedResources
    then unsupported "MALLP linearity violation: each live Nat argument must occur exactly once"
    else pure ()
  (code, tokens, remaining) <- either unsupported pure
    (compileNatResourceExpr 0 expectedResources expression)
  if null remaining
    then pure (code, tokens)
    else unsupported ("MALLP resource leak: unconsumed arguments " ++ show remaining)

decodeNatPrimitive :: TPrim -> [NatExpr] -> Either String NatExpr
decodeNatPrimitive PAdd [left, right] =
  Right (NatBinary NatAdd left right)
decodeNatPrimitive PSub [_, _] =
  Left "PSub is signed integer subtraction; Nat monus is lowered from builtin NatMinus"
decodeNatPrimitive PMul [left, right] =
  Right (NatBinary NatMultiply left right)
decodeNatPrimitive primitive _ =
  Left ("unsupported Nat primitive or arity: " ++ show primitive)

formToText :: FthForm -> Text
formToText (RSAtom atom) = atom <> " "
formToText (RSList forms) = T.concat (map formToText forms)
formToText (RSDotted forms tailForm) = T.concat (map formToText forms) <> tailForm

safeForthName :: QName -> Text
safeForthName name =
  let raw = map escape (prettyShow (qnameName name))
      escaped = case raw of
        [] -> "agdaWord"
        first : rest | isDigit first -> 'z' : first : rest
        _ -> raw
  in T.pack escaped
  where
    escape c
      | isAlphaNum c || c `elem` ("!$%&*+-./:<=>?@^_~" :: String) = c
      | otherwise = '_'

strictWord :: QName -> FthForm -> FthForm
strictWord name body =
  RSAtom $ T.concat [": ", safeForthName name, " ", formToText body, ";"]

unsupported :: String -> TCM a
unsupported message = fail ("agda2MALLPForth: " ++ message)

-- Count references to one de Bruijn variable.  TLam, TLet, and constructor
-- alternatives extend the local binder depth; a TCase scrutinee itself is
-- also a use of its indexed variable.
natVariableUses :: Int -> TTerm -> Int
natVariableUses target = count 0
  where
    count depth (TVar index)
      | index == target + depth = 1
      | otherwise = 0
    count depth (TApp function arguments) =
      count depth function + sum (map (count depth) arguments)
    count depth (TLam body) = count (depth + 1) body
    count depth (TLet bound body) =
      count depth bound + count (depth + 1) body
    count depth (TCase index _ fallback alternatives) =
      (if index == target + depth then 1 else 0)
        + count depth fallback
        + sum (map (countAlternative depth) alternatives)
    count depth (TCoerce inner) = count depth inner
    count _ _ = 0

    countAlternative depth (TACon _ arity body) =
      count (depth + arity) body
    countAlternative depth (TAGuard guard body) =
      count depth guard + count depth body
    countAlternative depth (TALit _ body) = count depth body

-- Closed Nat let-bindings can be substituted at every use.  The environment
-- contains only closed NatExpr values: this decoder rejects top-level
-- lambdas, and every accepted binding is built solely from total, pure Nat
-- operations.  Reusing one of these expressions duplicates a closed proof
-- tree, not a live MALLP assumption; an unused lazy binding consumes no
-- resource and is skipped without decoding or evaluating its body.
combineNatTerms :: NatOp -> NatTerm -> NatTerm -> Either String NatTerm
combineNatTerms operation (NatClosed left) (NatClosed right) =
  Right (NatClosed (NatBinary operation left right))
combineNatTerms operation (NatOpen left) (NatClosed right) =
  Right (NatOpen (NatLinearLeft operation left right))
combineNatTerms operation (NatClosed left) (NatOpen right) =
  Right (NatOpen (NatLinearRight operation left right))
combineNatTerms _ (NatOpen _) (NatOpen _) =
  Left "MALLP linearity violation: one live Nat resource is used twice"

decodeNatTerm :: [NatTerm] -> TTerm -> TCM NatTerm
decodeNatTerm environment term = do
  let (headTerm, args) = tAppView term
  case headTerm of
    TLit (LitNat n)
      | null args && n >= 0 -> pure (NatClosed (NatLiteral (fromInteger n)))
    TVar index
      | null args ->
          case drop index environment of
            value : _ -> pure value
            [] -> unsupported ("unbound Treeless variable: " ++ show index)
    TLet bound body
      | null args ->
          if natVariableUses 0 body == 0
            then decodeNatTerm environment body
            else do
              value <- decodeNatTerm environment bound
              case value of
                NatOpen _ | natVariableUses 0 body > 1 ->
                  unsupported "MALLP linearity violation: a binding that captures a live resource is used more than once"
                _ -> decodeNatTerm (value : environment) body
    TPrim primitive -> do
      operands <- traverse (decodeNatTerm environment) args
      case (primitive, operands) of
        (PAdd, [left, right]) ->
          either unsupported pure (combineNatTerms NatAdd left right)
        (PMul, [left, right]) ->
          either unsupported pure (combineNatTerms NatMultiply left right)
        (PSub, [_, _]) ->
          unsupported "PSub is signed integer subtraction; Nat monus is lowered only from builtin NatMinus"
        (_, _) ->
          unsupported ("unsupported Nat primitive or arity: " ++ show primitive)
    TDef name -> do
      plusName <- getBuiltinName builtinNatPlus
      minusName <- getBuiltinName builtinNatMinus
      operands <- traverse (decodeNatTerm environment) args
      case operands of
        [left, right] | Just name == plusName ->
          either unsupported pure (combineNatTerms NatAdd left right)
        [left, right] | Just name == minusName ->
          either unsupported pure (combineNatTerms NatMonus left right)
        _ -> unsupported "user functions and non-binary definitions are outside the admitted Nat core"
    TCoerce inner
      | null args -> decodeNatTerm environment inner
    _ -> unsupported ("Treeless term is outside the admitted Nat core: " ++ show headTerm)

renderNatOp :: NatOp -> FthForm
renderNatOp operation = RSAtom $ case operation of
  NatAdd -> "MALLP-NAT-ADD"
  NatMonus -> "MALLP-NAT-MONUS"
  NatMultiply -> "MALLP-NAT-MUL"

renderNatExpr :: NatExpr -> FthForm
renderNatExpr (NatLiteral n) =
  RSAtom $ T.concat ["s\" ", T.pack (show n), "\" MALLP-PARSE-NAT"]
renderNatExpr (NatBinary operation left right) =
  RSList [renderNatExpr left, renderNatExpr right, renderNatOp operation]

renderNatLinearExpr :: NatLinearExpr -> FthForm
renderNatLinearExpr NatArgument = RSList []
renderNatLinearExpr (NatLinearLeft operation input right) =
  RSList [renderNatLinearExpr input, renderNatExpr right, renderNatOp operation]
renderNatLinearExpr (NatLinearRight operation left input) =
  RSList [renderNatExpr left, RSAtom "SWAP", renderNatLinearExpr input, renderNatOp operation]

renderNatTerm :: NatTerm -> FthForm
renderNatTerm (NatClosed expression) = renderNatExpr expression
renderNatTerm (NatOpen expression) = renderNatLinearExpr expression

-- Admit the exact two-resource primitive shape.  De Bruijn index 1 is the
-- first source argument and index 0 is the second.  Both must occur once;
-- arbitrary expression trees require the general resource-indexed decoder.
treelessVariableIndex :: TTerm -> Maybe Int
treelessVariableIndex (TVar index) = Just index
treelessVariableIndex (TCoerce inner) = treelessVariableIndex inner
treelessVariableIndex _ = Nothing

decodeNatBinaryLinearTerm :: TTerm -> TCM NatBinaryLinearExpr
decodeNatBinaryLinearTerm term = do
  let (headTerm, arguments) = tAppView term
  operation <- case headTerm of
    TPrim PAdd -> pure NatAdd
    TPrim PMul -> pure NatMultiply
    TPrim PSub ->
      unsupported "PSub is signed integer subtraction; Nat monus uses builtin NatMinus"
    TDef name -> do
      plusName <- getBuiltinName builtinNatPlus
      minusName <- getBuiltinName builtinNatMinus
      case () of
        _ | Just name == plusName -> pure NatAdd
          | Just name == minusName -> pure NatMonus
          | otherwise -> unsupported "two-argument Nat function must use a declared Nat primitive"
    _ -> unsupported ("unsupported two-argument Nat function body: " ++ show headTerm)
  case traverse treelessVariableIndex arguments of
    Just [1, 0] -> pure (NatBinaryArguments operation)
    Just [0, 1] -> pure (NatBinaryArgumentsExchanged operation)
    _ -> unsupported "MALLP linearity violation: binary Nat primitive must consume each of its two arguments exactly once"

renderNatBinaryLinearExpr :: NatBinaryLinearExpr -> FthForm
renderNatBinaryLinearExpr (NatBinaryArguments operation) =
  renderNatOp operation
renderNatBinaryLinearExpr (NatBinaryArgumentsExchanged operation) =
  RSList [RSAtom "SWAP", renderNatOp operation]

decodeBoolTerm :: [QName] -> [Bool] -> TTerm -> TCM Bool
decodeBoolTerm callStack environment term = do
  trueName <- getBuiltinName builtinTrue
  falseName <- getBuiltinName builtinFalse
  let (headTerm, arguments) = tAppView term
      matches expected actual = Just actual == expected
      chooseConstructor expected (TACon name arity body) =
        matches expected name && arity == 0
      chooseConstructor _ _ = False
      chooseGuard [] fallback = decodeBoolTerm callStack environment fallback
      chooseGuard (TAGuard guard body : rest) fallback = do
        matchesGuard <- decodeBoolTerm callStack environment guard
        if matchesGuard
          then decodeBoolTerm callStack environment body
          else chooseGuard rest fallback
      chooseGuard (_ : rest) fallback = chooseGuard rest fallback
      lookupBoolean index =
        case drop index environment of
          value : _ -> pure value
          [] -> unsupported ("unbound Treeless Bool variable: " ++ show index)
  case headTerm of
    TCon name
      | null arguments && matches trueName name -> pure True
      | null arguments && matches falseName name -> pure False
    TDef name
      | null arguments && matches trueName name -> pure True
      | null arguments && matches falseName name -> pure False
    TVar index
      | null arguments -> lookupBoolean index
    TCoerce inner
      | null arguments -> decodeBoolTerm callStack environment inner
    TLet bound body
      | null arguments ->
          if natVariableUses 0 body == 0
            then decodeBoolTerm callStack environment body
            else do
              value <- decodeBoolTerm callStack environment bound
              decodeBoolTerm callStack (value : environment) body
    TCase index _ fallback alternatives
      | null arguments -> do
          scrutinee <- lookupBoolean index
          let constructor = if scrutinee then trueName else falseName
          case find (chooseConstructor constructor) alternatives of
            Just (TACon _ _ body) ->
              decodeBoolTerm callStack environment body
            _ -> chooseGuard alternatives fallback
    TPrim PIf
      | [condition, whenTrue, whenFalse] <- arguments -> do
          selected <- decodeBoolTerm callStack environment condition
          decodeBoolTerm callStack environment
            (if selected then whenTrue else whenFalse)
    TDef name -> inlineBoolFunction callStack environment name arguments
    _ -> unsupported ("Treeless term is outside the closed Bool fragment: " ++ show headTerm)

inlineBoolFunction :: [QName] -> [Bool] -> QName -> [TTerm] -> TCM Bool
inlineBoolFunction callStack environment name arguments
  | name `elem` callStack =
      unsupported ("recursive Bool call requires a certified recursor: " ++ prettyShow name)
  | otherwise = do
      definition <- getConstInfo name
      case theDef definition of
        Function{} -> do
          arity <- boolFunctionArity definition
          case arity of
            Just expected | expected == length arguments -> do
              body <- toTreeless EagerEvaluation name
              case body of
                Nothing -> unsupported ("Bool helper has no Treeless body: " ++ prettyShow name)
                Just functionTerm -> do
                  let (actualArity, functionBody) = tLamView functionTerm
                  if actualArity /= expected
                    then unsupported ("Bool helper lambda arity mismatch: " ++ prettyShow name)
                    else pure ()
                  argumentValues <- traverse
                    (decodeBoolTerm callStack environment) arguments
                  decodeBoolTerm (name : callStack)
                    (reverse argumentValues ++ environment) functionBody
            _ -> unsupported
              ("called definition is not a first-order Bool function: " ++ prettyShow name)
        _ -> unsupported ("called Treeless definition is not a function: " ++ prettyShow name)

decodeBoolResourceTerm :: [QName] -> [BoolExpr] -> TTerm -> TCM BoolExpr
decodeBoolResourceTerm callStack environment term = do
  trueName <- getBuiltinName builtinTrue
  falseName <- getBuiltinName builtinFalse
  let (headTerm, arguments) = tAppView term
      matches expected actual = Just actual == expected
      lookupBoolean index =
        case drop index environment of
          value : _ -> pure value
          [] -> unsupported ("unbound Treeless Bool resource: " ++ show index)
      findConstructor expected alternatives =
        find (\alternative -> case alternative of
          TACon name arity _ -> matches expected name && arity == 0
          _ -> False) alternatives
      decodeConstructor expected alternatives fallback =
        case findConstructor expected alternatives of
          Just (TACon _ _ body) ->
            decodeBoolResourceTerm callStack environment body
          _ -> decodeBoolResourceGuards callStack environment alternatives fallback
  case headTerm of
    TCon name
      | null arguments && matches trueName name ->
          pure (BoolLiteral True)
      | null arguments && matches falseName name ->
          pure (BoolLiteral False)
    TDef name
      | null arguments && matches trueName name ->
          pure (BoolLiteral True)
      | null arguments && matches falseName name ->
          pure (BoolLiteral False)
    TVar index
      | null arguments -> lookupBoolean index
    TCoerce inner
      | null arguments -> decodeBoolResourceTerm callStack environment inner
    TLet bound body
      | null arguments ->
          let uses = natVariableUses 0 body
          in if uses == 0
               then decodeBoolResourceTerm callStack environment body
               else do
                 value <- decodeBoolResourceTerm callStack environment bound
                 if uses > 1 && any (not . null)
                      (boolExprResourcePaths value)
                   then unsupported "MALLP linearity violation: a Bool let capturing a live resource is reused"
                   else decodeBoolResourceTerm callStack (value : environment) body
    TCase index _ fallback alternatives
      | null arguments -> do
          scrutinee <- lookupBoolean index
          whenTrue <- decodeConstructor trueName alternatives fallback
          whenFalse <- decodeConstructor falseName alternatives fallback
          pure (BoolConditional scrutinee whenTrue whenFalse)
    TPrim PIf
      | [condition, whenTrue, whenFalse] <- arguments -> do
          decodedCondition <- decodeBoolResourceTerm callStack environment condition
          decodedTrue <- decodeBoolResourceTerm callStack environment whenTrue
          decodedFalse <- decodeBoolResourceTerm callStack environment whenFalse
          pure (BoolConditional decodedCondition decodedTrue decodedFalse)
    TDef name -> inlineBoolResourceFunction callStack environment name arguments
    _ -> unsupported
      ("Treeless term is outside the linear Bool fragment: " ++ show headTerm)

decodeBoolResourceGuards
  :: [QName]
  -> [BoolExpr]
  -> [TAlt]
  -> TTerm
  -> TCM BoolExpr
decodeBoolResourceGuards callStack environment alternatives fallback =
  case alternatives of
    [] -> decodeBoolResourceTerm callStack environment fallback
    TAGuard guard body : rest -> do
      condition <- decodeBoolResourceTerm callStack environment guard
      whenTrue <- decodeBoolResourceTerm callStack environment body
      whenFalse <- decodeBoolResourceGuards callStack environment rest fallback
      case condition of
        BoolLiteral True -> pure whenTrue
        BoolLiteral False -> pure whenFalse
        _ -> pure (BoolConditional condition whenTrue whenFalse)
    _ : rest ->
      decodeBoolResourceGuards callStack environment rest fallback

inlineBoolResourceFunction
  :: [QName]
  -> [BoolExpr]
  -> QName
  -> [TTerm]
  -> TCM BoolExpr
inlineBoolResourceFunction callStack environment name arguments
  | name `elem` callStack =
      unsupported ("recursive Bool call requires a certified recursor: " ++ prettyShow name)
  | otherwise = do
      definition <- getConstInfo name
      case theDef definition of
        Function{} -> do
          arity <- boolFunctionArity definition
          case arity of
            Just expected | expected == length arguments -> do
              body <- toTreeless EagerEvaluation name
              case body of
                Nothing -> unsupported ("Bool helper has no Treeless body: " ++ prettyShow name)
                Just functionTerm -> do
                  let (actualArity, functionBody) = tLamView functionTerm
                  if actualArity /= expected
                    then unsupported ("Bool helper lambda arity mismatch: " ++ prettyShow name)
                    else pure ()
                  values <- traverse
                    (decodeBoolResourceTerm callStack environment) arguments
                  decodeBoolResourceTerm (name : callStack)
                    (reverse values ++ environment) functionBody
            _ -> unsupported
              ("called definition is not a first-order Bool function: " ++ prettyShow name)
        _ -> unsupported ("called Treeless definition is not a function: " ++ prettyShow name)

isBuiltinType :: QName -> I.Type -> TCM Bool
isBuiltinType builtinName ty = do
  reduced <- reduce ty
  pure $ case I.unEl reduced of
    I.Def actual [] -> actual == builtinName
    _ -> False

hasNatResult :: Definition -> TCM Bool
hasNatResult definition = do
  natName <- getBuiltinName builtinNat
  TelV _ resultType <- telView (defType definition)
  case natName of
    Nothing -> pure False
    Just name -> isBuiltinType name resultType

natFunctionArity :: Definition -> TCM (Maybe Int)
natFunctionArity definition = do
  natName <- getBuiltinName builtinNat
  TelV telescope resultType <- telView (defType definition)
  case natName of
    Nothing -> pure Nothing
    Just name -> do
      resultIsNat <- isBuiltinType name resultType
      argumentTypes <- traverse (\domain -> isBuiltinType name (snd (I.unDom domain)))
        (I.telToList telescope)
      pure $ if resultIsNat && and argumentTypes
        then Just (length argumentTypes)
        else Nothing

boolFunctionArity :: Definition -> TCM (Maybe Int)
boolFunctionArity definition = do
  boolName <- getBuiltinName builtinBool
  TelV telescope resultType <- telView (defType definition)
  case boolName of
    Nothing -> pure Nothing
    Just name -> do
      resultIsBool <- isBuiltinType name resultType
      argumentTypes <- traverse
        (\domain -> isBuiltinType name (snd (I.unDom domain)))
        (I.telToList telescope)
      pure $ if resultIsBool && and argumentTypes
        then Just (length argumentTypes)
        else Nothing

hasBoolResult :: Definition -> TCM Bool
hasBoolResult definition = do
  arity <- boolFunctionArity definition
  pure (arity == Just 0)

hasUnitResult :: Definition -> TCM Bool
hasUnitResult definition = do
  unitName <- getBuiltinName builtinUnit
  TelV _ resultType <- telView (defType definition)
  reducedResultType <- reduce resultType
  pure $ case (unitName, I.unEl reducedResultType) of
    (Just expected, I.Def actual []) -> expected == actual
    _ -> False

decodeUnitTerm :: TTerm -> TCM ()
decodeUnitTerm term = do
  unitConstructor <- getBuiltinName builtinUnitUnit
  let (headTerm, args) = tAppView term
      matches constructor = Just constructor == unitConstructor
  case headTerm of
    TCon name | null args && matches name -> pure ()
    TDef name | null args && matches name -> pure ()
    -- Agda erases the unique unit constructor in Treeless output. The
    -- result-type gate has already established that this is a Unit value.
    TErased | null args -> pure ()
    TCoerce inner | null args -> decodeUnitTerm inner
    _ -> unsupported ("Treeless term is outside the closed Unit fragment: " ++ show headTerm)


compileDefinition :: Definition -> TCM (Maybe CompiledDefinition)
compileDefinition definition
  | defNoCompilation definition || not (usableModality (getModality definition)) =
      pure Nothing
  | otherwise = case theDef definition of
      Function{} -> do
        isNat <- hasNatResult definition
        natArity <- natFunctionArity definition
        isBool <- hasBoolResult definition
        boolArity <- boolFunctionArity definition
        isUnit <- hasUnitResult definition
        if isNat then do
          body <- toTreeless EagerEvaluation (defName definition)
          case (natArity, body) of
            (Just arity, Just term) -> do
              (code, tokens) <- compileNatResourceFunction (defName definition) arity term
              pure (Just (CompiledDefinition
                (defName definition) (strictWord (defName definition) code) tokens))
            (Just _, Nothing) -> pure Nothing
            (Nothing, _) -> unsupported "Nat definition has a non-Nat argument or result"
        else if isBool then do
          body <- toTreeless EagerEvaluation (defName definition)
          case body of
            Nothing -> pure Nothing
            Just term -> do
              value <- decodeBoolTerm [] [] term
              let (forthBoolean, formalBoolean) =
                    if value then ("TRUE", FormalTrueWord) else ("FALSE", FormalFalseWord)
              pure (Just (CompiledDefinition
                (defName definition)
                (strictWord (defName definition) (RSAtom forthBoolean))
                [formalBoolean]))
        else if maybe False (> 0) boolArity then do
          body <- toTreeless EagerEvaluation (defName definition)
          case (boolArity, body) of
            (Just arity, Just term) -> do
              (code, tokens) <-
                compileBoolResourceFunction (defName definition) arity term
              pure (Just (CompiledDefinition
                (defName definition) (strictWord (defName definition) code) tokens))
            (Just _, Nothing) -> pure Nothing
            _ -> unsupported "Bool function arity classification changed during compilation"
        else if isUnit then do
          body <- toTreeless EagerEvaluation (defName definition)
          case body of
            Nothing -> pure Nothing
            Just term -> do
              decodeUnitTerm term
              pure (Just (CompiledDefinition
                (defName definition) (strictWord (defName definition) (RSList [])) []))
        else pure Nothing
      _ -> pure Nothing

readStrictRuntime :: IO String
readStrictRuntime = do
  path <- getDataFileName "FLib.fth"
  runtime <- TIO.readFile path
  let begin = "\\ MALLP-STRICT-BEGIN"
      end = "\\ MALLP-STRICT-END"
      (_, afterBegin) = T.breakOn begin runtime
  if T.null afterBegin
    then fail "FLib.fth is missing the strict MALLP runtime"
    else do
      let sectionStart = T.drop (T.length begin) afterBegin
          (section, afterEnd) = T.breakOn end sectionStart
      if T.null afterEnd
        then fail "FLib.fth has an unterminated strict MALLP runtime"
        else pure (T.unpack section)

renderForm :: FthForm -> Text
renderForm = encodeOne printer . fromRich
  where
    printer :: SExprPrinter Text (SExpr Text)
    printer = basicPrint id

agdaStringLiteral :: Text -> Text
agdaStringLiteral value = T.pack (show (T.unpack value))

formalTokenTerm :: FormalToken -> Text
formalTokenTerm (FormalPushLiteral value) =
  "textPushLiteral " <> T.pack (show value)
formalTokenTerm FormalAddWord = "textAddWord"
formalTokenTerm FormalMonusWord = "textMonusWord"
formalTokenTerm FormalMultiplyWord = "textMultiplyWord"
formalTokenTerm FormalSwapWord = "textSwapWord"
formalTokenTerm (FormalRollWord depth) =
  "textRollWord " <> T.pack (show depth)
formalTokenTerm FormalTrueWord = "textTrueWord"
formalTokenTerm FormalFalseWord = "textFalseWord"
formalTokenTerm (FormalIf whenTrue whenFalse) =
  "textIf (" <> formalTokenList whenTrue <> ") (" <>
    formalTokenList whenFalse <> ")"

formalTokenList :: [FormalToken] -> Text
formalTokenList [] = "[]"
formalTokenList tokens =
  T.intercalate " ∷ " (map formalTokenTerm tokens) <> " ∷ []"

rendererCertificate :: [CompiledDefinition] -> Text
rendererCertificate definitions = T.unlines $
  [ "module MALLPEmittedRenderer where"
  , ""
  , "open import Agda.Builtin.String using (String)"
  , "open import Agda.Builtin.List using (List; []; _∷_)"
  , "open import Agda.Builtin.Equality using (_≡_; refl)"
  , "open import ForthRenderer using"
  , "  (ForthTextToken; textPushLiteral; textAddWord; textMonusWord; textMultiplyWord;"
  , "   textSwapWord; textRollWord; textTrueWord; textFalseWord; textIf; renderForthWordText)"
  , ""
  ] ++ concat
    [ let index = T.pack (show position)
          actualName = "actualWord" <> index
          formalName = "formalWord" <> index
          proofName = "wordRendererCorrect" <> index
          actualText = renderForm (compiledForm definition)
          expectedName = safeForthName (compiledName definition)
      in [ actualName <> " : String"
         , actualName <> " = " <> agdaStringLiteral actualText
         , ""
         , formalName <> " : String"
         , formalName <> " = renderForthWordText "
             <> agdaStringLiteral expectedName <> " ("
             <> formalTokenList (compiledTokens definition) <> ")"
         , ""
         , proofName <> " : " <> actualName <> " ≡ " <> formalName
         , proofName <> " = refl"
         , ""
         ]
    | (position, definition) <- zip [0 :: Int ..] definitions
    ]

emitForthModule :: () -> () -> IsMain -> TopLevelModuleName -> [Maybe CompiledDefinition] -> TCM ()
emitForthModule _ _ _ moduleName maybeDefinitions = do
  runtime <- IO.liftIO readStrictRuntime
  let definitions = catMaybes maybeDefinitions
      body = T.intercalate "\n\n"
        (map (renderForm . compiledForm) definitions)
      output = T.pack runtime <> "\n" <> body <> "\n"
      baseName = prettyShow (NE.last (moduleNameParts moduleName))
      filename = baseName ++ ".fth"
  IO.liftIO $ do
    TIO.writeFile filename output
    TIO.writeFile "MALLPEmittedRenderer.agda" (rendererCertificate definitions)

backend :: Backend
backend = Backend backend'

backend' :: Backend' () () () () (Maybe CompiledDefinition)
backend' = Backend'
  { backendName = "agda2forth"
  , options = ()
  , commandLineFlags = []
  , isEnabled = \_ -> True
  , preCompile = pure
  , postCompile = \_ _ _ -> pure ()
  , preModule = \_ _ _ _ -> pure (Recompile ())
  , compileDef = \_ _ _ definition -> compileDefinition definition
  , postModule = emitForthModule
  , backendVersion = Nothing
  , scopeCheckingSuffices = False
  , backendInteractTop = Nothing
  , backendInteractHole = Nothing
  , mayEraseType = \_ -> pure True
  }

main :: IO ()
main = runAgda [backend]
