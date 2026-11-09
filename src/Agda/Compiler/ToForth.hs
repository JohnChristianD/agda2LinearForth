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
  , compiledWitness :: Maybe CompilerWitness
  }

-- A general arithmetic tree over labelled linear resources. Labels are
-- Treeless de Bruijn indices; admission requires each top-level argument
-- label exactly once before any target code is emitted.
data NatResourceExpr
  = NatResourceLiteral Natural
  | NatResourceVariable Int
  | NatResourceBinary NatOp NatResourceExpr NatResourceExpr
  -- Treeless PAdd has its operands reversed relative to source order.
  | NatResourceAddReversed NatResourceExpr NatResourceExpr
  deriving (Eq, Show)

natResourceVariables :: NatResourceExpr -> [Int]
natResourceVariables (NatResourceLiteral _) = []
natResourceVariables (NatResourceVariable index) = [index]
natResourceVariables (NatResourceBinary _ left right) =
  natResourceVariables left ++ natResourceVariables right
natResourceVariables (NatResourceAddReversed left right) =
  natResourceVariables left ++ natResourceVariables right

data BoolExpr
  = BoolLiteral Bool
  | BoolVariable Int
  | BoolConditional BoolExpr BoolExpr BoolExpr
  deriving (Eq, Show)

data BoolPairExpr = BoolPairFields Int Int
  deriving (Eq, Show)

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

data CompilerWitness
  = NatResourceWitness NatResourceExpr
  | BoolConstantWitness Bool
  | BoolFunctionWitness Int BoolExpr
  | BoolPairWitness QName QName BoolPairExpr
  | UnitWitness
  | Word64IdentityWitness
  deriving (Eq, Show)

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
        -- Agda's Treeless PAdd spine is reversed relative to source order.
        -- PMul, however, retains source order in the pinned compiler API.
        -- Keep the two cases explicit: commutativity is not definitional,
        -- and the generated source certificate checks each orientation.
        (PAdd, [left, right]) ->
          pure (NatResourceAddReversed right left)
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

-- Select one owned resource, preserving the residual context.  The active
-- depth counts computed sibling results already stacked above live inputs.
compileResourceUse
  :: String
  -> Int
  -> [Int]
  -> Int
  -> Either String (FthForm, [FormalToken], [Int])
compileResourceUse errorPrefix active context index =
  case elemIndex index context of
    Nothing -> Left (errorPrefix ++ show index)
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

compileNatResourceExpr
  :: Int
  -> [Int]
  -> NatResourceExpr
  -> Either String (FthForm, [FormalToken], [Int])
compileNatResourceExpr _ context (NatResourceLiteral value) =
  Right (renderNatLiteral value, [FormalPushLiteral value], context)
compileNatResourceExpr active context (NatResourceVariable index) =
  compileResourceUse
    "MALLP resource is missing, duplicated, or out of scope: "
    active context index
compileNatResourceExpr active context (NatResourceBinary operation left right) =
  compileNatResourceBinary active context operation left right
compileNatResourceExpr active context (NatResourceAddReversed left right) =
  compileNatResourceBinary active context NatAdd left right

compileNatResourceBinary
  :: Int
  -> [Int]
  -> NatOp
  -> NatResourceExpr
  -> NatResourceExpr
  -> Either String (FthForm, [FormalToken], [Int])
compileNatResourceBinary active context operation left right = do
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
  compileResourceUse
    "MALLP Bool resource is missing, duplicated, or out of scope: "
    0 context index
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

decodeBoolPairField :: TTerm -> TCM Int
decodeBoolPairField term =
  case tAppView term of
    (TVar index, []) | index == 0 || index == 1 -> pure index
    (TCoerce inner, []) -> decodeBoolPairField inner
    (headTerm, _) ->
      unsupported ("BoolPair field is outside the linear field fragment: " ++ show headTerm)

decodeBoolPairConstructor :: QName -> TTerm -> TCM BoolPairExpr
decodeBoolPairConstructor constructor term =
  case tAppView term of
    (TCon actual, [first, second]) | actual == constructor -> do
      firstField <- decodeBoolPairField first
      secondField <- decodeBoolPairField second
      pure (BoolPairFields firstField secondField)
    (TDef actual, [first, second]) | actual == constructor -> do
      firstField <- decodeBoolPairField first
      secondField <- decodeBoolPairField second
      pure (BoolPairFields firstField secondField)
    (headTerm, arguments) ->
      unsupported
        ("BoolPair branch must rebuild its constructor with both fields: "
          ++ show (headTerm, arguments))

decodeBoolPairFunction :: QName -> QName -> TTerm -> TCM BoolPairExpr
decodeBoolPairFunction owner constructor term = do
  let (actualArity, body) = tLamView term
  if actualArity /= 1
    then unsupported ("BoolPair function requires one pair argument, received " ++ show actualArity)
    else decodeCase body
  where
    decodeCase expression =
      case tAppView expression of
        (TCase index _ _ alternatives, [])
          | index == 0 ->
              case find (matchesConstructor constructor) alternatives of
                Just (TACon _ 2 branch) ->
                  decodeBoolPairConstructor constructor branch
                _ -> unsupported "BoolPair case must consume its two-field constructor"
        (TPrim PSeq, [strictTerm, continuation]) ->
          case tAppView strictTerm of
            (TVar 0, []) -> decodeCase continuation
            _ -> unsupported "BoolPair strict sequence must force its owned pair argument"
        (TCoerce inner, []) -> decodeCase inner
        (headTerm, arguments) ->
          unsupported ("Treeless BoolPair term must be a consuming constructor case: "
            ++ show (headTerm, arguments))

    matchesConstructor expected (TACon actual arity _) =
      expected == actual && arity == 2
    matchesConstructor _ _ = False

compileBoolPairResource
  :: Int
  -> [Int]
  -> Int
  -> Either String (FthForm, [FormalToken], [Int])
compileBoolPairResource active context index =
  compileResourceUse
    "MALLP BoolPair field missing, duplicated, or out of scope: "
    active context index

compileBoolPairFunction
  :: QName
  -> QName
  -> TTerm
  -> TCM (BoolPairExpr, FthForm, [FormalToken])
compileBoolPairFunction owner constructor term = do
  expression <- decodeBoolPairFunction owner constructor term
  let (first, second) = case expression of
        BoolPairFields left right -> (left, right)
      actualResources = sort [first, second]
      expectedResources = [0, 1]
  if actualResources /= expectedResources
    then unsupported "MALLP tensor elimination must consume both BoolPair fields exactly once"
    else pure ()
  if expression /= BoolPairFields 0 1 && expression /= BoolPairFields 1 0
    then unsupported "BoolPair compiler certificates currently cover identity and field swap"
    else pure ()
  (firstCode, firstTokens, afterFirst) <-
    either unsupported pure (compileBoolPairResource 0 expectedResources first)
  (secondCode, secondTokens, remaining) <-
    either unsupported pure (compileBoolPairResource 1 afterFirst second)
  if null remaining
    then pure (expression, RSList [firstCode, secondCode], firstTokens ++ secondTokens)
    else unsupported ("MALLP BoolPair resource leak: " ++ show remaining)

compileBoolResourceFunction
  :: QName
  -> Int
  -> TTerm
  -> TCM (BoolExpr, FthForm, [FormalToken])
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
  let proofSupported =
        (arity == 1 && expression == BoolVariable 0)
        || (arity == 1
            && expression ==
              BoolConditional (BoolVariable 0) (BoolLiteral False) (BoolLiteral True))
        || (arity == 2
            && expression ==
              BoolConditional (BoolVariable 1) (BoolVariable 0) (BoolVariable 0))
  if not proofSupported
    then unsupported "Bool resource tree is linear but outside the currently certified identity/invert/choose fragment"
    else pure ()
  (code, tokens, remaining) <-
    either unsupported pure (compileBoolResourceExpr expectedResources expression)
  if null remaining
    then pure (expression, code, tokens)
    else unsupported ("MALLP Bool resource leak: unconsumed arguments " ++ show remaining)

compileNatResourceFunction
  :: QName
  -> Int
  -> TTerm
  -> TCM (NatResourceExpr, FthForm, [FormalToken])
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
    then pure (expression, code, tokens)
    else unsupported ("MALLP resource leak: unconsumed arguments " ++ show remaining)

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

renderNatOp :: NatOp -> FthForm
renderNatOp operation = RSAtom $ case operation of
  NatAdd -> "MALLP-NAT-ADD"
  NatMonus -> "MALLP-NAT-MONUS"
  NatMultiply -> "MALLP-NAT-MUL"

renderNatLiteral :: Natural -> FthForm
renderNatLiteral value =
  RSAtom $ T.concat ["s\" ", T.pack (show value), "\" MALLP-PARSE-NAT"]

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
    TPrim PSeq
      | [strictTerm, continuation] <- arguments -> do
          _ <- decodeBoolTerm callStack environment strictTerm
          decodeBoolTerm callStack environment continuation
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
    -- Agda's Uncase pass erases a case with identical branches while keeping
    -- PSeq (scrutinee) body to preserve strict pattern-match evaluation.
    -- Reconstitute the additive elimination so the scrutinee remains a
    -- linearly consumed resource and each branch shares the same context.
    TPrim PSeq
      | [strictTerm, continuation] <- arguments -> do
          condition <- decodeBoolResourceTerm callStack environment strictTerm
          branch <- decodeBoolResourceTerm callStack environment continuation
          pure (BoolConditional condition branch branch)
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

word64FunctionArity :: Definition -> TCM (Maybe Int)
word64FunctionArity definition = do
  word64Name <- getBuiltinName builtinWord64
  TelV telescope resultType <- telView (defType definition)
  case word64Name of
    Nothing -> pure Nothing
    Just name -> do
      resultIsWord64 <- isBuiltinType name resultType
      argumentTypes <- traverse
        (\domain -> isBuiltinType name (snd (I.unDom domain)))
        (I.telToList telescope)
      pure $ if resultIsWord64 && and argumentTypes
        then Just (length argumentTypes)
        else Nothing

decodeWord64Identity :: TTerm -> TCM ()
decodeWord64Identity term =
  case tAppView term of
    (TVar 0, []) -> pure ()
    (TCoerce inner, []) -> decodeWord64Identity inner
    (headTerm, arguments) ->
      unsupported
        ("Word64 identity is the admitted exact two-limb fragment; unsupported term: "
          ++ show (headTerm, arguments))

compileWord64IdentityFunction
  :: QName
  -> Int
  -> TTerm
  -> TCM (FthForm, [FormalToken])
compileWord64IdentityFunction owner arity term = do
  let (actualArity, body) = tLamView term
  if arity /= 1 || actualArity /= 1
    then unsupported
      ("Word64 target representation currently admits one owned two-limb argument: "
        ++ prettyShow owner)
    else pure ()
  decodeWord64Identity body
  -- Word64 is one source resource represented by (high low) cells. The
  -- identity function consumes and returns that pair unchanged.
  pure (RSList [], [])


-- Recognize a closed, non-indexed one-constructor product of exactly two
-- Bool fields. This is a small tensor slice driven by Agda's resolved type
-- and constructor declarations, not a source-name whitelist.
boolPairFunctionConstructor :: Definition -> TCM (Maybe (QName, QName))
boolPairFunctionConstructor definition = do
  boolName <- getBuiltinName builtinBool
  TelV telescope resultType <- telView (defType definition)
  case (boolName, I.telToList telescope) of
    (Just bool, [domain]) -> do
      argumentType <- reduce (snd (I.unDom domain))
      reducedResult <- reduce resultType
      case (I.unEl argumentType, I.unEl reducedResult) of
        (I.Def argumentName [], I.Def resultName [])
          | argumentName == resultName -> do
              typeDefinition <- getConstInfo argumentName
              case theDef typeDefinition of
                Datatype{dataPars = 0, dataIxs = 0, dataCons = [constructor]} -> do
                  constructorDefinition <- getConstInfo constructor
                  TelV fields constructorResult <-
                    telView (defType constructorDefinition)
                  resultMatches <- isBuiltinType argumentName constructorResult
                  fieldMatches <- traverse
                    (\field -> isBuiltinType bool (snd (I.unDom field)))
                    (I.telToList fields)
                  pure $
                    if length fieldMatches == 2 && and fieldMatches && resultMatches
                      then Just (argumentName, constructor)
                      else Nothing
                _ -> pure Nothing
        _ -> pure Nothing
    _ -> pure Nothing

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
        boolPairConstructor <- boolPairFunctionConstructor definition
        word64Arity <- word64FunctionArity definition
        isUnit <- hasUnitResult definition
        if isNat then do
          body <- toTreeless EagerEvaluation (defName definition)
          case (natArity, body) of
            (Just arity, Just term) -> do
              (resourceWitness, code, tokens) <-
                compileNatResourceFunction (defName definition) arity term
              pure (Just (CompiledDefinition
                (defName definition) (strictWord (defName definition) code) tokens
                (Just (NatResourceWitness resourceWitness))))
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
                [formalBoolean] (Just (BoolConstantWitness value))))
        else if maybe False (> 0) boolArity then do
          body <- toTreeless EagerEvaluation (defName definition)
          case (boolArity, body) of
            (Just arity, Just term) -> do
              (expression, code, tokens) <-
                compileBoolResourceFunction (defName definition) arity term
              pure (Just (CompiledDefinition
                (defName definition) (strictWord (defName definition) code) tokens
                (Just (BoolFunctionWitness arity expression))))
            (Just _, Nothing) -> pure Nothing
            _ -> unsupported "Bool function arity classification changed during compilation"
        else if word64Arity == Just 1 then do
          body <- toTreeless EagerEvaluation (defName definition)
          case body of
            Just term -> do
              (code, tokens) <-
                compileWord64IdentityFunction (defName definition) 1 term
              pure (Just (CompiledDefinition
                (defName definition) (strictWord (defName definition) code) tokens
                (Just Word64IdentityWitness)))
            Nothing -> pure Nothing
        else case word64Arity of
          Just 0 -> unsupported
            "closed Word64 literals need a proved two-limb numeric renderer"
          Just _ -> unsupported
            "Word64 functions currently require one live owned two-limb argument"
          Nothing -> case boolPairConstructor of
            Just (pairType, constructor) -> do
              body <- toTreeless EagerEvaluation (defName definition)
              case body of
                Nothing -> pure Nothing
                Just term -> do
                  (expression, code, tokens) <-
                    compileBoolPairFunction (defName definition) constructor term
                  pure (Just (CompiledDefinition
                    (defName definition) (strictWord (defName definition) code) tokens
                    (Just (BoolPairWitness pairType constructor expression))))
            Nothing ->
              if isUnit then do
                body <- toTreeless EagerEvaluation (defName definition)
                case body of
                  Nothing -> pure Nothing
                  Just term -> do
                    decodeUnitTerm term
                    pure (Just (CompiledDefinition
                      (defName definition) (strictWord (defName definition) (RSList [])) []
                      (Just UnitWitness)))
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

agdaNatOpTerm :: NatOp -> Text
agdaNatOpTerm NatAdd = "addOp"
agdaNatOpTerm NatMonus = "monusOp"
agdaNatOpTerm NatMultiply = "multiplyOp"

-- Reify the accepted Haskell resource tree into Agda's count-indexed AST.
-- The returned labels retain left-to-right environment order.
agdaNatResourceExprTerm :: NatResourceExpr -> (Text, [Int])
agdaNatResourceExprTerm (NatResourceLiteral value) =
  ("(resourceLiteral " <> T.pack (show value) <> ")", [])
agdaNatResourceExprTerm (NatResourceVariable index) =
  ("resourceArgument", [index])
agdaNatResourceExprTerm (NatResourceBinary operation left right) =
  agdaNatResourceBinaryTerm operation left right
agdaNatResourceExprTerm (NatResourceAddReversed left right) =
  agdaNatResourceBinaryTerm NatAdd left right

agdaNatResourceBinaryTerm
  :: NatOp -> NatResourceExpr -> NatResourceExpr -> (Text, [Int])
agdaNatResourceBinaryTerm operation left right =
  let (leftTerm, leftResources) = agdaNatResourceExprTerm left
      (rightTerm, rightResources) = agdaNatResourceExprTerm right
  in ( "(resourceBinary " <> agdaNatOpTerm operation <> " "
         <> leftTerm <> " " <> rightTerm <> ")"
     , leftResources ++ rightResources
     )

-- Treeless variables use de Bruijn order: index zero is the final source
-- argument.  Reify each resource label back into source argument order.
agdaNatResourceEnvironmentTerm :: Int -> [Int] -> Text
agdaNatResourceEnvironmentTerm arity =
  foldr
    (\index environment ->
      "(natEnvironmentCons argument"
        <> T.pack (show (arity - index - 1))
        <> " " <> environment <> ")")
    "natEnvironmentNil"

agdaNatResourceEvalTerm :: Int -> NatResourceExpr -> Text
agdaNatResourceEvalTerm arity expression =
  let (expressionTerm, variables) = agdaNatResourceExprTerm expression
      environment = agdaNatResourceEnvironmentTerm arity variables
  in "(evalNatResourceExpr " <> expressionTerm <> " (" <> environment <> "))"

-- The Forth data stack is top-first: final source argument is at the head.
-- Keep the caller's residual stack as an explicit untouched suffix.
agdaNatResourceInitialStackTerm :: Int -> Text -> Text
agdaNatResourceInitialStackTerm arity residualStack =
  case reverse [0 .. arity - 1] of
    [] -> residualStack
    indices ->
      T.intercalate " ∷ "
        [ "argument" <> T.pack (show index) | index <- indices ]
        <> " ∷ " <> residualStack

-- Prove source evaluation equals the resource-tree evaluator.  PAdd nodes
-- are the only Treeless nodes whose operand order differs from source order.
agdaNatResourceSourceProofTerm :: Int -> NatResourceExpr -> Text
agdaNatResourceSourceProofTerm _ expression
  | null (natResourceVariables expression) = "refl"
agdaNatResourceSourceProofTerm _ (NatResourceLiteral _) = "refl"
agdaNatResourceSourceProofTerm _ (NatResourceVariable _) = "refl"
agdaNatResourceSourceProofTerm arity (NatResourceBinary operation left right) =
  "(cong₂ (applyNatOp " <> agdaNatOpTerm operation <> ") "
    <> agdaNatResourceSourceProofTerm arity left <> " "
    <> agdaNatResourceSourceProofTerm arity right <> ")"
agdaNatResourceSourceProofTerm arity (NatResourceAddReversed left right)
  | null (natResourceVariables left) || null (natResourceVariables right) =
      "(cong₂ (applyNatOp addOp) "
        <> agdaNatResourceSourceProofTerm arity left <> " "
        <> agdaNatResourceSourceProofTerm arity right <> ")"
  | otherwise =
      "(trans (cong₂ (applyNatOp addOp) "
        <> agdaNatResourceSourceProofTerm arity right <> " "
        <> agdaNatResourceSourceProofTerm arity left <> ") "
        <> "(natAdd-comm "
        <> agdaNatResourceEvalTerm arity right <> " "
        <> agdaNatResourceEvalTerm arity left <> "))"

agdaNatIndexTerm :: Int -> Text
agdaNatIndexTerm arity =
  T.concat (replicate arity "(suc ") <> "zero" <> T.replicate arity ")"

formalNatTokenTerm :: FormalToken -> Text
formalNatTokenTerm (FormalPushLiteral value) =
  "(pushLiteral " <> T.pack (show value) <> ")"
formalNatTokenTerm FormalAddWord = "addWord"
formalNatTokenTerm FormalMonusWord = "monusWord"
formalNatTokenTerm FormalMultiplyWord = "multiplyWord"
formalNatTokenTerm FormalSwapWord = "swapWord"
formalNatTokenTerm (FormalRollWord depth) =
  "(rollWord " <> T.pack (show depth) <> ")"
formalNatTokenTerm token =
  error ("non-Nat token in unary Nat proof certificate: " ++ show token)

formalNatTokenList :: [FormalToken] -> Text
formalNatTokenList [] = "[]"
formalNatTokenList tokens =
  T.intercalate " ∷ " (map formalNatTokenTerm tokens) <> " ∷ []"

formalBoolTokenTerm :: FormalToken -> Text
formalBoolTokenTerm FormalTrueWord = "pushTrueToken"
formalBoolTokenTerm FormalFalseWord = "pushFalseToken"
formalBoolTokenTerm FormalSwapWord = "boolSwapToken"
formalBoolTokenTerm (FormalIf whenTrue whenFalse) =
  "(boolIfToken (" <> formalBoolTokenList whenTrue <> ") ("
    <> formalBoolTokenList whenFalse <> "))"
formalBoolTokenTerm token =
  error ("non-Boolean token in Bool proof certificate: " ++ show token)

formalBoolTokenList :: [FormalToken] -> Text
formalBoolTokenList [] = "[]"
formalBoolTokenList tokens =
  T.intercalate " ∷ " (map formalBoolTokenTerm tokens) <> " ∷ []"

sourceAgdaName :: TopLevelModuleName -> QName -> Text
sourceAgdaName sourceModule name =
  T.pack (prettyShow sourceModule) <> "." <>
    T.pack (prettyShow (qnameName name))


compilerWitnessCertificate
  :: TopLevelModuleName
  -> Int
  -> CompiledDefinition
  -> [Text]
compilerWitnessCertificate sourceModule position definition =
  case compiledWitness definition of
    Just (NatResourceWitness _) -> []
    Just (BoolConstantWitness value) ->
      boolConstantCertificate sourceModule suffix definition value
    Just (BoolFunctionWitness arity expression) ->
      boolFunctionCertificate sourceModule suffix definition arity expression
    Just (BoolPairWitness pairType constructor expression) ->
      boolPairCertificate sourceModule suffix definition pairType constructor expression
    Just UnitWitness ->
      unitCertificate sourceModule suffix definition
    Just Word64IdentityWitness ->
      word64Certificate sourceModule suffix definition
    Nothing ->
      error ("compiled definition has no semantic witness: " ++ prettyShow (compiledName definition))
  where
    suffix = T.pack (show position)

boolConstantCertificate
  :: TopLevelModuleName
  -> Text
  -> CompiledDefinition
  -> Bool
  -> [Text]
boolConstantCertificate sourceModule suffix definition value =
  [ proofName <> " : BoolProof"
  , proofName <> " = " <> proofTerm
  , ""
  , derivationName <> " : MALLP [] (just boolFormula)"
  , derivationName <> " = boolProofDerivation " <> proofName
  , ""
  , compilerTokensName <> " : List BoolForthToken"
  , compilerTokensName <> " = " <> formalBoolTokenList (compiledTokens definition)
  , ""
  , modelTokensName <> " : List BoolForthToken"
  , modelTokensName <> " = renderBoolCode (compileBoolProof " <> proofName <> ")"
  , ""
  , tokenCorrespondenceName <> " : " <> compilerTokensName <> " ≡ " <> modelTokensName
  , tokenCorrespondenceName <> " = refl"
  , ""
  , textCorrespondenceName <> " :"
  , "  mapBoolForthTokensAsText " <> compilerTokensName
      <> " ≡ " <> formalTokenList (compiledTokens definition)
  , textCorrespondenceName <> " = refl"
  , ""
  , executionName <> " :"
  , "  (residualStack : List Bool) →"
  , "  execBoolTokens " <> compilerTokensName
      <> " residualStack ≡ just (interpretBoolProof " <> proofName <> " ∷ residualStack)"
  , executionName <> " residualStack ="
  , "  trans (cong (λ tokens → execBoolTokens tokens residualStack) "
      <> tokenCorrespondenceName <> ")"
  , "    (boolProofForthSound " <> proofName <> " residualStack)"
  , ""
  , sourceSemanticsName <> " : " <> sourceFunction <> " ≡ " <> boolLiteral
  , sourceSemanticsName <> " = refl"
  , ""
  , sourceSoundName <> " :"
  , "  (residualStack : List Bool) →"
  , "  execBoolTokens " <> compilerTokensName
      <> " residualStack ≡ just (" <> sourceFunction <> " ∷ residualStack)"
  , sourceSoundName <> " residualStack ="
  , "  trans (" <> executionName <> " residualStack)"
  , "    (cong (λ result → just (result ∷ residualStack))"
  , "      (sym " <> sourceSemanticsName <> "))"
  , ""
  ]
  where
    proofName = "boolConstantProof" <> suffix
    derivationName = "boolConstantMALLP" <> suffix
    compilerTokensName = "boolConstantCompilerTokens" <> suffix
    modelTokensName = "boolConstantModelTokens" <> suffix
    tokenCorrespondenceName = "boolConstantTokenCorrespondence" <> suffix
    textCorrespondenceName = "boolConstantTextCorrespondence" <> suffix
    executionName = "boolConstantExecution" <> suffix
    sourceSemanticsName = "boolConstantSourceSemantics" <> suffix
    sourceSoundName = "boolConstantSourceSound" <> suffix
    proofTerm = if value then "boolTrueProof" else "boolFalseProof"
    boolLiteral = if value then "true" else "false"
    sourceFunction = sourceAgdaName sourceModule (compiledName definition)

boolFunctionCertificate
  :: TopLevelModuleName
  -> Text
  -> CompiledDefinition
  -> Int
  -> BoolExpr
  -> [Text]
boolFunctionCertificate sourceModule suffix definition arity expression =
  case (arity, expression) of
    (1, BoolVariable 0) ->
      emitBoolFunction
        "dualPos boolFormula ∷ []" "boolIdentityMALLP"
        "renderBoolCode (boolIdentity {Γ = boolCell ∷ []})"
        ["argument0"] "argument0" "argument0" "refl"
        ["sourceSemantics argument0 = refl"]
    (1, BoolConditional (BoolVariable 0) (BoolLiteral False) (BoolLiteral True)) ->
      emitBoolFunction
        "dualPos boolFormula ∷ []" "invertBoolMALLP"
        "renderBoolCode (compileBoolRuntimeCase invertBoolProof)"
        ["argument0"] "argument0" "boolNot argument0"
        "invertBoolRuntimeMALLP-forth-sound argument0 residualStack"
        [ "sourceSemantics true = refl"
        , "sourceSemantics false = refl"
        ]
    (2, BoolConditional (BoolVariable 1) (BoolVariable 0) (BoolVariable 0)) ->
      emitBoolFunction
        "dualPos boolFormula ∷ dualPos boolFormula ∷ []"
        "boolCaseWithResidualMALLP"
        "renderBoolCode compileBoolCaseWithResidual"
        ["argument0", "argument1"]
        "argument1" "argument1"
        "boolCaseWithResidualMALLP-forth-sound argument0 argument1 residualStack"
        [ "sourceSemantics true argument1 = refl"
        , "sourceSemantics false argument1 = refl"
        ]
    _ -> error ("uncertified Bool expression reached certificate generation: " ++ show expression)
  where
    emitBoolFunction contextTerm derivationTerm modelTerm argumentNames
      stackArguments expectedResult modelProof sourceSemanticsClauses =
        let sourceFunction = sourceAgdaName sourceModule (compiledName definition)
            derivationName = "boolFunctionMALLP" <> suffix
            compilerTokensName = "boolFunctionCompilerTokens" <> suffix
            modelTokensName = "boolFunctionModelTokens" <> suffix
            tokenCorrespondenceName = "boolFunctionTokenCorrespondence" <> suffix
            textCorrespondenceName = "boolFunctionTextCorrespondence" <> suffix
            executionName = "boolFunctionExecution" <> suffix
            sourceSemanticsName = "boolFunctionSourceSemantics" <> suffix
            sourceSoundName = "boolFunctionSourceSound" <> suffix
            argumentBinders =
              T.intercalate " → "
                [ "(" <> argument <> " : Bool)" | argument <- argumentNames ]
            sourceCall = T.unwords (sourceFunction : argumentNames)
            stackTerm =
              T.intercalate " ∷ " stackArguments <> " ∷ residualStack"
            argumentClause = T.unwords argumentNames
            sourceSemanticsType =
              T.intercalate " → "
                ([ "(" <> argument <> " : Bool)" | argument <- argumentNames ]
                  ++ [ sourceCall <> " ≡ " <> expectedResult ])
            executionType =
              (if null argumentNames then [] else [ "  " <> argumentBinders <> " →" ])
                ++ [ "  (residualStack : List Bool) →"
                   , "  execBoolTokens " <> compilerTokensName
                       <> " (" <> stackTerm <> ") ≡"
                   , "  just (" <> expectedResult <> " ∷ residualStack)"
                   ]
            sourceSoundBody =
              [ sourceSoundName <> " " <> argumentClause <> " residualStack ="
              , "  trans (" <> executionName <> " " <> argumentClause <> " residualStack)"
              , "    (cong (λ result → just (result ∷ residualStack))"
              , "      (sym (" <> sourceSemanticsName <> " " <> argumentClause <> ")))"
              ]
        in
          [ derivationName <> " : MALLP (" <> contextTerm <> ") (just boolFormula)"
          , derivationName <> " = " <> derivationTerm
          , ""
          , compilerTokensName <> " : List BoolForthToken"
          , compilerTokensName <> " = " <> formalBoolTokenList (compiledTokens definition)
          , ""
          , modelTokensName <> " : List BoolForthToken"
          , modelTokensName <> " = " <> modelTerm
          , ""
          , tokenCorrespondenceName <> " : " <> compilerTokensName <> " ≡ " <> modelTokensName
          , tokenCorrespondenceName <> " = refl"
          , ""
          , textCorrespondenceName <> " :"
          , "  mapBoolForthTokensAsText " <> compilerTokensName
              <> " ≡ " <> formalTokenList (compiledTokens definition)
          , textCorrespondenceName <> " = refl"
          , ""
          , executionName <> " :"
          ] ++ executionType ++
          [ executionName <> " " <> argumentClause <> " residualStack ="
          , "  trans (cong (λ tokens → execBoolTokens tokens (" <> stackTerm <> "))"
              <> " " <> tokenCorrespondenceName <> ")"
          , "    (" <> modelProof <> ")"
          , ""
          , sourceSemanticsName <> " : " <> sourceSemanticsType
          ] ++ sourceSemanticsClauses ++
          [ ""
          , sourceSoundName <> " :"
          ] ++ executionType ++ sourceSoundBody ++
          [ "" ]

boolPairCertificate
  :: TopLevelModuleName
  -> Text
  -> CompiledDefinition
  -> QName
  -> QName
  -> BoolPairExpr
  -> [Text]
boolPairCertificate sourceModule suffix definition pairType constructor expression =
  let sourceFunction = sourceAgdaName sourceModule (compiledName definition)
      pairTypeName = sourceAgdaName sourceModule pairType
      constructorName = sourceAgdaName sourceModule constructor
      isSwap = expression == BoolPairFields 0 1
      derivationTerm = if isSwap then "boolPairSwapMALLP" else "boolPairIdentityMALLP"
      modelTerm =
        if isSwap
          then "renderBoolCode compileBoolPairSwap"
          else "renderBoolCode (boolIdentity {Γ = boolCell ∷ boolCell ∷ []})"
      modelProof =
        if isSwap
          then "boolPairSwapMALLP-forth-sound first second residualStack"
          else "boolPairIdentityForthSound second first residualStack"
      outputFirst = if isSwap then "second" else "first"
      outputSecond = if isSwap then "first" else "second"
      derivationName = "boolPairMALLP" <> suffix
      compilerTokensName = "boolPairCompilerTokens" <> suffix
      modelTokensName = "boolPairModelTokens" <> suffix
      tokenCorrespondenceName = "boolPairTokenCorrespondence" <> suffix
      textCorrespondenceName = "boolPairTextCorrespondence" <> suffix
      stackName = "boolPairStack" <> suffix
      sourceSemanticsName = "boolPairSourceSemantics" <> suffix
      executionName = "boolPairExecution" <> suffix
      sourceSoundName = "boolPairSourceSound" <> suffix
  in
    [ stackName <> " : " <> pairTypeName <> " → List Bool → List Bool"
    , stackName <> " (" <> constructorName <> " first second) residualStack ="
    , "  second ∷ first ∷ residualStack"
    , ""
    , derivationName <> " : MALLP (dualPos boolPairFormula ∷ []) (just boolPairFormula)"
    , derivationName <> " = " <> derivationTerm
    , ""
    , compilerTokensName <> " : List BoolForthToken"
    , compilerTokensName <> " = " <> formalBoolTokenList (compiledTokens definition)
    , ""
    , modelTokensName <> " : List BoolForthToken"
    , modelTokensName <> " = " <> modelTerm
    , ""
    , tokenCorrespondenceName <> " : " <> compilerTokensName <> " ≡ " <> modelTokensName
    , tokenCorrespondenceName <> " = refl"
    , ""
    , textCorrespondenceName <> " :"
    , "  mapBoolForthTokensAsText " <> compilerTokensName
        <> " ≡ " <> formalTokenList (compiledTokens definition)
    , textCorrespondenceName <> " = refl"
    , ""
    , sourceSemanticsName <> " :"
    , "  (first second : Bool) →"
    , "  " <> sourceFunction <> " (" <> constructorName <> " first second) ≡"
    , "    " <> constructorName <> " " <> outputFirst <> " " <> outputSecond
    , sourceSemanticsName <> " first second = refl"
    , ""
    , executionName <> " :"
    , "  (first second : Bool) →"
    , "  (residualStack : List Bool) →"
    , "  execBoolTokens " <> compilerTokensName
        <> " (" <> stackName <> " (" <> constructorName
        <> " first second) residualStack) ≡"
    , "  just (" <> outputFirst <> " ∷ " <> outputSecond <> " ∷ residualStack)"
    , executionName <> " first second residualStack ="
    , "  trans (cong (λ tokens → execBoolTokens tokens ("
        <> stackName <> " (" <> constructorName
        <> " first second) residualStack)) " <> tokenCorrespondenceName <> ")"
    , "    (" <> modelProof <> ")"
    , ""
    , sourceSoundName <> " :"
    , "  (first second : Bool) →"
    , "  (residualStack : List Bool) →"
    , "  execBoolTokens " <> compilerTokensName
        <> " (" <> stackName <> " (" <> constructorName
        <> " first second) residualStack) ≡"
    , "  just (" <> stackName <> " (" <> sourceFunction
        <> " (" <> constructorName <> " first second)) residualStack)"
    , sourceSoundName <> " first second residualStack ="
    , "  trans (" <> executionName <> " first second residualStack)"
    , "    (cong (λ pairValue → just (" <> stackName
        <> " pairValue residualStack))"
    , "      (sym (" <> sourceSemanticsName <> " first second)))"
    , ""
    ]

unitCertificate
  :: TopLevelModuleName
  -> Text
  -> CompiledDefinition
  -> [Text]
unitCertificate sourceModule suffix definition =
  [ derivationName <> " : MALLP [] (just one⁺)"
  , derivationName <> " = unitOneProof"
  , ""
  , compilerTokensName <> " : List ForthToken"
  , compilerTokensName <> " = " <> formalNatTokenList (compiledTokens definition)
  , ""
  , modelTokensName <> " : List ForthToken"
  , modelTokensName <> " = compileUnitProof unitOneProof"
  , ""
  , tokenCorrespondenceName <> " : " <> compilerTokensName <> " ≡ " <> modelTokensName
  , tokenCorrespondenceName <> " = refl"
  , ""
  , sourceSemanticsName <> " : " <> sourceFunction <> " ≡ tt"
  , sourceSemanticsName <> " = refl"
  , ""
  , executionName <> " : (residualStack : List Nat) →"
  , "  execTokens " <> compilerTokensName <> " residualStack ≡ just residualStack"
  , executionName <> " residualStack ="
  , "  trans (cong (λ tokens → execTokens tokens residualStack) "
      <> tokenCorrespondenceName <> ") refl"
  , ""
  ]
  where
    derivationName = "unitMALLP" <> suffix
    compilerTokensName = "unitCompilerTokens" <> suffix
    modelTokensName = "unitModelTokens" <> suffix
    tokenCorrespondenceName = "unitTokenCorrespondence" <> suffix
    sourceSemanticsName = "unitSourceSemantics" <> suffix
    executionName = "unitExecution" <> suffix
    sourceFunction = sourceAgdaName sourceModule (compiledName definition)

word64Certificate
  :: TopLevelModuleName
  -> Text
  -> CompiledDefinition
  -> [Text]
word64Certificate sourceModule suffix definition =
  [ derivationName <> " :"
  , "  MALLP (dualPos word64Formula ∷ []) (just word64Formula)"
  , derivationName <> " = word64IdentityMALLP"
  , ""
  , compilerTokensName <> " : List ForthToken"
  , compilerTokensName <> " = " <> formalNatTokenList (compiledTokens definition)
  , ""
  , tokenCorrespondenceName <> " : " <> compilerTokensName <> " ≡ word64IdentityTokens"
  , tokenCorrespondenceName <> " = refl"
  , ""
  , sourceSemanticsName <> " :"
  , "  (word : Word64) → " <> sourceFunction <> " word ≡ word"
  , sourceSemanticsName <> " word = refl"
  , ""
  , representationName <> " :"
  , "  {word : Word64} →"
  , "  (representation : Word64Representation word) → Word64Representation word"
  , representationName <> " representation ="
  , "  word64IdentityPreservesRepresentation representation"
  , ""
  , executionName <> " :"
  , "  {word : Word64} →"
  , "  (representation : Word64Representation word) →"
  , "  (residualStack : List Nat) →"
  , "  execTokens " <> compilerTokensName
      <> " (lowLimb representation ∷ highLimb representation ∷ residualStack) ≡"
  , "  just (lowLimb representation ∷ highLimb representation ∷ residualStack)"
  , executionName <> " representation residualStack ="
  , "  trans (cong (λ tokens → execTokens tokens"
      <> " (lowLimb representation ∷ highLimb representation ∷ residualStack))"
      <> " " <> tokenCorrespondenceName <> ")"
  , "    (word64IdentityForthSound representation residualStack)"
  , ""
  ]
  where
    derivationName = "word64IdentityMALLPGenerated" <> suffix
    compilerTokensName = "word64IdentityCompilerTokens" <> suffix
    tokenCorrespondenceName = "word64IdentityTokenCorrespondence" <> suffix
    sourceSemanticsName = "word64IdentitySourceSemantics" <> suffix
    representationName = "word64IdentityRepresentationPreserved" <> suffix
    executionName = "word64IdentityExecution" <> suffix
    sourceFunction = sourceAgdaName sourceModule (compiledName definition)

rendererCertificate :: TopLevelModuleName -> [CompiledDefinition] -> Text
rendererCertificate sourceModule definitions = T.unlines $
  [ "{-# OPTIONS --with-K --rewriting --confluence-check --lossy-unification --exact-split --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections #-}"
  , "module MALLPEmittedRenderer where"
  , ""
  , "import " <> T.pack (prettyShow sourceModule)
  , "open import Agda.Builtin.String using (String)"
  , "open import Agda.Builtin.List using (List; []; _∷_)"
  , "open import Agda.Builtin.Equality using (_≡_; refl)"
  , "open import MALLPForth using"
  , "  (ForthTextToken; textPushLiteral; textAddWord; textMonusWord; textMultiplyWord;"
  , "   textSwapWord; textRollWord; textTrueWord; textFalseWord; textIf; renderForthWordText;"
  , "   mapBoolForthTokensAsText; renderBoolCode; compileBoolCaseWithResidual;"
  , "   compileBoolPairSwap; Nat; zero; suc; just; NatOp; addOp; monusOp; multiplyOp;"
  , "   ForthToken; pushLiteral; addWord; monusWord; multiplyWord; swapWord; rollWord;"
  , "   MALLPNatTheory; natContext; natFormula; natEnvironmentCons; natEnvironmentNil; interpretMALLPNatProof;"
  , "   evalNatResourceExpr;"
  , "   NatResourceExpr; resourceLiteral; resourceArgument; resourceBinary; natResourceProof; natResource-proof-derivation; natResourceProof-adequate;"
  , "   execTokens; NatStackBounded; execBoundedTokens; execBoundedTokens-preserves;"
  , "   BoundedForthTrace; execBoundedTokens-trace; cong; cong₂; trans; sym;"
  , "   applyNatOp; natAdd-comm)"
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
    ++ concat
    [ let
        { expressionName = "natResourceExpression" <> index
        ; derivationName = "natResourceDerivation" <> index
        ; compilerTokensName = "natResourceCompilerTokens" <> index
        ; executionName = "natResourceCompilerExecution" <> index
        ; sourceSoundName = "natResourceSourceSound" <> index
        ; boundedSoundName = "natResourceBoundedSourceSound" <> index
        ; boundedTraceName = "natResourceBoundedTrace" <> index
        ; sourceProofName = "sourceNatResourceSemantics" <> index
        ; arity = length (natResourceVariables expression)
        ; argumentNames =
            [ "argument" <> T.pack (show argument)
            | argument <- [0 .. arity - 1]
            ]
        ; argumentBinders =
            T.intercalate " → "
              [ "(" <> argument <> " : Nat)" | argument <- argumentNames ]
        ; sourceFunction =
            T.pack (prettyShow sourceModule) <> "." <>
              T.pack (prettyShow (qnameName (compiledName definition)))
        ; sourceCall = T.unwords (sourceFunction : argumentNames)
        ; resourceEnvironment =
            agdaNatResourceEnvironmentTerm arity (natResourceVariables expression)
        ; initialStack = agdaNatResourceInitialStackTerm arity "residualStack"
        ; sourceProofTerm =
            agdaNatResourceSourceProofTerm arity expression
        ; sourceProofArguments = T.unwords (sourceProofName : argumentNames)
        ; executionArguments = T.unwords (executionName : argumentNames)
        ; sourceSoundArguments = T.unwords (sourceSoundName : argumentNames)
        ; boundedSoundArguments =
            T.unwords (boundedSoundName : ("bound" : argumentNames))
        ; boundedTraceArguments =
            T.unwords (boundedTraceName : ("bound" : argumentNames))
        ; resourceTerm = fst (agdaNatResourceExprTerm expression)
        ; sourceTypeLines =
            (if null argumentNames then [] else [ "  " <> argumentBinders <> " →" ])
              ++ [ "    " <> sourceCall <> " ≡"
                 , "      interpretMALLPNatProof (natResourceProof " <> expressionName <> ")"
                 , "        (" <> resourceEnvironment <> ")"
                 ]
        }
      in
        [ expressionName <> " : NatResourceExpr " <> agdaNatIndexTerm arity
        , expressionName <> " = " <> resourceTerm
        , ""
        , derivationName <> " : MALLPNatTheory (natContext "
            <> agdaNatIndexTerm arity <> ") (just natFormula)"
        , derivationName <> " = natResource-proof-derivation " <> expressionName
        , ""
        , compilerTokensName <> " : List ForthToken"
        , compilerTokensName <> " = " <> formalNatTokenList (compiledTokens definition)
        , ""
        , executionName <> " :"
        ] ++
        (if null argumentNames then [] else [ "  " <> argumentBinders <> " →" ]) ++
        [ "  (residualStack : List Nat) →"
        , "  execTokens " <> compilerTokensName
        , "    (" <> initialStack <> ") ≡"
        , "  just (interpretMALLPNatProof (natResourceProof " <> expressionName <> ")"
        , "    (" <> resourceEnvironment <> ") ∷ residualStack)"
        , executionArguments <> " residualStack ="
        , "  trans refl"
        , "    (cong (λ value → just (value ∷ residualStack))"
        , "      (sym (natResourceProof-adequate " <> expressionName
            <> " (" <> resourceEnvironment <> "))))"
        , ""
        , sourceProofName <> " :"
        ] ++ sourceTypeLines ++
        [ sourceProofArguments <> " ="
        , "  trans (" <> sourceProofTerm <> ")"
        , "    (sym (natResourceProof-adequate " <> expressionName
            <> " (" <> resourceEnvironment <> ")))"
        , ""
        , sourceSoundName <> " :"
        ] ++
        (if null argumentNames then [] else [ "  " <> argumentBinders <> " →" ]) ++
        [ "  (residualStack : List Nat) →"
        , "  execTokens " <> compilerTokensName
        , "    (" <> initialStack <> ") ≡"
        , "  just (" <> sourceCall <> " ∷ residualStack)"
        , sourceSoundArguments <> " residualStack ="
        , "  trans (" <> executionArguments <> " residualStack)"
        , "    (cong (λ value → just (value ∷ residualStack))"
        , "      (sym (" <> sourceProofArguments <> ")))"
        , ""
        , boundedSoundName <> " :"
        , "  (bound : Nat) →"
        ] ++
        (if null argumentNames then [] else [ "  " <> argumentBinders <> " →" ]) ++
        [ "  (residualStack : List Nat) →"
        , "  (inputStackBounded : NatStackBounded bound (" <> initialStack <> ")) →"
        , "  (result : List Nat) →"
        , "  execBoundedTokens bound " <> compilerTokensName
        , "    (" <> initialStack <> ") ≡ just result →"
        , "  result ≡ " <> sourceCall <> " ∷ residualStack"
        , boundedSoundArguments <> " residualStack inputStackBounded result boundedExecution ="
        , "  execBoundedTokens-preserves bound " <> compilerTokensName
        , "    (" <> initialStack <> ") result ("
            <> sourceCall <> " ∷ residualStack)"
        , "    boundedExecution (" <> sourceSoundArguments <> " residualStack)"
        , ""
        , boundedTraceName <> " :"
        , "  (bound : Nat) →"
        ] ++
        (if null argumentNames then [] else [ "  " <> argumentBinders <> " →" ]) ++
        [ "  (residualStack : List Nat) →"
        , "  (inputStackBounded : NatStackBounded bound (" <> initialStack <> ")) →"
        , "  (result : List Nat) →"
        , "  execBoundedTokens bound " <> compilerTokensName
        , "    (" <> initialStack <> ") ≡ just result →"
        , "  BoundedForthTrace bound " <> compilerTokensName
        , "    (" <> initialStack <> ") result"
        , boundedTraceArguments <> " residualStack inputStackBounded result boundedExecution ="
        , "  execBoundedTokens-trace bound " <> compilerTokensName
        , "    (" <> initialStack <> ") result inputStackBounded boundedExecution"
        , ""
        ]
      | (index, definition, expression) <-
          [ (T.pack (show position), definition, expression)
          | (position, definition) <- zip [0 :: Int ..] definitions
          , Just (NatResourceWitness expression) <- [compiledWitness definition]
          ]
    ]
    ++ concat
    [ [ "chooseBoolCompilerTokens : List ForthTextToken"
      , "chooseBoolCompilerTokens = " <> formalTokenList (compiledTokens definition)
      , ""
      , "chooseBoolMALLPTokens : List ForthTextToken"
      , "chooseBoolMALLPTokens = mapBoolForthTokensAsText"
          <> " (renderBoolCode compileBoolCaseWithResidual)"
      , ""
      , "chooseBoolTokenCorrespondence :"
      , "  chooseBoolCompilerTokens ≡ chooseBoolMALLPTokens"
      , "chooseBoolTokenCorrespondence = refl"
      , ""
      ]
    | definition <- definitions
    , safeForthName (compiledName definition) == "chooseBool"
    ] ++ concat
    [ [ "swapBoolPairCompilerTokens : List ForthTextToken"
      , "swapBoolPairCompilerTokens = " <> formalTokenList (compiledTokens definition)
      , ""
      , "swapBoolPairMALLPTokens : List ForthTextToken"
      , "swapBoolPairMALLPTokens = mapBoolForthTokensAsText"
          <> " (renderBoolCode compileBoolPairSwap)"
      , ""
      , "swapBoolPairTokenCorrespondence :"
      , "  swapBoolPairCompilerTokens ≡ swapBoolPairMALLPTokens"
      , "swapBoolPairTokenCorrespondence = refl"
      , ""
      ]
    | definition <- definitions
    , safeForthName (compiledName definition) == "swapBoolPair"
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
    TIO.writeFile "MALLPEmittedRenderer.agda" (rendererCertificate moduleName definitions)

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
