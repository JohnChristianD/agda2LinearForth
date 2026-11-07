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

data NatExpr
  = NatLiteral Natural
  | NatBinary NatOp NatExpr NatExpr
  deriving (Eq, Show)

data NatLinearExpr
  = NatArgument
  | NatLinearLeft NatOp NatLinearExpr NatExpr
  | NatLinearRight NatOp NatExpr NatLinearExpr
  deriving (Eq, Show)

data NatTerm
  = NatClosed NatExpr
  | NatOpen NatLinearExpr
  deriving (Eq, Show)

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
      case operands of
        [left, right] ->
          either unsupported pure (combineNatTerms (case primitive of
            PAdd -> NatAdd
            PMul -> NatMultiply
            _ -> NatAdd) left right)
            >>= \result -> case primitive of
              PAdd -> pure result
              PMul -> pure result
              PSub -> unsupported "PSub is signed integer subtraction; Nat monus is lowered only from builtin NatMinus"
              _ -> unsupported ("unsupported Nat primitive: " ++ show primitive)
        _ -> unsupported ("unsupported Nat primitive arity: " ++ show primitive)
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

decodeBoolTerm :: TTerm -> TCM Bool
decodeBoolTerm term = do
  trueName <- getBuiltinName builtinTrue
  falseName <- getBuiltinName builtinFalse
  let (headTerm, args) = tAppView term
      matches expected actual = Just actual == expected
  case headTerm of
    TCon name
      | null args && matches trueName name -> pure True
      | null args && matches falseName name -> pure False
    TDef name
      | null args && matches trueName name -> pure True
      | null args && matches falseName name -> pure False
    TCoerce inner
      | null args -> decodeBoolTerm inner
    _ -> unsupported ("Treeless term is outside the closed Bool fragment: " ++ show headTerm)

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
      pure $ case (resultIsNat, argumentTypes) of
        (True, []) -> Just 0
        (True, [True]) -> Just 1
        _ -> Nothing

hasBoolResult :: Definition -> TCM Bool
hasBoolResult definition = do
  boolName <- getBuiltinName builtinBool
  TelV _ resultType <- telView (defType definition)
  reducedResultType <- reduce resultType
  pure $ case (boolName, I.unEl reducedResultType) of
    (Just expected, I.Def actual []) -> expected == actual
    _ -> False

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


compileDefinition :: Definition -> TCM (Maybe FthForm)
compileDefinition definition
  | defNoCompilation definition || not (usableModality (getModality definition)) =
      pure Nothing
  | otherwise = case theDef definition of
      Function{} -> do
        isNat <- hasNatResult definition
        natArity <- natFunctionArity definition
        isBool <- hasBoolResult definition
        isUnit <- hasUnitResult definition
        if isNat then do
          body <- toTreeless EagerEvaluation (defName definition)
          case (natArity, body) of
            (Just 0, Just term) -> do
              expression <- decodeNatTerm [] term
              case expression of
                NatClosed closed -> pure (Just (strictWord (defName definition) (renderNatExpr closed)))
                NatOpen _ -> unsupported "nullary Nat definition unexpectedly contains an open argument"
            (Just 1, Just term) -> do
              let (arity, bodyTerm) = tLamView term
              unless (arity == 1) $
                unsupported ("expected one Treeless lambda for unary Nat definition, received " ++ show arity)
              expression <- decodeNatTerm [NatOpen NatArgument] bodyTerm
              case expression of
                NatOpen linear -> pure (Just (strictWord (defName definition) (renderNatLinearExpr linear)))
                NatClosed _ -> unsupported "MALLP linearity violation: unary Nat argument is unused"
            (Nothing, _) -> unsupported "Nat definition must have zero arguments or one linear Nat argument"
            (_, Nothing) -> pure Nothing
            _ -> unsupported "unsupported Nat function arity"
        else if isBool then do
          body <- toTreeless EagerEvaluation (defName definition)
          case body of
            Nothing -> pure Nothing
            Just term -> do
              value <- decodeBoolTerm term
              let forthBoolean = if value then "TRUE" else "FALSE"
              pure (Just (strictWord (defName definition) (RSAtom forthBoolean)))
        else if isUnit then do
          body <- toTreeless EagerEvaluation (defName definition)
          case body of
            Nothing -> pure Nothing
            Just term -> do
              decodeUnitTerm term
              pure (Just (strictWord (defName definition) (RSList [])))
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

emitForthModule :: () -> () -> IsMain -> TopLevelModuleName -> [Maybe FthForm] -> TCM ()
emitForthModule _ _ _ moduleName definitions = do
  runtime <- IO.liftIO readStrictRuntime
  let body = T.intercalate "\n\n" (map renderForm (catMaybes definitions))
      output = T.pack runtime <> "\n" <> body <> "\n"
      filename = prettyShow (NE.last (moduleNameParts moduleName)) ++ ".fth"
  IO.liftIO $ TIO.writeFile filename output

backend :: Backend
backend = Backend backend'

backend' :: Backend' () () () () (Maybe FthForm)
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
