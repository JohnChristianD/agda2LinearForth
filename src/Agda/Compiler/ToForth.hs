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
decodeNatTerm :: [NatExpr] -> TTerm -> TCM NatExpr
decodeNatTerm environment term = do
  let (headTerm, args) = tAppView term
  case headTerm of
    TLit (LitNat n)
      | null args && n >= 0 -> pure (NatLiteral (fromInteger n))
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
              decodeNatTerm (value : environment) body
    TPrim primitive -> do
      operands <- traverse (decodeNatTerm environment) args
      either unsupported pure (decodeNatPrimitive primitive operands)
    TDef name -> do
      plusName <- getBuiltinName builtinNatPlus
      minusName <- getBuiltinName builtinNatMinus
      operands <- traverse (decodeNatTerm environment) args
      case operands of
        [left, right] | Just name == plusName ->
          pure (NatBinary NatAdd left right)
        [left, right] | Just name == minusName ->
          pure (NatBinary NatMonus left right)
        _ -> unsupported "user functions and non-binary definitions are outside the closed Nat fragment"
    TCoerce inner
      | null args -> decodeNatTerm environment inner
    _ -> unsupported ("Treeless term is outside the closed Nat fragment: " ++ show headTerm)

renderNatExpr :: NatExpr -> FthForm
renderNatExpr (NatLiteral n) =
  RSAtom $ T.concat ["s\" ", T.pack (show n), "\" MALLP-PARSE-NAT"]
renderNatExpr (NatBinary operation left right) =
  let word = case operation of
        NatAdd -> "MALLP-NAT-ADD"
        NatMonus -> "MALLP-NAT-MONUS"
        NatMultiply -> "MALLP-NAT-MUL"
  in RSList [renderNatExpr left, renderNatExpr right, RSAtom word]

hasNatResult :: Definition -> TCM Bool
hasNatResult definition = do
  natName <- getBuiltinName builtinNat
  TelV _ resultType <- telView (defType definition)
  reducedResultType <- reduce resultType
  pure $ case (natName, I.unEl reducedResultType) of
    (Just expected, I.Def actual []) -> expected == actual
    _ -> False

compileDefinition :: Definition -> TCM (Maybe FthForm)
compileDefinition definition
  | defNoCompilation definition || not (usableModality (getModality definition)) =
      pure Nothing
  | otherwise = case theDef definition of
      Function{} -> do
        isNat <- hasNatResult definition
        if not isNat
          then pure Nothing
          else do
            body <- toTreeless EagerEvaluation (defName definition)
            case body of
              Nothing -> pure Nothing
              Just term -> do
                expression <- decodeNatTerm [] term
                pure (Just (strictWord (defName definition) (renderNatExpr expression)))
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
