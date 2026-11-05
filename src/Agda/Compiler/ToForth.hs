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
import Agda.Utils.Either
import Agda.Utils.Functor
import Data.Char (isAlphaNum, isDigit)
import qualified Data.List.NonEmpty as NE
import Data.SCargot
import Data.SCargot.Repr
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Control.Monad.IO.Class as IO
import Data.Maybe (catMaybes)
import Paths_agda2forth (getDataFileName)

type FthForm = RichSExpr Text

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

compileNatTerm :: TTerm -> TCM FthForm
compileNatTerm term = do
  let (headTerm, args) = tAppView term
  case headTerm of
    TLit (LitNat n)
      | null args && n >= 0 ->
          pure $ RSAtom $ T.concat ["s\" ", T.pack (show n), "\" MALLP-PARSE-NAT"]
    TPrim primitive -> do
      operands <- traverse compileNatTerm args
      case (primitive, operands) of
        (PAdd, [left, right]) -> binary "MALLP-NAT-ADD" left right
        (PSub, [left, right]) -> binary "MALLP-NAT-MONUS" left right
        (PMul, [left, right]) -> binary "MALLP-NAT-MUL" left right
        _ -> unsupported ("unsupported Nat primitive or arity: " ++ show primitive)
    TDef name -> do
      plusName <- getBuiltinName builtinNatPlus
      minusName <- getBuiltinName builtinNatMinus
      operands <- traverse compileNatTerm args
      case operands of
        [left, right] | Just name == plusName ->
          binary "MALLP-NAT-ADD" left right
        [left, right] | Just name == minusName ->
          binary "MALLP-NAT-MONUS" left right
        _ -> unsupported "user functions and non-binary definitions are outside the closed Nat fragment"
    TCoerce inner
      | null args -> compileNatTerm inner
    _ -> unsupported ("Treeless term is outside the closed Nat fragment: " ++ show headTerm)
  where
    binary word left right = pure $ RSList [left, right, RSAtom word]

compileDefinition :: Definition -> TCM (Maybe FthForm)
compileDefinition definition
  | defNoCompilation definition || not (usableModality (getModality definition)) =
      pure Nothing
  | otherwise = case theDef definition of
      Function{} -> do
        body <- toTreeless EagerEvaluation (defName definition)
        case body of
          Nothing -> pure Nothing
          Just term -> Just . strictWord (defName definition) <$> compileNatTerm term
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

postModule :: () -> () -> IsMain -> TopLevelModuleName -> [Maybe FthForm] -> TCM ()
postModule _ _ _ moduleName definitions = do
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
  , postModule = postModule
  , backendVersion = Nothing
  , scopeCheckingSuffices = False
  , backendInteractTop = Nothing
  , backendInteractHole = Nothing
  , mayEraseType = \_ -> pure True
  }

main :: IO ()
main = runAgda [backend]
