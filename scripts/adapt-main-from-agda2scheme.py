#!/usr/bin/env python3
"""Generate the Forth backend driver from the pinned Agda2Scheme driver.

Only backend-specific choices are changed here. The shared backend lifecycle,
options API, and module pipeline come from the fetched Agda2Scheme source.
"""
from pathlib import Path
import sys


def replace_once(source: str, old: str, new: str) -> str:
    count = source.count(old)
    if count != 1:
        raise SystemExit(
            f"expected exactly one {old!r} in Agda2Scheme Main.hs; found {count}"
        )
    return source.replace(old, new, 1)


def adapt(source: str) -> str:
    source = replace_once(
        source,
        "import Agda.Compiler.ToScheme",
        "import Agda.Compiler.ToForth",
    )
    source = source.replace("SchOptions", "FthOptions")
    source = source.replace("schFlags", "fthFlags")
    source = source.replace("schPreCompile", "fthPreCompile")
    source = source.replace("schPostModule", "fthPostModule")
    source = source.replace("schEvaluation", "fthEvaluation")
    source = replace_once(source, '"agda2scheme"', '"agda2forth"')

    start_token = "fthPostModule ::"
    end_token = "evaluationFlag ::"
    if source.count(start_token) != 1 or source.count(end_token) != 1:
        raise SystemExit("Agda2Scheme module-output hook shape changed; review the adapter.")
    start = source.index(start_token)
    end = source.index(end_token, start)
    if start >= end:
        raise SystemExit("Agda2Scheme post-module hook boundary is invalid.")

    target_hook = """fthPostModule :: FthOptions -> () -> IsMain -> TopLevelModuleName -> [(IsMain, Definition)] -> TCM ()
fthPostModule opts _ isMain modName defs = do
  forms <- runToForthM opts $ do
    preamble <- fthPreamble
    compiled <- catMaybes <$> traverse (toForth . snd) defs
    return $ preamble ++ compiled

  let defToText = encodeOne printer . fromRich
      modText   = T.append
        (T.pack getFLib)
        (makeDefines
          (T.intercalate "\\n\\n" $
            map (fixWord . defToText) forms))
      fileName  = prettyShow (NE.last $ moduleNameParts modName) ++ ".fth"

  liftIO $ T.writeFile fileName modText

  where
    printer :: SExprPrinter Text (SExpr Text)
    printer = basicPrint id

"""
    return source[:start] + target_hook + source[end:]


if len(sys.argv) != 2:
    raise SystemExit("usage: adapt-main-from-agda2scheme.py PATH_TO_SCHEME_Main.hs")
print(adapt(Path(sys.argv[1]).read_text()), end="")
