module AgdaSpecCheck where

import Agda.Main (runAgda)

-- Run Agda's normal type checker, without loading any user standard library.
-- Agda.Builtin modules remain available from the Agda installation.
main :: IO ()
main = runAgda []
