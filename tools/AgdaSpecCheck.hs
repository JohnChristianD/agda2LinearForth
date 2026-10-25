module Main where

import Agda.Main (runAgda)
import System.Environment (getArgs)

-- Forward CLI options to Agda's normal checker. The CI passes --no-libraries
-- and explicit module paths so Agda.Builtin remains available without a user library.
main :: IO ()
main = getArgs >>= runAgda
