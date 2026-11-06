module Main where

import Agda.Compiler.NatCore
import Agda.Syntax.Treeless (TPrim(..))
import Control.Monad (unless)
import System.Exit (die)

main :: IO ()
main = do
  assertEqual
    "PAdd decodes as Nat addition"
    (Right (NatBinary NatAdd (NatLiteral 2) (NatLiteral 3)))
    (decodeNatPrimitive PAdd [NatLiteral 2, NatLiteral 3])
  assertEqual
    "PMul decodes as Nat multiplication"
    (Right (NatBinary NatMultiply (NatLiteral 2) (NatLiteral 3)))
    (decodeNatPrimitive PMul [NatLiteral 2, NatLiteral 3])
  assert "PSub is rejected until signedness evidence is available"
    (case decodeNatPrimitive PSub [NatLiteral 5, NatLiteral 2] of
       Left _ -> True
       Right _ -> False)
  assert "wrong primitive arity is rejected"
    (case decodeNatPrimitive PAdd [NatLiteral 2] of
       Left _ -> True
       Right _ -> False)

assert :: String -> Bool -> IO ()
assert label ok = unless ok (die ("FAIL: " ++ label))

assertEqual :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEqual label expected actual =
  assert (label ++ "\n  expected: " ++ show expected ++ "\n  actual:   " ++ show actual)
    (expected == actual)
