module Agda.Compiler.NatCore
  ( NatOp(..)
  , NatExpr(..)
  , decodeNatPrimitive
  ) where

import Agda.Syntax.Treeless (TPrim(..))
import Numeric.Natural (Natural)

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
  Left "PSub is signed integer subtraction; Nat monus is lowered only from builtin NatMinus"
decodeNatPrimitive PMul [left, right] =
  Right (NatBinary NatMultiply left right)
decodeNatPrimitive primitive _ =
  Left ("unsupported Nat primitive or arity: " ++ show primitive)
