module Agda.Compiler.NatCore
  ( NatOp(..)
  , NatExpr(..)
  , decodeNatPrimitive
  ) where

import Agda.Syntax.Treeless (TPrim(..))

data NatOp
  = NatAdd
  | NatMonus
  | NatMultiply
  deriving (Eq, Show)

data NatExpr
  = NatLiteral Integer
  | NatBinary NatOp NatExpr NatExpr
  deriving (Eq, Show)

decodeNatPrimitive :: TPrim -> [NatExpr] -> Either String NatExpr
decodeNatPrimitive PAdd [left, right] =
  Right (NatBinary NatAdd left right)
decodeNatPrimitive PSub [left, right] =
  Right (NatBinary NatMonus left right)
decodeNatPrimitive PMul [left, right] =
  Right (NatBinary NatMultiply left right)
decodeNatPrimitive primitive _ =
  Left ("unsupported Nat primitive or arity: " ++ show primitive)
