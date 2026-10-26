module CheckedScalar where

open import Agda.Builtin.Nat using (Nat; _+_)

scalarAdd : Nat → Nat → Nat
scalarAdd left right = left + right

scalarAnswer : Nat
scalarAnswer = scalarAdd 20 5
