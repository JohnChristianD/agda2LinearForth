module CheckedScalar where

open import Agda.Builtin.Nat using (Nat; _+_; _∸_; _*_)

scalarAdd : Nat → Nat → Nat
scalarAdd left right = left + right

scalarSubtract : Nat → Nat → Nat
scalarSubtract left right = left ∸ right

scalarMultiply : Nat → Nat → Nat
scalarMultiply left right = left * right

scalarAddAnswer : Nat
scalarAddAnswer = scalarAdd 20 5

scalarSubtractAnswer : Nat
scalarSubtractAnswer = scalarSubtract 20 5

scalarMultiplyAnswer : Nat
scalarMultiplyAnswer = scalarMultiply 6 7
