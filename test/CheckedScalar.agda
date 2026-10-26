module CheckedScalar where

open import Agda.Builtin.Nat using (Nat; _+_; _<_; _-_)
open import Agda.Builtin.Bool using (Bool)

scalarAdd : Nat → Nat → Nat
scalarAdd left right = left + right

scalarAddAnswer : Nat
scalarAddAnswer = scalarAdd 20 5

scalarSubtract : Nat → Nat → Nat
scalarSubtract left right = left - right

scalarSubtractAnswer : Nat
scalarSubtractAnswer = scalarSubtract 20 5

scalarSubtractReverseAnswer : Nat
scalarSubtractReverseAnswer = scalarSubtract 5 20

scalarLessThan : Nat → Nat → Bool
scalarLessThan left right = left < right

scalarLessThanTrueAnswer : Bool
scalarLessThanTrueAnswer = scalarLessThan 5 20

scalarLessThanFalseAnswer : Bool
scalarLessThanFalseAnswer = scalarLessThan 20 5
