module CheckedScalar where

open import Agda.Builtin.Nat using (Nat; _+_; _*_; _==_; _<_; _-_)
open import Agda.Builtin.Bool using (Bool; true; false)

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

scalarMultiply : Nat → Nat → Nat
scalarMultiply left right = left * right

scalarMultiplyAnswer : Nat
scalarMultiplyAnswer = scalarMultiply 6 7

scalarEqual : Nat → Nat → Bool
scalarEqual left right = left == right

scalarEqualTrueAnswer : Bool
scalarEqualTrueAnswer = scalarEqual 20 20

scalarEqualFalseAnswer : Bool
scalarEqualFalseAnswer = scalarEqual 20 5

scalarChoose : Bool → Nat → Nat → Nat
scalarChoose true yes no = yes
scalarChoose false yes no = no

scalarChooseTrueAnswer : Nat
scalarChooseTrueAnswer = scalarChoose true 11 17

scalarChooseFalseAnswer : Nat
scalarChooseFalseAnswer = scalarChoose false 11 17

scalarLessThan : Nat → Nat → Bool : Nat → Nat → Bool
scalarLessThan left right = left < right

scalarLessThanTrueAnswer : Bool
scalarLessThanTrueAnswer = scalarLessThan 5 20

scalarLessThanFalseAnswer : Bool
scalarLessThanFalseAnswer = scalarLessThan 20 5
