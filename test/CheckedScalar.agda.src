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

scalarSubtractEqualAnswer : Nat
scalarSubtractEqualAnswer = scalarSubtract 5 5

scalarSubtractZeroLeftAnswer : Nat
scalarSubtractZeroLeftAnswer = scalarSubtract 0 5

scalarSubtractZeroZeroAnswer : Nat
scalarSubtractZeroZeroAnswer = scalarSubtract 0 0

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

scalarLessThan : Nat → Nat → Bool
scalarLessThan left right = left < right

scalarLessThanTrueAnswer : Bool
scalarLessThanTrueAnswer = scalarLessThan 5 20

scalarLessThanFalseAnswer : Bool
scalarLessThanFalseAnswer = scalarLessThan 20 5

-- These values deliberately keep builtins under-applied across a function boundary.
-- The emitter must preserve their curried meaning, not treat a primitive as a result.
scalarCurriedAdd : Nat → Nat → Nat
scalarCurriedAdd = _+_

scalarCurriedAddAnswer : Nat
scalarCurriedAddAnswer = scalarCurriedAdd 20 5

scalarAddFive : Nat → Nat
scalarAddFive = _+_ 5

scalarAddFiveAnswer : Nat
scalarAddFiveAnswer = scalarAddFive 20

-- Partial application of a user definition exercises the ordinary closure path too.
scalarAddThroughClosure : Nat → Nat
scalarAddThroughClosure = scalarAdd 5

scalarAddThroughClosureAnswer : Nat
scalarAddThroughClosureAnswer = scalarAddThroughClosure 20

scalarSubtractTwenty : Nat → Nat
scalarSubtractTwenty = _-_ 20

scalarSubtractTwentyAnswer : Nat
scalarSubtractTwentyAnswer = scalarSubtractTwenty 5

scalarSubtractFive : Nat → Nat
scalarSubtractFive = _-_ 5

scalarSubtractFiveAnswer : Nat
scalarSubtractFiveAnswer = scalarSubtractFive 20

scalarMultiplySeven : Nat → Nat
scalarMultiplySeven = _*_ 7

scalarMultiplySevenAnswer : Nat
scalarMultiplySevenAnswer = scalarMultiplySeven 6

scalarEqualFive : Nat → Bool
scalarEqualFive = _==_ 5

scalarEqualFiveTrueAnswer : Bool
scalarEqualFiveTrueAnswer = scalarEqualFive 5

scalarEqualFiveFalseAnswer : Bool
scalarEqualFiveFalseAnswer = scalarEqualFive 6

scalarLessThanFive : Nat → Bool
scalarLessThanFive = _<_ 5

scalarLessThanFiveTrueAnswer : Bool
scalarLessThanFiveTrueAnswer = scalarLessThanFive 20

scalarLessThanFiveFalseAnswer : Bool
scalarLessThanFiveFalseAnswer = scalarLessThanFive 4
