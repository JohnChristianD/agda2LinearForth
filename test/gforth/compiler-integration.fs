\ Compiler/runtime integration regressions for supported Nat primitives.
\ This deliberately exercises compiler-generated applications, not direct ABI calls.

: expect-natural ( actual expected -- )
  <> IF
    ." generated primitive result mismatch" cr
    -4101 THROW
  THEN
;

: generated-add-test ( -- )
  scalarAddAnswer dethunk 25 expect-natural
;
generated-add-test

: generated-subtract-test ( -- )
  scalarSubtractAnswer dethunk 15 expect-natural
;
generated-subtract-test

: generated-subtract-reverse-test ( -- )
  scalarSubtractReverseAnswer dethunk 0 expect-natural
;
generated-subtract-reverse-test

: generated-subtract-equal-test ( -- )
  scalarSubtractEqualAnswer dethunk 0 expect-natural
;
generated-subtract-equal-test

: generated-subtract-zero-left-test ( -- )
  scalarSubtractZeroLeftAnswer dethunk 0 expect-natural
;
generated-subtract-zero-left-test

: generated-subtract-zero-zero-test ( -- )
  scalarSubtractZeroZeroAnswer dethunk 0 expect-natural
;
generated-subtract-zero-zero-test

: generated-multiply-test ( -- )
  scalarMultiplyAnswer dethunk 42 expect-natural
;
generated-multiply-test

: generated-equality-true-test ( -- )
  scalarEqualTrueAnswer dethunk -1 expect-natural
;
generated-equality-true-test

: generated-equality-false-test ( -- )
  scalarEqualFalseAnswer dethunk 0 expect-natural
;
generated-equality-false-test

: generated-conditional-true-test ( -- )
  scalarChooseTrueAnswer dethunk 11 expect-natural
;
generated-conditional-true-test

: generated-conditional-false-test ( -- )
  scalarChooseFalseAnswer dethunk 17 expect-natural
;
generated-conditional-false-test

: generated-less-than-true-test ( -- )
  scalarLessThanTrueAnswer dethunk -1 expect-natural
;
generated-less-than-true-test

: generated-less-than-false-test ( -- )
  scalarLessThanFalseAnswer dethunk 0 expect-natural
;
generated-less-than-false-test

: generated-curried-builtin-add-test ( -- )
  scalarCurriedAddAnswer dethunk 25 expect-natural
;
generated-curried-builtin-add-test

: generated-partial-builtin-add-test ( -- )
  scalarAddFiveAnswer dethunk 25 expect-natural
;
generated-partial-builtin-add-test

: generated-partial-user-function-test ( -- )
  scalarAddThroughClosureAnswer dethunk 25 expect-natural
;
generated-partial-user-function-test

: generated-partial-monus-twenty-test ( -- )
  scalarSubtractTwentyAnswer dethunk 15 expect-natural
;
generated-partial-monus-twenty-test

: generated-partial-monus-five-test ( -- )
  scalarSubtractFiveAnswer dethunk 0 expect-natural
;
generated-partial-monus-five-test

: generated-partial-multiply-test ( -- )
  scalarMultiplySevenAnswer dethunk 42 expect-natural
;
generated-partial-multiply-test

: generated-partial-equality-true-test ( -- )
  scalarEqualFiveTrueAnswer dethunk -1 expect-natural
;
generated-partial-equality-true-test

: generated-partial-equality-false-test ( -- )
  scalarEqualFiveFalseAnswer dethunk 0 expect-natural
;
generated-partial-equality-false-test

: generated-partial-less-than-true-test ( -- )
  scalarLessThanFiveTrueAnswer dethunk -1 expect-natural
;
generated-partial-less-than-true-test

: generated-partial-less-than-false-test ( -- )
  scalarLessThanFiveFalseAnswer dethunk 0 expect-natural
;
generated-partial-less-than-false-test

: assert-empty-data-stack ( -- )
  depth 0<> abort" compiler integration leaked data-stack values"
;
assert-empty-data-stack
BYE
