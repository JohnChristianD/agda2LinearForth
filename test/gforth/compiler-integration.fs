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

depth 0<> abort" compiler integration leaked data-stack values"
BYE
