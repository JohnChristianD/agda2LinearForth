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

: generated-less-than-true-test ( -- )
  scalarLessThanTrueAnswer dethunk -1 expect-natural
;
generated-less-than-true-test

: generated-less-than-false-test ( -- )
  scalarLessThanFalseAnswer dethunk 0 expect-natural
;
generated-less-than-false-test

BYE
