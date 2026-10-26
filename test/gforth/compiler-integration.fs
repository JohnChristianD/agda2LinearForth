\ Compiler/runtime integration regressions for supported Nat primitives.
\ The generated file loads FLib.fth and defines CheckedScalar's Forth words.

: integration-assert ( flag -- )
  0= IF -4100 THROW THEN
;

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

: generated-multiply-test ( -- )
  scalarMultiplyAnswer dethunk 42 expect-natural
;
generated-multiply-test

BYE
