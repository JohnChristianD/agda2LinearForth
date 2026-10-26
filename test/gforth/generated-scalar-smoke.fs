\ Integration test for code produced by the unchanged Agda2Forth backend.
\ Compile CheckedScalar.agda, then load CheckedScalar.fth before this file.

: generated-assert ( flag -- )
  0= IF -4095 THROW THEN
;

: checked-generated-scalar ( -- )
  0 ['] scalarAnswer ABI-CHECKED-RUN-NAT
  ABI-SCALAR-INFO { value mode meta }
  value 25 <> IF
    ." generated scalar payload mismatch: " value . cr
    -4091 THROW
  THEN
  mode MODE-MODAL <> IF
    ." generated scalar mode mismatch: " mode . cr
    -4092 THROW
  THEN
;

checked-generated-scalar
BYE
