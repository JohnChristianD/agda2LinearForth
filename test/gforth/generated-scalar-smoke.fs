\ End-to-end regression for generated code from the unchanged Agda2Forth backend.

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
