\ End-to-end check that an oversized Agda Nat literal fails catchably.

: abi-assert ( flag -- )
  0= IF -4210 THROW THEN
;

: oversized-natural-literal-test ( -- )
  tooLarge deepdethunk DROP
;
' oversized-natural-literal-test CATCH ABI-ERR-NAT-OVERFLOW = abi-assert

: assert-empty-data-stack ( -- )
  depth 0<> abort" oversized Nat literal test leaked data-stack values"
;
assert-empty-data-stack
." oversized-nat-literal-tests-passed" cr
BYE
