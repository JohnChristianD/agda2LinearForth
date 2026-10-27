\ Unsupported Agda axioms must remain catchable errors after code generation.

: abi-assert ( flag -- )
  0= IF -4200 THROW THEN
;

: unsupported-axiom-test ( -- )
  axiomUse deepdethunk DROP
;
' unsupported-axiom-test CATCH ABI-ERR-COMPILED-UNSUPPORTED = abi-assert

: assert-empty-data-stack ( -- )
  depth 0<> abort" unsupported axiom test leaked data-stack values"
;
assert-empty-data-stack
." unsupported-axiom-tests-passed" cr
BYE
