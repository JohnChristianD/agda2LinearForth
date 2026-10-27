\ Unsupported source literals must raise catchable ABI errors, not BYE.
: unsupported-assert ( flag -- )
  0= IF -4202 THROW THEN
;

: expect-unsupported-error { xt -- }
  xt CATCH ABI-ERR-COMPILED-UNSUPPORTED = unsupported-assert
;

: force-unsupported-string ( -- )
  unsupported dethunk DROP
;
' force-unsupported-string expect-unsupported-error

: assert-empty-data-stack ( -- )
  depth 0<> abort" unsupported boundary test leaked data-stack values"
;
assert-empty-data-stack
." unsupported-boundary-tests-passed" cr
BYE
