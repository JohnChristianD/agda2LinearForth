include data/FLib.fth

\ Checked ABI smoke and negative-boundary tests for GNU Gforth.
\ Run after loading data/FLib.fth. Arbitrary Forth is outside the safety claim.

: abi-assert ( flag -- )
  0= IF -4096 THROW THEN
;

: assert30 ( n -- )
  30 = abi-assert
;

: modal-body ( x -- ) drop ;
' modal-body declareModalSafeXT
123 MODE-MODAL ABI-MAKE-SCALAR ABI-MAKE-RESULT assertModalValue DROP
' modal-body makeTHUNK promoteModal DROP

: linear-body ( x -- ) drop ;
: linear-function ( x -- ) drop ;
' linear-body declareLinearSafeXT
' linear-function declareLinearSafeXT

: check-linear-move { child fn -- }
  child fn pass DROP
  child metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
;

' linear-body makeTHUNK assertLinear
' linear-function makeTHUNK assertLinear
check-linear-move

: add2 ( x y -- z ) + ;
' add2 makeTHUNK 10 swap pass 20 swap pass dethunk assert30

: unknown-handle-test ( -- )
  123 assertLinear DROP
;
' unknown-handle-test CATCH ABI-ERR-UNKNOWN-HANDLE = abi-assert

: unsupported-boundary-test ( -- )
  ABI-ERROR-COMPILED-UNSUPPORTED
;
' unsupported-boundary-test CATCH ABI-ERR-COMPILED-UNSUPPORTED = abi-assert

\ A caught invalid operation must return to the test harness, not BYE the VM.
\ Legacy symbols remain loadable; their general behavior is outside this ABI proof.
' print 0<> abi-assert
' pass 0<> abi-assert
' dethunk 0<> abi-assert
BYE
