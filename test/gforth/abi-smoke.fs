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
VARIABLE modal-payload-handle
VARIABLE modal-result-handle
123 MODE-MODAL ABI-MAKE-SCALAR DUP modal-payload-handle !
ABI-MAKE-RESULT DUP modal-result-handle !
modal-result-handle @ metadata@ META-PAYLOAD cells + @
modal-payload-handle @ = abi-assert
modal-result-handle @ assertModalValue DROP

\ Result mode derives from the payload, not from the producing closure.
: linear-returns-modal ( -- handle ) 456 MODE-MODAL ABI-MAKE-SCALAR ;
' linear-returns-modal declareLinearSafeXT
' linear-returns-modal makeTHUNK assertLinear toResult assertModalValue DROP

\ Checked result conversion rejects raw, untracked payloads.
: linear-returns-raw ( -- n ) 456 ;
' linear-returns-raw declareLinearSafeXT
VARIABLE raw-linear-thunk
' linear-returns-raw makeTHUNK assertLinear raw-linear-thunk !
: raw-linear-result-test ( -- ) raw-linear-thunk @ toResult DROP ;
' raw-linear-result-test CATCH ABI-ERR-RESULT-PAYLOAD = abi-assert

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

\ A linear closure that throws must retire its moved linear captures before rethrow.
VARIABLE throw-child
VARIABLE throw-closure
VARIABLE throw-capture
: fail-after-capture ( x -- ) drop -4321 THROW ;
' fail-after-capture declareLinearSafeXT
' linear-body makeTHUNK assertLinear DUP throw-child !
' fail-after-capture makeTHUNK assertLinear
pass throw-closure !
throw-closure @ metadata@ META-ENV cells + @ @ throw-capture !

: force-failing-linear-closure ( -- )
  throw-closure @ dethunk DROP
;
' force-failing-linear-closure CATCH -4321 = abi-assert
throw-child @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
throw-closure @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
throw-capture @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert

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
