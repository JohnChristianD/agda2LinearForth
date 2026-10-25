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

\ A linear result owns a fresh live payload handle. The source handle is consumed;
\ unwrapping transfers the moved handle out and consumes the wrapper.
VARIABLE original-linear-payload
VARIABLE linear-result-wrapper
VARIABLE moved-linear-payload
: linear-result-move-test ( -- )
  77 MODE-LINEAR ABI-MAKE-SCALAR DUP original-linear-payload !
  ABI-MAKE-RESULT DUP linear-result-wrapper !
  original-linear-payload @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
  linear-result-wrapper @ cell+ @ DUP moved-linear-payload !
  original-linear-payload @ <> abi-assert
  moved-linear-payload @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  linear-result-wrapper @ ABI-UNWRAP-RESULT moved-linear-payload @ = abi-assert
  linear-result-wrapper @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
  moved-linear-payload @ ABI-SCALAR-INFO { payloadValue payloadMode payloadMeta }
  payloadValue 77 = abi-assert
  payloadMode MODE-LINEAR = abi-assert
;
linear-result-move-test

\ Moving a linear closure must preserve its live captured resources through the wrapper.
VARIABLE original-linear-capture
VARIABLE source-linear-closure
VARIABLE linear-closure-result
VARIABLE moved-linear-closure
: identity-body ( x -- x ) ;
' identity-body declareLinearSafeXT
: linear-closure-result-move-test ( -- )
  55 MODE-LINEAR ABI-MAKE-SCALAR
  ' identity-body makeTHUNK assertLinear pass DUP source-linear-closure !
  source-linear-closure @ metadata@ META-ENV cells + @ @ DUP original-linear-capture !
  original-linear-capture @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  ABI-MAKE-RESULT DUP linear-closure-result !
  source-linear-closure @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
  linear-closure-result @ cell+ @ DUP moved-linear-closure !
  moved-linear-closure @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  original-linear-capture @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  linear-closure-result @ ABI-UNWRAP-RESULT moved-linear-closure @ = abi-assert
  linear-closure-result @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
  original-linear-capture @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
;
linear-closure-result-move-test

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

\ Checked arithmetic takes handles and returns a handle; result mode is the join of operand modes.
: checked-add-test ( -- )
  10 MODE-LINEAR ABI-MAKE-SCALAR
  20 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-ADD ABI-SCALAR-INFO { value mode meta }
  value 30 = abi-assert
  mode MODE-LINEAR = abi-assert
;
checked-add-test

: checked-modal-reuse-test ( -- )
  10 MODE-MODAL ABI-MAKE-SCALAR DUP ABI-NAT-ADD ABI-SCALAR-INFO { value mode meta }
  value 20 = abi-assert
  mode MODE-MODAL = abi-assert
;
checked-modal-reuse-test

: checked-linear-alias-test ( -- )
  9 MODE-LINEAR ABI-MAKE-SCALAR DUP ABI-NAT-ADD DROP
;
' checked-linear-alias-test CATCH ABI-ERR-ALIASED-LINEAR-OPERANDS = abi-assert

\ Arithmetic domain errors are named and catchable; failed operations retain live operands.
: checked-quot-zero-test ( -- )
  10 MODE-LINEAR ABI-MAKE-SCALAR
  0 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-QUOT DROP
;
' checked-quot-zero-test CATCH ABI-ERR-ARITHMETIC-DOMAIN = abi-assert

: checked-rem-zero-test ( -- )
  10 MODE-LINEAR ABI-MAKE-SCALAR
  0 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-REM DROP
;
' checked-rem-zero-test CATCH ABI-ERR-ARITHMETIC-DOMAIN = abi-assert

: checked-overflow-test ( -- )
  ABI-MAX-NAT MODE-LINEAR ABI-MAKE-SCALAR
  1 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-ADD DROP
;
' checked-overflow-test CATCH ABI-ERR-NAT-OVERFLOW = abi-assert

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
