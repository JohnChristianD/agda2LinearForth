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
  ['] identity-body makeTHUNK assertLinear pass DUP source-linear-closure !
  source-linear-closure @ metadata@ META-ENV cells + @ @ DUP original-linear-capture ! DROP
  original-linear-capture @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  ABI-MAKE-RESULT DUP linear-closure-result !
  source-linear-closure @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
  linear-closure-result @ cell+ @ DUP moved-linear-closure !
  moved-linear-closure @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  original-linear-capture @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  linear-closure-result @ ABI-UNWRAP-RESULT moved-linear-closure @ = abi-assert
  linear-closure-result @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
  original-linear-capture @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
  DROP
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

\ The compiler's arithmetic adapters dispatch handles through the same ABI.
: checked-add-adapter-test ( -- )
  8 MODE-LINEAR ABI-MAKE-SCALAR
  9 MODE-MODAL ABI-MAKE-SCALAR
  ABI-ADD-OR-LEGACY ABI-SCALAR-INFO { value mode meta }
  value 17 = abi-assert
  mode MODE-LINEAR = abi-assert
;
checked-add-adapter-test

: legacy-add-adapter-test ( -- )
  8 9 ABI-ADD-OR-LEGACY 17 = abi-assert
;
legacy-add-adapter-test

\ These definitions mirror the fixed ToForth.hs preamble: push each local,
\ deepdethunk it, then use the ordinary Forth arithmetic token. Late-bound
\ operator dispatch must recognize checked handles while preserving raw/raw.
: generated-add { left right -- result }
  left deepdethunk right deepdethunk +
;
: generated-sub { left right -- result }
  left deepdethunk right deepdethunk -
;
: generated-mul { left right -- result }
  left deepdethunk right deepdethunk *
;
: generated-quot { left right -- result }
  left deepdethunk right deepdethunk /
;
: generated-rem { left right -- result }
  left deepdethunk right deepdethunk mod
;
: generated-eq { left right -- result }
  left deepdethunk right deepdethunk =
;
: generated-geq { left right -- result }
  left deepdethunk right deepdethunk >=
;
: generated-lt { left right -- result }
  left deepdethunk right deepdethunk <
;

: generated-checked-arithmetic-test ( -- )
  19 MODE-LINEAR ABI-MAKE-SCALAR
  7 MODE-MODAL ABI-MAKE-SCALAR
  generated-sub ABI-SCALAR-INFO { value mode meta }
  value 12 = abi-assert
  mode MODE-LINEAR = abi-assert

  3 MODE-LINEAR ABI-MAKE-SCALAR
  4 MODE-MODAL ABI-MAKE-SCALAR
  generated-mul ABI-SCALAR-INFO { value mode meta }
  value 12 = abi-assert
  mode MODE-LINEAR = abi-assert

  18 MODE-LINEAR ABI-MAKE-SCALAR
  3 MODE-MODAL ABI-MAKE-SCALAR
  generated-quot ABI-SCALAR-INFO { value mode meta }
  value 6 = abi-assert
  mode MODE-LINEAR = abi-assert

  17 MODE-MODAL ABI-MAKE-SCALAR
  5 MODE-MODAL ABI-MAKE-SCALAR
  generated-rem ABI-SCALAR-INFO { value mode meta }
  value 2 = abi-assert
  mode MODE-MODAL = abi-assert
;
generated-checked-arithmetic-test

: generated-checked-comparison-test ( -- )
  4 MODE-MODAL ABI-MAKE-SCALAR
  4 MODE-MODAL ABI-MAKE-SCALAR
  generated-eq ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
  mode MODE-MODAL = abi-assert

  5 MODE-LINEAR ABI-MAKE-SCALAR
  4 MODE-MODAL ABI-MAKE-SCALAR
  generated-geq ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
  mode MODE-LINEAR = abi-assert

  3 MODE-MODAL ABI-MAKE-SCALAR
  4 MODE-LINEAR ABI-MAKE-SCALAR
  generated-lt ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
  mode MODE-LINEAR = abi-assert
;
generated-checked-comparison-test

: generated-legacy-dispatch-test ( -- )
  19 7 generated-sub 12 = abi-assert
  3 4 generated-mul 12 = abi-assert
  18 3 generated-quot 6 = abi-assert
  17 5 generated-rem 2 = abi-assert
  4 4 generated-eq -1 = abi-assert
  5 4 generated-geq -1 = abi-assert
  3 4 generated-lt -1 = abi-assert
;
generated-legacy-dispatch-test

: generated-mixed-values-fail-closed ( -- )
  7 MODE-MODAL ABI-MAKE-SCALAR 3 generated-add DROP
;
' generated-mixed-values-fail-closed CATCH
  ABI-ERR-MIXED-ABI-VALUES = abi-assert

\ The fixed compiler preamble uses IF on the forced condition. deepdethunk must
\ validate/unbox a checked boolean; a linear boolean is consumed exactly once.
: checked-condition { condition yes no -- selected }
  condition deepdethunk IF yes deepdethunk ELSE no deepdethunk THEN
;
: generated-checked-condition-test ( -- )
  5 MODE-LINEAR ABI-MAKE-SCALAR
  5 MODE-MODAL ABI-MAKE-SCALAR
  generated-eq
  7 MODE-MODAL ABI-MAKE-SCALAR
  9 MODE-MODAL ABI-MAKE-SCALAR
  checked-condition ABI-SCALAR-INFO { value mode meta }
  value 7 = abi-assert
  mode MODE-MODAL = abi-assert
;
generated-checked-condition-test

: mixed-add-adapter-test ( -- )
  8 MODE-MODAL ABI-MAKE-SCALAR 9 ABI-ADD-OR-LEGACY DROP
;
' mixed-add-adapter-test CATCH ABI-ERR-MIXED-ABI-VALUES = abi-assert

: checked-modal-reuse-test ( -- )
  10 MODE-MODAL ABI-MAKE-SCALAR DUP ABI-NAT-ADD ABI-SCALAR-INFO { value mode meta }
  value 20 = abi-assert
  mode MODE-MODAL = abi-assert
;
checked-modal-reuse-test

\ Agda booleans have a distinct checked representation: true=-1, false=0.
: checked-eq-true-test ( -- )
  4 MODE-MODAL ABI-MAKE-SCALAR
  4 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-EQ ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
  mode MODE-MODAL = abi-assert
;
checked-eq-true-test

: checked-eq-false-test ( -- )
  4 MODE-MODAL ABI-MAKE-SCALAR
  5 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-EQ ABI-BOOL-INFO { value mode meta }
  value 0 = abi-assert
  mode MODE-MODAL = abi-assert
;
checked-eq-false-test

: checked-geq-test ( -- )
  5 MODE-MODAL ABI-MAKE-SCALAR
  4 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-GEQ ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
;
checked-geq-test

: checked-lt-test ( -- )
  4 MODE-MODAL ABI-MAKE-SCALAR
  5 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-LT ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
;
checked-lt-test

\ A checked linear boolean can be moved into a result wrapper and unwrapped once.
: checked-linear-boolean-result-test ( -- )
  6 MODE-LINEAR ABI-MAKE-SCALAR
  6 MODE-MODAL ABI-MAKE-SCALAR
  ABI-NAT-EQ DUP isBoolean abi-assert
  DUP ABI-BOOL-INFO { boolValue boolMode boolMeta }
  boolValue -1 = abi-assert
  boolMode MODE-LINEAR = abi-assert
  ABI-MAKE-RESULT { wrapper }
  wrapper metadata@ META-MODE cells + @ MODE-LINEAR = abi-assert
  wrapper ABI-UNWRAP-RESULT { movedBool }
  movedBool isBoolean abi-assert
  movedBool ABI-BOOL-INFO { movedValue movedMode movedMeta }
  movedValue -1 = abi-assert
  movedMode MODE-LINEAR = abi-assert
;
checked-linear-boolean-result-test

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
