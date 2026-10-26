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

VARIABLE retained-dividend
VARIABLE retained-divisor
10 MODE-LINEAR ABI-MAKE-SCALAR retained-dividend !
0 MODE-MODAL ABI-MAKE-SCALAR retained-divisor !
: checked-quot-zero-preserves-inputs ( -- )
  retained-dividend @ retained-divisor @ ABI-NAT-QUOT DROP
;
' checked-quot-zero-preserves-inputs CATCH ABI-ERR-ARITHMETIC-DOMAIN = abi-assert
retained-dividend @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
retained-divisor @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert

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

\ Identity exhaustion must fail before changing HERE, NEXT-HANDLE-ID, or the metadata list.
: assert-id-exhaustion-atomic { xt -- }
  NEXT-HANDLE-ID @ { previousId }
  HANDLE-META-HEAD @ { previousHead }
  here { previousHere }
  ABI-MAX-NAT NEXT-HANDLE-ID !
  xt CATCH ABI-ERR-ID-OVERFLOW = abi-assert
  here previousHere = abi-assert
  HANDLE-META-HEAD @ previousHead = abi-assert
  NEXT-HANDLE-ID @ ABI-MAX-NAT = abi-assert
  previousId NEXT-HANDLE-ID !
;

: identity-exhaustion-scalar ( -- ) 1 MODE-MODAL ABI-MAKE-SCALAR DROP ;
' identity-exhaustion-scalar assert-id-exhaustion-atomic

: identity-exhaustion-boolean ( -- ) -1 MODE-MODAL ABI-MAKE-BOOL DROP ;
' identity-exhaustion-boolean assert-id-exhaustion-atomic

: identity-exhaustion-thunk ( -- ) ' modal-body makeTHUNK DROP ;
' identity-exhaustion-thunk assert-id-exhaustion-atomic

: identity-exhaustion-legacy-result ( -- ) 123 makeRESULT DROP ;
' identity-exhaustion-legacy-result assert-id-exhaustion-atomic

VARIABLE identity-test-linear-handle
88 MODE-LINEAR ABI-MAKE-SCALAR identity-test-linear-handle !
: identity-exhaustion-linear-move ( -- )
  identity-test-linear-handle @ DUP metadata@ moveLinearHandle DROP
;
' identity-exhaustion-linear-move assert-id-exhaustion-atomic
identity-test-linear-handle @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert

: identity-test-body ( x -- x ) ;
' identity-test-body makeTHUNK CONSTANT identity-test-thunk
: identity-exhaustion-pass ( -- ) 1 identity-test-thunk pass DROP ;
' identity-exhaustion-pass assert-id-exhaustion-atomic

\ ABI-BINARY must not consume inputs if result allocation fails.
VARIABLE identity-binary-linear
VARIABLE identity-binary-modal
10 MODE-LINEAR ABI-MAKE-SCALAR identity-binary-linear !
20 MODE-MODAL ABI-MAKE-SCALAR identity-binary-modal !
: identity-exhaustion-binary ( -- )
  identity-binary-linear @ identity-binary-modal @ ABI-NAT-ADD DROP
;
' identity-exhaustion-binary assert-id-exhaustion-atomic
identity-binary-linear @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert
identity-binary-modal @ metadata@ META-STATE cells + @ OWN-LIVE = abi-assert

\ A caught invalid operation must return to the test harness, not BYE the VM.
\ Legacy symbols remain loadable; their general behavior is outside this ABI proof.
' print 0<> abi-assert
' pass 0<> abi-assert
' dethunk 0<> abi-assert
\ A zero execution token is a null code pointer, not a callable closure.
\ It must throw before allocating a handle or metadata record.
: zero-code-token-test ( -- )
  here { before }
  ' zero-code-token-candidate CATCH { caught }
  caught 0<> abi-assert
  here before = abi-assert
;
: zero-code-token-candidate ( -- ) 0 makeTHUNK DROP ;
zero-code-token-test

\ Nested linear captures must all be retired if a closure aborts during force.
VARIABLE nested-linear-input
VARIABLE nested-first-closure
VARIABLE nested-outer-closure
VARIABLE nested-moved-closure
VARIABLE nested-linear-leaf
: nested-fail-after-capture ( x -- ) drop -4333 THROW ;
' nested-fail-after-capture declareLinearSafeXT
: build-nested-linear-closure ( -- )
  99 MODE-LINEAR ABI-MAKE-SCALAR DUP nested-linear-input !
  ' identity-body makeTHUNK assertLinear pass nested-first-closure !
  nested-first-closure @ metadata@ META-ENV cells + @ @ nested-linear-leaf !
  ' nested-fail-after-capture makeTHUNK assertLinear
  nested-first-closure @ swap pass nested-outer-closure !
  nested-outer-closure @ metadata@ META-ENV cells + @ @ nested-moved-closure !
;
build-nested-linear-closure
: force-nested-linear-closure ( -- ) nested-outer-closure @ dethunk DROP ;
' force-nested-linear-closure CATCH -4333 = abi-assert
nested-linear-input @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
nested-first-closure @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
nested-outer-closure @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
nested-moved-closure @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert
nested-linear-leaf @ metadata@ META-STATE cells + @ OWN-CONSUMED = abi-assert

BYE
