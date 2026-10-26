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

\ Same emitted operator shape as the fixed ToForth.hs preamble.
: generated-style-add { m n -- result } m deepdethunk n deepdethunk + ;
: generated-style-sub { m n -- result } m deepdethunk n deepdethunk - ;
: generated-style-mul { m n -- result } m deepdethunk n deepdethunk * ;
: generated-style-quot { m n -- result } m deepdethunk n deepdethunk / ;
: generated-style-rem { m n -- result } m deepdethunk n deepdethunk mod ;
: generated-style-eq { m n -- result } m deepdethunk n deepdethunk = ;
: generated-style-geq { m n -- result } m deepdethunk n deepdethunk >= ;
: generated-style-lt { m n -- result } m deepdethunk n deepdethunk < ;
: generated-style-if { b x y -- result }
  b deepdethunk IF x deepdethunk ELSE y deepdethunk THEN
;

: checked-generated-add-test ( -- )
  20 5 2 ' generated-style-add ABI-CHECKED-RUN-NAT
  ABI-SCALAR-INFO { value mode meta }
  value 25 = abi-assert
  mode MODE-MODAL = abi-assert
;
checked-generated-add-test

: checked-generated-sub-test ( -- )
  17 5 2 ' generated-style-sub ABI-CHECKED-RUN-NAT ABI-SCALAR-INFO { value mode meta }
  value 12 = abi-assert
;
checked-generated-sub-test

: checked-generated-mul-test ( -- )
  6 7 2 ' generated-style-mul ABI-CHECKED-RUN-NAT ABI-SCALAR-INFO { value mode meta }
  value 42 = abi-assert
;
checked-generated-mul-test

: checked-generated-quot-test ( -- )
  21 4 2 ' generated-style-quot ABI-CHECKED-RUN-NAT ABI-SCALAR-INFO { value mode meta }
  value 5 = abi-assert
;
checked-generated-quot-test

: checked-generated-rem-test ( -- )
  21 4 2 ' generated-style-rem ABI-CHECKED-RUN-NAT ABI-SCALAR-INFO { value mode meta }
  value 1 = abi-assert
;
checked-generated-rem-test

: checked-generated-eq-test ( -- )
  7 7 2 ' generated-style-eq ABI-CHECKED-RUN-BOOL ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
  mode MODE-MODAL = abi-assert
;
checked-generated-eq-test

: checked-generated-geq-test ( -- )
  7 8 2 ' generated-style-geq ABI-CHECKED-RUN-BOOL ABI-BOOL-INFO { value mode meta }
  value 0 = abi-assert
;
checked-generated-geq-test

: checked-generated-lt-test ( -- )
  7 8 2 ' generated-style-lt ABI-CHECKED-RUN-BOOL ABI-BOOL-INFO { value mode meta }
  value -1 = abi-assert
;
checked-generated-lt-test

: checked-generated-if-test ( -- )
  0 44 55 3 ' generated-style-if ABI-CHECKED-RUN-NAT ABI-SCALAR-INFO { value mode meta }
  value 55 = abi-assert
;
checked-generated-if-test

: generated-style-quot-zero ( -- result ) 10 0 ' generated-style-quot execute ;
: checked-generated-exception-test ( -- )
  0 ' generated-style-quot-zero ABI-CHECKED-RUN-NAT DROP
;
' checked-generated-exception-test CATCH ABI-ERR-ARITHMETIC-DOMAIN = abi-assert
ABI-CHECKED-MODE @ 0= abi-assert

\ The opt-in gate is off by default; legacy cell arithmetic is preserved.
8 9 + 17 = abi-assert

BYE
