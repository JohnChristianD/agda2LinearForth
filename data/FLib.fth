variable MAXNUM 100000000000000 MAXNUM !
s" unsupported or invalid operation emitted by agda2forth" exception constant ABI-ERR-COMPILED-UNSUPPORTED
: ABI-ERROR-COMPILED-UNSUPPORTED ( -- ) ABI-ERR-COMPILED-UNSUPPORTED THROW ;

variable ENDFLAG 1234 ENDFLAG !
s" unknown or unmanaged value handle" exception constant ABI-ERR-UNKNOWN-HANDLE
s" use after linear handle consumption" exception constant ABI-ERR-CONSUMED-HANDLE
s" linear capture was not accounted for" exception constant ABI-ERR-LINEAR-CAPTURE
s" invalid ABI scalar mode" exception constant ABI-ERR-INVALID-MODE
s" result payload has no checked mode" exception constant ABI-ERR-RESULT-UNKNOWN-MODE
s" expected a checked result wrapper" exception constant ABI-ERR-RESULT-KIND
s" cannot unwrap a consumed or malformed result payload" exception constant ABI-ERR-RESULT-PAYLOAD
s" expected a scalar handle" exception constant ABI-ERR-EXPECTED-SCALAR
s" arithmetic result exceeds the checked cell range" exception constant ABI-ERR-NAT-OVERFLOW
s" linear scalar operand aliases another operand" exception constant ABI-ERR-ALIASED-LINEAR-OPERANDS
s" cannot mix checked handles with legacy raw values" exception constant ABI-ERR-MIXED-ABI-VALUES
s" scalar payload is outside the checked natural range" exception constant ABI-ERR-NAT-NEGATIVE
s" natural division or remainder by zero" exception constant ABI-ERR-ARITHMETIC-DOMAIN
s" closure has no metadata" exception constant ABI-ERR-CLOSURE-METADATA
s" cannot move unknown linear representation" exception constant ABI-ERR-UNKNOWN-REPRESENTATION
s" assertLinear requires a closure thunk" exception constant ABI-ERR-ASSERT-LINEAR-KIND
s" assertLinear requires registered safe captures" exception constant ABI-ERR-ASSERT-LINEAR-ENV
s" closure XT lacks a linear-safe contract" exception constant ABI-ERR-LINEAR-UNSAFE-XT
s" assertModalValue requires a RESULT wrapper" exception constant ABI-ERR-ASSERT-MODAL-KIND
s" promoteModal requires a THUNK closure" exception constant ABI-ERR-PROMOTE-KIND
s" closure XT lacks a modal-safe contract" exception constant ABI-ERR-MODAL-UNSAFE-XT
s" modal promotion requires an entirely modal environment" exception constant ABI-ERR-MODAL-ENV
s" checked linear closure cannot capture an untracked value" exception constant ABI-ERR-LINEAR-UNTRACKED-CAPTURE
s" checked modal closure cannot capture an untracked value" exception constant ABI-ERR-MODAL-UNTRACKED-CAPTURE
s" linear value cannot enter an unknown closure" exception constant ABI-ERR-LINEAR-UNKNOWN-CLOSURE
s" closure XT lacks a linear-capture contract" exception constant ABI-ERR-LINEAR-CAPTURE-UNSAFE-XT
s" linear closure cannot capture itself" exception constant ABI-ERR-LINEAR-SELF-CAPTURE

s" unreachable Agda branch" exception constant ABI-ERR-UNREACHABLE
: ABI-ERROR-UNREACHABLE ( -- ) ABI-ERR-UNREACHABLE THROW ;

: -= 1 - ;
: += 1 + ;
: dropN ( x1 x2 .. xn n -- )
    0 do
        drop
    loop
;
: printType ( o1 -- )
    dup MAXNUM @ <
    if .
    else @ 1 cells + @ execute
    then
;
: fillArray ( xn .. x2 x1 addr n -- )
    0 do
        dup rot rot i cells + !
    loop drop
;

: fillHere ( ENDFLAG xn .. x2 x1 -- )
    BEGIN
    ,
    dup ENDFLAG = if
        ,
        exit
    then
    AGAIN
;

: pushArrayN { addr n -- xn .. x2 x1 }
    n 0 > if n 0 do
        addr i cells + @
    loop
    then
;


: pushArray { addr -- xn .. x2 x1 ENDFLAG }
    ENDFLAG
    0
    BEGIN
    addr 1 pick cells + @
    dup ENDFLAG = if
        2drop
        EXIT
    then
    swap 1 +
    AGAIN
;
defer passMany
: curry ( x xt1 -- xt2 )
    swap 2>r 
    :noname r> postpone literal r> compile, postpone ; 
;
variable THUNK 1 cells allot 2 thunk !
variable RESULT 1 cells allot 2 RESULT !
variable SCALAR 1 cells allot
variable ABI-BOOL-TAG 1 cells allot

0 constant META-NEXT
1 constant META-HANDLE
2 constant META-KIND
3 constant META-CODE
4 constant META-ENV
5 constant META-ENVCOUNT
6 constant META-MODE
7 constant META-STATE
8 constant META-PAYLOAD
9 constant META-ID
10 constant META-CELLS

0 constant KIND-THUNK
1 constant KIND-RESULT
2 constant KIND-SCALAR
3 constant KIND-BOOLEAN

\ Gforth cell arithmetic is signed. Restrict checked naturals to its nonnegative range.
0 invert 1 rshift constant ABI-MAX-NAT
\ Internal boundary state only; this is not a third Agda/source-language type.
\ Checked generated code must establish MODE-LINEAR or MODE-MODAL explicitly.
0 constant MODE-UNANNOTATED
1 constant MODE-LINEAR
2 constant MODE-MODAL
0 constant OWN-LIVE
1 constant OWN-CONSUMED

variable HANDLE-META-HEAD
variable MODAL-SAFE-HEAD
variable LINEAR-SAFE-HEAD
variable NEXT-HANDLE-ID
0 NEXT-HANDLE-ID !

s" checked ABI identity space exhausted" exception constant ABI-ERR-ID-OVERFLOW

: requireIdentityRoom { count -- }
    NEXT-HANDLE-ID @ ABI-MAX-NAT count - > IF ABI-ERR-ID-OVERFLOW THROW THEN
;

: reserveMeta ( -- meta )
    align here META-CELLS cells allot
;

: initializeMeta { handle kind code env count mode state meta -- meta }
    1 requireIdentityRoom
    HANDLE-META-HEAD @ meta META-NEXT cells + !
    handle meta META-HANDLE cells + !
    kind meta META-KIND cells + !
    code meta META-CODE cells + !
    env meta META-ENV cells + !
    count meta META-ENVCOUNT cells + !
    mode meta META-MODE cells + !
    state meta META-STATE cells + !
    0 meta META-PAYLOAD cells + !
    NEXT-HANDLE-ID @ meta META-ID cells + !
    NEXT-HANDLE-ID @ 1+ NEXT-HANDLE-ID !
    meta HANDLE-META-HEAD !
    meta
;

: newMeta { handle kind code env count mode state -- meta }
    reserveMeta { meta }
    handle kind code env count mode state meta initializeMeta
;

\ Return metadata for a runtime-managed handle, or zero.
\ Do not dereference arbitrary cells to guess whether they are object pointers.
: metadata@ { handle -- meta }
    HANDLE-META-HEAD @
    BEGIN dup WHILE
        dup META-HANDLE cells + @ handle = IF EXIT THEN
        META-NEXT cells + @
    REPEAT
;

: requireLiveMeta { handle -- meta }
    handle metadata@ dup 0= IF drop ABI-ERR-UNKNOWN-HANDLE THROW THEN
    dup META-STATE cells + @ OWN-CONSUMED = IF ABI-ERR-CONSUMED-HANDLE THROW THEN
    dup META-KIND cells + @ CASE
        KIND-THUNK OF handle @ THUNK <> IF ABI-ERR-UNKNOWN-REPRESENTATION THROW THEN ENDOF
        KIND-RESULT OF handle @ RESULT <> IF ABI-ERR-UNKNOWN-REPRESENTATION THROW THEN ENDOF
        KIND-SCALAR OF handle @ SCALAR <> IF ABI-ERR-UNKNOWN-REPRESENTATION THROW THEN ENDOF
        KIND-BOOLEAN OF handle @ ABI-BOOL-TAG <> IF ABI-ERR-UNKNOWN-REPRESENTATION THROW THEN ENDOF
        drop ABI-ERR-UNKNOWN-REPRESENTATION THROW
    ENDCASE
;

: isThunk { handle -- flag }
    handle metadata@ dup 0= IF drop 0 EXIT THEN
    drop
    handle @ THUNK =
;

: isResult { handle -- flag }
    handle metadata@ dup 0= IF drop 0 EXIT THEN
    drop
    handle @ RESULT =
;

: isScalar { handle -- flag }
    handle metadata@ dup 0= IF drop 0 EXIT THEN
    drop
    handle @ SCALAR =
;

: isBoolean { handle -- flag }
    handle metadata@ dup 0= IF drop 0 EXIT THEN
    drop
    handle @ ABI-BOOL-TAG =
;

: xtInList? { xt headAddr -- flag }
    headAddr @
    BEGIN dup WHILE
        dup @ xt = IF drop -1 EXIT THEN
        cell+ @
    REPEAT
;

: declareXT { xt headAddr -- }
    xt headAddr xtInList? IF EXIT THEN
    align here 2 cells allot { node }
    xt node !
    headAddr @ node cell+ !
    node headAddr !
;

\ Trusted code-contract declarations. These are assertions by the integrator,
\ not proofs inferred from an arbitrary Forth execution token.
: declareModalSafeXT ( xt -- )
    MODAL-SAFE-HEAD declareXT
;

: declareLinearSafeXT ( xt -- )
    LINEAR-SAFE-HEAD declareXT
;

: modalSafeXT? { xt -- flag }
    xt MODAL-SAFE-HEAD xtInList?
;

: linearSafeXT? { xt -- flag }
    xt LINEAR-SAFE-HEAD xtInList?
;

: trackedEnv? { meta -- flag }
    meta META-ENVCOUNT cells + @ { count }
    meta META-ENV cells + @ { env }
    0 { i }
    -1 { good }
    BEGIN i count < WHILE
        env i cells + @ metadata@ { child }
        child 0= IF
            0 TO good
        ELSE
            child META-STATE cells + @ OWN-CONSUMED = IF 0 TO good THEN
            child META-MODE cells + @ MODE-UNANNOTATED = IF 0 TO good THEN
        THEN
        i 1+ TO i
    REPEAT
    good
;

: modalEnv? { meta -- flag }
    meta META-ENVCOUNT cells + @ { count }
    meta META-ENV cells + @ { env }
    0 { i }
    -1 { good }
    BEGIN i count < WHILE
        env i cells + @ metadata@ { child }
        child 0= IF
            0 TO good
        ELSE
            child META-STATE cells + @ OWN-CONSUMED = IF 0 TO good THEN
            child META-MODE cells + @ MODE-MODAL <> IF 0 TO good THEN
        THEN
        i 1+ TO i
    REPEAT
    good
;

: checkLinearEnvConsumed { meta result -- }
    meta META-ENVCOUNT cells + @ { count }
    meta META-ENV cells + @ { env }
    0 { i }
    BEGIN i count < WHILE
        env i cells + @ { childHandle }
        childHandle metadata@ { child }
        child 0<> IF
            child META-MODE cells + @ MODE-LINEAR = IF
                child META-STATE cells + @ OWN-LIVE = IF
                    childHandle result <> IF ABI-ERR-LINEAR-CAPTURE THROW THEN
                THEN
            THEN
        THEN
        i 1+ TO i
    REPEAT
;

: combineModes { left right -- mode }
    left MODE-UNANNOTATED = right MODE-UNANNOTATED = OR IF MODE-UNANNOTATED EXIT THEN
    left MODE-LINEAR = right MODE-LINEAR = OR IF MODE-LINEAR EXIT THEN
    MODE-MODAL
;

: invokeClosure ( handle ENDFLAG -- handle ENDFLAG args... )
    \ dethunk calls this through PERFORM with the original handle and sentinel
    \ already on the data stack. Duplicate the handle for lookup but preserve
    \ the force protocol's stack prefix.
    1 pick { handle }
    handle metadata@ dup 0= IF drop ABI-ERR-CLOSURE-METADATA THROW THEN
    { meta }
    meta META-ENV cells + @
    meta META-ENVCOUNT cells + @
    pushArrayN
    meta META-CODE cells + @ execute
;

: moveLinearHandle { handle meta -- moved }
    handle metadata@ meta <> IF ABI-ERR-UNKNOWN-REPRESENTATION THROW THEN
    handle requireLiveMeta DROP
    meta META-MODE cells + @ MODE-LINEAR <> IF ABI-ERR-UNKNOWN-REPRESENTATION THROW THEN
    0 { moved }
    handle @ THUNK = IF
        align here 2 cells allot TO moved
        THUNK moved !
        ['] invokeClosure moved cell+ !
        moved KIND-THUNK
            meta META-CODE cells + @
            meta META-ENV cells + @
            meta META-ENVCOUNT cells + @
            MODE-LINEAR OWN-LIVE newMeta DROP
    ELSE handle @ RESULT = IF
        handle cell+ @ { contained }
        meta META-PAYLOAD cells + @ contained <> IF ABI-ERR-RESULT-PAYLOAD THROW THEN
        contained requireLiveMeta { containedMeta }
        containedMeta META-MODE cells + @ MODE-LINEAR <> IF ABI-ERR-RESULT-PAYLOAD THROW THEN
        align here 2 cells allot TO moved
        RESULT moved !
        contained moved cell+ !
        moved KIND-RESULT 0 0 0 MODE-LINEAR OWN-LIVE newMeta { movedMeta }
        contained movedMeta META-PAYLOAD cells + !
    ELSE handle @ SCALAR = IF
        align here 2 cells allot TO moved
        SCALAR moved !
        handle cell+ @ moved cell+ !
        moved KIND-SCALAR 0 0 0 MODE-LINEAR OWN-LIVE newMeta DROP
    ELSE handle @ ABI-BOOL-TAG = IF
        align here 2 cells allot TO moved
        ABI-BOOL-TAG moved !
        handle cell+ @ moved cell+ !
        moved KIND-BOOLEAN 0 0 0 MODE-LINEAR OWN-LIVE newMeta DROP
    ELSE
        ABI-ERR-UNKNOWN-REPRESENTATION THROW
    THEN THEN THEN THEN
    OWN-CONSUMED meta META-STATE cells + !
    moved
;

: captureValue { handle -- captured }
    handle metadata@ { meta }
    meta 0= IF handle EXIT THEN
    handle requireLiveMeta DROP
    meta META-MODE cells + @ MODE-LINEAR = IF
        handle meta moveLinearHandle
    ELSE
        handle
    THEN
;

: assertLinear { handle -- handle }
    handle requireLiveMeta { meta }
    handle isThunk 0= IF ABI-ERR-ASSERT-LINEAR-KIND THROW THEN
    meta trackedEnv? 0= IF ABI-ERR-ASSERT-LINEAR-ENV THROW THEN
    meta META-CODE cells + @ linearSafeXT?
        0= IF ABI-ERR-LINEAR-UNSAFE-XT THROW THEN
    MODE-LINEAR meta META-MODE cells + !
    handle
;

s" linear payload cannot be modal" exception constant ABI-ERR-MODAL-PAYLOAD
s" unregistered modal payload" exception constant ABI-ERR-UNREGISTERED-MODAL-PAYLOAD

: modalPayload? { handle -- flag }
    handle metadata@ { meta }
    meta 0= IF 0 EXIT THEN
    meta META-STATE cells + @ OWN-LIVE <> IF 0 EXIT THEN
    meta META-MODE cells + @ MODE-MODAL <> IF 0 EXIT THEN
    meta META-KIND cells + @ KIND-SCALAR = IF -1 EXIT THEN
    meta META-KIND cells + @ KIND-BOOLEAN = IF -1 EXIT THEN
    meta META-KIND cells + @ KIND-THUNK = IF
        meta META-CODE cells + @ modalSafeXT? 0= IF 0 EXIT THEN
        meta modalEnv? 0= IF 0 EXIT THEN
        -1 EXIT
    THEN
    meta META-KIND cells + @ KIND-RESULT = IF
        handle cell+ @ { payload }
        meta META-PAYLOAD cells + @ payload <> IF 0 EXIT THEN
        payload RECURSE EXIT
    THEN
    0
;

: ABI-MAKE-SCALAR { value mode -- handle }
    mode MODE-LINEAR = mode MODE-MODAL = OR 0= IF ABI-ERR-INVALID-MODE THROW THEN
    value 0< IF ABI-ERR-NAT-NEGATIVE THROW THEN
    value ABI-MAX-NAT > IF ABI-ERR-NAT-OVERFLOW THROW THEN
    align here 2 cells allot { handle }
    SCALAR handle !
    value handle cell+ !
    handle KIND-SCALAR 0 0 0 mode OWN-LIVE newMeta DROP
    handle
;

s" expected a checked boolean handle" exception constant ABI-ERR-EXPECTED-BOOLEAN
s" invalid Agda boolean payload" exception constant ABI-ERR-INVALID-BOOLEAN

: ABI-MAKE-BOOL { value mode -- handle }
    mode MODE-LINEAR = mode MODE-MODAL = OR 0= IF ABI-ERR-INVALID-MODE THROW THEN
    value 0= value -1 = OR 0= IF ABI-ERR-INVALID-BOOLEAN THROW THEN
    align here 2 cells allot { handle }
    ABI-BOOL-TAG handle !
    value handle cell+ !
    handle KIND-BOOLEAN 0 0 0 mode OWN-LIVE newMeta DROP
    handle
;

: ABI-BOOL-INFO { handle -- value mode meta }
    handle requireLiveMeta { meta }
    meta META-KIND cells + @ KIND-BOOLEAN <> IF ABI-ERR-EXPECTED-BOOLEAN THROW THEN
    meta META-MODE cells + @ { mode }
    mode MODE-LINEAR = mode MODE-MODAL = OR 0= IF ABI-ERR-INVALID-MODE THROW THEN
    handle cell+ @ { value }
    value 0= value -1 = OR 0= IF ABI-ERR-INVALID-BOOLEAN THROW THEN
    value mode meta
;

\ Validate a checked numeric scalar without consuming or changing it.
: ABI-SCALAR-INFO { handle -- value mode meta }
    handle requireLiveMeta { meta }
    meta META-KIND cells + @ KIND-SCALAR <> IF ABI-ERR-EXPECTED-SCALAR THROW THEN
    meta META-MODE cells + @ { mode }
    mode MODE-LINEAR = mode MODE-MODAL = OR 0= IF ABI-ERR-INVALID-MODE THROW THEN
    handle cell+ @ { value }
    value 0< IF ABI-ERR-NAT-NEGATIVE THROW THEN
    value ABI-MAX-NAT > IF ABI-ERR-NAT-OVERFLOW THROW THEN
    value mode meta
;

: ABI-ADD-RAW { left right -- value }
    left ABI-MAX-NAT right - > IF ABI-ERR-NAT-OVERFLOW THROW THEN
    left right +
;

: ABI-SUB-RAW { left right -- value }
    left right < IF 0 ELSE left right - THEN
;

: ABI-MUL-RAW { left right -- value }
    right 0<> IF
        left ABI-MAX-NAT right / > IF ABI-ERR-NAT-OVERFLOW THROW THEN
    THEN
    left right *
;

: ABI-QUOT-RAW { left right -- value }
    right 0= IF ABI-ERR-ARITHMETIC-DOMAIN THROW THEN
    left right /
;

: ABI-REM-RAW { left right -- value }
    right 0= IF ABI-ERR-ARITHMETIC-DOMAIN THROW THEN
    left right mod
;

: ABI-EQ-RAW { left right -- value }
    left right = IF -1 ELSE 0 THEN
;

: ABI-GEQ-RAW { left right -- value }
    left right >= IF -1 ELSE 0 THEN
;

: ABI-LT-RAW { left right -- value }
    left right < IF -1 ELSE 0 THEN
;

\ Consume linear operands only after validation, computation and result allocation succeed.
: ABI-BINARY { leftHandle rightHandle operation makeResult -- resultHandle }
    leftHandle ABI-SCALAR-INFO { leftValue leftMode leftMeta }
    rightHandle ABI-SCALAR-INFO { rightValue rightMode rightMeta }
    leftHandle rightHandle = IF
        leftMode MODE-LINEAR = IF ABI-ERR-ALIASED-LINEAR-OPERANDS THROW THEN
    THEN
    leftValue rightValue operation EXECUTE { resultValue }
    leftMode rightMode combineModes { resultMode }
    resultValue resultMode makeResult EXECUTE { resultHandle }
    leftMode MODE-LINEAR = IF OWN-CONSUMED leftMeta META-STATE cells + ! THEN
    rightMode MODE-LINEAR = IF OWN-CONSUMED rightMeta META-STATE cells + ! THEN
    resultHandle
;

: ABI-NAT-ADD ( leftHandle rightHandle -- resultHandle )
    ['] ABI-ADD-RAW ['] ABI-MAKE-SCALAR ABI-BINARY
;

: ABI-NAT-SUB ( leftHandle rightHandle -- resultHandle )
    ['] ABI-SUB-RAW ['] ABI-MAKE-SCALAR ABI-BINARY
;

: ABI-NAT-MONUS ( leftHandle rightHandle -- resultHandle )
    ['] ABI-SUB-RAW ['] ABI-MAKE-SCALAR ABI-BINARY
;

: ABI-NAT-MUL ( leftHandle rightHandle -- resultHandle )
    ['] ABI-MUL-RAW ['] ABI-MAKE-SCALAR ABI-BINARY
;

: ABI-NAT-QUOT ( leftHandle rightHandle -- resultHandle )
    ['] ABI-QUOT-RAW ['] ABI-MAKE-SCALAR ABI-BINARY
;

: ABI-NAT-REM ( leftHandle rightHandle -- resultHandle )
    ['] ABI-REM-RAW ['] ABI-MAKE-SCALAR ABI-BINARY
;

: ABI-NAT-EQ ( leftHandle rightHandle -- resultHandle )
    ['] ABI-EQ-RAW ['] ABI-MAKE-BOOL ABI-BINARY
;

: ABI-NAT-GEQ ( leftHandle rightHandle -- resultHandle )
    ['] ABI-GEQ-RAW ['] ABI-MAKE-BOOL ABI-BINARY
;

: ABI-NAT-LT ( leftHandle rightHandle -- resultHandle )
    ['] ABI-LT-RAW ['] ABI-MAKE-BOOL ABI-BINARY
;

\ Dual-entry arithmetic preserves the legacy raw-cell stack effect while routing
\ fully managed scalar operands through the checked handle ABI. Mixed calls fail closed.
: ABI-DISPATCH-BINARY { left right checked legacy -- result }
    left metadata@ { leftMeta }
    right metadata@ { rightMeta }
    leftMeta 0<> rightMeta 0<> AND IF
        left isScalar 0= IF ABI-ERR-EXPECTED-SCALAR THROW THEN
        right isScalar 0= IF ABI-ERR-EXPECTED-SCALAR THROW THEN
        left right checked EXECUTE EXIT
    THEN
    leftMeta 0<> rightMeta 0<> OR IF ABI-ERR-MIXED-ABI-VALUES THROW THEN
    left right legacy EXECUTE
;

: ABI-ADD-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-ADD ['] + ABI-DISPATCH-BINARY
;
: ABI-SUB-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-SUB ['] - ABI-DISPATCH-BINARY
;
: ABI-MONUS-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-MONUS ['] - ABI-DISPATCH-BINARY
;
: ABI-MUL-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-MUL ['] * ABI-DISPATCH-BINARY
;
: ABI-QUOT-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-QUOT ['] / ABI-DISPATCH-BINARY
;
: ABI-REM-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-REM ['] mod ABI-DISPATCH-BINARY
;
: ABI-EQ-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-EQ ['] = ABI-DISPATCH-BINARY
;
: ABI-GEQ-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-GEQ ['] >= ABI-DISPATCH-BINARY
;
: ABI-LT-OR-LEGACY ( left right -- result )
    ['] ABI-NAT-LT ['] < ABI-DISPATCH-BINARY
;

: assertModalValue { handle -- handle }
    handle requireLiveMeta { meta }
    handle isResult 0= IF ABI-ERR-ASSERT-MODAL-KIND THROW THEN
    meta META-MODE cells + @ MODE-LINEAR = IF ABI-ERR-MODAL-PAYLOAD THROW THEN
    handle cell+ @ { payload }
    payload metadata@ 0= IF ABI-ERR-UNREGISTERED-MODAL-PAYLOAD THROW THEN
    meta META-PAYLOAD cells + @ payload <> IF ABI-ERR-MODAL-PAYLOAD THROW THEN
    payload modalPayload? 0= IF ABI-ERR-MODAL-PAYLOAD THROW THEN
    MODE-MODAL meta META-MODE cells + !
    handle
;

\ Checked result constructor. A linear payload is moved to a fresh live handle
\ before the wrapper becomes live; the wrapper then owns that handle by identity.
\ Modal payloads remain shared only after the full modal-payload predicate passes.
: ABI-MAKE-RESULT { payload -- wrapper }
    payload requireLiveMeta { pm }
    pm META-MODE cells + @ { mode }
    mode MODE-UNANNOTATED = IF ABI-ERR-RESULT-UNKNOWN-MODE THROW THEN
    mode MODE-MODAL = IF
        payload modalPayload? 0= IF ABI-ERR-MODAL-PAYLOAD THROW THEN
        1 requireIdentityRoom
    ELSE
        2 requireIdentityRoom
    THEN
    align here 2 cells allot { wrapper }
    RESULT wrapper !
    0 wrapper cell+ !
    reserveMeta { wrapperMeta }

    payload { storedPayload }
    mode MODE-LINEAR = IF
        payload pm moveLinearHandle TO storedPayload
    THEN

    storedPayload wrapper cell+ !
    wrapper KIND-RESULT 0 0 0 MODE-UNANNOTATED OWN-CONSUMED wrapperMeta initializeMeta DROP
    storedPayload wrapperMeta META-PAYLOAD cells + !
    mode wrapperMeta META-MODE cells + !
    OWN-LIVE wrapperMeta META-STATE cells + !
    wrapper
;

\ A linear wrapper transfers its contained live token out and is consumed.
\ A modal wrapper is reusable and may yield the same modal payload repeatedly.
: ABI-UNWRAP-RESULT { wrapper -- payload }
    wrapper requireLiveMeta { wm }
    wrapper isResult 0= IF ABI-ERR-RESULT-KIND THROW THEN
    wm META-MODE cells + @ { mode }
    mode MODE-UNANNOTATED = IF ABI-ERR-RESULT-UNKNOWN-MODE THROW THEN
    wrapper cell+ @ { payload }
    payload metadata@ dup 0= IF drop ABI-ERR-RESULT-PAYLOAD THROW THEN
    { pm }
    wm META-PAYLOAD cells + @ payload <> IF ABI-ERR-RESULT-PAYLOAD THROW THEN
    mode MODE-MODAL = IF
        pm META-MODE cells + @ MODE-MODAL <> IF ABI-ERR-MODAL-PAYLOAD THROW THEN
        payload modalPayload? 0= IF ABI-ERR-MODAL-PAYLOAD THROW THEN
        payload EXIT
    THEN
    mode MODE-LINEAR <> IF ABI-ERR-RESULT-UNKNOWN-MODE THROW THEN
    pm META-MODE cells + @ MODE-LINEAR <> IF ABI-ERR-RESULT-PAYLOAD THROW THEN
    pm META-STATE cells + @ OWN-LIVE <> IF ABI-ERR-RESULT-PAYLOAD THROW THEN
    OWN-CONSUMED wm META-STATE cells + !
    payload
;

: promoteModal { handle -- handle }
    handle requireLiveMeta { meta }
    handle isThunk 0= IF ABI-ERR-PROMOTE-KIND THROW THEN
    meta META-CODE cells + @ modalSafeXT? 0= IF ABI-ERR-MODAL-UNSAFE-XT THROW THEN
    meta modalEnv? 0= IF ABI-ERR-MODAL-ENV THROW THEN
    MODE-MODAL meta META-MODE cells + !
    handle
;

: makeTHUNK { xt -- handle }
    xt isThunk xt isResult OR IF xt EXIT THEN
    align here 2 cells allot { handle }
    THUNK handle !
    ['] invokeClosure handle cell+ !
    handle KIND-THUNK xt 0 0 MODE-UNANNOTATED OWN-LIVE newMeta DROP
    handle
;

:noname ." T: " ; THUNK 1 cells + !

: makeRESULT { value -- handle }
    align here 2 cells allot { handle }
    RESULT handle !
    value handle cell+ !
    handle KIND-RESULT 0 0 0 MODE-UNANNOTATED OWN-LIVE newMeta { resultMeta }
    value metadata@ 0<> IF value resultMeta META-PAYLOAD cells + ! THEN
    handle
;


:noname ." S: " ; SCALAR 1 cells + !
:noname ." B: " ; ABI-BOOL-TAG 1 cells + !
:noname ." R: " ; RESULT 1 cells + !



: shallowPrint { o1 }
    ." ("
    o1 MAXNUM @ <
    if o1 .
    else
        o1 ENDFLAG = if
            ." ENDFLAG??!?! "
        else
        o1 isThunk if
            ." THUNK"
        else o1 isResult if
            ." RES: "
            o1 1 cells + @ recurse
        else
            o1 @ 1 cells + @ 
            execute
            o1 @ @ 1 >
            if
                o1 @ @ 1 do
                    o1 i cells + @
                    recurse
                loop
            then
        then
        then
        then
    then
        ." )"
;
variable target

\ On exceptional exit from a checked linear closure, its uniquely-owned linear
\ captures cannot remain live under a consumed parent. Retire the linear subtree.
\ This traversal relies on the checked ABI's acyclic, allocate-new descriptors.
: consumeLinearTree { handle -- }
    handle metadata@ { childMeta }
    childMeta 0= IF ABI-ERR-UNKNOWN-HANDLE THROW THEN
    childMeta META-MODE cells + @ MODE-LINEAR <> IF EXIT THEN
    childMeta META-STATE cells + @ OWN-CONSUMED = IF EXIT THEN
    childMeta META-KIND cells + @ KIND-THUNK = IF
        childMeta META-ENVCOUNT cells + @ { count }
        childMeta META-ENV cells + @ { env }
        0 { i }
        BEGIN i count < WHILE
            env i cells + @ { nestedHandle }
            nestedHandle metadata@ { nestedMeta }
            nestedMeta 0= IF ABI-ERR-LINEAR-CAPTURE THROW THEN
            nestedMeta META-MODE cells + @ MODE-LINEAR = IF
                nestedHandle RECURSE
            THEN
            i 1+ TO i
        REPEAT
    ELSE
        childMeta META-KIND cells + @ KIND-RESULT = IF
            handle cell+ @ { payload }
            payload metadata@ { payloadMeta }
            payloadMeta 0= IF ABI-ERR-LINEAR-CAPTURE THROW THEN
            payloadMeta META-MODE cells + @ MODE-LINEAR = IF
                payload RECURSE
            THEN
        THEN
    THEN
    OWN-CONSUMED childMeta META-STATE cells + !
;

: consumeLinearCapturesOnThrow { closureMeta -- }
    closureMeta META-ENVCOUNT cells + @ { count }
    closureMeta META-ENV cells + @ { env }
    0 { i }
    BEGIN i count < WHILE
        env i cells + @ { child }
        child metadata@ { childMeta }
        childMeta 0= IF ABI-ERR-LINEAR-CAPTURE THROW THEN
        childMeta META-MODE cells + @ MODE-LINEAR = IF
            child consumeLinearTree
        THEN
        i 1+ TO i
    REPEAT
;

: dethunk { value -- result }
    BEGIN
        value metadata@ { meta }
        meta 0= IF value EXIT THEN
        meta META-STATE cells + @ OWN-CONSUMED = IF ABI-ERR-CONSUMED-HANDLE THROW THEN
        value @ THUNK = IF
            meta META-MODE cells + @ MODE-LINEAR = IF
                OWN-CONSUMED meta META-STATE cells + !
            THEN
            \ CATCH preserves the pre-call stack on failure, but does not roll
            \ back metadata writes. Explicitly retire the linear capture tree,
            \ then rethrow the original code to the caller.
            value ENDFLAG value cell+ @ CATCH
            DUP 0<> IF
                { thrownCode }
                meta META-MODE cells + @ MODE-LINEAR = IF
                    meta consumeLinearCapturesOnThrow
                THEN
                thrownCode THROW
            THEN
            DROP
            passMany NIP TO value
            meta META-MODE cells + @ MODE-LINEAR = IF
                meta value checkLinearEnvConsumed
            THEN
        ELSE
            value @ RESULT = IF
                meta META-MODE cells + @ MODE-LINEAR = IF
                    OWN-CONSUMED meta META-STATE cells + !
                THEN
                value cell+ @ TO value
            ELSE
                value EXIT
            THEN
        THEN
    AGAIN
;

: toResult { handle -- resultHandle }
    handle metadata@ { originalMeta }
    originalMeta 0= IF
        \ Preserve the legacy conversion for unmanaged records.
        RESULT handle !
        handle EXIT
    THEN
    handle isResult IF handle EXIT THEN

    \ A managed thunk stores an invocation XT, not its computed payload.
    \ Force it and allocate a fresh RESULT instead of rewriting an aliased
    \ closure handle in place.
    handle dethunk { payload }

    \ Result mode belongs to the returned payload, not to the closure that
    \ produced it. Keep the historical unchecked route only for legacy values.
    originalMeta META-MODE cells + @ MODE-UNANNOTATED = IF
        payload makeRESULT EXIT
    THEN

    payload metadata@ dup 0= IF
        drop ABI-ERR-RESULT-PAYLOAD THROW
    THEN
    drop
    payload ABI-MAKE-RESULT
;

: deepDethunk ( [THUNK o1] -- o1 )
    BEGIN
    dethunk                     ( o1 )
    dup isScalar IF EXIT THEN
    dup isBoolean IF EXIT THEN
    dup MAXNUM @ < 0 =          ( o1 0/-1 )
    if
        dup @ THUNK = 0 =   ( o1 0/-1 )
        over @ RESULT = 0 = ( o1 0/-1 0/-1)
        * if            ( o1 )
            dup @ @ 1 >                 ( o1 0/-1 )
            if                          ( o1 )
                dup @ @ 1 do                ( o1 )
                    dup i cells + @ recurse     ( o1 o1[i] )
                    over i cells + !          ( o1 )
                loop
            then
            EXIT
        then
    else EXIT
    then
    AGAIN
;


: pushThunks { o1 } ( o1 -- o2 o3 .. on )
    o1 MAXNUM @ < 0 =
    if
        o1 @ THUNK = if
            o1
        else
            o1 @ @ 1 >
            if
                o1 @ @ 1 do
                    o1 i cells + @ recurse
                loop
            then
        then
    then
;

: deepDethunk2 ( [THUNK o1] -- o1 )
    begin
    dup isThunk while
        dethunk
    repeat
;

: pass { x h -- result }
    h metadata@ 0<> IF h requireLiveMeta DROP THEN
    h isThunk IF
        h requireLiveMeta { hm }
        hm META-MODE cells + @ { functionMode }
        x metadata@ { xm }
        xm 0<> IF x requireLiveMeta DROP THEN
        MODE-UNANNOTATED { argumentMode }
        xm 0<> IF xm META-MODE cells + @ TO argumentMode THEN

        functionMode MODE-LINEAR = argumentMode MODE-UNANNOTATED = AND
            IF ABI-ERR-LINEAR-UNTRACKED-CAPTURE THROW THEN
        functionMode MODE-MODAL = argumentMode MODE-UNANNOTATED = AND
            IF ABI-ERR-MODAL-UNTRACKED-CAPTURE THROW THEN
        argumentMode MODE-LINEAR = IF
            functionMode MODE-UNANNOTATED = IF ABI-ERR-LINEAR-UNKNOWN-CLOSURE THROW THEN
            hm META-CODE cells + @ linearSafeXT? 0=
                IF ABI-ERR-LINEAR-CAPTURE-UNSAFE-XT THROW THEN
        THEN
        x h = argumentMode MODE-LINEAR = AND
            IF ABI-ERR-LINEAR-SELF-CAPTURE THROW THEN

        x captureValue { captured }
        hm META-ENVCOUNT cells + @ { oldCount }
        hm META-ENV cells + @ { oldEnv }
        oldCount 1+ { newCount }
        align here newCount cells allot { newEnv }
        0 { i }
        BEGIN i oldCount < WHILE
            oldEnv i cells + @
            newEnv i cells + !
            i 1+ TO i
        REPEAT
        captured newEnv oldCount cells + !

        align here 2 cells allot { newHandle }
        THUNK newHandle !
        ['] invokeClosure newHandle cell+ !
        functionMode argumentMode combineModes { newMode }
        newHandle KIND-THUNK
            hm META-CODE cells + @
            newEnv newCount newMode OWN-LIVE newMeta DROP
        functionMode MODE-LINEAR = IF
            OWN-CONSUMED hm META-STATE cells + !
        THEN
        newHandle
    ELSE
        h
    THEN
;

:noname ( ENDFLAG xn .. x2 x1 [THUNK xt1] -- [THUNK xt2])
    BEGIN
    swap
    dup ENDFLAG = if
        drop
        EXIT
    then
    swap pass
    AGAIN
; is passMany

: foldThunks ( addr - THUNK )
    pushArray       ( xn .. x2 x1 ENDFLAG )
    makeTHUNK       ( [THUNK xn] .. x2 x1 ENDFLAG)
    BEGIN
    swap            ( xn-1 [THUNK xn] .. x2 x1 ENDFLAG )
    dup ENDFLAG = if 
        drop        ( [THUNK xn] )
        EXIT
    then
    makeTHUNK pass
    AGAIN
;

variable WILDCARD 1 cells allot
: makeWILDCARD wildcard here 1 fillArray here 1 cells allot ;
:noname ." WILDCARD " ; WILDCARD 1 cells + !

variable wildcards 10 cells allot
variable pointer

: print { o1 }
    ." ("
    o1 MAXNUM @ <
    if o1 .
    else
        o1 dethunk drop
        o1 @ 1 cells + @ execute
        o1 @ @ 1 >
        if
            o1 @ @ 1 do
                o1 i cells + @
                recurse
            loop
        then
    then
        ." )"
;

: thunklessPrint { o1 }
    ." ("
    o1 MAXNUM @ <
    if o1 .
    else
        o1 dethunk drop
        o1 THUNK = 0 = if
            o1 @ 1 cells + @ execute
        then
        o1 @ @ 1 >
        if
            o1 @ @ 1 do
                o1 i cells + @
                recurse
            loop
        then
    then
        ." )"
;

: obj= ( o1 o2 -- 0/-1 )
    dup MAXNUM @ >          ( o1 o2 0/-1 )
    if                      ( o1 o2 )
        dup @ WILDCARD =        ( o1 o2 0\-1 )
        if                      ( o1 o2 )
            drop                            ( o1 )
            wildcards pointer @ cells + !   ( )
            pointer @ 1 + pointer !
            -1                              ( -1 )
            EXIT
        then
    then
    swap dup MAXNUM @ >     ( o2 o1 0/-1 )
    if                      ( o2 o1 )
        dup @ WILDCARD =        ( o2 o1 0/-1)
        if                      ( o2 o1 )
            drop                            ( o2 )
            wildcards pointer @ cells + !   ( )
            pointer @ 1 + pointer !
            -1                              ( -1 )
            EXIT
        then                    ( o1 o2 )
    then                    ( o1 o2 )
        \ deepdethunk                                ( o1 o22 )
        dethunk                                ( o1 o22 )
        \ swap deepdethunk                           ( o22 o11 )
        swap dethunk                           ( o22 o11 )
        dup MAXNUM @ <  ( o22 o11 0/-1 )
        rot             ( o11 0/-1 o22 )
        dup MAXNUM @ <  ( o11 0/-1 o22 0/-1 )
        rot +           ( o11 o22 0/-1 )
        if
            =
            EXIT
        then
        2dup                                        ( o22 o11 o22 o11 )
        @ swap @                                    ( o22 o11 t11 t22 )
        =                                           ( o22 o11 0/-1 )
        swap dup @ @                                ( o22 0/-1 o11 n )
        rot swap                                    ( o22 o11 0/-1 n )
        1 > *                                       ( o22 o11 0/-1 )
        if                                          ( o22 o11 )
            dup @ @ 1                                   ( o22 o11 n 1 )
            -1                                          ( o22 o11 n 1 -1 )
            begin
                2 pick 2 pick                               ( o22 o11 n i -1 n i )
                >                                           ( o22 o11 n i -1 0/-1 )
            while                                       ( o22 o11 n i -1 )
                3 pick 2 pick                               ( o22 o11 n i -1 o11 i )
                cells + @                                   ( o22 o11 n i -1 o11[i] )
                5 pick 3 pick                               ( o22 o11 n i -1 o11[i] o22 i )
                cells + @                                   ( o22 o11 n i -1 o11[i] o22[i] )
                swap recurse                                ( o22 o11 n i -1 0/-1 )
                *                                           ( o22 o11 n i 0/-1 )
                dup 0 = if                                  ( o22 o11 n i 0/-1 )
                    swap drop 1 pick 1 + swap               ( o22 o11 n n+1 0 )
                then
                swap 1 + swap
            repeat
                                                        ( o22 o11 n i -1 )
            >r                                          ( o22 o11 n i )
            4 dropn                                     ( )
            r>                                          ( 0/-1 )
        else
            @ swap @ =                                  ( 0/-1 )
        then
;

: fastConsume ( n -- 0 )
    BEGIN
        dup 0 = if
            EXIT
        then
        1 -
    AGAIN
;

: fastPow2 ( n -- 2^n )
    1 swap  ( 1 n -- 2^n )
    BEGIN   ( m n -- m * 2^n )
        dup 0 =
        if
            drop
            EXIT
        then
        swap 2 * swap 1 -
    AGAIN
;

: fastRange ( n -- [addr of arr n] )
    here swap
    BEGIN   ( addr n )
    dup 0 = if  ( addr n )
        ,       ( addr )
        EXIT
    then
    dup ,       ( addr n )
    1 -         ( addr n-1 )
    AGAIN
;

: cell- -1 cells ;

: mid ( l r -- mid ) over - 2/ cell- and + ;
 
: exch ( addr1 addr2 -- ) dup @ >r over @ swap ! r> swap ! ;
 
: partition ( l r -- l r r2 l2 )
  2dup mid @ >r ( r: pivot )
  2dup begin
    swap begin dup @  r@ < while cell+ repeat
    swap begin r@ over @ < while cell- repeat
    2dup <= if 2dup exch >r cell+ r> cell- then
  2dup > until  r> drop ;
 
: fastQsort ( l r -- )
  partition  swap rot
  \ 2over 2over - + < if 2swap then
  2dup < if recurse else 2drop then
  2dup < if recurse else 2drop then ;
 
: fastSort ( array len -- )
  dup 2 < if 2drop exit then
  1- cells over + fastQsort ;

\ Opt-in scalar ABI gate for audited generated entrypoints. Off by default.
\ Do not pass untrusted execution tokens to ABI-CHECKED-RUN-*.
variable ABI-CHECKED-MODE
0 ABI-CHECKED-MODE !

s" checked entrypoint returned a non-scalar ABI value" exception constant ABI-ERR-CHECKED-RESULT
s" checked entrypoint stack effect mismatch" exception constant ABI-ERR-CHECKED-STACK
s" checked conditional requires a canonical boolean" exception constant ABI-ERR-CHECKED-CONDITION

\ Capture the actual native operators before defining checked dispatch wrappers.
: ABI-LEGACY-PLUS + ;
: ABI-LEGACY-MINUS - ;
: ABI-LEGACY-STAR * ;
: ABI-LEGACY-SLASH / ;
: ABI-LEGACY-MOD mod ;
: ABI-LEGACY-EQUAL = ;
: ABI-LEGACY-GE >= ;
: ABI-LEGACY-LT < ;

: ABI-CHECKED? ( -- flag ) ABI-CHECKED-MODE @ 0<> ;

\ Raw natural cells in the scalar subset become immutable modal handles.
\ A tracked value must already be a scalar handle; wrong-kind handles fail closed.
: ABI-COERCE-NAT { value -- handle }
    value metadata@ { meta }
    meta 0<> IF
        value ABI-SCALAR-INFO DROP DROP DROP
        value EXIT
    THEN
    value 0< IF ABI-ERR-NAT-NEGATIVE THROW THEN
    value ABI-MAX-NAT > IF ABI-ERR-NAT-OVERFLOW THROW THEN
    value MODE-MODAL ABI-MAKE-SCALAR
;

: ABI-CHECKED-BINARY { left right checked legacy -- result }
    ABI-CHECKED? 0= IF
        left right legacy EXECUTE EXIT
    THEN
    left ABI-COERCE-NAT { leftHandle }
    right ABI-COERCE-NAT { rightHandle }
    leftHandle rightHandle checked EXECUTE
;

\ inputCount describes the compiled entrypoint's scalar input stack arity.
\ CATCH restores the entry stack on THROW; this gate always restores its prior mode.
: ABI-CHECKED-EXECUTE { inputCount xt -- value }
    DEPTH { depthBefore }
    ABI-CHECKED-MODE @ { previousMode }
    1 ABI-CHECKED-MODE !
    xt CATCH { status }
    status 0<> IF previousMode ABI-CHECKED-MODE ! status THROW THEN
    \ Force the returned thunk while the checked gate is still active so lazily
    \ emitted arithmetic cannot escape through the legacy raw-cell operators.
    ['] deepdethunk CATCH { forceStatus }
    previousMode ABI-CHECKED-MODE !
    forceStatus 0<> IF forceStatus THROW THEN
    DEPTH depthBefore ABI-LEGACY-MINUS
    1 inputCount ABI-LEGACY-MINUS
    ABI-LEGACY-EQUAL 0= IF ABI-ERR-CHECKED-STACK THROW THEN
;

: ABI-CHECKED-RUN-NAT { inputCount xt -- handle }
    inputCount xt ABI-CHECKED-EXECUTE { result }
    result ABI-COERCE-NAT
;

: ABI-CHECKED-RUN-BOOL { inputCount xt -- handle }
    inputCount xt ABI-CHECKED-EXECUTE { result }
    result metadata@ { meta }
    meta 0<> IF
        result ABI-BOOL-INFO DROP DROP DROP
        result EXIT
    THEN
    result 0= result -1 = OR 0= IF ABI-ERR-INVALID-BOOLEAN THROW THEN
    result MODE-MODAL ABI-MAKE-BOOL
;

\ Check the runtime condition convention used by Agda: false=0, true=-1.
\ A managed linear boolean is consumed only after validation.
: ABI-CHECKED-IF-FLAG { value -- flag }
    ABI-CHECKED? 0= IF value EXIT THEN
    value metadata@ { meta }
    meta 0= IF
        value 0= value -1 = OR 0= IF ABI-ERR-CHECKED-CONDITION THROW THEN
        value EXIT
    THEN
    value ABI-BOOL-INFO { flag mode boolMeta }
    mode MODE-LINEAR = IF OWN-CONSUMED boolMeta META-STATE cells + ! THEN
    flag
;

\ These operator names are emitted by the unchanged ToForth.hs scalar preamble.
\ They dispatch only while the opt-in checked gate is active.
: + { left right -- result }
    left right ['] ABI-NAT-ADD ['] ABI-LEGACY-PLUS ABI-CHECKED-BINARY
;
: - { left right -- result }
    left right ['] ABI-NAT-SUB ['] ABI-LEGACY-MINUS ABI-CHECKED-BINARY
;
: * { left right -- result }
    left right ['] ABI-NAT-MUL ['] ABI-LEGACY-STAR ABI-CHECKED-BINARY
;
: / { left right -- result }
    left right ['] ABI-NAT-QUOT ['] ABI-LEGACY-SLASH ABI-CHECKED-BINARY
;
: mod { left right -- result }
    left right ['] ABI-NAT-REM ['] ABI-LEGACY-MOD ABI-CHECKED-BINARY
;
: = { left right -- result }
    left right ['] ABI-NAT-EQ ['] ABI-LEGACY-EQUAL ABI-CHECKED-BINARY
;
: >= { left right -- result }
    left right ['] ABI-NAT-GEQ ['] ABI-LEGACY-GE ABI-CHECKED-BINARY
;
: < { left right -- result }
    left right ['] ABI-NAT-LT ['] ABI-LEGACY-LT ABI-CHECKED-BINARY
;

\ Shadow IF only for subsequently compiled definitions. Its previous compilation
\ semantics remain the branch implementation; the added runtime check is inert
\ outside ABI-CHECKED-MODE.
: IF POSTPONE ABI-CHECKED-IF-FLAG POSTPONE IF ; IMMEDIATE
