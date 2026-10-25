variable MAXNUM 100000000000000 MAXNUM !
variable ENDFLAG 1234 ENDFLAG !
s" unknown or unmanaged value handle" exception constant ABI-ERR-UNKNOWN-HANDLE
s" use after linear handle consumption" exception constant ABI-ERR-CONSUMED-HANDLE
s" linear capture was not accounted for" exception constant ABI-ERR-LINEAR-CAPTURE
s" invalid ABI scalar mode" exception constant ABI-ERR-INVALID-MODE
s" expected a scalar handle" exception constant ABI-ERR-EXPECTED-SCALAR
s" arithmetic result exceeds the checked cell range" exception constant ABI-ERR-NAT-OVERFLOW
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

0 constant META-NEXT
1 constant META-HANDLE
2 constant META-KIND
3 constant META-CODE
4 constant META-ENV
5 constant META-ENVCOUNT
6 constant META-MODE
7 constant META-STATE
8 constant META-CELLS

0 constant KIND-THUNK
1 constant KIND-RESULT
2 constant KIND-SCALAR
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

: newMeta { handle kind code env count mode state -- meta }
    align here META-CELLS cells allot { meta }
    HANDLE-META-HEAD @ meta META-NEXT cells + !
    handle meta META-HANDLE cells + !
    kind meta META-KIND cells + !
    code meta META-CODE cells + !
    env meta META-ENV cells + !
    count meta META-ENVCOUNT cells + !
    mode meta META-MODE cells + !
    state meta META-STATE cells + !
    meta HANDLE-META-HEAD !
    meta
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
    ELSE
        handle @ RESULT = IF
            align here 2 cells allot TO moved
            RESULT moved !
            handle cell+ @ moved cell+ !
            moved KIND-RESULT 0 0 0 MODE-LINEAR OWN-LIVE newMeta DROP
        ELSE
            ABI-ERR-UNKNOWN-REPRESENTATION THROW
        THEN
    THEN
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
    meta META-KIND cells + @ KIND-THUNK = IF
        meta META-CODE cells + @ modalSafeXT? 0= IF 0 EXIT THEN
        meta modalEnv? 0= IF 0 EXIT THEN
        -1 EXIT
    THEN
    meta META-KIND cells + @ KIND-RESULT = IF
        handle cell+ @ RECURSE EXIT
    THEN
    0
;

: assertModalValue { handle -- handle }
    handle requireLiveMeta { meta }
    handle isResult 0= IF ABI-ERR-ASSERT-MODAL-KIND THROW THEN
    handle cell+ @ { payload }
    payload metadata@ 0= IF ABI-ERR-UNREGISTERED-MODAL-PAYLOAD THROW THEN
    payload modalPayload? 0= IF ABI-ERR-MODAL-PAYLOAD THROW THEN
    MODE-MODAL meta META-MODE cells + !
    handle
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
    handle KIND-RESULT 0 0 0 MODE-UNANNOTATED OWN-LIVE newMeta DROP
    handle
;

: ABI-MAKE-SCALAR { value mode -- handle }
    mode MODE-LINEAR = mode MODE-MODAL = OR 0= IF ABI-ERR-INVALID-MODE THROW THEN
    align here 2 cells allot { handle }
    SCALAR handle !
    value handle cell+ !
    handle KIND-SCALAR 0 0 0 mode OWN-LIVE newMeta DROP
    handle
;

:noname ." S: " ; SCALAR 1 cells + !
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
: dethunk { value -- result }
    BEGIN
        value metadata@ { meta }
        meta 0= IF value EXIT THEN
        meta META-STATE cells + @ OWN-CONSUMED = IF ABI-ERR-CONSUMED-HANDLE THROW THEN
        value @ THUNK = IF
            meta META-MODE cells + @ MODE-LINEAR = IF
                OWN-CONSUMED meta META-STATE cells + !
            THEN
            value ENDFLAG value cell+ PERFORM
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
    payload makeRESULT { resultHandle }
    originalMeta META-MODE cells + @
    resultHandle metadata@ META-MODE cells + !
    resultHandle
;

: deepDethunk ( [THUNK o1] -- o1 )
    BEGIN
    dethunk                     ( o1 )
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
  