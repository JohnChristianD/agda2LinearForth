variable MAXNUM 100000000000000 MAXNUM !
variable ENDFLAG 1234 ENDFLAG !
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
0 constant MODE-UNKNOWN
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
    handle metadata@ dup 0= abort" unregistered value handle"
    dup META-STATE cells + @ OWN-CONSUMED = abort" use after linear handle consumption"
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
            child META-MODE cells + @ MODE-UNKNOWN = IF 0 TO good THEN
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
                    childHandle result <> abort" linear capture neither consumed, moved, nor returned"
                THEN
            THEN
        THEN
        i 1+ TO i
    REPEAT
;

: combineModes { left right -- mode }
    left MODE-UNKNOWN = right MODE-UNKNOWN = OR IF MODE-UNKNOWN EXIT THEN
    left MODE-LINEAR = right MODE-LINEAR = OR IF MODE-LINEAR EXIT THEN
    MODE-MODAL
;

: invokeClosure { handle -- }
    handle metadata@ dup 0= abort" closure has no metadata"
    { meta }
    meta META-ENV cells + @
    meta META-ENVCOUNT cells + @
    pushArrayN
    meta META-CODE cells + @ execute
;

: moveLinearHandle { handle meta -- moved }
    0 { moved }
    handle @ THUNK = IF
        THUNK align here 2 cells allot TO moved
        THUNK moved !
        ['] invokeClosure moved cell+ !
        moved KIND-THUNK
            meta META-CODE cells + @
            meta META-ENV cells + @
            meta META-ENVCOUNT cells + @
            MODE-LINEAR OWN-LIVE newMeta DROP
    ELSE
        handle @ RESULT = IF
            RESULT align here 2 cells allot TO moved
            RESULT moved !
            handle cell+ @ moved cell+ !
            moved KIND-RESULT 0 0 0 MODE-LINEAR OWN-LIVE newMeta DROP
        ELSE
            abort" cannot move unknown linear handle representation"
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
    handle isThunk 0= abort" assertLinear requires a closure thunk; results inherit mode from checked closures"
    meta trackedEnv? 0= abort" cannot assert linearity with unknown or consumed captures"
    meta META-CODE cells + @ linearSafeXT?
        0= abort" closure XT lacks a linear-safe contract"
    MODE-LINEAR meta META-MODE cells + !
    handle
;

: assertModalValue { handle -- handle }
    handle requireLiveMeta { meta }
    handle isResult 0= abort" assertModalValue requires a RESULT wrapper"
    MODE-MODAL meta META-MODE cells + !
    handle
;

: promoteModal { handle -- handle }
    handle requireLiveMeta { meta }
    handle isThunk 0= abort" promoteModal requires a THUNK closure"
    meta META-CODE cells + @ modalSafeXT? 0= abort" closure XT lacks a modal-safe contract"
    meta modalEnv? 0= abort" promotion rejected: environment is not entirely registered and modal"
    MODE-MODAL meta META-MODE cells + !
    handle
;

: makeTHUNK { xt -- handle }
    xt isThunk xt isResult OR IF xt EXIT THEN
    THUNK align here 2 cells allot { handle }
    THUNK handle !
    ['] invokeClosure handle cell+ !
    handle KIND-THUNK xt 0 0 MODE-UNKNOWN OWN-LIVE newMeta DROP
    handle
;

:noname ." T: " ; THUNK 1 cells + !

: makeRESULT { value -- handle }
    RESULT align here 2 cells allot { handle }
    RESULT handle !
    value handle cell+ !
    handle KIND-RESULT 0 0 0 MODE-UNKNOWN OWN-LIVE newMeta DROP
    handle
;

:noname ." R: " ; RESULT 1 cells + !

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
        meta META-STATE cells + @ OWN-CONSUMED = abort" use after linear handle consumption"
        value @ THUNK = IF
            meta META-MODE cells + @ MODE-LINEAR = IF
                OWN-CONSUMED meta META-STATE cells + !
            THEN
            value ENDFLAG value DUP cell+ PERFORM
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
        MODE-UNKNOWN { argumentMode }
        xm 0<> IF xm META-MODE cells + @ TO argumentMode THEN

        functionMode MODE-LINEAR = argumentMode MODE-UNKNOWN = AND
            abort" checked linear closure cannot capture an untracked value"
        functionMode MODE-MODAL = argumentMode MODE-UNKNOWN = AND
            abort" checked modal closure cannot capture an untracked value"
        argumentMode MODE-LINEAR = IF
            functionMode MODE-UNKNOWN = abort" linear value cannot enter an unknown closure"
            hm META-CODE cells + @ linearSafeXT? 0=
                abort" closure XT lacks a linear-capture contract"
        THEN
        x h = argumentMode MODE-LINEAR = AND
            abort" linear closure cannot capture itself"

        x captureValue { captured }
        hm META-ENVCOUNT cells + @ { oldCount }
        hm META-ENV cells + @ { oldEnv }
        oldCount 1+ { newCount }
        align here newCount cells allot { newEnv }
        captured newEnv !
        0 { i }
        BEGIN i oldCount < WHILE
            oldEnv i cells + @
            newEnv i 1+ cells + !
            i 1+ TO i
        REPEAT

        THUNK align here 2 cells allot { newHandle }
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
  