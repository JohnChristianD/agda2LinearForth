\ MALLP-STRICT-BEGIN
\ Checked Gforth runtime for the Agda bounded token machine.
\ All failed tokens raise one exception, matching Agda Maybe's single nothing.
\ Nat cells and ROLL immediates use the same positive signed-cell bound.

[undefined] AGDA2FORTH-MALLP-LOADED [if]
true constant AGDA2FORTH-MALLP-LOADED

0 invert 1 rshift constant MALLP-MAX-NAT
s" MALLP: token failure" exception constant MALLP-ERR

: MALLP-REQUIRE-STACK { required -- }
    depth required < IF MALLP-ERR THROW THEN
;

: MALLP-CHECK-NAT { value -- }
    value 0< IF MALLP-ERR THROW THEN
    value MALLP-MAX-NAT > IF MALLP-ERR THROW THEN
;

: MALLP-PARSE-NAT ( addr len -- value )
    2 MALLP-REQUIRE-STACK
    { addr len -- }
    len 0= IF MALLP-ERR THROW THEN
    0 { acc }
    0 { index }
    BEGIN index len < WHILE
        addr index + c@ [CHAR] 0 - { digit }
        digit 0< digit 9 > OR IF MALLP-ERR THROW THEN
        acc MALLP-MAX-NAT 10 / > IF MALLP-ERR THROW THEN
        acc 10 * { scaled }
        scaled MALLP-MAX-NAT digit - > IF MALLP-ERR THROW THEN
        scaled digit + TO acc
        index 1+ TO index
    REPEAT
    acc
;

: MALLP-NAT-ADD ( left right -- result )
    2 MALLP-REQUIRE-STACK
    { left right -- }
    left MALLP-CHECK-NAT
    right MALLP-CHECK-NAT
    left MALLP-MAX-NAT right - > IF MALLP-ERR THROW THEN
    left right + { result }
    result MALLP-CHECK-NAT
    result
;

: MALLP-NAT-MONUS ( left right -- result )
    2 MALLP-REQUIRE-STACK
    { left right -- }
    left MALLP-CHECK-NAT
    right MALLP-CHECK-NAT
    left right < IF 0 ELSE left right - THEN { result }
    result
;

: MALLP-NAT-MUL ( left right -- result )
    2 MALLP-REQUIRE-STACK
    { left right -- }
    left MALLP-CHECK-NAT
    right MALLP-CHECK-NAT
    right 0<> IF
        left MALLP-MAX-NAT right / > IF MALLP-ERR THROW THEN
    THEN
    left right * { result }
    result MALLP-CHECK-NAT
    result
;

: MALLP-NAT-LITERAL ( "digits" -- )
    PARSE-NAME MALLP-PARSE-NAT POSTPONE LITERAL
; IMMEDIATE

: MALLP-TRUE ( -- flag ) -1 ;
: MALLP-FALSE ( -- flag ) 0 ;

: MALLP-SWAP ( x y -- y x )
    2 MALLP-REQUIRE-STACK
    SWAP
;

: MALLP-NAT-ROLL ( ... depth -- ... )
    1 MALLP-REQUIRE-STACK
    DEPTH 1- { available }
    { roll-index -- }
    roll-index MALLP-CHECK-NAT
    roll-index available >= IF MALLP-ERR THROW THEN
    roll-index ROLL
;

: MALLP-CHECK-BOOL ( flag -- flag )
    1 MALLP-REQUIRE-STACK
    { value -- }
    value 0 <> value -1 <> AND IF MALLP-ERR THROW THEN
    value
;

: MALLP-IF ( flag -- )
    POSTPONE MALLP-CHECK-BOOL
    POSTPONE IF
; IMMEDIATE

: MALLP-ELSE POSTPONE ELSE ; IMMEDIATE
: MALLP-THEN POSTPONE THEN ; IMMEDIATE

\ Canonical Codyad exponent ABI:
\   sign = 0, magnitude = 0  : zero
\   sign = 1, magnitude > 0  : positive
\   sign = 2, magnitude > 0  : negative
\ The source mantissa producer is an opaque execution-token cell below the
\ exponent. These words touch only top two cells:
\ ( ... mantissa-xt sign magnitude -- ... mantissa-xt sign' magnitude' )

: MALLP-CODYAD-CHECK-EXPONENT ( sign magnitude -- sign magnitude )
    2 MALLP-REQUIRE-STACK
    { sign magnitude -- }
    sign MALLP-CHECK-NAT
    magnitude MALLP-CHECK-NAT
    sign 0= IF
        magnitude 0<> IF MALLP-ERR THROW THEN
    ELSE
        sign 1 = IF
            magnitude 0= IF MALLP-ERR THROW THEN
        ELSE
            sign 2 = IF
                magnitude 0= IF MALLP-ERR THROW THEN
            ELSE
                MALLP-ERR THROW
            THEN
        THEN
    THEN
    sign magnitude
;

: MALLP-CODYAD-SHIFT-LEFT ( sign magnitude -- sign' magnitude' )
    MALLP-CODYAD-CHECK-EXPONENT
    { sign magnitude -- }
    sign 0= IF
        1 1
    ELSE
        sign 1 = IF
            magnitude MALLP-MAX-NAT = IF MALLP-ERR THROW THEN
            1 magnitude 1+
        ELSE
            magnitude 1 = IF
                0 0
            ELSE
                2 magnitude 1-
            THEN
        THEN
    THEN
;

: MALLP-CODYAD-SHIFT-RIGHT ( sign magnitude -- sign' magnitude' )
    MALLP-CODYAD-CHECK-EXPONENT
    { sign magnitude -- }
    sign 0= IF
        2 1
    ELSE
        sign 1 = IF
            magnitude 1 = IF
                0 0
            ELSE
                1 magnitude 1-
            THEN
        ELSE
            magnitude MALLP-MAX-NAT = IF MALLP-ERR THROW THEN
            2 magnitude 1+
        THEN
    THEN
;

[then]
\ MALLP-STRICT-END
