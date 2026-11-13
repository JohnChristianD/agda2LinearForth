\ MALLP-STRICT-BEGIN
\ Checked Gforth boundary for MALLPForth.execBoundedToken.
\ Every semantic failure maps to Agda's single Maybe nothing case.
\ Target Nat values and ROLL immediates fit the positive signed-cell bound.
\ Boolean control accepts precisely Gforth FALSE (0) and TRUE (-1).

[undefined] AGDA2FORTH-MALLP-LOADED [if]
true constant AGDA2FORTH-MALLP-LOADED

0 invert 1 rshift constant MALLP-MAX-NAT
s" MALLP: negative natural" exception constant MALLP-ERR-NEGATIVE
s" MALLP: natural overflow" exception constant MALLP-ERR-OVERFLOW
s" MALLP: invalid natural literal" exception constant MALLP-ERR-LITERAL
s" MALLP: ROLL stack underflow" exception constant MALLP-ERR-STACK

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

: MALLP-NAT-ROLL ( ... depth -- ... )
    { depth }
    depth MALLP-CHECK-NAT
    depth DEPTH >= IF MALLP-ERR-STACK THROW THEN
    depth ROLL
;


: MALLP-ROLL ( ... depth -- ... )
    1 MALLP-REQUIRE-STACK
    { index -- }
    index MALLP-CHECK-NAT
    depth index <= IF MALLP-ERR THROW THEN
    index ROLL
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

[then]
\ MALLP-STRICT-END
