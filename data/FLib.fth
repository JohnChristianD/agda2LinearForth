\ MALLP-STRICT-BEGIN
\ Strict Laurent-MALLP scalar runtime, matching MALLPForth.execBoundedToken.
\ MALLP-MAX-NAT is the largest nonnegative signed Gforth cell, the bound
\ supplied to Agda's bounded token interpreter.
\ Agda's just stack is the same returned Forth stack; its collapsed nothing
\ failure is represented by THROW (observable through CATCH).
\ Arithmetic consumes both operands and checks the returned result.
\ No descriptors, thunks, closures, arena allocation, or GC.
[undefined] AGDA2FORTH-MALLP-LOADED [if]
true constant AGDA2FORTH-MALLP-LOADED

0 invert 1 rshift constant MALLP-MAX-NAT
s" MALLP: negative natural" exception constant MALLP-ERR-NEGATIVE
s" MALLP: natural overflow" exception constant MALLP-ERR-OVERFLOW
s" MALLP: invalid natural literal" exception constant MALLP-ERR-LITERAL
s" MALLP: ROLL stack underflow" exception constant MALLP-ERR-STACK

: MALLP-CHECK-NAT { value -- }
    value 0< IF MALLP-ERR-NEGATIVE THROW THEN
    value MALLP-MAX-NAT > IF MALLP-ERR-OVERFLOW THROW THEN
;

: MALLP-PARSE-NAT { addr len -- value }
    len 0= IF MALLP-ERR-LITERAL THROW THEN
    0 { acc }
    0 { index }
    BEGIN index len < WHILE
        addr index + c@ [CHAR] 0 - { digit }
        digit 0< digit 9 > OR IF MALLP-ERR-LITERAL THROW THEN
        acc MALLP-MAX-NAT 10 / > IF MALLP-ERR-OVERFLOW THROW THEN
        acc 10 * { scaled }
        scaled MALLP-MAX-NAT digit - > IF MALLP-ERR-OVERFLOW THROW THEN
        scaled digit + TO acc
        index 1+ TO index
    REPEAT
    acc MALLP-CHECK-NAT
    acc
;

: MALLP-NAT-ADD ( left right -- result )
    { left right }
    left MALLP-CHECK-NAT
    right MALLP-CHECK-NAT
    left MALLP-MAX-NAT right - > IF MALLP-ERR-OVERFLOW THROW THEN
    left right + { result }
    result MALLP-CHECK-NAT
    result
;

: MALLP-NAT-MONUS ( left right -- result )
    { left right }
    left MALLP-CHECK-NAT
    right MALLP-CHECK-NAT
    left right < IF 0 ELSE left right - THEN { result }
    result MALLP-CHECK-NAT
    result
;

: MALLP-NAT-MUL ( left right -- result )
    { left right }
    left MALLP-CHECK-NAT
    right MALLP-CHECK-NAT
    right 0<> IF
        left MALLP-MAX-NAT right / > IF MALLP-ERR-OVERFLOW THROW THEN
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





[then]
\ MALLP-STRICT-END
