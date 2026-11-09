\ Strict Laurent-MALLP scalar-stack runtime checks.
\ Loaded after MALLPStrict.fth, which must contain only the strict runtime.

: strict-assert-boolean { actual expected -- }
  actual expected <> IF
    ." strict MALLP boolean mismatch" cr
    -4202 THROW
  THEN
;

: strict-assert-bool-pair { actual-bottom actual-top expected-bottom expected-top -- }
  actual-bottom expected-bottom <> IF
    ." strict MALLP pair bottom mismatch" cr
    -4204 THROW
  THEN
  actual-top expected-top <> IF
    ." strict MALLP pair top mismatch" cr
    -4205 THROW
  THEN
;

: strict-assert-word64 { actual-high actual-low expected-high expected-low -- }
  actual-high expected-high <> IF
    ." strict MALLP Word64 high limb mismatch" cr
    -4206 THROW
  THEN
  actual-low expected-low <> IF
    ." strict MALLP Word64 low limb mismatch" cr
    -4207 THROW
  THEN
;

: strict-assert-natural { actual expected -- }
  actual expected <> IF
    ." strict MALLP natural mismatch" cr
    -4201 THROW
  THEN
;

answerAdd 20 strict-assert-natural
answerMonus 0 strict-assert-natural
answerMultiply 20 strict-assert-natural
answerLet 40 strict-assert-natural
answerLetShared 169 strict-assert-natural
answerLetUnused 7 strict-assert-natural
answerTrue TRUE strict-assert-boolean
answerFalse FALSE strict-assert-boolean
answerMatchedTrue FALSE strict-assert-boolean
answerMatchedFalse TRUE strict-assert-boolean
TRUE invertBool FALSE strict-assert-boolean
FALSE invertBool TRUE strict-assert-boolean
TRUE FALSE chooseBool FALSE strict-assert-boolean
FALSE TRUE chooseBool TRUE strict-assert-boolean
TRUE FALSE swapBoolPair FALSE TRUE strict-assert-bool-pair
answerUnit
10 answerIdentity 10 strict-assert-natural
10 answerAddFive 15 strict-assert-natural
3 answerMonusFive 0 strict-assert-natural
3 answerFiveMonus 2 strict-assert-natural
4 answerMultiplyFive 20 strict-assert-natural

7 13 answerAddTwo 20 strict-assert-natural
2 5 answerMonusTwo 0 strict-assert-natural
5 2 answerMonusTwo 3 strict-assert-natural
2 5 answerReverseMonusTwo 3 strict-assert-natural
4 5 answerMultiplyTwo 20 strict-assert-natural

4294967295 4294967295 answerWord64Identity
4294967295 4294967295 strict-assert-word64

2 3 4 answerThree 18 strict-assert-natural
2 3 4 answerThreeLet 18 strict-assert-natural
2 3 4 5 answerFour 48 strict-assert-natural

2 3 4 answerCallThree 9 strict-assert-natural
2 3 4 answerCallNested 18 strict-assert-natural

: testStrictOverflow ( -- )
  MALLP-MAX-NAT 1 MALLP-NAT-ADD { ignored }
;
' testStrictOverflow CATCH MALLP-ERR-OVERFLOW strict-assert-natural

: testStrictNegative ( -- )
  -1 MALLP-CHECK-NAT
;
' testStrictNegative CATCH MALLP-ERR-NEGATIVE strict-assert-natural

\ The bounded Nat machine accepts the positive cell boundary and rejects
\ arithmetic or decimal inputs that exceed it.
MALLP-MAX-NAT 0 MALLP-NAT-ADD MALLP-MAX-NAT strict-assert-natural
: testStrictMultiplyOverflow ( -- )
  MALLP-MAX-NAT 2 MALLP-NAT-MUL { ignored }
;
' testStrictMultiplyOverflow CATCH MALLP-ERR-OVERFLOW strict-assert-natural

: testStrictParseMax ( -- )
  MALLP-MAX-NAT 0 <# #S #> MALLP-PARSE-NAT
  MALLP-MAX-NAT strict-assert-natural
;
testStrictParseMax
s" 000123" MALLP-PARSE-NAT 123 strict-assert-natural

: testStrictLiteralEmpty ( -- )
  s" " MALLP-PARSE-NAT { ignored }
;
' testStrictLiteralEmpty CATCH MALLP-ERR-LITERAL strict-assert-natural

: testStrictLiteralInvalid ( -- )
  s" 12x" MALLP-PARSE-NAT { ignored }
;
' testStrictLiteralInvalid CATCH MALLP-ERR-LITERAL strict-assert-natural

: testStrictLiteralNegative ( -- )
  s" -1" MALLP-PARSE-NAT { ignored }
;
' testStrictLiteralNegative CATCH MALLP-ERR-LITERAL strict-assert-natural

: testStrictLiteralOverflow ( -- )
  s" 999999999999999999999999999999999999999999999999999999999999999999"
    MALLP-PARSE-NAT { ignored }
;
' testStrictLiteralOverflow CATCH MALLP-ERR-OVERFLOW strict-assert-natural

: assert-empty-stack ( -- )
  depth 0<> IF -4203 THROW THEN
;
assert-empty-stack
cr ." mallp-strict-tests-passed" cr
BYE
