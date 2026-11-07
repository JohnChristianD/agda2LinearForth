\ Strict Laurent-MALLP scalar-stack runtime checks.
\ Loaded after MALLPStrict.fth, which must contain only the strict runtime.

: strict-assert-boolean { actual expected -- }
  actual expected <> IF
    ." strict MALLP boolean mismatch" cr
    -4202 THROW
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
answerUnit
: testStrictOverflow ( -- )
  MALLP-MAX-NAT 1 MALLP-NAT-ADD { ignored }
;
' testStrictOverflow CATCH MALLP-ERR-OVERFLOW strict-assert-natural

: testStrictNegative ( -- )
  -1 MALLP-CHECK-NAT
;
' testStrictNegative CATCH MALLP-ERR-NEGATIVE strict-assert-natural

: assert-empty-stack ( -- )
  depth 0<> IF -4203 THROW THEN
;
assert-empty-stack
cr ." mallp-strict-tests-passed" cr
BYE
