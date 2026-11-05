\\ Strict Laurent-MALLP scalar-stack runtime checks.
\\ Loaded after MALLPStrict.fth, which must contain only the strict runtime.

: strict-assert-natural { actual expected -- }
  actual expected <> IF
    ." strict MALLP natural mismatch" cr
    -4201 THROW
  THEN
;

answerAdd 20 strict-assert-natural
answerMonus 0 strict-assert-natural
answerMultiply 20 strict-assert-natural
: testStrictOverflow ( -- )
  MALLP-MAX-NAT 1 MALLP-NAT-ADD DROP
;
' testStrictOverflow CATCH 0= abort" strict MALLP overflow was accepted"

: testStrictNegative ( -- )
  -1 MALLP-CHECK-NAT DROP
;
' testStrictNegative CATCH 0= abort" strict MALLP negative Nat was accepted"

depth 0<> abort" strict MALLP leaked data-stack cells"
cr ." mallp-strict-tests-passed" cr
BYE
