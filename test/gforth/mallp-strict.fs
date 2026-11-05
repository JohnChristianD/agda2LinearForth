\ Strict MALLP runtime tests. MALLPStrict.fth is loaded before this file.
answerAdd 20 <> abort" strict MALLP addition failed"
answerMonus 0 <> abort" strict MALLP monus failed"
answerMultiply 20 <> abort" strict MALLP multiplication failed"
answerQuotient 7 <> abort" strict MALLP quotient failed"

: testStrictOverflow ( -- )
  MALLP-MAX-NAT 1 MALLP-NAT-ADD
;
' testStrictOverflow catch 0= abort" strict MALLP overflow was accepted"

: testStrictNegative ( -- )
  -1 MALLP-CHECK-NAT
;
' testStrictNegative catch 0= abort" strict MALLP negative Nat was accepted"

cr ." mallp-strict-tests-passed" cr
bye
