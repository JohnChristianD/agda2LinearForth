---
id: gforth-runtime-semantics
type: research
status: in_progress
blocked_by: []
---

## Question

What exact operational semantics must the compiler model for words in data/FLib.fth?

## Evidence gathered

- MALLP-CHECK-NAT: input one signed cell; negative values throw MALLP-ERR-NEGATIVE; values above maxNat throw MALLP-ERR-OVERFLOW; normal return consumes input and leaves no data-stack value.
- MALLP-PARSE-NAT: consumes addr len; accepts nonempty ASCII decimal digits only; returns one Nat. Empty or malformed literal throws MALLP-ERR-LITERAL. Before each multiply it checks acc <= floor(maxNat/10); before adding digit it checks scaled <= maxNat-digit.
- MALLP-NAT-ADD: consumes two checked Nat operands; checks left <= maxNat-right; returns sum or throws overflow.
- MALLP-NAT-MONUS: consumes two checked Nat operands; returns zero when left < right, otherwise left-right.
- MALLP-NAT-MUL: consumes two checked Nat operands; for right != 0 checks left <= floor(maxNat/right); returns product or throws overflow.
- All current helpers use Gforth locals. Treat each verified helper as an abstract stack-effect word, but prove its implementation against Gforth's local semantics.
- THROW has a nonzero exception path. CATCH restores the data stack to its saved depth on caught exception. Gforth exception creates user-defined exception codes.
- MALLP-MAX-NAT is 0 invert 1 rshift. For cell width w, this is 2^(w-1)-1. CI does not pin Gforth version or assert cell width; target semantics must parameterize width and CI must assert supported target.
- Current runtime uses no return-stack words, no heap allocation, and no dynamic dictionary operations. Parser reads immutable input bytes with c@. First model needs data stack, locals, parser input, signed-cell arithmetic, and error outcomes only.

## Remaining result

Specify formal subset interpreter and prove every helper's success, failure, and stack behavior. Pin or assert Gforth version/cell width in CI; separately integration-test model against Gforth.

No general heap, closures, FFI, unrestricted dictionary, or return-stack semantics until an accepted source feature requires them.

## Primary sources

- https://gforth.org/manual/Exception-handling.html
- https://gforth.org/manual/Locals.html
- https://gforth.org/manual/Bitwise-arithmetic.html
- https://github.com/JohnChristianD/agda2MALLPForth/blob/master/data/FLib.fth
