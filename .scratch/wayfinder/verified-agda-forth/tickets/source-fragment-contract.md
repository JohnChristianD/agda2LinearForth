---
id: source-fragment-contract
type: grilling
status: open
blocked_by: []
---

## Question

What precise source fragment is the compiler allowed to accept, and what does “full coverage” mean for that fragment?

Settle support boundaries for closed versus open terms, argument variables, named calls, recursion, constructors, cases, lazy lets, literals, Nat/Int/Word64/Float, and module dependencies. Preserve the explicit no-IO requirement and strict MALLP resource discipline.

## Required result

A total acceptance predicate over the version-pinned Treeless AST; a total classification of every Treeless constructor; a precise definition of accepted programs; and a rule that unsupported reachable runtime forms always produce diagnostics rather than disappearing from emitted output.

“Full coverage” means every pinned constructor is classified and every accepted program is covered by the theorem—not that every Agda builtin is lowerable. Resolve the initial implementation order without adding speculative IRs.
