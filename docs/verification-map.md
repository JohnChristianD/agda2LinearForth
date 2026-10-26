# End-to-end compiler/runtime verification map

## Destination

Prove that every program in a clearly bounded supported Agda/Treeless fragment is translated into Forth whose concrete stack, descriptor heap, ownership, exception, and observation behaviour refines the source semantics. Keep Haskell compiler sources pinned and unchanged unless that constraint is explicitly revised.

## Notes

Use Agda --safe --no-libraries core. Keep the WP transformer as the only contract API. Pair Agda state-transition/WP lemmas with tests and operation-level contracts for the corresponding Forth words. A green test is evidence for its tested cases, not a universal refinement proof.

## Decisions so far

- WP-only contracts: wp, operational SemanticTriple, sequencing/CATCH laws, wpCatchPreserves, wpFrameRule, and WP leastness/validity live in formal/LinearModalSafety.agda.
- Allocation atomicity is the first paired operation-level obligation: identity exhaustion is modelled in ABIAllocationWP and checked against concrete Forth preflight plus adversarial Gforth assertions.
- The generated scalar example previously returned 5 rather than 25. Keep that counterexample open; allocation atomicity does not fix compiler application/lowering.

## Not yet specified

- The exact source/Treeless grammar and semantic relation used as the theorem's domain.
- A formally checked emitter relation for literals, curried application, closures/environments, constructors, pattern matches, conditionals, and primitive calls.
- Concrete state interpretation for dictionary entries/code pointers, output and CATCH/THROW; footprints and invariants for every state-mutating word.
- Whether the target theorem is forward simulation only, adequacy/reflection, or a stronger equivalence, plus treatment of divergence.

## Out of scope

- Unrestricted arbitrary hand-written Forth, raw memory access, unknown execution tokens, and unsupported Agda constructs; these must fail closed or be excluded explicitly, not silently covered by the supported-fragment theorem.
