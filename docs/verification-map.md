# End-to-end compiler/runtime verification map

## Destination

Prove that every program in a clearly bounded supported Agda/Treeless fragment is translated into Forth whose concrete stack, descriptor heap, ownership, exception, and observation behaviour refines the source semantics. Keep Haskell compiler sources pinned and unchanged unless that constraint is explicitly revised.

## Notes

Use Agda --safe --no-libraries core. Keep the WP transformer as the only contract API. Pair Agda full-state WP lemmas with tests and operation-level contracts for the corresponding Forth words. `ToForth.hs` is now the single allowed Haskell exception to upstream identity checks. A green test is evidence for its tested cases, not a universal refinement proof. Do not assert a generic frame rule until a concrete runtime footprint is proved.

## Decisions so far

- WP-only contracts: wp, operational SemanticTriple, sequencing/CATCH laws, wpCatchPreserves, WP leastness/validity, and allocation/null-token contracts live in formal/LinearModalSafety.agda. The artificial generic frame abstraction was removed; stack, heap and metadata belong in the complete state.
- Allocation atomicity is the first paired operation-level obligation: identity exhaustion is modelled in ABIAllocationWP and checked against concrete Forth preflight plus adversarial Gforth assertions. The checked binary transaction has WP lemmas for arithmetic/result-allocation failures and Gforth checks that both input handles remain live.
- The generated scalar example previously returned 5 rather than 25. Keep that counterexample open; allocation atomicity does not fix compiler application/lowering.

## Not yet specified

- The exact source/Treeless grammar and semantic relation used as the theorem's domain.
- Whether memory should remain in a dictionary-allocated arena with lifetime-long tombstones or move to `ALLOCATE`-backed blocks with explicit ownership/freeing; any choice must preserve metadata-list validity and exception atomicity.
- A formally checked emitter relation for literals, curried application, closures/environments, constructors, pattern matches, conditionals, and primitive calls.
- Concrete state interpretation for dictionary entries/code pointers, output and CATCH/THROW; footprints and invariants for every state-mutating word.
- Whether the target theorem is forward simulation only, adequacy/reflection, or a stronger equivalence, plus treatment of divergence.

## Out of scope

- Unrestricted arbitrary hand-written Forth, raw memory access, unknown execution tokens, and unsupported Agda constructs; these must fail closed or be excluded explicitly, not silently covered by the supported-fragment theorem.
