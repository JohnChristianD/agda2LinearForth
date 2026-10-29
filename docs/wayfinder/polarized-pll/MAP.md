# Wayfinder map: TypeTopology numerics to verified polarized Forth

## Destination

Produce a reviewable specification and implementation route for the relevant ideas in TypeTopology's CompactTypes, CoNaturals, and Dyadics, and prove a bounded end-to-end compiler/runtime correctness theorem for a precisely stated fragment of Olivier Laurent's polarized linear logic (PLL).

The destination is not “some tests pass.” It is: source calculus, proof rules, operational semantics, resource discipline, target ABI, compiler relation, and theorem are explicit and linked; CI executes examples generated from the formal specification. Never claim full Laurent PLL if only a smaller fragment is implemented.

## Notes

- Keep Agda as the source of truth and use the existing agda2forth stack/runtime unless evidence forces a different target boundary.
- No new classical assumptions. State all postulates and their use.
- No Float-related work.
- Avoid importing TypeTopology wholesale. Audit dependencies and assumptions, then adapt only the needed definitions.
- Compactness/searchability, conatural numbers, and dyadic rationals are distinct concepts; do not collapse them into one feature.
- Runtime tests are necessary evidence, not substitutes for a refinement theorem.
- The user explicitly requested implementation, not planning alone. After the blocking source/assumption and calculus decisions are settled, continue with a small vertical slice and its end-to-end refinement proof; do not stop at the roadmap.
- GitHub Issues are disabled for this repository, so this local Markdown map is the tracker.

## Decisions so far

- None yet.

## Decision tickets

- [Source and assumption audit](tickets/01-source-and-assumptions.md)
- [Define the exact PLL fragment](tickets/02-pll-fragment.md)
- [Choose representations and the compiler-correctness boundary](tickets/03-representations-and-refinement.md)

## Not yet specified

- How much of CompactTypes is actually needed for the desired theorem versus being adjacent inspiration.
- Whether conaturals/dyads are represented as executable finite observations, streams, or abstract values. This determines what the Forth target can honestly implement.
- The exact polarization, exponentials, context discipline, cut/reduction relation, and theorem strength to claim.
- Whether the existing Forth ABI can model linear resource usage directly or needs a restricted intermediate representation.
- Which upstream proofs can be ported without introducing extensionality, choice, or library dependencies unavailable in the target repository.

## Out of scope

- Whole-repository TypeTopology import without a dependency audit.
- Claiming end-to-end correctness from selected examples alone.
- Unrelated compiler cleanup.
