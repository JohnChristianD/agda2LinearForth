# Wayfinder map: verified no-IO Agda-to-Forth compiler

## Destination

Reach a compositional, machine-checkable compiler-correctness result for a clearly delimited MALLP-compatible Agda fragment, compiled through Agda 2.8.0.2 Treeless into a typed Forth program and a formal model of the Gforth subset it uses.

“Full coverage” means **every constructor in the pinned Agda/Treeless interface is classified exactly once** as (1) runtime-lowered, (2) erased with evidence, (3) consumed during elaboration/type checking, or (4) rejected with a diagnostic. It does not mean every Agda builtin must become a Forth word. IO, FFI, and effectful runtime features are rejected. Every accepted term must fall under the composed semantic-preservation theorem; unsupported reachable forms must fail closed.

## Notes

- Repository: `JohnChristianD/agda2MALLPForth`; base: `master`.
- Agda source pin: `v2.8.0.2` in `cabal.project`.
- Preserve the current option policy. **Do not add `--safe`**; the project intentionally retains documented postulates and rewrite assumptions.
- No IO sites: reachable IO, FFI, or effectful runtime builtins are rejected before code emission. No IO IR or FFI event semantics are introduced.
- Keep Laurent MALLP strict: no weakening, contraction, or exponentials are smuggled into the resource model.
- Ponytail constraint: use the smallest pass structure that covers accepted semantics. PureCake's ThunkLang/EnvLang/StateLang are models to study, not mandatory IRs for the closed Nat fragment.
- GitHub Issues are disabled for this repository. This map and its tickets use a local Markdown tracker under this directory. Ticket filenames are their stable identities; `blocked_by` in each ticket records dependencies.
- REA reverse-engineering workflows are out of scope here: this is an inspectable source repository, not a shipped binary or opaque application.

## Decisions so far

- Current executable backend coverage is only closed Nat literals, addition, monus, and multiplication. The Haskell backend emits text directly; the Agda Forth syntax is not connected to that output.
- The current formal MALLP calculus is proof-tree syntax. It has no computational proof-term bridge to Treeless or emitted Forth.
- The RSED file's signed integer functions and sample equations are separate from the compiler proof; they do not establish general integer correctness or Forth lowering.
- PureCake's strongest reusable method is **relation-first verification**: define pass relations, prove each relation preserves semantics, then prove the concrete compiler functions inhabit those relations. Its paper also makes the frontend trust boundary explicit; its end-to-end result composes with CakeML's separately verified compiler. See [PureCake paper](https://cakeml.org/pldi23-purecake.pdf) and [official project](https://github.com/CakeML/pure).
- Hamano–Scott provides a categorical interpretation framework for polarized MALL, using an ambient *-autonomous category with reflective/coreflective polarized subcategories. It can interpret MALLP derivations and justify the linear/polarity structure; it does **not** prove an operational compiler or the generated Forth code. Full completeness for MALLP fails in the paper's hypercoherence model. See [Hamano–Scott (2007)](https://www.site.uottawa.ca/~phil/papers/Hamano_Scott_pol_MALL.pdf).
- Agda's Treeless syntax is explicitly backend-facing and includes more constructors than the current decoder handles. Its `TLet` has a demand condition (“evaluate only when used”), and `TCase` carries case information and alternatives. See [Agda 2.8.0.2 Treeless API](https://hackage-content.haskell.org/package/Agda-2.8.0.2/docs/Agda-Syntax-Treeless.html).

## Not yet specified

- The exact exhaustive Agda 2.8.0.2 inventory and a generated/version-checked coverage manifest.
- The admitted source fragment beyond closed Nat expressions: open variables, function calls, recursion, constructors, cases, and lazy/demand behavior.
- The exact theorem boundary between checked Agda source, Agda's internal Treeless conversion, and the compiler-owned core.
- A Gforth operational semantics matching the actual runtime words, cell bound, parser, exceptions, and stack effects.
- The concrete Hamano–Scott model and the bridge from MALLP derivations to source usage and target stack resources.
- The final composed theorem and the division between a formal Gforth-subset theorem and empirical execution by the installed Gforth implementation.

## Out of scope

- Compiling IO, FFI, or effectful runtime code.
- Claiming that every builtin is executable. Every builtin must be classified; incompatible or unimplemented runtime families are rejected.
- Proving Agda's type checker, kernel, or the Agda Treeless generator correct in this first backend-verification milestone. The initial backend theorem starts at a pinned, accepted Treeless term; the upstream frontend remains in the trusted computing base unless a later milestone adds a source-to-Treeless theorem.
- Claiming a verified Gforth machine-code backend. The initial target theorem is for a formal model of the emitted Forth subset; execution under real Gforth remains an integration check unless a verified Gforth implementation/compiler is separately connected.

## Open frontier

- [Agda 2.8.0.2 inventory](tickets/agda-2-8-0-2-inventory.md) — research; unblocked.
- [Gforth runtime semantics](tickets/gforth-runtime-semantics.md) — research; unblocked.
- [Source fragment and coverage contract](tickets/source-fragment-contract.md) — grilling; unblocked.
- [Agda frontend trust boundary](tickets/frontend-trust-boundary.md) — grilling; depends on the inventory.
- [Hamano–Scott bridge](tickets/hamano-scott-bridge.md) — research/design; depends on the source contract.
- [Pass relations and compiler composition](tickets/pass-relations.md) — task; blocked by the inventory, runtime model, source contract, frontend boundary, and categorical bridge.
- [Renderer and Gforth simulation](tickets/renderer-runtime-simulation.md) — task; blocked by pass relations and runtime semantics.

## Stopping condition

The map is clear when the source boundary, trust boundary, exhaustive manifest, target semantics, linear adequacy bridge, and proof composition are decided. At that point collapse the decisions into a buildable specification, then implement the smallest complete verified slice. Do not add a new per-builtin proof workaround when a single generic semantic rule and its implementation relation cover the family.
