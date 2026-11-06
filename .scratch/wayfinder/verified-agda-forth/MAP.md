# Wayfinder map: verified no-IO Agda-to-Forth compiler

## Destination

Reach a compositional, machine-checkable compiler-correctness result for a clearly delimited MALLP-compatible Agda fragment, compiled through Agda 2.8.0.2 Treeless into a typed Forth program and a formal model of the Gforth subset it uses.

“Full coverage” means every constructor in the pinned Agda/Treeless interface is classified exactly once as (1) runtime-lowered, (2) erased with evidence, (3) consumed during elaboration/type checking, or (4) rejected with a diagnostic. It does not mean every Agda builtin must become a Forth word. IO, FFI, and effectful runtime features are rejected. Every accepted term must fall under the composed semantic-preservation theorem; unsupported reachable forms must fail closed.

## Notes

- Repository: JohnChristianD/agda2MALLPForth; base: master.
- Agda source pin: v2.8.0.2 in cabal.project.
- Preserve current option policy. Do not add --safe; the project intentionally retains documented postulates and rewrite assumptions.
- No IO sites: reachable IO, FFI, and effectful runtime builtins are rejected before code emission. No IO IR or FFI event semantics are introduced.
- Keep Laurent MALLP strict: no weakening, contraction, or exponentials are smuggled into the resource model.
- Ponytail constraint: use the smallest pass structure that covers accepted semantics. PureCake's ThunkLang/EnvLang/StateLang are models to study, not mandatory IRs for the closed Nat fragment.
- GitHub Issues are disabled. This map and tickets use a local Markdown tracker; filenames are stable identities and blocked_by records dependencies.
- REA binary/application reverse-engineering workflows are out of scope: this is an inspectable source repository.

## Decisions so far

- Current executable backend coverage is only closed Nat literals, addition, monus, and multiplication. Haskell emits text directly; the Agda Forth syntax is disconnected from the Haskell output.
- Current formal MALLP calculus is proof-tree syntax. There is no computational proof-term bridge to Treeless or emitted Forth.
- RSED signed integer functions and sample equations are separate from the compiler proof; they do not establish general integer correctness or Forth lowering.
- Pinned inventory baseline: Agda v2.8.0.2 has 203 BuiltinId and 111 PrimitiveId constructors. Treeless has 14 TTerm, 23 TPrim, 3 TAlt, 7 CaseType, and 2 TError constructors. CaseInfo has caseLazy, caseErased, caseType; ArgUsage is ArgUsed/ArgUnused; EvaluationStrategy is LazyEvaluation/EagerEvaluation. Counts are research observations; per-constructor manifest and drift test remain open.
- Actual toTreeless pipeline: translateBuiltins first; fixed point (max five iterations) of simplifyTTerm, eraseTerms, caseToSeq, recoverAsPatterns; identity-function detection; then usedArguments fixed point and optional stripUnusedArguments. Backend currently asks EagerEvaluation with EraseUnused. Erasure uses Agda relevance, forced-argument, and usage facts; never guess erasure from names.
- Builtin translation: Nat zero/suc become integer literals/arithmetic; Nat plus/times/less/equality map to PAdd/PMul/PLt/PEqI; Integer pos/negsuc use identity and signed arithmetic; primForce becomes PSeq plus a demand-preserving let. Crucially Nat minus is deliberately not translated to PSub: Agda documents PSub as signed integer subtraction, while Nat minus is truncated monus.
- Potential soundness hole: current compileNatTerm maps every TPrim PSub to Nat monus without type evidence. This conflicts with Agda's pinned translation. PSub must be rejected in the initial closed-Nat slice unless typed proof licenses a Nat-specific lowering. PAdd/PMul also need source representation and range evidence before choosing bounded Nat runtime.
- PureCake method: define syntactic relations, prove each relation preserves semantics, then prove concrete compiler functions inhabit those relations. Its paper makes frontend trust boundaries explicit and composes with CakeML's verified backend. Sources: https://cakeml.org/pldi23-purecake.pdf and https://github.com/CakeML/pure.
- Hamano–Scott provides categorical interpretation for polarized MALL using an ambient *-autonomous category with reflective/coreflective polarized subcategories. It can interpret MALLP derivations and justify linear/polarity structure; it does not prove operational compiler correctness or generated Forth behavior. Full completeness for MALLP fails in the paper's hypercoherence model. Source: https://www.site.uottawa.ca/~phil/papers/Hamano_Scott_pol_MALL.pdf.
- Gforth runtime derives MALLP-MAX-NAT as 0 invert 1 rshift, the maximum nonnegative signed cell for the active cell width. Parser accepts a nonempty ASCII decimal digit sequence only and checks overflow before multiplication/addition. Add, monus, and multiply check operands and throw explicit errors. Gforth locals and THROW are used. CI currently installs Gforth from Ubuntu packages without pinning version or asserting cell width.
- A runtime overflow exception cannot stand in for Agda Nat semantics: Agda's Nat is unbounded and a source expression that returns a large Nat succeeds. The bounded-runtime theorem therefore needs a compile-time proof that every literal and every intermediate subexpression stays at or below the target maximum, or the runtime must move to arbitrary precision. For the initial closed fragment, recursively compute each Nat node's value and prove the bound for all nodes; overflow tests then verify the runtime's defensive error path, not a source-level result.
- Treeless TLet evaluates its bound term only when used; sharing is optional. TCase scrutinizes a variable; constructor alternatives are tried before ordered guards, and constructor alternatives bind an explicit arity. Source: https://hackage-content.haskell.org/package/Agda-2.8.0.2/docs/Agda-Syntax-Treeless.html.

## Not yet specified

- Explicit per-constructor inventory manifest and version-drift test.
- Admitted source fragment beyond closed Nat expressions: open variables, functions, recursion, constructors, cases, lazy/demand behavior.
- Exact theorem boundary between checked Agda source, Agda's Treeless conversion, and compiler-owned core.
- Gforth operational semantics matching cell width, parser, locals, exceptions, stack effects, and target implementation/version.
- Concrete Hamano–Scott model and bridge from MALLP derivations to source usage and target stack resources.
- Final composed theorem and division between a formal Gforth-subset theorem and empirical execution by installed Gforth.

## Out of scope

- Compiling IO, FFI, or effectful runtime code.
- Claiming every builtin is executable. Every builtin must be classified; incompatible/unimplemented runtime families are rejected.
- Proving Agda's type checker, kernel, or Treeless generator correct in the first backend-verification milestone. Initial backend theorem starts at pinned accepted Treeless; upstream frontend remains in TCB unless a later milestone proves source-to-Treeless.
- Claiming a verified Gforth machine-code backend. Initial target theorem is for a formal model of emitted Forth subset; real Gforth is integration-tested unless a verified Gforth implementation/compiler is separately connected.

## Open frontier

- [Agda 2.8.0.2 inventory](tickets/agda-2-8-0-2-inventory.md) — research; in progress.
- [Gforth runtime semantics](tickets/gforth-runtime-semantics.md) — research; in progress.
- [Source fragment and coverage contract](tickets/source-fragment-contract.md) — grilling; in progress.
- [Agda frontend trust boundary](tickets/frontend-trust-boundary.md) — grilling; depends on inventory.
- [Hamano–Scott bridge](tickets/hamano-scott-bridge.md) — research/design; depends on source contract.
- [Pass relations and compiler composition](tickets/pass-relations.md) — task; blocked by inventory, runtime model, source contract, frontend boundary, and categorical bridge.
- [Renderer and Gforth simulation](tickets/renderer-runtime-simulation.md) — task; blocked by pass relations and runtime semantics.

## Stopping condition

Map is clear when source boundary, trust boundary, exhaustive manifest, target semantics, linear adequacy bridge, and proof composition are decided. Then collapse decisions into a buildable specification and implement the smallest complete verified slice. Do not add per-builtin proof workarounds when one generic semantic rule and implementation relation cover the family.
