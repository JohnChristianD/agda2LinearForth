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

- Current executable backend coverage is only closed Nat literals, addition, builtin Nat monus, and multiplication. A small Haskell `NatExpr` core now separates Treeless decoding from Forth rendering. `TPrim PSub` is rejected: the pinned Treeless primitive is signed subtraction, while Nat monus is lowered only from the builtin Nat-minus definition. The Agda Forth syntax is still disconnected from Haskell output.
- Focused decoder checks assert Nat `PAdd`/`PMul` lowering, reject `PSub`, and reject invalid primitive arity. The existing Agda/Gforth fixture continues to exercise builtin Nat monus. The new decoder is not yet connected to a type/provenance proof or a boundedness certificate; current PAdd/PMul acceptance is an implementation subset, not a semantic-preservation theorem.
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

## Recommended proof architecture

Use **both Nat and Int**, in one compiler-specific, type-indexed source semantics, with distinct constructors and proofs:

- Nat semantics: literals, addition, multiplication, and truncated subtraction/monus. The first executable milestone remains closed Nat expressions. Because Agda Nat is unbounded while the current Gforth cell is bounded, carry a proof that every intermediate result fits MALLP-MAX-NAT; otherwise reject statically or use arbitrary precision.
- Int semantics: canonical Agda Int values, with pos n interpreted as n and negsuc n as -(n+1). Prove general addition, subtraction, multiplication, equality, ordering, normalization, and embedding laws against an integer model. Do not reuse Nat monus for signed subtraction. The current RSED arithmetic definitions and examples are not these general correctness proofs and are not connected to the compiler theorem.
- Make operation types explicit in the core: NatAdd/NatMonus/NatMul versus IntAdd/IntSub/IntMul. A flattened Treeless PSub/PAdd/PMul tag alone is insufficient to recover source meaning after builtin translation. Preserve source-type/provenance evidence before that information is erased, and reject unknown or ambiguous cases.
- The Agda mirror should define typed source expressions, source evaluation, typed Forth stack code, and a simulation theorem. Then prove the actual Haskell decoder and renderer satisfy the formal relations. A parallel Agda model with no relation to the Haskell output remains a shadow specification, not implementation verification.

### Lists, coinduction, and strictness

- **List:** introduce lists as a generic inductive data type with constructor and consuming case semantics, rather than hard-coding ad hoc list primitives. Prove constructor layout, match/branch joins, structural recursion, and stack/resource use. Agda's ordinary List is unrestricted; the MALLP source fragment must enforce a usage judgment or explicitly restrict list programs to linear use. Sharing or discarding list values cannot be implicit.
- **Coinduction:** classify ∞, ♯, ♭, primForce, and primForceLemma together. Model observation of a productive stream, guarded construction, and force as a demand boundary. Start with finite-prefix observation; a reusable memoized stream needs a separate duplicability policy.
- **Strictness:** do not equate EagerEvaluation with a proof of strictness preservation. Treeless TLet is demand-sensitive, caseLazy/caseErased affect matching, and primForce is translated through PSeq and a let. The closed, total Nat fragment can be shown strict/eager and avoid thunks. Coinductive and genuinely lazy cases need explicit delay/force semantics and a proof that evaluation order, sharing, and observable divergence/errors are preserved.

### PureCake comparison and pass selection

Use PureCake's relation-first proof pattern, not a one-to-one copy of every intermediate language:
1. Closed total Nat: typed Nat core → bounded indexed stack code → formal Forth interpreter. No heap, closure, EnvLang, or StateLang needed.
2. Finite List and recursion: add generic data/case and recursive-call semantics, with a linear usage proof.
3. Coinduction/strictness: add a minimal delay/force stage and observation semantics. Introduce explicit environments only when closures require them; introduce mutable thunk state only if the chosen semantics genuinely shares/memoizes evaluation.
4. Compose each implemented pass relation into one theorem, then connect Haskell output tokens to the Agda renderer/interpreter. PureCake's IO/FFI path is excluded by the no-IO policy.

Hamano–Scott interpretation is an independent adequacy layer for the MALLP derivation and its resource discipline. It must connect to typed source usage and target stack transitions; categorical soundness alone does not prove the compiler's operational behavior.

## Comparison with larger verified-extraction stacks

This project borrows proof architecture, not the scale or exact trust claims of the LambdaBox/Peregrine/MetaCoq ecosystem. Peregrine puts a verified Rocq middle end around LambdaBox and connects several proof-assistant frontends (Agda, Lean, Rocq) with multiple backends (CakeML, C, Rust, OCaml, WebAssembly, and others). That is a substantially broader, layered extraction system. This repository starts with one pinned Agda Treeless frontend and one explicitly modelled Forth target subset; its upstream Agda frontend and deployed Gforth implementation remain trusted until separately verified. Do not describe this as equivalent to Peregrine or a machine-code end-to-end theorem. Sources: https://peregrine-project.github.io/ and https://github.com/peregrine-project/peregrine-tool.

PureCake is the more useful pass-proof template for this task: relate source and target syntax, prove relation-level semantic preservation, then prove the implemented transformations satisfy those relations. Its lazy-to-strict stages (ThunkLang, EnvLang, StateLang) are introduced to account for delay/force, environments, and sharing. This project excludes PureCake's IO/FFI path and should add only the stages required by its chosen source fragment. Sources: https://cakeml.org/pldi23-purecake.pdf and https://github.com/CakeML/pure.

Hamano–Scott interpretation belongs beside the operational proof, not in place of it: it interprets the MALLP derivation/resource discipline categorically. A separate adequacy theorem must connect that interpretation to typed source usage and the Forth stack machine.

## Current implementation slice

- `NatCore` defines a closed typed Nat expression (`NatLiteral` / `NatBinary`) and a pure Treeless-primitive decoder. The compiler now decodes into this core before rendering Forth.
- `PSub` is rejected rather than silently reinterpreted as monus. The only monus path remains Agda's builtin Nat-minus definition.
- `test/NatCore.hs` covers PAdd, PMul, PSub rejection, and arity rejection; CI runs it alongside the Agda proof and Gforth fixture.
- This is a narrow correctness repair and a useful seam, not yet a verified compiler slice: result-type/provenance checks, Nat intermediate bounds, full constructor manifest, and an Agda relation for the Haskell decoder remain open.

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

## Remaining milestones

1. Generate a version-locked manifest covering every BuiltinId, PrimitiveId, TTerm, TPrim, TAlt, CaseType, CaseInfo, TError, ArgUsage, and EvaluationStrategy constructor. Each receives exactly one disposition: lower, erase with Agda evidence, compile-time only, or reject. CI must regenerate and compare the manifest.
2. Settle the typed source fragment and preserve type/provenance before Treeless builtin lowering.
3. Define formal Gforth cell, stack, locals, parser, and exception semantics; pin or assert the real Gforth cell width/version in CI.
4. Prove the Nat slice with a boundedness certificate; prove Int separately against integer semantics before adding Int lowering.
5. Add List/case/recursion and coinduction/demand semantics only after their ownership and strictness rules are formalized.
6. Connect Haskell decoding, target AST construction, rendering, and generated output to Agda's proof relations.
7. Compose frontend-boundary, pass-simulation, renderer, and target-interpreter theorems. Keep Agda's upstream typechecker/Treeless conversion and real Gforth compiler explicit in the trusted boundary until they are separately related or verified.

## Stopping condition

Map is clear when source boundary, trust boundary, exhaustive manifest, target semantics, linear adequacy bridge, and proof composition are decided. Then collapse decisions into a buildable specification and implement the smallest complete verified slice. Do not add per-builtin proof workarounds when one generic semantic rule and implementation relation cover the family.
