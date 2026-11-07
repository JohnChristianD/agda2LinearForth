# Wayfinder map: MALLP-only PureCake verification

## Destination

Prove a compositional compiler-correctness theorem for a MALLP-restricted pure subset of PureCake-style programming, starting from pinned Agda 2.8.0.2 Treeless and ending at a formal model of the emitted Forth subset.

Coverage is exact and fail-closed: every reachable source/IR construct is either lowered with a semantic-preservation theorem, erased with Agda evidence, consumed during elaboration, or rejected with a diagnostic. “PureCake coverage” does not mean the whole PureCake language is already compiled here.

## Repository invariants

- Only `src/Agda/Compiler/ToForth.hs` may differ from pinned Agda2Scheme Haskell sources.
- Agda source pin: `v2.8.0.2` in `cabal.project`.
- Keep existing proof options and postulate boundary; do not silently add `--safe`.
- No IO, FFI, monadic effects, weakening, contraction, or exponentials in the admitted MALLP source fragment.
- Keep the implementation minimal. Add an IR stage only when an admitted feature needs it and its pass theorem can be stated.
- `.scratch/wayfinder/verified-agda-forth/MAP.md` and `README.md` are the two tracked Markdown documents expected by provenance CI.

## Implemented formal fragment

The checked Agda file now contains:

1. `MALLP`: Laurent's polarized sequent proof-tree calculus. It remains the general logical calculus; it has no computational lambda terms.
2. `MALLPNatProof`: a focused computational signature for the closed Nat backend. Literal axioms consume zero Nat assumptions; each binary primitive axiom consumes two; cut composes resource-indexed proofs.
3. `MALLPNatTheory`: an explicit MALLP-with-Nat-signature derivation layer. `embedNatProof` embeds the focused Nat proofs into this theory. This is an extension by primitive Nat constants, not a derivation of arithmetic from pure MALLP connectives.
4. `interpretMALLPNatProof`: an environment semantics for the ordered Nat resources.
5. `natExprProof-adequate`: proves that the Nat proof-term interpretation equals `evalNatExpr`.
6. `natMALLP-forth-sound`: composes the proof-term interpretation with indexed Forth execution and the abstract postfix-token interpreter; the original residual stack is preserved.

This theorem is an Agda theorem about the formal Nat AST, code AST, and token interpreter. It does not yet establish that Haskell decoding/rendering or real Gforth implements those definitions.

## MALLP-only PureCake coverage matrix

| PureCake-style feature | Current disposition | Evidence / missing obligation |
| --- | --- | --- |
| Closed Nat literals | Formally covered in focused Nat theory | Nullary proof axiom; evaluation adequacy and token-machine theorem |
| Nat addition | Formally covered in focused Nat theory | Binary primitive axiom and cut; source provenance in Treeless still open |
| Nat monus | Formally covered in focused Nat theory | Separate Nat operation; never reinterpret signed `PSub` |
| Nat multiplication | Formally covered in focused Nat theory | Binary primitive axiom and cut; source provenance in Treeless still open |
| Abstraction/application and closures | Rejected | No linear lambda proof terms, closure typing, or closure-conversion simulation |
| User function calls | Rejected | No call graph / function-environment semantics or recursive-call pass |
| Constructors and finite ADTs | Rejected | No constructor layout, field ownership, or consuming case semantics |
| Pattern matching / additive branches | Rejected | No branch-sensitive resource join or target branch simulation |
| Lists | Rejected | No generic inductive representation, list eliminator, or linear-use proof |
| Structural recursion | Rejected | No recursive-call relation or induction/termination simulation |
| General `letrec` | Out of base fragment | Requires a separately specified fixpoint/recursive-type extension |
| Delay / force / coinductive streams | Rejected | No demand/observation relation or guarded productivity proof |
| Shared/memoized thunks | Out of base fragment | Repeated forcing requires an explicit duplicability policy and state semantics |
| Int, Word64, Float, Char, String | Rejected | Distinct representations and primitive semantics required |
| IO, FFI, monadic effects | Rejected | Outside the pure source language |

A passing fixture does not change a row's disposition. A feature becomes covered only after the source construct, resource judgement, pass relation, target operation, and simulation theorem are all present.

## Resource discipline

Each accepted variable/field/argument has a usage count fixed by the MALLP derivation. Tensor splits resources; additive choice selects one branch; no rule may silently copy or discard a resource. Agda's ordinary typing is not a linearity proof. Erasure is admissible only with the checker-provided relevance/usage evidence.

The current Nat proof language has no variables or captures, so its resource invariant is structural: literals consume none, binary operations consume two, and cut substitutes one produced value into one linear assumption. This explains why its generated stack code needs no duplicate/drop primitive.

## PureCake method and pass boundary

PureCake's useful contribution is the proof method: define source and target semantics, relate each pass by a syntactic simulation/refinement relation, prove the implemented transformation satisfies that relation, then compose. Its HOL4 theorem for PureLang-to-CakeML does not transfer to this Agda/Haskell/Forth repository.

Smallest sensible pass sequence:

1. **Closed Nat:** typed Nat expression → focused MALLP Nat proof → bounded indexed stack code → formal token interpreter. No heap, closure, environment, or thunk IR is needed.
2. **Finite data and recursion (future):** add typed constructors, consuming case semantics, recursive-call relation, and branch-sensitive resource proof.
3. **Laziness (future):** start with one-shot stateless delay/force if the source fragment requires it. Add environments for closures and mutable thunk state only when captured-resource ownership and repeated demand require them.
4. **Composition:** prove each pass relation and connect generated Haskell output to the Agda renderer/token semantics; then relate the formal Forth subset to the selected Gforth implementation.

## Remaining semantic gaps

- **Proof-certificate enforcement:** the Haskell backend currently does not consume or validate an `MALLPNatProof` certificate. The formal proof fragment is not yet a compiler admission gate.
- **Treeless provenance:** a top-level Nat result check does not establish that each `PAdd`/`PMul` node is Nat-typed. Preserve type evidence before builtin lowering, or reject ambiguous nodes.
- **Range:** Agda Nat is unbounded; current Gforth cells are finite signed cells. Prove every literal and intermediate fits a target limit, or use verified arbitrary precision. A runtime overflow throw is not Agda Nat semantics.
- **Manifest:** classify every pinned BuiltinId, PrimitiveId, TTerm, TPrim, TAlt, CaseType, CaseInfo, TError, ArgUsage, and EvaluationStrategy constructor exactly once; add a pin-drift check.
- **Haskell relation:** prove the actual decoder, AST/rendering path, and emitted tokens satisfy the Agda relations. A parallel formal renderer alone is not implementation verification.
- **Gforth relation:** formalize cell width, parser, arithmetic, stack effects, exceptions, dictionary/resource behavior, and relate the actual Gforth execution to the formal machine.
- **Frontend trust:** Agda's type checker and Treeless generator remain trusted inputs unless a separate source-to-Treeless theorem is added.
- **Hamano–Scott:** categorical soundness is an adequacy layer for MALLP proofs, not an operational compiler theorem. Define the required *-autonomous/category structure and connect it to source usage and target resources before making categorical coverage claims.

## CI acceptance

The relevant gates are: repository/upstream provenance; Agda 2.8.0.2 CLI; both Agda formal checks; Haskell backend build; closed-Nat fixture generation; generated-code restrictions; real Gforth integration fixture. A green run establishes these gates only. The formal MALLP Nat theorem is checked by the Agda proof gate, not inferred from the fixture.

## Stop condition

Do not broaden the language until the current formal Nat proof checks on the latest commit. Then close proof-certificate enforcement, Treeless provenance, range semantics, Haskell renderer correspondence, and formal-to-real Gforth refinement. Only after those pass should ADTs, recursion, closures, or laziness be added.
