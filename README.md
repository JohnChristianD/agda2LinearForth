# agda2MALLPForth

`agda2MALLPForth` is a Haskell backend for a deliberately small Agda-to-Forth fragment. Its formal companion studies Laurent's polarized multiplicative-additive linear logic (MALLP), a typed Forth token machine, and generated Agda correspondence certificates.

**Scope:** this is a proof-producing compiler prototype for an explicitly admitted source subset. It is not a verified compiler for all Agda, and the Agda machine is not a formalization of the Gforth implementation.

## Toolchain and compatibility

CI installs the latest stable Agda package from Hackage. The latest observed run resolved Agda 2.8.0.2. `cabal.project` contains `packages: .`; the Cabal file leaves Agda version selection open. This is a moving toolchain selection rather than a fixed compiler pin.

The root pragma is:

```agda
{-# OPTIONS --rewriting --confluence-check --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections #-}
```

The generated renderer keeps one renderer-specific option:

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections #-}
```

The physics specification uses the same option list, replacing `--rewriting` with `--safe`; it contains no postulates or rewrite declarations. The MALLP root remains intentionally unsafe because it contains positive postulates and a registered rewrite system. `--exact-split` is enabled by default. `--lossy-unification` remains isolated to generated resource certificates: removing it leaves unification metas unresolved in `MALLPEmittedRenderer.agda` under Agda 2.8.0.2. It is a sound but incomplete elaboration heuristic, not a logical axiom or runtime rule. `--type-in-type` is absent.

CI triggers on `push` and `pull_request`; there is no schedule. The public `agda2forth` entrypoint, CLI argument shape, existing compiler invocation, generated renderer filename, and remaining Agda options are compatibility boundaries.

`Set : Set` is a universe-formation judgement, not an Agda term or proposition, and type-in-type collapses the universe hierarchy rather than providing a sound impredicative universe. Removing `--type-in-type` does not remove universe polymorphism: `Level`, `Set ℓ`, and explicit level quantification remain available. The current Foundations are not all universe-uniform, however: several core packages (including PEA, SBR, and MALLP) are formulated at the base `Set` level, while the negative logical schemas quantify over universe levels.

`--two-level` is not needed to recover synthetic uniformity or parametricity. It adds Agda's separate strict `SSet` hierarchy alongside the ordinary `Set` hierarchy; it is useful for two-level / cubical developments, not as a replacement for type-in-type or as a parametricity switch.

## Foundations: positive and negative sides

The root module publicly re-exports six mathematical `Foundations` packages and Laurent MALLP. Their assumptions, constructive content, universe scope, and non-claims are deliberately distinguished.

| Package | Positive or constructive content | Negative boundary / not claimed |
| --- | --- | --- |
| `ForsterEnumerability` | A concrete register-machine interpreter; analytic enumerable families; a global positive `parametricEA : ParametricEA` postulate; uniform family compilation with the parameter supplied at runtime. Soundness and completeness preserve the enumerated range. | PEA is assumed, not derived for every family. Range equality does not require identical stage-by-stage output. Typed program syntax is not proved equivalent to numeric Gödel coding or Turing computability. |
| `SymmetricBarRecursion` | A finite-partial-map interface for Spector-style symmetric bar recursion; positive stop/step equations; finite selection products, backward induction, Bellman equations, and conditional optimality proofs. | `symmetricBarRec` and its equations are postulated under `SymmetricBarCondition`. They do not provide a terminating evaluator by themselves. The full Escardó–Oliva equivalence is not formalized here. |
| `DoubleNegation` | Double-negated DNE and Peirce are derived from the double-negated excluded-middle schema. Ordinary DNS is derived from a negative no-counterexample postulate. | The negative assumptions are `¬¬ExcludedMiddle`, `¬¬FunctionExtensionality`, `¬DNSCounterexample`, and `¬¬DependentChoice`; none supplies a positive decision procedure, pointwise witness, or choice sequence. |
| `MacLaneCoherence` | A thin free monoidal category on Nat-labelled generators, with executable tensor normal forms and coherence proofs. | The proof uses K/UIP. It has no direct compiler consumer and is not a general coherence theorem for arbitrary MALLP models. |
| `CohesiveRetractions` | An abstract `Π ⊣ Disc ⊣ Γ ⊣ coDisc` record, full-faithfulness and finite-product preservation contracts, plus a concrete nonidentity finite-posetal model: three H-objects and two G-objects with distinct modalities. | The finite model is a pair of thin finite categories, not a cohesive topos or ∞-topos. It is not assembled with MALLP into the Hamano–Scott *-autonomous categorical model. |
| `QuotientReflection` | Idempotent endomaps, fixed-point carriers, normalizer/kernel correspondence, a reflective subcategory and idempotent reflection monad; a raw-to-canonical semantic rewrite. | This is a proof-relevant type-theoretic quotient/reflection construction, not proof that arbitrary user data has a useful canonicalizer. |
| `LaurentPolarizedMALLP` | Proof-relevant polarized MALLP syntax with tensor, par, additives, shifts, exchange, and cut. It is used by selected Nat and Bool resource derivations. | There are no weakening, contraction, or exponential rules. A positive cut-elimination normalizer record is postulated; it is not a derived Gentzen reduction procedure and has no relational-denotation preservation theorem yet. |

## MALLP as a constraint on generalized SBR-Bellman objectives

`SBRMALLPBellman` makes the non-PEA resource calculus an actual objective constraint. A Bellman objective is packaged with two MALLP derivations and relational-soundness obligations: the base derivation consumes one encoded partial-map state; the step derivation consumes that state and one encoded continuation, each exactly once, and produces the encoded objective value. The SBR stop and step equations transport those local certificates to the corresponding SBR branches.

This is a proof obligation on the generalized Bellman algebra, independent of PEA. It lets an objective be rejected unless its base/step semantics have a resource-safe MALLP realization. It does **not** derive the SBR oracle, prove global recursion termination, or claim every arbitrary higher-order continuation has a MALLP encoding; the encoding and derivations are supplied as explicit data.

## One constraint across all Foundations

`UnifiedFoundationsOptimization Atom` exposes `DynamicProgrammingMALLPOptimization`, one dependent record joining all seven Foundations around one dynamic-programming objective:

- PEA candidate-family coverage and a runtime-parameterized uniform program.
- A finite payoff, preorder, horizon, selection function, Bellman value, and backward-induction optimality.
- The same SBR state/value is required to agree with the finite dynamic-programming value; stop/step equations and the MALLP-certified Bellman base/step are in that record.
- An idempotent quotient representative; base and step maps must respect normalization.
- A cohesive `H → G` state/candidate view, and a Mac Lane-normalized tensor layout for entry, continuation, and result.
- Explicit negative logical assumptions, the identity rewrite equations, and the MALLP cut-elimination assumption.

The record is a conjunction of proof obligations, not an axiom that manufactures fields. Positive PEA, SBR, identity, and cut-elimination assumptions remain explicit. The finite DP value is required to equal the SBR value on the normalized initial state, while the Bellman base/step are independently certified by MALLP. 

## Is MALLP needed for Bellman optimization?

**No, not for the finite Bellman theorem itself.** The finite selection-product and backward-induction development is generic in move type, payoff type, preorder, horizon, and a supplied selector. Its Bellman equations and induction proofs need neither PEA nor MALLP.

**SBR matters beyond the finite horizon.** It is the intended general recursion interface for bar-recursive or infinite-horizon constructions. In this file, however, the SBR operator remains an assumption and the formal bridge from SBR to selection is only a one-step instance. The complete general bar-recursion/backward-induction equivalence is not yet proved.

**MALLP now also constrains generalized SBR-Bellman objectives.** The `SBRMALLPBellman` contract requires proof-relevant MALLP certificates for the base and continuation-dependent step maps, with relational soundness and exact resource use. It remains a contract on those maps, not a proof that the postulated SBR oracle itself is implemented by MALLP. As a programming calculus, MALLP still cannot automatically represent arbitrary functions that duplicate or discard inputs. The compiler proves selected Nat/Bool resource paths; it does not compile every strategy function.

**The other foundations are conditional infrastructure, not prerequisites for finite optimality:** PEA concerns uniform enumerability and effective codes; double-negation schemas concern logical strength; quotient reflection is relevant when states or payoffs are identified by an idempotent normalizer; cohesion matters when state spaces carry a genuine cohesive structure; Mac Lane coherence governs monoidal syntax. None independently establishes existence of an optimizer.

An optimal selector is always a premise in the general theorem. To establish existence for a particular problem, supply an attaining choice principle, a finite search argument, compactness/continuity hypotheses, or another domain-specific existence proof. No theorem here says that every arbitrary payoff has a maximum.

## Selection and Bellman layer

A selection function has type `Selection X R = (X → R) → X`. Its product composes a first move with a continuation-dependent response for the second move. `productSelection-bellman` states the resulting continuation equation. `backwardInduction` recursively builds a selector for finite plays, and `backwardInduction-bellman` gives its Bellman decomposition.

`OptimalSelection` packages the local condition that a chosen move is at least as good as every candidate in a supplied preorder. `productSelection-optimal` and `backwardInduction-optimal` prove global optimality from those local premises. These proofs are constructive and finite; they do not construct local maximizers.

`symmetricBarRec-selection-one-step` connects a one-step selection instance with the registered SBR stop/step equations. This is a small bridge, not the full general theorem.

Reference: Martín Escardó and Paulo Oliva, [“Selection Functions, Bar Recursion and Backward Induction”](https://doi.org/10.1017/S0960129509990351), *Mathematical Structures in Computer Science* 20(2), 127–168 (2010).

## MALLP resource discipline and compiler admission

MALLP contexts contain negative formulas and at most one positive stoup. Tensor partitions resources; exchange is represented by `ContextPermutation`; additive `with` gives the same context to mutually exclusive branches. That shared branch context is additive choice, not simultaneous contraction.

The backend admits a narrow closed, first-order fragment:

- Nat literals, addition, saturating monus, multiplication, closed lets, exact-once live Nat resources, supported `ROLL`/`SWAP`, and acyclic first-order Nat helper inlining.
- Closed Bool values, selected first-order Bool functions, linear Bool use, and supported additive cases.
- A non-indexed two-field Bool product when both fields are consumed exactly once.
- Nullary Unit values, represented by an empty target stack effect. Argument-bearing Unit functions are skipped rather than silently discarding their live input.
- Unary Word64 identity, represented by two target cells and no emitted operation.

Recursion, arbitrary higher-order functions, general ADTs/lists, general heap/closure behavior, general effects, general call-by-need execution, and general Word64 arithmetic are not admitted backend features. Formal signatures or models for some of these constructs do not imply a working Haskell lowering.

`MALLPNatTheory` gives closed arithmetic primitives a linear MALLP signature; composition is cut. `MALLPProtocolTheory` states resource contracts for operations such as thunk forcing, effect emission, application, and list folding. A signature is an assumption about an operation, not a proof that Haskell or Gforth implements it.

`MALLPRelationalDenotation` interprets the MALLP proof constructors in a Rel-style semantics. It is not yet combined with the finite cohesive model into the full Hamano–Scott categorical model. The cut-normalizer assumption is not yet shown sound for this relational denotation.

## Compiler/proof correspondence

The strongest end-to-end slice is the admitted Nat path:

1. Haskell decodes a Treeless definition into a labelled Nat resource tree and checks exact-once use of every live input.
2. The generated `MALLPEmittedRenderer.agda` reifies that tree as `NatResourceExpr`.
3. Agda constructs the corresponding cut-containing MALLP derivation, proves resource adequacy, and equates its cut count/class with the source tree.
4. The generated certificate uses the exact token list carried by the Haskell `CompiledDefinition`.
5. Agda executes that token list on the source inputs and an arbitrary residual stack, proving source-result equality.
6. Bool and BoolPair paths decode the exact emitted text-token list into the supported Boolean machine grammar and execute it with residual-stack preservation.
7. Renderer equalities connect the formal token renderer with the actual Forth string emitted by Haskell.

The strict regression fixture pins 29 emitted Forth definitions. The generic Nat resource certificate manifest covers 20 Nat definitions. These are per-definition witnesses, not a theorem that the Haskell compiler is correct for all inputs.

The compiler emits checked `MALLP-SWAP`, `MALLP-ROLL`, and `MALLP-IF` words. The shared runtime checks stack depth, Nat immediates, arithmetic operands/results, and canonical Agda Bool values (`FALSE = 0`, `TRUE = -1`). Its failure paths share one Gforth throw code, corresponding to Agda's `nothing`. The correspondence covers representable signed-cell values and available Gforth stack capacity; host exhaustion and arbitrary untyped calls remain outside the typed compiler contract.

| Source family | Established link | Boundary |
| --- | --- | --- |
| Nat | Resource derivation, exact Haskell token correspondence, formal token execution, source equality, residual-stack preservation. | Bounded-machine converse needs intermediate-state bounds; real Gforth remains external. |
| Bool | Exact token decoding, formal Boolean-machine execution, MALLP derivations, source equalities for admitted shapes. | Decoder recognizes only the supported TRUE/FALSE/MALLP-SWAP/MALLP-IF grammar, not arbitrary Forth. |
| BoolPair | Exact emitted-token decoding, tensor field-swap derivation, source/target composition. | Only the detected two-Bool field-swap shape is admitted. |
| Unit | Nullary source result, empty-token correspondence, multiplicative-unit proof, stack identity. | Argument-bearing Unit functions are skipped. |
| Word64 | Explicit high/low limb representation and unary identity correspondence. | Constructing representations for all words, arithmetic, and real Gforth limb semantics are outside this theorem. |
| Gforth | Runtime fixture exercises arithmetic, parsing, overflow, invalid literals, argument order, and stack behavior. | `MALLP-PARSE-NAT`, runtime words, and Gforth internals are not mechanized as an implementation refinement. |

## Registered rewrite system

The root module registers five rules and checks their combined confluence with `--confluence-check`. The universe/identity equations `refl↓` and `Id-∙` are retained in a separate registration.

| Registered rule | Direction | Status / client |
| --- | --- | --- |
| `parametricCodePEA-code` | `parametricCodePEA F i ↦ programCode (compileFamily parametricEA F) i` | Positive PEA code-selection equation; `parametricEA-rewrite-client`. |
| `sBR-stop` | A present key reduces `symmetricBarRec` to `base entries`. | Positive SBR stop equation; stop computation client. |
| `sBR-step` | An absent key reduces to `step entries` with a continuation over the extended map. | Positive SBR step equation; step-then-stop client. |
| `quotient-raw-sound` | `denoteQuotient (rawₑ x) ↦ denoteQuotient (canonicalizedₑ x)`. | Derived from idempotence; quotient reduction client. |
| `cutEliminate-idempotent` | `cutEliminate (cutEliminate proof) ↦ cutEliminate proof`. | Positive cut-normalizer contract; idempotence client. |

`cutEliminate-cut-free` remains a theorem of the postulated normalizer record, but is **not** a registered rewrite. Registering it alongside idempotence created an overlap: `hasCut (cutEliminate (cutEliminate p))` had two distinct immediate reducts. Keeping only the idempotence rewrite preserves confluence of the registered system.

Confluence checks interactions among rewrite rules. It does not prove the postulates, establish termination of SBR, or make the cut-elimination oracle semantically sound. A rewrite equation can be useful as a conversion law without defining a terminating evaluator.

## Assumption ledger

Positive assumptions:

- `Id`, `ext`, `refl↓`, and `Id-∙` for the universe/identity encoding.
- `parametricEA : ParametricEA`, preserving enumeration range uniformly by a single program per family and runtime parameter.
- `symmetricBarRec`, `sBR-stop`, and `sBR-step`, under `SymmetricBarCondition`.
- `mallpCutElimination`, giving a same-sequent, cut-free, idempotent normalizer.

Negative assumptions:

- `¬¬ExcludedMiddle` at each stated universe level.
- `¬¬FunctionExtensionality` at the stated universe levels.
- Countable DNS for families `Nat → Set ℓ`, represented by the negative axiom `negativeDNS : ¬ DNSCounterexampleAt`; ordinary DNS is derived constructively from that counterexample refutation.
- `¬¬DependentChoice` for type-valued serial relations.

Constructively derived rather than postulated:

- Double-negated DNE and Peirce derived from the `¬¬ExcludedMiddle` assumption; ordinary DNS derived from `negativeDNS`; finite bounded-search correctness, finite Bellman equations, conditional finite optimality, finite cohesive-model laws, and quotient-reflection laws.

## CI and trust boundary

The workflow installs Gforth and the current Haskell/Agda toolchain, type-checks `formal/MALLPForth.agda` with rewrite confluence checking, type-checks `formal/SovereignRationalSEDPhysics.agda` under its `--safe` pragma, builds the backend, compiles the strict source fixture, type-checks the generated renderer certificate, and runs the Gforth fixture. The source and Forth fixtures are materialized transiently by CI; no tracked test directory is required.

Successful CI establishes that these checks pass under the declared options and assumptions. The Escardó–Coquand–Danielsson–Norell–Xu result preserves natural-number canonicity for jointly consistent negative postulates in intensional MLTT; it is not by itself a canonicity theorem for this entire Agda development, which also contains positive postulates and rewriting. The current checks do not discharge those positive postulates, prove PEA/SBR consistency, verify Gforth, establish general Haskell compiler correctness, or prove the MALLP cut-normalizer preserves the Rel denotation. The PR remains an isolated feature branch until reviewed and merged.
