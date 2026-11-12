# agda2MALLPForth

`agda2MALLPForth` is a Haskell backend that emits a deliberately small Forth subset for Agda definitions. The project studies a polarized multiplicative-additive linear logic (MALLP) account of resource use, a formal Forth token machine, and generated Agda correspondence certificates.

The target is a proof-producing compiler pipeline for an explicitly admitted source fragment. The project is **not yet a fully verified Agda-to-Gforth compiler**, and the formal model is not a formalization of Gforth itself.

## Current toolchain and immutable entrypoints

The current CI job installs the latest stable Agda package from Hackage. Its
10 November 2026 run resolved **Agda 2.8.0.2**. The current `cabal.project`
contains only `packages: .`, and `agda2forth.cabal` declares `Agda` without
an exact version bound; the workflow has no numeric CLI version assertion.
This is a moving latest-stable selection, not an exact pin.

The root and generated-renderer option pragmas remain distinct:

- Root `formal/MALLPForth.agda`: `--rewriting --confluence-check --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections`.
- Generated `MALLPEmittedRenderer.agda`: `--with-K --rewriting --confluence-check --lossy-unification --exact-split --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections`.

The root module leaves K enabled by Agda's default; it does not pass
`--without-K`. The generated certificate explicitly requests `--with-K`.
`--lossy-unification` and `--exact-split` occur in the generated-renderer
pragma, not the root pragma. This branch removes only the root
`--type-in-type` option; every other pragma entry, the generated-renderer
pragma, and every CLI invocation are preserved. The workflow does not use
`--safe`. The CLI flags `--no-prop --no-erasure` are used for the
generated-renderer check, not for the root-module checks.


The GitHub Actions workflow runs on `push` and `pull_request` only; it has
no scheduled trigger. The public `agda2forth` entrypoint, existing command
lines, argument shape, output names, Agda invocations, and both option
pragmas are compatibility constraints. `MALLPEmittedRenderer.agda` is
transient generated output, not a tracked Agda source file.

**Trust boundary:** the root module now uses Agda's predicative universe hierarchy; the `Id`/`ext` encoding signatures are lifted to `Set₁`. Explicit positive and negative postulates remain, so successful type-checking is relative to those assumptions, K/UIP, and the rest of the configured theory. No axiom-free consistency claim is made. `Set : Set` is a universe-formation judgement, not an Agda term or proposition; its double negation cannot be added as a well-typed axiom.

## Admission and failure behavior

The backend reads Agda's Treeless representation and recognizes a closed, first-order subset. It fails closed for unsupported term shapes rather than treating the full Agda language as compilable.

Currently admitted source forms include:

- Nat literals, addition, saturating monus, multiplication, closed lets, exact-once live Nat resources, supported `ROLL`/`SWAP` selection, and acyclic first-order Nat helper inlining.
- Closed Bool values, selected first-order Bool functions, linear Bool resource use, and supported additive Bool cases.
- A closed, non-indexed two-field Bool product whose two fields are each consumed exactly once.
- Nullary Unit values, represented by an empty target stack effect. Unit-returning functions with arguments are skipped: emitting no tokens for them would silently discard live resources.
- Unary Word64 identity, represented by two target cells and no emitted operation.

Recursion, arbitrary higher-order functions, general algebraic data, lists, general closure and heap behavior, general effects, general call-by-need execution, and general Word64 arithmetic are not admitted compiler features. Some have formal models or protocol signatures, but those are not evidence that the Haskell backend implements them.

Compiler classification is based on the resolved Agda type and Treeless shape. Definitions marked `no-compilation` or with unusable modality are intentionally skipped. Unsupported admitted-shape attempts produce compiler errors; absence of a generated word is not a proof of semantic preservation.

## MALLP resource discipline

The indexed `MALLP` judgement is the logical core. Its constructors contain no weakening, contraction, or exponential rules. Tensor introduction partitions contexts; exchange is an explicit `ContextPermutation`; additive `with` gives both mutually exclusive branches the same context. The shared branch context is additive reuse, not contraction in a single execution.



The core MALLP syntax remains **cut-admitting**: `mallp-cut` is a primitive derivation constructor. `hasCut`, `cutCount`, and `classifyMALLP` inspect and classify cut use. A positive `mallpCutElimination` postulate supplies a same-sequent normalizer whose result is cut-free and whose operation is idempotent; the two corresponding equations are registered as rewrite rules. This is a complete *axiomatized normalization contract*, not a derived Gentzen reduction algorithm. It currently carries no proof that the normalizer preserves the relational denotation below, so semantic soundness of that oracle remains an explicit trust obligation. The focused Nat proof language also admits cut. Its cut-count functions account for the cuts introduced by composition, and the resource compiler emits a certificate equating the cut count and cut class of each generated MALLP Nat derivation with those predicted by its `NatResourceExpr`. The count is a proof-tree metric: both branches of additive `with` contribute, even though only one branch executes.

The Haskell Nat resource decoder tracks labelled Treeless variables and requires each live argument exactly once. The Bool resource decoder checks every additive path for exact-once usage. Bool-pair lowering requires each field once. Unit owns no runtime cell. These admission checks are concrete compiler invariants; they do not by themselves prove every Haskell pass correct.

`MALLPNatTheory` layers a closed arithmetic primitive signature and cut over MALLP. `MALLPProtocolTheory` declares signatures for operations such as thunk forcing, effect emission, linear application, list construction, and list folding. A declared signature states a resource contract; it does **not** prove that a concrete Haskell lowering or Gforth runtime word implements that contract.

`MALLPRelationalDenotation` gives a Rel-style interpretation of the proof constructors. `CohesiveRetractions` separately specifies the cohesive adjoint quadruple and supplies the identity-Set model, but those pieces are not assembled with MALLP into Hamano–Scott's *-autonomous category with products. No categorical soundness theorem for that combined model is claimed.

## SBR, selection products, and Bellman optimality

`Foundations.SymmetricBarRecursion` is now the second foundation, immediately after Forster enumerability. Its `symmetricBarRec` operator and the `sBR-stop`/`sBR-step` equations remain positive postulates; the supplied `SymmetricBarCondition` is still a premise. Markov/μ-search and its least-witness axiom have been deleted. The bounded finite-prefix search, `LeastWitness`, soundness, minimality, and completeness proofs remain as ordinary structurally recursive results under `FiniteListComputation`; these finite results do not require MP.

The SBR foundation also contains Escardó–Oliva-style selection functions `Selection X R = (X → R) → X`, their product, and finite `backwardInduction`. `productSelection-bellman` and `backwardInduction-bellman` state the compositional Bellman equations. For an explicit preorder on payoffs, `OptimalSelection` says each local selector chooses an element at least as good as every candidate; `productSelection-optimal` and `backwardInduction-optimal` prove global optimality from those local optimality premises. These theorems do not manufacture maximizers: existence of an optimal selector is a separate input. `symmetricBarRec-selection-one-step` proves an actual one-step selection instance by conversion using the registered SBR step/stop equations. This is a formal finite bridge, not a mechanization of the whole Escardó–Oliva equivalence between general bar recursion and iterated selection products.

Reference: Martín Escardó and Paulo Oliva, [“Selection Functions, Bar Recursion and Backward Induction”](https://doi.org/10.1017/S0960129509990351), *Mathematical Structures in Computer Science* 20(2), 127–168 (2010). They establish bar recursion as a generalization of backward induction and explain finite bar recursion through the selection monad.

The Bellman results are generic over payoff functions, but their translation into MALLP is constrained by MALLP's actual resource discipline. MALLP has no weakening, contraction, or exponentials. Thus an arbitrary unrestricted function that duplicates or discards inputs is not automatically representable as an MALLP program. A Bellman strategy has an MALLP derivation only when its concrete operations admit a linear resource derivation (or are supplied as explicitly trusted primitives); no universal arbitrary-function MALLP compiler theorem is claimed.

## Compiler/proof correspondence

The current Nat path is the strongest end-to-end slice:

1. Haskell decodes an admitted Treeless term into a labelled Nat resource tree and checks exact-once resource use.
2. The generated `MALLPEmittedRenderer.agda` reifies that tree as the count-indexed Agda `NatResourceExpr`.
3. Agda constructs the associated cut-containing MALLP derivation and proves its interpretation adequate for the resource evaluator. It also computes the derivation's cut count/class and proves these agree with the source resource tree.
4. The certificate contains the exact token list held by the Haskell `CompiledDefinition`, not a separately handwritten expected program.
5. Agda's `execTokens` evaluates that exact Nat token list on the source arguments and an arbitrary residual stack.
6. For Bool and BoolPair, the generated certificate decodes the exact Haskell-emitted `ForthTextToken` list into the Boolean machine's token grammar, then executes that list on an arbitrary residual stack. The decoder rejects non-Boolean instructions; a proved round trip connects the renderer's Boolean token encoding to the executable Boolean machine.
7. Generated source equalities connect each admitted source function to its MALLP interpretation and machine result. A separate renderer equality checks the exact Forth text emitted by Haskell against the formal text renderer.

The strict fixture currently pins **29 emitted Forth definitions**. The generic Nat resource certificate manifest covers **20 Nat definitions**. The unary and direct-binary Nat paths also retain specialized witnesses.

### Coverage by source family

| Source family | Current formal/compiler link | Remaining boundary |
| --- | --- | --- |
| General admitted Nat resources | Exact Haskell token list, MALLP derivation, formal execution, source equality, residual-stack preservation | Bounded-machine completeness requires an explicit intermediate-state bound trace; actual Gforth remains external |
| Unary/direct-binary Nat | Specialized derivations, token correspondence, and source equalities | These specialized witnesses are narrower than arbitrary source programs |
| Bool | Per-definition exact Haskell token equality, fail-closed text-token decoding, Boolean-machine execution on arbitrary residual stacks, MALLP derivations, and source-result equalities for closed values, inversion, and chooser/case | The Boolean decoder handles only `TRUE`, `FALSE`, `SWAP`, and nested `IF`; it is not a parser or semantics for arbitrary Forth text |
| Bool pair | Generated encoder fixes source pair layout as `second ∷ first`; exact emitted text-token decoding, MALLP tensor-swap derivation, Boolean-machine execution, and source-to-target composition are checked | Only the detected one-constructor, two-Bool field-swap shape is admitted |
| Unit | Nullary per-definition source result (`tt`), exact empty-token correspondence, multiplicative-unit proof, and residual-stack identity are checked | Argument-bearing Unit functions are skipped; the strict fixture includes a Nat-to-Unit regression case so the 29-definition manifest rejects accidental emission |
| Word64 identity | Generated certificate uses `Word64Representation`, explicit high/low-limb encoding, residual-stack preservation, and the formal two-cell identity code | The representation witness is supplied; constructing it for arbitrary words, Word64 arithmetic, and concrete Gforth limb semantics remain outside the theorem |
| Gforth runtime/parser | Integration and boundary tests | `MALLP-PARSE-NAT`, arithmetic words, stack/error behavior, and Gforth internals are not mechanized as an implementation refinement |

The bounded Nat machine proves that successful bounded execution preserves the corresponding unbounded result. The converse is conditional: every intermediate abstract stack and operation result must stay within the cell bound. `BoundedExecutionTrace` records that condition token by token; a final-result bound alone is insufficient because an intermediate addition or multiplication may overflow before later code reduces the value.

At one-token granularity, `execBoundedToken-failure-classification` classifies failure under a bounded input stack: either the unbounded token has the same stack/roll error, or it succeeds with a result whose new head exceeds the cell bound. Literal, addition, and multiplication overflow have concrete Agda witnesses; monus has no overflow branch because its saturating result is bounded by its left operand. This is a formal token-model classification, not a proof of Gforth's concrete error words or of failure behavior for every whole-program path.

The Forth runtime in `data/FLib.fth` checks nonnegative cell values and overflow for decimal parsing, addition, saturating monus, and multiplication. `test/gforth/mallp-strict.fs` exercises successful operations, overflow, invalid literals, argument order, and stack behavior. These tests corroborate the model but do not verify the implementation of Gforth itself.

## Global rewrites and proof clients

The root module registers five rules with `--rewriting` and checks their
interactions with `--confluence-check`. A separate registration retains
`refl↓` and `Id-∙`. Directions below are the registered left-to-right
directions.

| Rule | Equation / direction | Computational client | Status |
| --- | --- | --- | --- |
| `parametricCodePEA-code` | `parametricCodePEA F i ↦ programCode (compileFamily parametricEA F) i` | `parametricEA-rewrite-client` | Positive Forster PEA selector; one program is chosen uniformly for each family, with the parameter supplied as input |
| `sBR-stop` | A present key rewrites `symmetricBarRec ... (inDomain present)` to `base entries` | `symmetricBarRec-stop-computes` and one-step selection bridge | Positive SBR stop equation |
| `sBR-step` | An absent key rewrites to `step entries` with a continuation over `extendFresh` and the next `omega`-selected key | `symmetricBarRec-step-then-stop-computes` and one-step selection bridge | Positive SBR recursive step equation |
| `quotient-raw-sound` | `denoteQuotient (rawₑ x) ↦ denoteQuotient (canonicalizedₑ x)` | `quotientReflectionRewriteSmoke` | Derived from `canonicalize-idempotent` |
| `cutEliminate-idempotent` | `cutEliminate (cutEliminate proof) ↦ cutEliminate proof` | `cutEliminate-idempotent-client` | Positive cut-elimination oracle law |
| `refl↓` | `ext A A ↦ Set` | No named downstream client | Positive universe/identity encoding rewrite |
| `Id-∙` | `Id A X Y ↦ ext (A X) (A Y)` | No named downstream client | Positive universe/identity encoding rewrite |

The finite `boundedSearch` evaluator remains structurally recursive on its fuel:
every successful result is proved to satisfy the predicate and to have all
earlier candidates false, while a `LeastWitness P n` forces fuel
`suc n` to return `just n`. No unbounded μ-search or Markov postulate
remains. The SBR clients exercise stop, step-then-stop, and a one-step
selection instance. The selection-product/backward-induction theorems
establish Bellman composition and conditional optimality from locally
optimal selectors. The quotient client exercises raw-to-canonical
reflection. PEA supplies one program per enumerable family, uniformly
parameterized by input; soundness/completeness preserve the enumerated range,
not the original stage order. PEA does not establish uniqueness of codes.

Confluence checking verifies interactions among the registered rules; it
does not prove the positive postulates, SBR termination, or semantic soundness
of the cut-elimination oracle. The SBR computation still depends on its
explicit bar-condition premise. The cut-elimination rewrite equations make
the assumed normalizer canonical/idempotent; they do not constitute a
derived Gentzen algorithm.


The useful distinction is: a rewrite's equation is its abstract law; its
interpreter/search/normalizer is its operational meaning; a client proof
exercises the conversion rule; and a generated or fixture witness shows a
concrete behavior. These layers are kept separate. A postulated equation is
reported as an assumption even when its client computes by conversion.

## Seven public foundation exports: availability versus consumption

The root `MALLPForth` module publicly re-exports all seven `Foundations` submodules. That makes their declarations available to importers of the root module. It does **not** mean every package is consumed by the Forth compiler.

| Public module | Actual role and current consumption |
| --- | --- |
| `ForsterEnumerability` | A step-indexed register-machine interpreter is the analytic model; `AnalyticEnumerableFamily` packages one uniform program with soundness/completeness. The global positive `parametricEA : ParametricEA` postulate supplies one program for every parametrically enumerable family, with the family parameter supplied at runtime. Its soundness/completeness fields preserve the enumerated range (rather than requiring the same stage-by-stage output sequence); `parametricCodePEA-code` is the registered code-selection rewrite. Codes remain typed register-program syntax, not a proved equivalence with numeric Gödel codes or Turing-machine computability. |
| `SymmetricBarRecursion` | Positive postulated symmetric bar recursion over finite partial maps, with stop/step rewrite equations; also contains selection products, finite backward induction, Bellman equations, conditional optimality proofs, and a one-step SBR/selection bridge. |
| `DoubleNegation` | Negative postulates for double-negated excluded middle, function extensionality, and countable double-negation shift. Double-negated DNE and Peirce are derived from double-negated excluded middle; no classical witness is supplied. |
| `MacLaneCoherence` | A thin free monoidal category on Nat-labelled generators: objects are parenthesized tensor expressions, homs are equality of flattened normal forms, and associators/unitors/coherence follow using UIP/K. This is a standalone foundation, not a Haskell compiler consumer. |
| `CohesiveRetractions` | The Π ⊣ Disc ⊣ Γ ⊣ coDisc adjunction data, full-faithfulness conditions, and finite-product preservation are explicit structures. The supplied Set model remains the degenerate identity-Set instance, not a nontrivial cohesive topos/site model. |
| `QuotientReflection` | Idempotent endomap, fixed-point quotient/normalizer, idempotent category/monad; canonicalization rewrite is used by a reduction client. |
| `LaurentPolarizedMALLP` | The linear logic core used directly by the Nat MALLP derivations and compiler proofs; its positive cut-elimination oracle preserves the sequent, returns cut-free proofs, and is idempotent. Idempotence is a registered rewrite; cut-freeness is an explicit theorem of the oracle record. |

Thus all seven are **globally consumable** through public exports, while actual consumption is selective. `ForsterEnumerability`, `MacLaneCoherence`, and `CohesiveRetractions` have no direct compiler consumer; they remain substantive standalone developments rather than artificial dependencies in unrelated lowering proofs.

## Evidence ledger

| Evidence class | Established result |
| --- | --- |
| Proved in Agda under the current theory | Nat resource derivation adequacy, exact-token execution and source-result equality with arbitrary residual-stack preservation; constructive bounded-search soundness, leastness, and completeness from an explicit least-witness; finite selection-product and backward-induction Bellman equations; conditional global optimality from local optimal selectors; one-step SBR/selection correspondence; cut-count/class agreement; per-definition Bool, BoolPair, Unit, and Word64-identity certificates for the listed forms; Mac Lane coherence using K; the identity-Set cohesive model |
| Agda typechecked | Baseline master checks cover the root MALLP module and separate RSED specification, plus the generated renderer certificate. The SBR/PEA/Bellman/negative-axiom/cut-normalizer branch is awaiting its own CI result; no `--safe` claim |
| CI checked | Haskell backend build, strict-source compilation, generated certificate type-check, Forth text rendering, and the existing Gforth fixture |
| Gforth tested | 29 emitted definitions plus decimal parsing, arithmetic, argument order, overflow, invalid-literal, and stack-boundary fixtures |
| Assumed or unverified | Positive identity/universe encoding, global PEA, symmetric bar recursion, and cut-elimination normalizer postulates; double-negated classical/function-extensionality/DNS schemas; semantic preservation of cut elimination; general correctness of the Haskell decoder/passes; concrete `MALLP-PARSE-NAT` and runtime-word refinement; Gforth internals; and primitive implementations declared by `MALLPProtocolTheory` |

The Boolean text-token decoder is a formal decoder for the compiler's typed token AST, not a parser for arbitrary rendered Forth strings. Its round-trip theorem makes the Boolean execution proof consume the same token constructors emitted in the generated certificate. The generic renderer equality then connects those constructors with the actual output string.

The generated certificates are per-definition witnesses, not a proof that
the Haskell compiler implementation is correct for all inputs. Tests
corroborate concrete runtime behavior; they do not close the Gforth trusted
boundary.

## Formal assumptions and unsupported claims

The remaining positive postulates are the universe/identity encoding (`Id`,
`ext`, `refl↓`, `Id-∙`), Forster PEA, the symmetric bar-recursion operator
with its stop/step equations, and the MALLP cut-elimination normalizer
record. PEA's universal selector preserves enumerated ranges and is uniformly
parameterized; it does not impose a stage-by-stage identity with each input
enumerator. The negative postulates are double-negated excluded middle,
function extensionality, and countable DNS; double-negated DNE and Peirce are derived.
The μ-search and Markov/least-witness postulates have been removed; the
finite bounded-search proofs remain constructive.

The MALLP cut-elimination oracle preserves the indexed sequent, returns a
cut-free derivation, and is idempotent. It does not currently include a
relational-denotation preservation theorem or a derived reduction procedure.
Therefore the cut-elimination law is an explicit trusted assumption, not a
verified implementation. The Bellman results prove finite compositionality
and optimality conditional on local optimal selectors; they do not establish
existence of a maximum for every payoff.

The cohesive modalities are parameterized by an explicit adjoint-quadruple
record. Its object universe is lifted predicatively so `Set` itself can be
a category object; the supplied Set interpretation is still the identity
quadruple, not a nontrivial cohesive topos. Mac Lane coherence uses UIP/K for
equality of parallel tensor-normalization paths. K remains enabled by the
root module's Agda default and is requested explicitly by the generated
renderer pragma. The root `--type-in-type` option has been removed.
`Set : Set` is a universe-formation judgement rather than a well-typed
proposition, so no double-negated axiom for that judgement is supplied. No
`--safe` or axiom-free consistency claim is made.

OTT was inspected but not integrated. The Agda OTT library brings a separate
impredicative universe/Prop encoding, postulated identity/coherence
principles, and modules that disable positivity and termination checks. It
does not shorten a proof needed by this compiler and would enlarge the
trusted assumptions. The separate Ott syntax tool does not emit Agda. No
OTT dependency or command change is justified.

The Haskell backend is not verified as a general Haskell program by the
generated certificates. Each certificate checks concrete emitted token data
against formal Agda semantics for its covered definition. The emitter writes
the generated certificate before the Forth module, so a certificate-file
write failure prevents Forth emission. Agda type-checks that certificate in a
separate CI step after both files have been written; a failed check fails the
workflow, but the local compiler invocation is not transactional and does
not itself run the certificate checker. The external Gforth interpreter and
concrete runtime words remain an external trusted/tested boundary.

Accordingly, the current result is a proof-producing, CI-checked compiler for
a restricted fragment, with its strongest composed source-to-target theorem
covering admitted Nat resource programs. Other source families have
per-definition certificates for the stated forms, not a general theorem for
their full type families. This is not yet PureCake-level verification of
every compiler pass or Gforth itself.

## Reproducible checks

The current workflow installs Agda from Hackage, type-checks both tracked
Agda developments, builds the backend, generates and type-checks the emitted
certificate, and executes the strict fixture under Gforth. It runs on
`push` and `pull_request` only. The generated certificate is produced in
the workflow; it is not a checked-in Agda file.

The following are the workflow's existing commands. `agda_bin_dir` and
`AGDA_BIN` are set by the workflow before the later steps.

~~~sh
cabal update
cabal install Agda --installdir="$agda_bin_dir" --overwrite-policy=always
"$AGDA_BIN" --no-fast-reduce --no-projection-like --confluence-check -i formal formal/MALLPForth.agda
"$AGDA_BIN" --no-fast-reduce --no-projection-like -i formal formal/SovereignRationalSEDPhysics.agda
cabal build agda2forth
cp test/MALLPStrict.agda.src test/MALLPStrict.agda
cabal run agda2forth -- -i test test/MALLPStrict.agda
"$AGDA_BIN" --no-prop --no-erasure -i formal -i . -i test MALLPEmittedRenderer.agda
gforth MALLPStrict.fth
~~~

The test fixture is a finite regression corpus, not a universal semantics theorem. Any newly admitted source construct must gain a real decoder/resource contract, a source-to-MALLP derivation, an exact emitted-token certificate, a target-machine simulation, and a documented external-runtime boundary before it is advertised as verified.