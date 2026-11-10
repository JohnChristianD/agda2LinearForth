# agda2MALLPForth

`agda2MALLPForth` is a Haskell backend that emits a deliberately small Forth subset for Agda definitions. The project studies a polarized multiplicative-additive linear logic (MALLP) account of resource use, a formal Forth token machine, and generated Agda correspondence certificates.

The target is a proof-producing compiler pipeline for an explicitly admitted source fragment. The project is **not yet a fully verified Agda-to-Gforth compiler**, and the formal model is not a formalization of Gforth itself.

## Current toolchain and immutable entrypoints

The current CI job installs the latest stable Agda package from Hackage. Its
10 November 2026 run resolved **Agda 2.8.0.2**. The current `cabal.project`
contains only `packages: .`, and `agda2forth.cabal` declares `Agda` without
an exact version bound; the workflow has no numeric CLI version assertion.
This is a moving latest-stable selection, not an exact pin.

The existing root and generated-renderer option pragmas are distinct and
unchanged:

- Root `formal/MALLPForth.agda`: `--rewriting --confluence-check --type-in-type --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections`.
- Generated `MALLPEmittedRenderer.agda`: `--with-K --rewriting --confluence-check --lossy-unification --exact-split --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections`.

The root module leaves K enabled by Agda's default; it does not pass
`--without-K`. The generated certificate explicitly requests `--with-K`.
`--lossy-unification` and `--exact-split` occur in the generated-renderer
pragma, not the root pragma. The root `--type-in-type` option remains a
consistency-breaking trust boundary. The workflow does not use `--safe`.
The CLI flags `--no-prop --no-erasure` are used for the generated-renderer
check, not for the root-module checks.

The GitHub Actions workflow runs on `push` and `pull_request` only; it has
no scheduled trigger. The public `agda2forth` entrypoint, existing command
lines, argument shape, output names, Agda invocations, and both option
pragmas are compatibility constraints. `MALLPEmittedRenderer.agda` is
transient generated output, not a tracked Agda source file.

**Trust boundary:** `--type-in-type` is consistency-breaking for ordinary dependent type theory, and the file also contains explicit postulates. Therefore successful Agda type-checking establishes checking relative to this configured theory and its assumptions; it is not an axiom-free consistency claim. This README does not silently change that foundation or its commands.

## Admission and failure behavior

The backend reads Agda's Treeless representation and recognizes a closed, first-order subset. It fails closed for unsupported term shapes rather than treating the full Agda language as compilable.

Currently admitted source forms include:

- Nat literals, addition, saturating monus, multiplication, closed lets, exact-once live Nat resources, supported `ROLL`/`SWAP` selection, and acyclic first-order Nat helper inlining.
- Closed Bool values, selected first-order Bool functions, linear Bool resource use, and supported additive Bool cases.
- A closed, non-indexed two-field Bool product whose two fields are each consumed exactly once.
- Unit, represented by an empty target stack effect.
- Unary Word64 identity, represented by two target cells and no emitted operation.

Recursion, arbitrary higher-order functions, general algebraic data, lists, general closure and heap behavior, general effects, general call-by-need execution, and general Word64 arithmetic are not admitted compiler features. Some have formal models or protocol signatures, but those are not evidence that the Haskell backend implements them.

Compiler classification is based on the resolved Agda type and Treeless shape. Definitions marked `no-compilation` or with unusable modality are intentionally skipped. Unsupported admitted-shape attempts produce compiler errors; absence of a generated word is not a proof of semantic preservation.

## MALLP resource discipline

The indexed `MALLP` judgement is the logical core. Its constructors contain no weakening, contraction, or exponential rules. Tensor introduction partitions contexts; exchange is an explicit `ContextPermutation`; additive `with` gives both mutually exclusive branches the same context. The shared branch context is additive reuse, not contraction in a single execution.

The core MALLP syntax is **cut-admitting**: `mallp-cut` is a primitive derivation constructor. `hasCut`, `cutCount`, and `classifyMALLP` inspect a derivation and distinguish cut-free proofs from proofs containing cut; they do not eliminate cuts. The focused Nat proof language also admits cut. Its cut-count functions account for the cuts introduced by composition, and the resource compiler now emits a certificate equating the cut count and cut class of each generated MALLP Nat derivation with those predicted by its `NatResourceExpr`. The count is a proof-tree metric: both branches of additive `with` contribute, even though only one branch executes.

The Haskell Nat resource decoder tracks labelled Treeless variables and requires each live argument exactly once. The Bool resource decoder checks every additive path for exact-once usage. Bool-pair lowering requires each field once. Unit owns no runtime cell. These admission checks are concrete compiler invariants; they do not by themselves prove every Haskell pass correct.

`MALLPNatTheory` layers a closed arithmetic primitive signature and cut over MALLP. `MALLPProtocolTheory` declares signatures for operations such as thunk forcing, effect emission, linear application, list construction, and list folding. A declared signature states a resource contract; it does **not** prove that a concrete Haskell lowering or Gforth runtime word implements that contract.

`MALLPRelationalDenotation` gives a Rel-style interpretation of the proof constructors. `CohesiveRetractions` separately specifies the cohesive adjoint quadruple and supplies the identity-Set model, but those pieces are not assembled with MALLP into Hamano–Scott's *-autonomous category with products. No categorical soundness theorem for that combined model is claimed.

## Compiler/proof correspondence

The current Nat path is the strongest end-to-end slice:

1. Haskell decodes an admitted Treeless term into a labelled Nat resource tree and checks exact-once resource use.
2. The generated `MALLPEmittedRenderer.agda` reifies that tree as the count-indexed Agda `NatResourceExpr`.
3. Agda constructs the associated cut-containing MALLP derivation and proves its interpretation adequate for the resource evaluator. It also computes the derivation's cut count/class and proves these agree with the source resource tree.
4. The certificate contains the exact token list held by the Haskell `CompiledDefinition`, not a separately handwritten expected program.
5. Agda's `execTokens` evaluates that exact list on the source arguments and an arbitrary residual stack.
6. A generated source-semantics equality connects the original source function to the MALLP interpretation; the equalities compose into source-result preservation.
7. A renderer equality checks the Forth text actually emitted by Haskell against the formal text renderer.

The strict fixture currently pins **29 emitted Forth definitions**. The generic Nat resource certificate manifest covers **20 Nat definitions**. The unary and direct-binary Nat paths also retain specialized witnesses.

### Coverage by source family

| Source family | Current formal/compiler link | Remaining boundary |
| --- | --- | --- |
| General admitted Nat resources | Exact Haskell token list, MALLP derivation, formal execution, source equality, residual-stack preservation | Bounded-machine completeness requires an explicit intermediate-state bound trace; actual Gforth remains external |
| Unary/direct-binary Nat | Specialized derivations, token correspondence, and source equalities | These specialized witnesses are narrower than arbitrary source programs |
| Bool | Per-definition token, execution, and source-semantic certificates for admitted closed values, inversion, and the chooser/case resource form | The admitted Bool resource grammar remains deliberately limited to those certified forms |
| Bool pair | Generated encoder fixes the source pair layout as `second ∷ first`; token equality, MALLP tensor-swap derivation, target execution, and source-to-target composition are checked | Only the detected one-constructor, two-Bool field-swap shape is admitted |
| Unit | Per-definition source result (`tt`), exact empty-token correspondence, multiplicative-unit proof, and residual-stack identity are checked | Unit is represented by the empty target stack effect, not a runtime cell |
| Word64 identity | Generated certificate uses `Word64Representation`, explicit high/low-limb encoding, residual-stack preservation, and the formal two-cell identity code | The representation witness is supplied; constructing it for arbitrary words, Word64 arithmetic, and concrete Gforth limb semantics remain outside the theorem |
| Gforth runtime/parser | Integration and boundary tests | `MALLP-PARSE-NAT`, arithmetic words, stack/error behavior, and Gforth internals are not mechanized as an implementation refinement |

The bounded Nat machine proves that successful bounded execution preserves the corresponding unbounded result. The converse is conditional: every intermediate abstract stack and operation result must stay within the cell bound. `BoundedExecutionTrace` records that condition token by token; a final-result bound alone is insufficient because an intermediate addition or multiplication may overflow before later code reduces the value.

The Forth runtime in `data/FLib.fth` checks nonnegative cell values and overflow for decimal parsing, addition, saturating monus, and multiplication. `test/gforth/mallp-strict.fs` exercises successful operations, overflow, invalid literals, argument order, and stack behavior. These tests corroborate the model but do not verify the implementation of Gforth itself.

## Global rewrites and proof clients

The root module registers five rules with `--rewriting` and checks their
interactions with `--confluence-check`. A separate registration retains
`refl↓` and `Id-∙`. Directions below are the registered left-to-right
directions.

| Rule | Equation / direction | Computational client | Status |
| --- | --- | --- | --- |
| `μ-step-true` | `μ-search P n true ↦ n` | `leastSearch-zero-computes` | Postulated search computation |
| `μ-step-false` | `μ-search P n false ↦ μ-search P (suc n) (P (suc n))` | `leastSearch-successor-computes` | Postulated recursive search step |
| `sBR-stop` | A present key rewrites `symmetricBarRec ... (inDomain present)` to `base entries` | `symmetricBarRec-stop-computes` | Postulated bar-recursion stop equation |
| `sBR-step` | An absent key rewrites to `step entries` with a continuation over `extendFresh` and the next `omega`-selected key | `symmetricBarRec-step-then-stop-computes` | Postulated recursive step equation |
| `quotient-raw-sound` | `denoteQuotient (rawₑ x) ↦ denoteQuotient (canonicalizedₑ x)` | `quotientReflectionRewriteSmoke` | Derived from `canonicalize-idempotent` |
| `refl↓` | `ext A A ↦ Set` | No named downstream client | Postulated universe/identity encoding rule |
| `Id-∙` | `Id A X Y ↦ ext (A X) (A Y)` | No named downstream client | Postulated universe/identity encoding rule |

The μ clients exercise zero and successor search steps. The symmetric-bar
clients exercise a stop and a one-step-then-stop path. The quotient client
exercises the raw-to-canonicalized normalizer equation. The last two
identity-encoding rules remain registered, but no compiler consumption is
claimed for them.

Confluence checking verifies interactions among the registered rules; it
does not prove the postulates or establish termination of unbounded
μ-search or symmetric bar recursion. The bar-recursion rule still depends
on its explicit bar-condition premise.

The useful distinction is: a rewrite's equation is its abstract law; its
interpreter/search/normalizer is its operational meaning; a client proof
exercises the conversion rule; and a generated or fixture witness shows a
concrete behavior. These layers are kept separate. A postulated equation is
reported as an assumption even when its client computes by conversion.

## Seven public foundation exports: availability versus consumption

The root `MALLPForth` module publicly re-exports all seven `Foundations` submodules. That makes their declarations available to importers of the root module. It does **not** mean every package is consumed by the Forth compiler.

| Public module | Actual role and current consumption |
| --- | --- |
| `ForsterEnumerability` | A step-indexed register-machine interpreter is the analytic model; `AnalyticEnumerableFamily` packages a single uniform program with soundness/completeness. `ParametricEA` states Forster's synthetic enumerability axiom as explicit data: its selector `parametricCode ea F i` is the typed-code analogue of the parameterized index function γ, and the fixed `universalEval` interprets those codes. `parametricEA-analytic` turns an EA witness into an analytic realizer. No inhabitant of `ParametricEA` is postulated; unlike the thesis's `Nat`-indexed universal enumerator, this formalization uses typed register-program syntax instead of numeric Gödel codes, and does not claim a proved equivalence with Turing-machine computability. |
| `MarkovLeastWitness` | Postulated unbounded μ-search/least-witness principle; its step rewrites have real computation clients |
| `MacLaneCoherence` | A thin free monoidal category on Nat-labelled generators: objects are parenthesized tensor expressions, homs are equality of flattened normal forms, and associators/unitors/coherence follow using UIP/K. This is a standalone foundation, not a Haskell compiler consumer. |
| `CohesiveRetractions` | The Π ⊣ Disc ⊣ Γ ⊣ coDisc adjunction data, full-faithfulness conditions, and finite-product preservation are explicit structures. The old bare global modality/iso postulates are replaced by a parameterized adjoint-quadruple record plus the degenerate identity-Set instance. This is standalone, not a compiler consumer or a nontrivial cohesive topos/site model. |
| `QuotientReflection` | Idempotent endomap, fixed-point quotient/normalizer, idempotent category/monad; canonicalization rewrite is used by a reduction client |
| `SymmetricBarRecursion` | Finite-entry threading interface with postulated symmetric bar recursion and stop/step equations; rewrite clients exercise those equations |
| `LaurentPolarizedMALLP` | The linear logic core used directly by the Nat MALLP derivations and compiler proofs |

Thus all seven are **globally consumable** through public exports, while actual consumption is selective. `ForsterEnumerability`, `MacLaneCoherence`, and `CohesiveRetractions` have no direct compiler consumer; they remain substantive standalone developments rather than artificial dependencies in unrelated lowering proofs.

## Evidence ledger

| Evidence class | Established result |
| --- | --- |
| Proved in Agda under the current theory | Nat resource derivation adequacy, exact-token execution and source-result equality with arbitrary residual-stack preservation; cut-count/class agreement; per-definition Bool, BoolPair, Unit, and Word64-identity certificates for the listed forms; Mac Lane coherence using K; the identity-Set cohesive model |
| Agda typechecked | The root MALLP module and separate RSED specification, plus the generated renderer certificate, under the existing options, rewrites, and postulates; no `--safe` claim |
| CI checked | Haskell backend build, strict-source compilation, generated certificate type-check, Forth text rendering, and the existing Gforth fixture |
| Gforth tested | 29 emitted definitions plus decimal parsing, arithmetic, argument order, overflow, invalid-literal, and stack-boundary fixtures |
| Assumed or unverified | `--type-in-type`, explicit postulates, general correctness of the Haskell decoder/passes, concrete `MALLP-PARSE-NAT` and runtime-word refinement, Gforth internals, and the primitive implementations declared by `MALLPProtocolTheory` |

The generated certificates are per-definition witnesses, not a proof that
the Haskell compiler implementation is correct for all inputs. Tests
corroborate concrete runtime behavior; they do not close the Gforth trusted
boundary.

## Formal assumptions and unsupported claims

The monolithic Agda module retains explicit postulates for the universe/identity
encoding, μ-search/least-witness assumptions, and symmetric bar recursion.
The cohesive modalities are parameterized by an explicit adjoint-quadruple
record; the supplied Set interpretation is the identity quadruple, not a
claim about a nontrivial cohesive topos. Mac Lane coherence uses UIP/K for
equality of parallel tensor-normalization paths. K remains enabled by the
root module's Agda default and is requested explicitly by the generated
renderer pragma. The root `--type-in-type` option remains a
consistency-breaking trust boundary. No `--safe` or axiom-free consistency
claim is made.

OTT was inspected but not integrated. The Agda OTT library brings a separate
impredicative universe/Prop encoding, postulated identity/coherence
principles, and modules that disable positivity and termination checks. It
does not shorten a proof needed by this compiler and would enlarge the
trusted assumptions. The separate Ott syntax tool does not emit Agda. No
OTT dependency or command change is justified.

The Haskell backend is not verified as a general Haskell program by the
generated certificates. Each certificate checks concrete emitted token data
against formal Agda semantics for its covered definition. The emitter writes
the generated certificate before the Forth module, so a certificate guard
failure occurs before a Forth artifact is left behind. The external Gforth
interpreter and concrete runtime words remain an external trusted/tested
boundary.

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