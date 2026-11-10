# agda2MALLPForth

`agda2MALLPForth` is a Haskell backend that emits a deliberately small Forth subset for Agda definitions. The project studies a polarized multiplicative-additive linear logic (MALLP) account of resource use, a formal Forth token machine, and generated Agda correspondence certificates.

The target is a proof-producing compiler pipeline for an explicitly admitted source fragment. The project is **not yet a fully verified Agda-to-Gforth compiler**, and the formal model is not a formalization of Gforth itself.

## Current toolchain and immutable entrypoints

As of 9 November 2026, the latest official stable Agda release is **2.8.0.2**. The repository pins that release in `cabal.project`, constrains the Cabal dependency to the 2.8 series, and checks the executable's numeric version in CI. Do not replace the pin with a prerelease or an unpinned moving target.

The root Agda module and its option pragma are intentionally retained. The normal CI invocation remains:

~~~sh
cabal build Agda:exe:agda
cabal build agda2forth
"$(cabal list-bin Agda:exe:agda)" --no-prop --no-erasure -i formal formal/MALLPForth.agda
"$(cabal list-bin Agda:exe:agda)" --no-prop --no-erasure -i formal formal/SovereignRationalSEDPhysics.agda
cp test/MALLPStrict.agda.src test/MALLPStrict.agda
cabal run agda2forth -- -i test test/MALLPStrict.agda
gforth MALLPStrict.fth
~~~

The GitHub Actions workflow runs on `push` to `master` and `pull_request`. It has no scheduled trigger. The public `agda2forth` entrypoint, existing command lines, argument shape, output names, and `formal/MALLPForth.agda` option pragma are part of the compatibility contract.

Current Agda options include `--with-K`, `--rewriting`, `--confluence-check`, `--lossy-unification`, `--exact-split`, `--guardedness`, `--type-in-type`, and the existing reduction/projection options. The build uses `--no-prop --no-erasure`; it does not use `--safe`.

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

The core MALLP syntax is **cut-admitting**: `mallp-cut` is a primitive derivation constructor. `hasCut`, `cutCount`, and `classifyMALLP` inspect a derivation and distinguish cut-free proofs from proofs containing cut; they do not eliminate cuts. The focused Nat proof language also admits cut. Its cut-count functions account for the cuts introduced by composition, and the resource compiler now emits a certificate equating the cut count and cut class of each generated MALLP Nat derivation with those predicted by its `NatResourceExpr`.

The Haskell Nat resource decoder tracks labelled Treeless variables and requires each live argument exactly once. The Bool resource decoder checks every additive path for exact-once usage. Bool-pair lowering requires each field once. Unit owns no runtime cell. These admission checks are concrete compiler invariants; they do not by themselves prove every Haskell pass correct.

`MALLPNatTheory` layers a closed arithmetic primitive signature and cut over MALLP. `MALLPProtocolTheory` declares signatures for operations such as thunk forcing, effect emission, linear application, list construction, and list folding. A declared signature states a resource contract; it does **not** prove that a concrete Haskell lowering or Gforth runtime word implements that contract.

`MALLPRelationalDenotation` gives a Rel-style interpretation of the proof constructors. It is not presented as the complete Hamano–Scott categorical model: the reflective/coreflective adjunction, *-autonomous structure, units/counits, products, and coherence laws are not all formalized here.

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

The root module registers the aggregate rewrite system with `--rewriting` and `--confluence-check`. The global rules are:

- `μ-step-true` and `μ-step-false` for least-search computation.
- `sBR-stop` and `sBR-step` for the symmetric bar-recursion interface.
- `quotient-raw-sound` connecting raw quotient representatives with canonicalized representatives.

A separate declaration registers `refl↓` and `Id-∙` for the project-owned universe/identity encoding. These equations are postulated; their use is an explicit axiom boundary.

The registered rules have computational clients: `leastSearch-zero-computes`, `leastSearch-successor-computes`, `symmetricBarRec-stop-computes`, `symmetricBarRec-step-then-stop-computes`, and `quotientReflectionRewriteSmoke`. These clients force the equations through conversion. The aggregate confluence check checks interactions among registered rules; it does not prove the postulates, termination of unbounded search, source-to-target semantics, or the full compiler correct.

The useful distinction is: a rewrite's equation is its abstract law; its interpreter/search/normalizer is its operational meaning; a client proof exercises the conversion rule; and the generated or fixture witness shows a concrete behavior. All four should agree. Rules without a justified operational meaning should remain explicitly axiomatic rather than be advertised as proved computation.

## Seven public foundation exports: availability versus consumption

The root `MALLPForth` module publicly re-exports all seven `Foundations` submodules. That makes their declarations available to importers of the root module. It does **not** mean every package is consumed by the Forth compiler.

| Public module | Actual role and current consumption |
| --- | --- |
| `ForsterEnumerability` | A step-indexed register-machine interpreter is the analytic model; `AnalyticEnumerableFamily` packages a single uniform program with soundness/completeness. `ParametricEA` states the synthetic uniform compiler principle as explicit data, and `parametricEA-analytic` turns any such witness into an analytic realizer. No inhabitant of `ParametricEA` is postulated; the program syntax is not claimed to be a numeric Gödel numbering, and no theorem of equivalence with Turing-machine computability is claimed. |
| `MarkovLeastWitness` | Postulated unbounded μ-search/least-witness principle; its step rewrites have real computation clients |
| `MacLaneCoherence` | A thin free monoidal category on Nat-labelled generators: objects are parenthesized tensor expressions, homs are certified equality of flattened normal forms, and associators/unitors and Mac Lane coherence are derived computationally. |
| `CohesiveRetractions` | The Π ⊣ Disc ⊣ Γ ⊣ coDisc adjunction data, full-faithfulness conditions, and finite-product preservation are explicit structures. The supplied executable instance is the degenerate identity cohesion on Set; this is not a nontrivial cohesive topos or a site/sheaf model. |
| `QuotientReflection` | Idempotent endomap, fixed-point quotient/normalizer, idempotent category/monad; canonicalization rewrite is used by a reduction client |
| `SymmetricBarRecursion` | Finite-entry threading interface with postulated symmetric bar recursion and stop/step equations; rewrite clients exercise those equations |
| `LaurentPolarizedMALLP` | The linear logic core used directly by the Nat MALLP derivations and compiler proofs |

Thus all seven are **globally consumable** through public exports, while actual consumption is selective. The three packages with no direct compiler role are retained as public foundational developments, not artificially threaded through unrelated compiler proofs.

## Formal assumptions and unsupported claims

The monolithic Agda module contains explicit postulates, including the universe/identity encoding, μ-search/least-witness assumptions, and symmetric bar recursion. The cohesive adjunction record itself is not postulated; its included Set interpretation is the identity quadruple. `--with-K` is retained because parts of the fixed-point quotient development use uniqueness of identity proofs. The root `--type-in-type` option remains a consistency-breaking trust boundary, and no `--safe` or axiom-free consistency claim is made.

The Haskell backend is not verified as a general Haskell program by the generated certificates. The certificate checks the concrete emitted token data against formal Agda semantics for the covered fragment. The external Gforth interpreter and the concrete runtime file remain an external trusted/tested boundary.

Accordingly, the current result is a proof-producing, CI-checked compiler for a restricted fragment, with its strongest source-to-target theorem covering admitted Nat resource programs. It is not yet PureCake-level verification of every compiler pass, every accepted type, or Gforth itself.

## Reproducible checks

The existing GitHub Actions workflow checks repository/upstream provenance, Agda 2.8.0.2 type-checking for both tracked Agda files, Haskell backend compilation, strict-source emission, generated certificate synchronization/type-checking, and Gforth execution. It runs only on pushes to `master` and pull requests.

~~~sh
cabal build Agda:exe:agda
cabal build agda2forth
"$(cabal list-bin Agda:exe:agda)" --no-prop --no-erasure -i formal formal/MALLPForth.agda
"$(cabal list-bin Agda:exe:agda)" --no-prop --no-erasure -i formal formal/SovereignRationalSEDPhysics.agda
cp test/MALLPStrict.agda.src test/MALLPStrict.agda
cabal run agda2forth -- -i test test/MALLPStrict.agda
gforth MALLPStrict.fth
~~~

The test fixture is a finite regression corpus, not a universal semantics theorem. Any newly admitted source construct must gain a real decoder/resource contract, a source-to-MALLP derivation, an exact emitted-token certificate, a target-machine simulation, and a documented external-runtime boundary before it is advertised as verified.