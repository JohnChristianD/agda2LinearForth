# agda2LinearForth — linear/modal runtime ABI specification

`agda2forth` compiles Agda programs into GNU Gforth source. This repository combines a legacy Forth compiler with a checked linear/modal ABI. The current emitter directly lowers saturated primitive and builtin Nat operations to ABI adapters; this repairs the known `20 + 5` scalar counterexample on the tested path. The README distinguishes (1) executable behavior, (2) a formal model, and (3) a proof that the implementation refines that model.

> **Whole-backend compiler/runtime refinement: NOT COMPLETE.** The compiler still emits raw Nat and Bool values in many contexts, so the generated program does not carry Girard modality evidence end to end. The checked ABI enforces mode/ownership rules when values are tracked handles, but the emitter does not yet establish that every source linear/modal value is represented by such a handle. Current CI tests selected generated arithmetic/comparison and direct ABI cases, not the whole backend.

## Source provenance and CI

The current source baseline pins upstream identities per file:

- `app/Main.hs` and `src/Agda/Compiler/Erase.hs` match compatible Agda2Scheme revision `6b3d975e9274448c09b5939e637b6718c2cfb10c`.
- `src/Main.hs` matches Agda2Forth revision `e83f8cc735bf220f80b3655ce2158a23818910fe`; `src/Agda/Compiler/ToForth.hs` is the single explicitly permitted Haskell exception and contains direct lowering for saturated primitive and builtin Nat applications.
- The compiler targets the Agda 2.6.2.x API era and CI installs Agda 2.6.2.2.
- GitHub Actions checks source provenance, builds/tests Haskell, runs the checked-ABI Gforth suite, type-checks the safe Agda specification, compiles selected fixtures, and executes compiler-generated scalar programs. The Gforth suites assert an empty data stack at completion so a successful `BYE` cannot silently hide leftover test results.
- CI pins the inspected `data/FLib.fth` blob (`46ba6a5ab8c657c42c07169cf13c95a5533b41e0`) so the manual Agda dispatch mirror cannot drift silently from the runtime source it describes. Changing the runtime requires an explicit update/review of this pin and the model.

Pinning proves byte-level provenance, not semantic correctness. Only `src/Agda/Compiler/ToForth.hs` may diverge from upstream; other Haskell source files remain pinned.

## One authoritative Agda specification

The proof source is consolidated into [`formal/LinearModalSafety.agda`](formal/LinearModalSafety.agda). The former four files have been merged into this single source of truth so CI checks one coherent specification rather than four modules that can drift apart.

The unified module contains:

- a descriptor heap and identity model, root/capture/payload invariants, freshness and uniqueness conditions;
- evidence-gated copy/discard, linear ownership, and modal-promotion preconditions;
- a complete-state WP model whose state includes descriptor heap, root references, identity counter, ownership modes and exceptions;
- direct weakest-precondition contracts for normal and exceptional outcomes, operational-semantic validity/leastness, sequencing and CATCH; no parallel triple API or generic frame theorem.
- typed stack-shape effects and constructive examples for selected checked operations;
- a model of raw Nat literals plus the emitter's direct ABI adapters for saturated addition and builtin Nat subtraction; raw/raw execution still falls back to the legacy arithmetic path;
- an explicit table mirroring the supported `TPrim` mappings and unsupported `fthError ... bye` path;
- a constructive decision table mirroring `ABI-DISPATCH-BINARY` for raw, checked-scalar and other tracked values.

The module imports only Agda's built-in natural numbers and equality, imports no standard library, uses `--safe`, and makes no postulates to assert the missing implementation theorem.

## What the current proofs establish

The constructive lemmas establish properties of the formal model:

1. A well-formed heap cannot contain duplicate descriptor identities.
2. The no-linear-aliasing invariant rejects aliased live linear operands under the checked arithmetic precondition.
3. A valid modal-promotion precondition excludes live linear captures and opaque-code witnesses.
4. The checked stack signatures cannot accept raw/raw operands for checked addition or equality.
5. The compiler boundary model emits natural literals as raw cells and boolean literals as raw `-1/0` cells. Compiler-generated regression witnesses cover addition, multiplication, Nat monus (ordinary, equal, zero and underflow cases), equality, less-than, and both Boolean branches. The independent Gforth ABI matrix covers raw/raw and checked-handle arithmetic, comparisons, boolean result kinds, mode propagation, linear consumption, mixed/wrong-kind rejection, division/remainder by zero, overflow, identity exhaustion and failure atomicity. Raw literals still lack checked mode evidence; a raw cell cannot satisfy the checked-value precondition.
6. The runtime-dispatch model routes raw/raw to the legacy path, two tracked scalar handles to the checked path, and mixed or wrong-kind tracked values to rejection.

Items 5 and 6 are explicitly models of source behavior inspected in `ToForth.hs` and `FLib.fth`, not machine-generated proofs of those files. A source hash does not establish semantic equivalence. The concrete runtime-preservation proof remains open.

## Can the end-to-end bug be fixed by changing only `.fth` files?

**Not completely, not while preserving source-level linear/modal semantics.** Forth can add runtime checks and fail-closed adapters. But the current compiler emits a literal such as `5` as a raw machine cell and emits ordinary operator names. It does not attach the source modality to that literal. After erasure, the runtime cannot reliably reconstruct whether an arbitrary unregistered cell is an Agda literal, an ordinary unmanaged value, or pointer-like data by inspecting its magnitude. Guessing would undermine the identity/representation boundary.

A Forth-only patch cannot establish full source-semantic refinement while compiler output omits required mode and value-construction evidence. A historical generated-scalar CI run emitted a body resembling `:noname { a c } a c pass ;` and returned `5`, not `25`, for `scalarAdd 20 5`. That was a real counterexample to the prior application-lowering path.

The compiler-side fix is now present in `src/Agda/Compiler/ToForth.hs`: saturated `TPrim` operations and builtin Nat addition/subtraction are lowered directly to `ABI-*-OR-LEGACY` adapters instead of being passed through generic closure application. CI run [40413449999](https://github.com/JohnChristianD/agda2LinearForth/actions/runs/40413449999) compiled and executed `test/CheckedScalar.agda`, checking addition, saturating Nat subtraction in both operand orders, multiplication, equality, less-than, and both Boolean branches. The green checkpoint at that time was commit `6a7b474bcf25620bc1f30d90de0c661c95a12676`; both the push and pull-request workflow runs passed. Generated bodies use `ABI-ADD-OR-LEGACY`, `ABI-MONUS-OR-LEGACY`, `ABI-MUL-OR-LEGACY`, `ABI-EQ-OR-LEGACY`, and `ABI-LT-OR-LEGACY`; `scalarAddAnswer` still uses `pass pass` to apply the actual function closure. That `pass pass` sequence is generic application and is not itself erroneous. This corrects the observed addition counterexample on the tested path, but does not prove the entire emitter or its mode/ownership behavior. The formal module preserves `historicalGeneratedScalarDoesNotRefineAddition` as a historical counterexample model, not a claim about the current output.

The new compiler-generated Nat-subtraction witnesses added here check both `20 ∸ 5 = 15` and `5 ∸ 20 = 0`. They also exposed a Forth adapter issue: `ABI-MONUS-OR-LEGACY` used plain signed `-` for raw/raw values. The adapter now uses `ABI-SUB-RAW`, whose zero-floor behavior matches Agda Nat subtraction. CI pins the new runtime blob. These tests add executable evidence for the scalar fragment, not a whole-backend refinement theorem.

The sound path is to change the emission contract or introduce a verified source-aware translation step, then prove that every supported generated form uses it. Unsupported forms must fail through a documented boundary, not silently use legacy operations or terminate via `BYE`.


## Preserved weakest-precondition and denotational semantics

This branch continues the merged WP model, co-adjusting formal/LinearModalSafety.agda with data/FLib.fth and the permitted ToForth.hs lowering exception. The WP-only model covers the operation-level contracts; generated-code tests cover selected scalar operations. The remaining compiler/runtime relation is still only partially established.

The primary contract interface is the WP transformer, taking a command, normal postcondition, exceptional postcondition, and the full abstract state. Sequential composition and CATCH have WP equations. SemanticTriple states correctness directly from Execution; wpSemanticallyAdmissible and wpLeastnessFromOperationalSemantics establish validity and leastness for the finite-outcome model. wpCatchPreserves is stated directly in WP. The former generic frame theorem was removed because its separate frame value was untouched by construction; it did not prove that any actual Forth word respects a concrete footprint. Full-state WP is enough in principle when stack, heap, code pointers, identity counter, roots and exceptions are all modelled in the state. Separation logic remains a useful optional locality technique, not a prerequisite for defining WP. These lemmas do not establish domain-theoretic admissibility over a Scott domain, and Execution does not yet model divergence.

This follows UPenn Software Foundations, where WP is characterized from operational evaluation and weakest-precondition validity; see https://softwarefoundations.cis.upenn.edu/current/current/slf-current/WPsem.html.

**Terminology warning:** the code's WP *admissibility/validity* lemma means that WP itself is a valid precondition. It does **not** establish domain-theoretic admissibility (closure under suprema of increasing chains). The latter requires an ordered semantic domain and an appropriate continuity/admissibility development, which this finite state/outcome model does not yet define.

The unified Agda file contains three semantic layers: a finite scalar fragment with explicit errors and mode propagation; CoreDenotation, a fuel-bounded compositional model of variables, closures, application, constructors, matching, result wrappers, exceptions and print traces; and ScottScalarDenotation, which separates divergence (bottom), normal returns and exceptions. It also retains normal/exceptional frame-contract lemmas and disjoint-update commutation. These are properties of the Agda models. They are **not yet** a compiler-correctness theorem or a proof that the unchanged Haskell emitter and existing Forth runtime implement every modeled transition.

### Where Kleene's first and second algebras fit

The nLab entries on [Kleene's first algebra](https://ncatlab.org/nlab/show/Kleene%27s%2Bfirst%2Balgebra), [Kleene's second algebra](https://ncatlab.org/nlab/show/Kleene%27s%2Bsecond%2Balgebra), and [partial combinatory algebras](https://ncatlab.org/nlab/show/partial%2Bcombinatory%2Balgebra) are useful, but for a different layer than WP itself.

- **Kleene's first algebra (K1)** models partial recursive computation through number-coded programs and application. It is the natural realizability reference for the Richman/RUSS and parametric-enumerability part of this project: a computational interpretation of propositions and effective program witnesses.
- **Kleene's second algebra (K2)** uses Baire-space functions and models function realizability / type-two computability. It becomes relevant if the denotational domain explicitly includes infinite streams, choice sequences, or computable analysis. It is not needed just to model finite Forth stacks and natural-number primitives.
- **Neither algebra automatically supplies** the Scott domain for this language, an end-to-end Forth refinement, or weakest-precondition leastness/admissibility proofs. A PCA provides an applicative/computability model; the compiler proof still needs a relation between source terms, emitted Forth, runtime states, and observations.
- **WP leastness** is an order-theoretic fact about predicates: the semantic WP is valid, and every other valid precondition entails it. **Domain-theoretic admissibility** is a separate question about predicates over a domain, typically closure under limits of increasing chains. The current state model uses finite execution outcomes and does not yet define a Scott domain/order for the full Forth state space, so it cannot claim that stronger admissibility property.

A sensible follow-on is to formalize the computability interpretation separately from the runtime WP core: first define the chosen K1/partial-recursive representation and the exact parametric-enumerability assumption; then prove the specific Rice-style result with its extensionality and coding hypotheses; only afterwards connect that result to the supported compiler fragment. Keep K2 optional unless the project adds genuinely type-two/infinite-input semantics. This follows the modular style demonstrated by [XDS-Agda](https://pdmosses.github.io/xds-agda/) without importing its domain postulates into the current safe file.

### Axiom and rewrite discipline

Keep parametric enumerability in a separate, explicitly assumed Richman/RUSS module. Do not silently conflate it with countable choice; derive any choice principle required by the exact PE formulation or state it separately. Do not combine full univalence with global K/UIP (Agda's with-K mode); an optional univalent synthetic-computability development belongs in a separate Cubical Agda / without-K track. The compiler/runtime WP model does not need RUSS axioms.

There are currently no custom Agda rewrite rules in this core. The confluence checker becomes relevant when actual rewrite rules are introduced, not just because postulates exist. Agda's checker addresses overlaps and the triangle property for rewrite rules; keep any such experiment isolated and run the checker after each rule-set change: https://agda.readthedocs.io/en/latest/language/rewriting.html.



### Linear logic, realizability, and concatenative semantics

Girard's exponential modality is not merely a “linear/modal” tag: the structural rules for weakening and contraction are controlled by the !-modality, and promotion has a restricted context. The current runtime mode fields and promotion preconditions are an operational proposal inspired by that discipline, not a complete formalization of Girard's proof rules. See [nLab's !-modality](https://ncatlab.org/nlab/show/%21-modality) and [linear logic](https://ncatlab.org/nlab/show/linear%2Blogic); the [Stanford Encyclopedia's linear logic entry](https://plato.stanford.edu/entries/logic-linear/) gives a second account.

Henry Baker's [Linear Logic and Permutation Stacks—The Forth Shall Be First](https://dcreager.net/papers/Baker1994/) motivates relating linear resource use to stack-machine operations, but it does not establish that this legacy Forth backend preserves linear use. Brent Kerby's [Theory of Concatenative Combinators](https://nsl.com/misc/papers/The%20Theory%20of%20Concatenative%20Combinators.htm) and the [Joy language reference](https://hypercubed.github.io/joy/joy.html) are useful for treating Forth-like composition and multiple return values as language semantics. They should inform the target-language denotation, not be cited as proofs about this implementation.

For computability foundations, [nLab's Kleene first algebra](https://ncatlab.org/nlab/show/Kleene%27s%2Bfirst%2Balgebra) is the type-one partial-recursive model relevant to RUSS/PE, while [Kleene's second algebra](https://ncatlab.org/nlab/show/Kleene%27s%2Bsecond%2Balgebra) is based on Baire-space functions and is more relevant to type-two or infinite-input computation. Richman's CPF-style axiom is described in the [Stanford Encyclopedia entry on constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/). These computability models are separate from the concrete Forth/compiler refinement theorem.

## Paired WP/runtime allocation-refinement step

ABIAllocationWP models the checked allocator's identity-exhaustion boundary. If an allocation group would exceed the identity bound, the Agda outcome is allocationFailed identityOverflowError state, preserving the arena cursor, identity counter and metadata count. Its WP theorem proves the specified exceptional postcondition for the unchanged state.

In data/FLib.fth, capacity is now checked before allocating handle/environment/metadata cells on scalar, boolean, thunk, legacy-result, linear-move and partial-application paths. test/gforth/abi-smoke.fs forces identity exhaustion in the real runtime and checks that HERE, HANDLE-META-HEAD and NEXT-HANDLE-ID remain unchanged while the operation throws ABI-ERR-ID-OVERFLOW. The CI workflow pins the revised runtime blob so the Agda model and Forth implementation cannot drift unnoticed.

This remains an operation-level refinement result under a non-interleaved, single-threaded mutation assumption, not the full compiler/runtime theorem. The scalar `20 + 5` mismatch was repaired on the tested generated path by direct compiler lowering. Current CI also checks `20 ∸ 5 = 15` and `5 ∸ 20 = 0`, including the raw/raw monus adapter fix. Generated application outside this primitive fragment, raw value modalities, constructors, pattern matching, linear capture accounting, and all exceptional paths still require source-to-Forth simulation proofs. The checked-binary regressions additionally verify that arithmetic and result-allocation failures leave both inputs live, matching the Agda WP contract and the implementation's final ownership-commit writes.

## What remains unproved

These are the outstanding obligations, not claims that CI has already discharged them:

- **Compiler completeness and soundness:** relate the supported Agda/Treeless fragment to emitted Forth, covering literals, booleans, primitives, constructors, matching, applications, closures and locals.
- **Runtime refinement:** prove operation by operation that actual Forth ABI words implement their Agda contracts.
- **Invariant preservation:** prove `WellFormed` after both normal return and exception for construction, binary operations, moving/capturing handles, result wrapping/unwrapping, force and promotion.
- **Exceptional behavior:** prove cleanup and rethrow behavior, including failures after state mutation. Gforth's `CATCH`/`THROW` stack restoration does not generically roll back arbitrary metadata or dictionary changes.
- **Closed-code evidence:** replace caller-asserted `declareModalSafeXT`/`declareLinearSafeXT` declarations with code-class evidence tied to an allowed compiler IR or a verified loader.
- **Unsupported paths:** the unchanged backend's `fthError` emits a diagnostic followed by `BYE`, while the checked runtime exposes catchable errors. That correspondence is not proved.
- **Operational regression coverage:** exercise all dispatch cases and generated examples against the source semantics, rather than relying only on direct ABI calls.

The WP/separation model is valuable because it makes intended preconditions, normal postconditions, exceptional postconditions and disjoint ownership explicit. It does not substitute for proving the implementation preserves those properties.

## Beginner's learning path

The aim is to learn enough vocabulary to read and extend this proof—not to prove the whole compiler as your first exercise.

### 1. Propositions as types and constructive proof

Start with the [Agda documentation's introduction to dependent types](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html), then the [Stanford Encyclopedia entry on intuitionistic type theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/) and [intuitionistic logic](https://plato.stanford.edu/entries/logic-intuitionistic/). The core idea is that a proposition is represented by a type and a proof is a value of that type. In this repo, `A → B` is implication, `A × B` is conjunction, `⊥` is contradiction, and a function constructing a contradiction proves that the given preconditions cannot all hold.

Useful terms: **proposition-as-type, Curry–Howard, dependent type, inductive family, constructor, pattern matching, empty type, equality elimination/substitution, constructive proof**.

### 2. Learn by reading XDS-Agda examples

Read [XDS-Agda](https://pdmosses.github.io/xds-agda/) and its [GitHub source](https://github.com/pdmosses/xds-agda). It demonstrates how to embed a programming-language semantics in Agda using definitions close to the mathematical notation. Start with a small semantic function and one property about it; do not copy the project's domain-theory postulates into this repository. This repo intentionally makes narrower, postulate-free claims.

Useful terms: **syntax, semantic domain, denotation, semantic function, compositionality, preservation lemma, model, refinement map**.

### 3. Read Gforth semantics before proving Forth behavior

The [GNU Gforth manual](https://gforth.org/manual/) is directly relevant. Focus on [literals](https://gforth.org/manual/Literals.html), [deferred words and name binding](https://gforth.org/manual/Deferred-Words.html), [interpretation and compilation semantics](https://gforth.org/manual/Interpretation-and-Compilation-Semantics.html), and [exception handling](https://gforth.org/manual/Exception-Handling.html). These explain why redefining a word does not retroactively change earlier compiled references, how literals are compiled into code, and how `CATCH`/`THROW` behave.

Useful terms: **data stack, stack effect, execution token (XT), dictionary entry, compile-time semantics, run-time semantics, static binding, literal, normal exit, exceptional exit**.

### 4. Weakest preconditions, derived Hoare triples, and separation reasoning

Dijkstra-style WP is the single contract mechanism: given a complete runtime state, it computes the condition required for normal and exceptional outcomes. The state must include more than the data stack: descriptor metadata, roots, code pointers, allocation counters and ownership modes affect behaviour too. The `WellFormed` predicate tracks identity uniqueness, references, ownership and linear non-aliasing. A separate separation-logic frame rule is not needed to define correctness; it becomes valuable only after a specific operation's footprint is proved.

Start with wp, wpSequence, wpCatch, SemanticTriple, wpCatchPreserves, and ABIAllocationWP in [the unified module](formal/LinearModalSafety.agda). UPenn's WP development is the closest contract reference. Separation-logic texts remain useful for footprint proofs, but this code no longer presents a generic frame lemma whose locality premise is true by construction.

Useful terms: **weakest precondition, operational outcome, stack effect, complete state, invariant, allocation footprint, aliasing, ownership transfer, normal/exceptional postcondition**.

### 5. Learn refinement last

Once a small runtime word has a proved WP contract, connect it to the actual implementation. A **refinement theorem** says each concrete execution step matches an abstract specified step. A **simulation** proof relates concrete and abstract states. For this project, the relation must connect generated Forth, the checked runtime representation, and the Agda state model. A green test suite alone cannot establish this for all inputs.

## Research anchors

- [UPenn Software Foundations: WP semantics](https://softwarefoundations.cis.upenn.edu/current/current/slf-current/WPsem.html) — defines WP from operational evaluation, proves validity and leastness, and develops WP-style frame/consequence rules. Use this as the reference for the Agda leastness and admissibility-of-the-precondition lemmas.
- [UPenn Software Foundations: Separation Logic Foundations](https://softwarefoundations.cis.upenn.edu/current/current/slf-current/) — heap predicates, separating conjunction, and frame rules. A frame proof applies to Forth code only after its actual footprint/locality is established.
- [XDS-Agda: mechanising denotational semantics](https://pdmosses.github.io/xds-agda/) and [its source](https://github.com/pdmosses/xds-agda) — an exemplary separation of syntax, domains, denotations, laws and examples. Its authors explicitly state that some domain-theory postulates are not classically set-theoretic, so do not copy them into the `--safe` runtime model without a separate consistency argument.
- [Haskell Wikibooks: Denotational semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics) — introductory Scott–Strachey denotation, partial values and compositional meaning.
- [nLab: linear logic](https://ncatlab.org/nlab/show/linear%2Blogic) and [!-modality](https://ncatlab.org/nlab/show/%21-modality) — the Girard exponential, restricted weakening/contraction, dereliction and promotion. These are the logic behind the resource discipline, not proof that a runtime mode bit alone implements linear logic.
- [nLab: Kleene's first algebra](https://ncatlab.org/nlab/show/Kleene%27s%2Bfirst%2Balgebra), [Kleene's second algebra](https://ncatlab.org/nlab/show/Kleene%27s%2Bsecond%2Balgebra), and [partial combinatory algebras](https://ncatlab.org/nlab/show/partial%2Bcombinatory%2Balgebra) — distinguish type-one partial recursive realizability (K1) from Baire-space/type-two computation (K2). Neither is an automatic model of the Forth runtime.
- [Stanford Encyclopedia: constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/) — Richman's CPF-style axiomatization of RUSS and its intuitionistic setting.
- [Stanford Encyclopedia: linear logic](https://plato.stanford.edu/entries/logic-linear/) — a complementary account of Girard's exponential and its structural rules.
- [Stanford Encyclopedia: intuitionistic logic](https://plato.stanford.edu/entries/logic-intuitionistic/) and [intuitionistic type theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/) — constructive reasoning and propositions as types.
- [Agda documentation: rewriting and confluence](https://agda.readthedocs.io/en/latest/language/rewriting.html) — the overlap and triangle conditions checked by `--confluence-check`. The current core has no custom rewrite rules, so there is no rule set to check yet.
- [Agda documentation: dependent types](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html) and [Jesper Cockx: Dependent Types](https://jesper.cx/) — Agda's type discipline and proof-oriented programming context.
- [Gforth manual](https://gforth.org/manual/) — semantics for the actual target language, especially stack effects, compile-time versus run-time semantics, `CATCH` and `THROW`.
- [Hoare Type Theory](https://github.com/imdea-software/htt) and [SPLean](https://github.com/verse-lab/splean) — comparative heap-contract and separation-style examples.
- Henry G. Baker, [Linear Logic and Permutation Stacks—The Forth Shall Be First](https://dcreager.net/papers/Baker1994/) — motivation for connecting linear resource use with stack-machine operations, not a proof that unrestricted Forth enforces linearity.
- Brent Kerby, [Theory of Concatenative Combinators](https://nsl.com/misc/papers/The%20Theory%20of%20Concatenative%20Combinators.htm), and the [Joy language reference](https://hypercubed.github.io/joy/joy.html) — useful language-level accounts of composition, combinators and multiple return values.
- M. Anton Ertl and Bernd Paysan, [Closures—The Forth Way](https://www.complang.tuwien.ac.at/papers/ertl%26paysan.pdf), EuroForth 2018 — closure/environment mechanisms, with memory management remaining an implementation concern.
- M. Anton Ertl, [Memory Safety Without Tagging nor Static Type Checking](https://repositum.tuwien.at/handle/20.500.12708/193614), EuroForth 2022 — a technique to study, not a proof of modal or linear semantics.


## Gforth end-to-end test inventory

The runtime tests and compiler-generated tests are deliberately separate layers. Both must pass; one cannot substitute for the other.

- `test/gforth/abi-smoke.fs`: raw/raw adapter behavior; checked scalar and boolean results; mode joins; linear consumption and alias rejection; Nat monus saturation; mixed and wrong-kind rejection; division/remainder domain errors; overflow; unsupported-operation errors; identity exhaustion before dictionary/metadata mutation; null execution-token rejection; result wrapping/unwrapping; nested closure capture retirement on exceptions; and final data-stack balance.
- `test/CheckedScalar.agda` plus `test/gforth/compiler-integration.fs`: compile actual Agda source and execute generated Forth for addition, multiplication, comparisons, conditionals, and Nat subtraction including underflow/equality/zero boundaries. This tests compiler output rather than manually invoking adapters.
- `.github/workflows/haskell.yml`: pins upstream source identity and the runtime blob, builds/tests Haskell, runs the ABI suite, checks the `--safe` Agda specification, compiles supported and unsupported fixtures, then runs generated code.

A green workflow certifies only these tested paths and the Agda model's type-check. It does not certify arbitrary Agda programs, all Forth words, or preservation of Girard's linear/exponential rules end to end. That remains an explicit open compiler-refinement obligation.
