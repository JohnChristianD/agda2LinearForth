# agda2LinearForth — linear/modal runtime ABI specification

`agda2forth` compiles Agda programs into GNU Gforth source. This repository combines a legacy Forth compiler with an intended checked linear/modal ABI. This README deliberately distinguishes (1) executable behavior, (2) a formal model, and (3) a proof that the implementation refines that model.

> **End-to-end compiler/runtime refinement: NOT COMPLETE.** The current Haskell backend emits raw natural-number and boolean literals and uses legacy Forth operators. The Agda model records that boundary and proves those output shapes do not carry checked ABI evidence. The dispatch decision table is a constructive model of the runtime's routing rules, not an extraction proof from Haskell/Forth.

## Source provenance and CI

The current source baseline pins upstream identities per file:

- `app/Main.hs` and `src/Agda/Compiler/Erase.hs` match compatible Agda2Scheme revision `6b3d975e9274448c09b5939e637b6718c2cfb10c`.
- `src/Main.hs` and `src/Agda/Compiler/ToForth.hs` match Agda2Forth revision `e83f8cc735bf220f80b3655ce2158a23818910fe`.
- The compiler targets the Agda 2.6.2.x API era and CI installs Agda 2.6.2.2.
- GitHub Actions checks source provenance, builds/tests Haskell, runs Gforth smoke tests, type-checks one safe Agda specification, and compiles selected fixtures.
- CI also pins the inspected `data/FLib.fth` blob (`7016170c970793dcc9eb372e8e1a0194286d953b`) so the manual Agda dispatch mirror cannot drift silently from the runtime source it describes. Changing the runtime requires an explicit update/review of this pin and the model.

Pinning proves byte-level provenance, not semantic correctness. The Haskell source is intentionally unchanged by this formal consolidation.

## One authoritative Agda specification

The proof source is consolidated into [`formal/LinearModalSafety.agda`](formal/LinearModalSafety.agda). The former four files have been merged into this single source of truth so CI checks one coherent specification rather than four modules that can drift apart.

The unified module contains:

- a descriptor heap and identity model, root/capture/payload invariants, freshness and uniqueness conditions;
- evidence-gated copy/discard, linear ownership, and modal-promotion preconditions;
- a disjoint-heap predicate (`Sep`) for separation-style reasoning;
- a weakest-precondition transformer for normal and exceptional outcomes, with operational-semantic characterization, validity/admissibility and leastness lemmas, plus derived Hoare notation and `CATCH`/sequencing laws;
- typed stack-shape effects and constructive examples for selected checked operations;
- a model of the raw-natural/legacy-add and raw-boolean output paths in the current compiler;
- an explicit table mirroring the current supported `TPrim` mappings and unsupported `fthError ... bye` path;
- a constructive decision table mirroring `ABI-DISPATCH-BINARY` for raw, checked-scalar and other tracked values.

The module imports only Agda's built-in natural numbers and equality, imports no standard library, uses `--safe`, and makes no postulates to assert the missing implementation theorem.

## What the current proofs establish

The constructive lemmas establish properties of the formal model:

1. A well-formed heap cannot contain duplicate descriptor identities.
2. The no-linear-aliasing invariant rejects aliased live linear operands under the checked arithmetic precondition.
3. A valid modal-promotion precondition excludes live linear captures and opaque-code witnesses.
4. The checked stack signatures cannot accept raw/raw operands for checked addition or equality.
5. The compiler boundary model emits natural literals as raw cells, boolean literals as raw `-1/0` cells, and natural addition through a legacy `add` footprint. Those raw shapes cannot satisfy checked-value preconditions.
6. The runtime-dispatch model routes raw/raw to the legacy path, two tracked scalar handles to the checked path, and mixed or wrong-kind tracked values to rejection.

Items 5 and 6 are explicitly models of source behavior inspected in `ToForth.hs` and `FLib.fth`, not machine-generated proofs of those files. A source hash does not establish semantic equivalence. The concrete runtime-preservation proof remains open.

## Can the end-to-end bug be fixed by changing only `.fth` files?

**Not completely, not while preserving source-level linear/modal semantics.** Forth can add runtime checks and fail-closed adapters. But the current compiler emits a literal such as `5` as a raw machine cell and emits ordinary operator names. It does not attach the source modality to that literal. After erasure, the runtime cannot reliably reconstruct whether an arbitrary unregistered cell is an Agda literal, an ordinary unmanaged value, or pointer-like data by inspecting its magnitude. Guessing would undermine the identity/representation boundary.

A Forth-only patch can improve runtime defense, but it cannot by itself establish full source-semantic refinement while the compiler output omits required mode and value-construction evidence. There is also a more direct counterexample for the current compiler/runtime combination: a prior generated-scalar integration run (using the same upstream-pinned, unchanged Haskell emitter) produced the body `:noname { a c } a c pass ;` and application sequence `5 20 scalarAdd pass pass`. The clean `FLib.fth` implementation of `pass { x h -- result }` returns `h` unchanged when `h` is not a thunk. With raw arguments `20` and `5`, this observed application path returns `5`, not source-level `20 + 5 = 25`.

The Agda file now includes a clearly labelled model of this observed path and the theorem `currentGeneratedScalarDoesNotRefineAddition`. This is a counterexample to the *manually audited output-body model*, not a mechanized extraction of the Haskell emitter. Its application to the actual backend relies on the generated output observed in CI and the inspected Forth fallback branch; the current PR's green CI does not rerun that end-to-end fixture. It nevertheless rules out honestly claiming that the current observed body implements natural addition. Changing Forth's general `pass` fallback to add values would be unsound: that word implements generic function application, not numeric addition. The responsible fix is to correct or constrain the emitted application/lowering protocol, then prove that compiler output refines the source semantics. The fixed `.hs` source constraint prevents this PR from pretending to make that compiler-side fix.

The sound path is to change the emission contract or introduce a verified source-aware translation step, then prove that every supported generated form uses it. Unsupported forms must fail through a documented boundary, not silently use legacy operations or terminate via `BYE`.


## Preserved weakest-precondition and denotational semantics

This branch is intentionally based on the last green master commit. It preserves PR #14's Agda model for continued review, but deliberately does **not** import that PR's experimental Forth changes, CI edits, debugging trace code, or generated-runtime regression. No Haskell, Forth runtime, workflow, or test files are changed here. The purpose is to assess and preserve formal ideas independently from the unresolved compiler/runtime failure.

The primary contract interface is the WP transformer, taking a command, normal postcondition, exceptional postcondition, and initial state. It computes the conditions required for the requested normal result or exceptional THROW outcome. Sequential composition and CATCH have WP equations. The new `SemanticTriple` predicate states correctness directly from `Execution`; `hoareToSemanticTriple` and `semanticTripleToHoare` show that this operational contract and the Hoare presentation agree. The lemmas `wpSemanticallyAdmissible` and `wpLeastnessFromOperationalSemantics` state that WP itself is valid and every semantically valid precondition entails it. They are sound for the current explicit finite-outcome model, where divergence is not a constructor of `Execution`.

Hoare triples are therefore redundant as an independent axiom/rule system, but not as readable specification syntax: keep them as a derived view. This follows UPenn Software Foundations, where `wp t Q` is defined from the operational evaluation predicate and characterized by `H ==> wp t Q` iff the triple is valid: https://softwarefoundations.cis.upenn.edu/current/current/slf-current/WPsem.html.

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

## What remains unproved

These are the outstanding obligations, not claims that CI has already discharged them:

- **Compiler completeness and soundness:** relate the supported Agda/Treeless fragment to emitted Forth, covering literals, booleans, primitives, constructors, matching, applications, closures and locals.
- **Runtime refinement:** prove operation by operation that actual Forth ABI words implement their Agda contracts.
- **Invariant preservation:** prove `WellFormed` after both normal return and exception for construction, binary operations, moving/capturing handles, result wrapping/unwrapping, force and promotion.
- **Exceptional behavior:** prove cleanup and rethrow behavior, including failures after state mutation. Gforth's `CATCH`/`THROW` stack restoration does not generically roll back arbitrary metadata or dictionary changes.
- **Closed-code evidence:** replace caller-asserted `declareModalSafeXT`/`declareLinearSafeXT` declarations with code-class evidence tied to an allowed compiler IR or a verified loader.
- **Unsupported paths:** the unchanged backend's `fthError` emits a diagnostic followed by `BYE`, while the checked runtime exposes catchable errors. That correspondence is not proved.
- **Operational regression coverage:** exercise all dispatch cases and generated examples against the source semantics, rather than relying only on direct ABI calls.

The Hoare/separation model is valuable because it makes intended preconditions, normal postconditions, exceptional postconditions and disjoint ownership explicit. It does not substitute for proving the implementation preserves those properties.

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

A Hoare triple `{P} C {Q}` says that, when precondition `P` holds, command `C` establishes normal postcondition `Q`; this repo additionally specifies what happens on exceptions. Separation logic adds a way to split a heap into disjoint ownership regions. In the model, `Sep` states a disjoint descriptor-identity split, while `WellFormed` combines ownership and aliasing invariants.

Start with the `Hoare`, `Sep`, and `catchPreserves` declarations in [the unified module](formal/LinearModalSafety.agda). Then compare the vocabulary with [Hoare Type Theory](https://github.com/imdea-software/htt) or [Separation Logic Proofs in Lean](https://github.com/verse-lab/splean). Those use other proof assistants; study their specifications and proof structure rather than trying to import their code into Agda.

Useful terms: **precondition, postcondition, Hoare triple, invariant, frame rule, separating conjunction, heap footprint, aliasing, ownership transfer, normal/exceptional postcondition**.

### 5. Learn refinement last

Once a small runtime word has a proved Hoare contract, connect it to the actual implementation. A **refinement theorem** says each concrete execution step matches an abstract specified step. A **simulation** proof relates concrete and abstract states. For this project, the relation must connect generated Forth, the checked runtime representation, and the Agda state model. A green test suite alone cannot establish this for all inputs.

## Research anchors

- [XDS-Agda: mechanising denotational semantics](https://pdmosses.github.io/xds-agda/) — close correspondence between a mathematical semantics and its Agda embedding.
- [Stanford: intuitionistic logic](https://plato.stanford.edu/entries/logic-intuitionistic/) and [intuitionistic type theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/) — constructive reasoning and propositions as types.
- [nLab: propositions as types](https://ncatlab.org/nlab/show/propositions%20as%20types) — a compact conceptual reference.
- [Gforth manual](https://gforth.org/manual/) — semantics for the actual target language.
- [Hoare Type Theory](https://github.com/imdea-software/htt) and [SPLean](https://github.com/verse-lab/splean) — comparative heap-contract and separation-style examples.
- Henry G. Baker, [Linear Logic and Permutation Stacks—The Forth Shall Be First](https://dcreager.net/papers/Baker1994/) — motivation for connecting Forth stack/resource behavior with linear reasoning, not a proof that unrestricted Forth enforces linearity.
- M. Anton Ertl and Bernd Paysan, [Closures—The Forth Way](https://www.complang.tuwien.ac.at/papers/ertl%26paysan.pdf), EuroForth 2018 — closure/environment mechanisms, with memory management remaining an implementation concern.
- M. Anton Ertl, [Memory Safety Without Tagging nor Static Type Checking](https://repositum.tuwien.at/handle/20.500.12708/193614), EuroForth 2022 — a technique to study, not a proof of modal or linear semantics.
