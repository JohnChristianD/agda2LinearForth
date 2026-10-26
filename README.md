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
- total Hoare triples with distinct normal and exceptional postconditions, plus a `CATCH` composition-preservation lemma;
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

A Forth-only patch can improve runtime defense, but it cannot by itself establish full source-semantic refinement while the compiler output omits required mode and value-construction evidence. The sound path is to change the emission contract or introduce a verified source-aware translation step, then prove that every supported generated form uses it. Unsupported forms must fail through a documented boundary, not silently use legacy operations or terminate via `BYE`.

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

### 4. Hoare logic and separation reasoning

A Hoare triple `{P} C {Q}` says that, when precondition `P` holds, command `C` establishes normal postcondition `Q`; this repo additionally specifies what happens on exceptions. Separation logic adds a way to split a heap into disjoint ownership regions. In the model, `Sep` states a disjoint descriptor-identity split, while `WellFormed` combines ownership and aliasing invariants.

Start with the `Hoare`, `Sep`, and `catchPreserves` declarations in [the unified module](formal/LinearModalSafety.agda). Then compare the vocabulary with [Hoare Type Theory](https://github.com/imdea-software/htt) or [Separation Logic Proofs in Lean](https://github.com/verse-lab/splean). Those use other proof assistants; study their specifications and proof structure rather than trying to import their code into Agda.

Useful terms: **precondition, postcondition, Hoare triple, invariant, frame rule, separating conjunction, heap footprint, aliasing, ownership transfer, normal/exceptional postcondition**.

### Denotational semantics, frame rule, and concurrent interference

The unified Agda specification now includes a Scott–Strachey-style, compositional denotation for a closed Nat/Bool expression fragment. Syntax is represented by an indexed `ScalarTerm`; `denoteScalar` interprets a term as an annotated natural or boolean, or a named checked arithmetic error. Addition, truncated subtraction/monus, multiplication, quotient, remainder, equality, order comparison and conditional selection all have explicit denotations. Constructive equations show how raw natural cells normalize to modal scalars, how already checked scalar modes are preserved, and how the Agda denotation agrees by definitional equality with the explicit bridge model for the enumerated operations.

This semantics is intentionally a finite, total fragment with explicit errors, not a domain model for arbitrary Forth or general recursion. Haskell's Scott–Strachey treatment of bottom and partial functions is important background, but this repository does not postulate domain-theory principles into its `--safe` proof. A future denotation for unrestricted execution would need to model divergence, mutable dictionary state, I/O, exceptions, and arbitrary execution-token effects rather than pretending the finite scalar fragment covers them.

The generic `frameRule` lifts a proved command to a state plus an untouched frame and shows that the frame invariant survives both normal and exceptional exits. `disjointUpdatesCommute` establishes that two deterministic updates to separate components of a product state commute. These are the basic interference-freedom ideas behind concurrent separation reasoning. They apply to a concrete Forth word only after its footprint/locality has been established: global metadata writes, dictionary compilation, or arbitrary `EXECUTE` are not local by default.

CI now compiles a small Agda scalar fixture and executes the emitted `.fth` through `ABI-CHECKED-RUN-NAT`. This is an end-to-end runtime test for that particular scalar entrypoint, not a theorem about all generated programs. Whole-backend correspondence for closures, application, constructor/matcher layout, capture ownership, and unsupported output remains open.

Useful references include the [Haskell Wikibooks chapter on denotational semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics), [XDS-Agda](https://pdmosses.github.io/xds-agda/), [nLab's denotational semantics overview](https://ncatlab.org/nlab/show/denotational%2Bsemantics), and the [Stanford Encyclopedia of Philosophy entry on constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/). The SEP describes RUSS as recursive-function theory using intuitionistic logic and summarizes Richman's CPF-based axiomatization; those foundations inform the constructive style here but do not prove the compiler/runtime correspondence.

### Checked scalar bridge and scope of the refinement claim

The fixed Haskell files are still untouched by this PR. The runtime adds an opt-in `ABI-CHECKED-RUN-NAT` / `ABI-CHECKED-RUN-BOOL` gate for an audited Forth entrypoint with an explicit input arity and exactly one result cell. While the gate is on, the unchanged backend's scalar preamble operators (`+`, `-`, `*`, `/`, `mod`, `=`, `>=`, `<`) route through the checked scalar ABI, and the subsequently compiled `IF` checks the canonical boolean representation or a checked boolean handle. The gate restores its previous setting on both normal and exceptional exit. When the gate is off, old native-cell operators retain their prior behavior.

Raw unboxed Nat cells in this profile are converted to immutable modal scalar handles; a registered checked scalar keeps its existing mode. The result adapter must declare whether the result is Nat or Bool, because after erasure a raw 0 does not itself tell us whether it represents Nat zero or false. Input arity is explicit so the runtime can check the expected net Forth stack effect (`n` inputs, one output). These checks validate the scalar protocol; they do not certify arbitrary Forth code passed as an execution token.

The unified standard-library-free `formal/LinearModalSafety.agda` now also contains explicit stack-effect witnesses for subtraction, multiplication, quotient, remainder, order comparisons, monus, modal/mixed modes, conditional selection, constructor/matcher schemas, result pack/unpack, and observation. Its scalar bridge lemmas prove payload/mode preservation and arithmetic/equality correspondence by Agda definitional equality. This answers why earlier examples looked like Nat addition/equality only: that was a short example set, not a justified limitation of the primitive catalogue.

## What is and is not proved

CI's Agda check proves the declarations in the unified model type-check; the Gforth smoke tests separately exercise the actual scalar dispatch words. A full compiler-to-runtime refinement theorem for every program emitted by `ToForth.hs` is still not established: the fixed backend also emits general thunk/application, constructor/matcher, wildcard, array, and legacy layout operations, while raw literals, booleans, code addresses, and capture ownership are not all accompanied by compiler-derived modality/code-safety evidence. Unsupported operations still include a `BYE` boundary. Thus this PR provides a concrete checked scalar subset and bridge-level correspondence, not a whole-program proof or a sandbox for untrusted execution tokens. The whole-backend theorem requires proving the remaining emitted forms against the concrete runtime contracts without misrepresenting the existing model as that proof.

That distinction follows constructive-methods practice: a typechecked proposition-as-types model is evidence about its definitions, not automatic evidence that a separate implementation realizes them. See the [Stanford Encyclopedia of Philosophy on constructive mathematics](https://plato.stanford.edu/entries/mathematics-constructive/), [nLab's realizability overview](https://ncatlab.org/nlab/show/realizability), [XDS-Agda](https://pdmosses.github.io/xds-agda/) for executable semantic models, and the [Gforth manual](https://gforth.org/manual/) for compilation/exception semantics relevant to the concrete target.

## 5. Learn refinement last

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
