# agda2LinearForth

`agda2forth` translates a selected subset of Agda programs to GNU Gforth source. The repository has three distinct artifacts: a Haskell backend, a Forth runtime/ABI, and a manually maintained Agda specification. They are connected by CI checks and selected executable tests, **not by a whole-backend compiler-correctness proof**.

This README documents the implementation that exists today. Proposed target IRs, a universal `APPLY` word, statically erased runtime tags, and future verification milestones are not described as completed features.

## Architecture and ownership

```text
Agda source
   |
   v
Agda frontend, type checking, and erasure
   |
   v
src/Agda/Compiler/ToForth.hs
   |
   v
generated Forth definitions + compiler preamble + data/FLib.fth
   |
   v
GNU Gforth
```

| File | Responsibility | Verification status |
| --- | --- | --- |
| `app/Main.hs`, `src/Main.hs` | Unmodified Agda2Scheme sources; not the selected Forth entrypoint | Exact upstream identity checked in CI |
| `src/Agda/Compiler/Erase.hs` | Upstream erasure implementation | Exact upstream identity checked in CI |
| `src/Agda/Compiler/ToForth.hs` | Sole project-specific Haskell backend and executable entrypoint | Builds and runs selected fixture tests; no Agda proof establishes that it implements the formal model |
| `data/FLib.fth` | Forth closure application, descriptor ABI, ownership checks, arithmetic adapters and runtime words | Selected direct Gforth tests; no proof that all runtime transitions refine the Agda model |
| `formal/LinearModalSafety.agda` | The only tracked `.agda` module; contains the descriptor/WP/runtime model plus nested `VerifiedCoreExecutable`, `VerifiedPLLCore`, and `SovereignRationalSED` modules, including Laurent MALLP | Agda type-checking proves properties of these models, not the Haskell/Forth implementation |
| `test/*.agda.src` | Compiler fixture inputs | CI stages one input as `.agda` per step, then deletes it; none is a second tracked `.agda` module |
| `test/gforth/*.fs` | Executable ABI and generated-program regressions | Executed directly by Gforth in CI |

All explanatory and verification documentation lives in this README. There are no separate formal-design or verification-map Markdown files.

### Source-provenance boundary

CI checks that:

- All Haskell files except `src/Agda/Compiler/ToForth.hs` are byte-identical to Agda2Scheme revision `24e02d9669f17d98ec67b8ad961cf9c3e602bf10`; CI verifies the complete changed-`.hs` path allowlist and exact content using `git fetch`, `git diff`, and Git blob hashes.
- `src/Agda/Compiler/ToForth.hs` owns the Forth backend entrypoint and is the sole Haskell exception. Cabal invokes its `main` directly. `src/Main.hs`, `app/Main.hs`, and `src/Agda/Compiler/Erase.hs` remain upstream-identical.
- CI asserts exactly one tracked `*.agda`: `formal/LinearModalSafety.agda`. Compiler test inputs are stored as `*.agda.src`; CI copies each to a temporary `.agda` for that step and removes it with an EXIT trap. No permanent helper scripts are used.
- `data/FLib.fth` matches the reviewed runtime blob pinned in CI as `30477369597107b579ffac29735c42b6e326b0d0`.

A hash match establishes byte identity with a reference file. It does not establish semantic correctness. In particular, the Agda model is manually written and maintained; a provenance check does not prove that `ToForth.hs` or `FLib.fth` implements it.

## Current compiler lowering

The backend consumes Agda's treeless syntax and directly emits Forth forms. There is **no Agda-defined target instruction language or verified pretty-printer boundary yet**.

### Saturated operations

For matching treeless argument shapes, `fthDirectPrimitive` emits the following words:

| Treeless operation | Emitted Forth |
| --- | --- |
| `PAdd` | `ABI-ADD-OR-LEGACY` |
| `PSub` | `ABI-SUB-OR-LEGACY` |
| `PMul` | `ABI-MUL-OR-LEGACY` |
| `PQuot` | `ABI-QUOT-OR-LEGACY` |
| `PRem` | `ABI-REM-OR-LEGACY` |
| `PEqI` | `ABI-EQ-OR-LEGACY` |
| `PGeq` | `ABI-GEQ-OR-LEGACY` |
| `PLt` | `ABI-LT-OR-LEGACY` |
| `PIf` with three arguments | Inline Forth `if ... else ... then` |

The builtin Nat addition and subtraction definitions also have exact-two-argument lowering paths. Addition emits `ABI-ADD-OR-LEGACY`; Nat subtraction emits `ABI-MONUS-OR-LEGACY`, preserving Nat's zero-floor behavior on the raw-cell path as well as the checked path. These cases are not a general primitive table for every Agda builtin.

### Partial application and function calls

The ordinary application mechanism is the runtime's existing `pass` path, together with the compiler's thunk/closure construction. There is no separate runtime word named `APPLY`; documentation referring to a future `APPLY` protocol would describe a proposed redesign, not this implementation.

Under-applied builtin Nat addition maps to the curried `add` word, and under-applied builtin Nat subtraction maps to `monus`. The generated-program fixture also exercises partial multiplication, partial equality, partial less-than, and partial application of a user-defined function.

The integration suite contains **23 expected Nat/Bool results**. Those executions are evidence for the exercised examples only. They do not establish all higher-order functions, closure combinations, constructors, pattern matches, or all argument shapes correct.

### Literals and unsupported terms

- Nat literals are emitted as decimal strings and parsed by `ABI-PARSE-NAT`; parsing produces one raw cell or throws a catchable range/format error.
- The special Boolean constructors are emitted as raw flags: `-1` for true and `0` for false.
- Not every source value is wrapped in a managed scalar/Boolean descriptor. Therefore a compiled value is not guaranteed to carry a runtime witness for its source modality.
- The shared unsupported-output path emits a diagnostic and invokes `ABI-ERROR-COMPILED-UNSUPPORTED`. That runtime word raises a catchable `THROW`; String-literal and referenced-axiom fixtures check the error code and stack balance. Unsupported primitives no longer fall through to generic closure application, malformed Bool cases fail closed, and unmatched unreachable pattern branches invoke the catchable `ABI-ERROR-UNREACHABLE` path.
- The literal fallback rejects kinds outside the directly emitted Nat path. String literals and referenced axioms now have dedicated catchable-boundary integration tests.
- Do not assume every unknown builtin fails closed. A definition not recognized by the direct/special mapping can fall through to generic name/application handling. An exhaustive checked allowlist for an explicitly supported source subset is still missing.

## Runtime ABI: `data/FLib.fth`

The runtime retains compatibility with raw legacy cells and also supports values represented by managed descriptors. These are distinct paths, not a guarantee that every generated source value uses the checked representation.

A managed descriptor tracks identity, kind, mode, life state, execution token, captured values, and optional result payload. Managed kinds include `THUNK`, `RESULT`, `SCALAR`, and `BOOLEAN`. Runtime modes include `MODE-UNANNOTATED`, `MODE-LINEAR`, and `MODE-MODAL`; unannotated is a runtime boundary state, not a third source modality.

The existing `pass` word handles closure application and checks metadata for managed closures/captures. `makeTHUNK`, `dethunk`, result wrappers, and capture-retirement code support closure execution and ownership transitions. Arithmetic adapters dispatch as follows:

- Two registered scalar handles use the checked operation.
- Raw Nat adapters validate nonnegativity and use checked finite-cell arithmetic for addition, multiplication, quotient, remainder, equality, greater-or-equal, and less-than; Nat monus uses its saturating raw operation. `ABI-PARSE-NAT` validates each decimal digit and bounds the accumulating value before producing a raw cell.
- Mixing raw and managed operands throws an error.
- Registered operands of an incompatible managed kind are rejected.
- `ABI-SUB-OR-LEGACY` remains a separate legacy subtraction path; Nat subtraction is lowered through `ABI-MONUS-OR-LEGACY`.

The runtime tests exercise checked operand/range validation, linear consumption and alias rejection, mode behavior, Nat monus, mixed representations, arithmetic-domain errors, overflow, identity exhaustion and failure atomicity, null execution tokens, result wrapping/unwrapping, and retirement of linear captures when a closure exits exceptionally.

The raw Nat arithmetic adapters and `ABI-PARSE-NAT` enforce nonnegative-cell inputs, bounded results, and catchable overflow/domain errors for their covered operations. The runtime checks each decimal literal rather than relying on an Agda-only representability witness. This still does not prove that every source type is in the supported subset. No claim is made that arbitrary Forth is sandboxed or that Girard's structural rules are preserved for every compiled Agda program.

## What the semantic model is—and is not

The accurate umbrella description is **a Dijkstra-style weakest-precondition model with explicit descriptor-heap and ownership invariants, plus a Laurent MALLP proof-rule development**. “Linear/modal safety” accurately names one part of that model: the runtime descriptor discipline distinguishes linear resources from modal resources, and the model permits duplication/discard only for modal descriptors. It is not yet accurate to describe the whole backend as a verified linear-modal compiler, because no source typing/usage theorem proves that every term accepted by the compiler obeys those rules.

The WP judgment is explicit. Commands return either a normal state or an exceptional state paired with a runtime error; the WP has separate normal and exceptional postconditions. Its `wpSequence`, `wpCatch`, and `SemanticTriple` laws are Dijkstra-style operational contracts. The present outcome type is total and does not itself model divergence; a separate finite-fuel denotation records exhaustion.

Calling this **separation logic** would overstate the formalization. The machine state has a descriptor heap represented as a list, roots, identity freshness, ownership, liveness, and reference invariants. But the file does not define a separating assertion connective over disjoint heaps, a heap-splitting composition algebra, or a general separation-logic frame rule. `stackTailFrame` is a proved suffix-preservation law for the abstract stack-effect relation; it is not a heap frame rule and proves nothing by itself about concrete Forth word footprints. The precise label is “WP plus explicit heap/ownership invariants,” not “Dijkstra separation logic.”

The Laurent MALLP calculus is another distinct component. Its formula grammar, duality, optional positive stoup, negative context, explicit exchange, cut, multiplicative/additive rules, units, and polarity shifts are formalized. It has no exponential modalities or Seely comonad. The runtime’s `modal` duplication/discard mode is not an implementation of a Laurent shift and is not derived from MALLP. The current file also contains separate foundational packages with explicit postulates and rewrite rules; the unified source is not axiom-free and is not checked with Agda `--safe`.

PureCake and CakeML provide the **desired proof decomposition**, not an already-realized proof result. This repository does not yet have PureCake's source-to-thunk pass chain, a typed Forth IR shared with Haskell, serializer correctness, or a final theorem relating actual generated Forth execution to source observations.
## What `formal/LinearModalSafety.agda` establishes

The formal source uses Agda builtins rather than the standard library. The compiler/runtime model and bounded Nat simulation are ordinary checked definitions, but the nested `SovereignRationalSED` foundation package is **not axiom-free**: it declares assumptions for an unbounded μ-search and its equations, arithmetical countable least-witness choice, cohesive modalities/retractions, quotient types, and symmetric bar recursion. It also enables rewrite rules for μ-search, bar recursion, and lookup/tabulation. Those declarations are trusted assumptions, not theorems proved by this repository, and their presence is why the unified file is not checked with `--safe`. The MALLP proof rules themselves contain no Seely/exponential constructors; that fact does not remove the separate foundational postulates elsewhere in the same file. The conatural model is a decreasing Boolean sequence. Formal checking uses Agda 2.8.0.2, `--without-K`, and the project options declared in the module. CI type-checks the root and its imports with:

```sh
agda --erasure --no-libraries -i formal formal/LinearModalSafety.agda
```

Its theorems concern explicitly defined Agda models. The module includes:

1. **Descriptor and ownership invariants.** An abstract state contains a descriptor heap, roots, and a fresh identity counter. The well-formedness predicate tracks identity uniqueness, registered references, live captures and payloads, ownership of linear resources, checked modes, and linear non-aliasing.
2. **Weakest-precondition contracts.** Commands produce a normal or exceptional outcome with state. WP uses separate normal and exceptional postconditions and includes sequencing and `CATCH` laws. This finite-outcome model is not a complete semantics for arbitrary divergence.
3. **Declarative stack effects.** `StackEffect` records allowed stack shapes for selected modeled operations. `stackTailFrame` proves a suffix-preservation property of that relation. It does not prove that the concrete Forth words obey the relation.
4. **Selected allocation, error, result, and closure contracts.** These are proofs about transitions defined in the Agda model, not automatic proofs about dictionary or metadata mutation in Gforth.
5. **Nat stack-program forward simulation and cell-bound contract.** The Nat fragment has a linear target-program representation: raw Nat-cell pushes followed by modeled `ABI-ADD-OR-LEGACY`, `ABI-MUL-OR-LEGACY`, and `ABI-MONUS-OR-LEGACY` instructions. An inductive execution relation specifies their abstract raw/raw stack behavior, and `runNatStackProgram` gives that instruction language an executable semantics with an explicit underflow result. `natStackExecSound` connects the relational and executable semantics. `StackSemanticPass` packages a lowering with an observation-preservation theorem; `composeStackSemanticPass` composes pass proofs. `natStackCompilerPass` instantiates this interface for `NatExpr → NatStackProgram`, while `NatCompilationCertificate` packages emission meaning, linearization, execution, and a finite-cell witness. `natStackExecAppend` proves sequencing, and `emissionTreeAgreesWithStackProgram` connects the tree-shaped emission mirror to the linear program. `natExpressionForwardSimulatesStackProgram` proves the expression denotation is placed above an arbitrary unchanged stack tail. Because Agda `Nat` is unbounded but a concrete Gforth cell is finite, `NatCellRepresentable` additionally requires every literal and intermediate result to fit a supplied bound. `natExpressionBoundedForwardSimulatesStackProgram` combines that witness with the stack simulation. `NatCompilationCertificate` packages the representability witness as proof data, but the Haskell compiler does not yet produce that certificate; the decimal parser and raw arithmetic adapters dynamically enforce finite-cell bounds. Choosing the model bound equal to the concrete `ABI-MAX-NAT` and proving the emitter/runtime bridge remain separate obligations.
6. **Curried closure model.** Separate lemmas show that the modeled curried addition, monus, and multiplication closures preserve their corresponding arithmetic when applied.
7. **Nat/Bool and compiler-boundary models.** Selected arithmetic, comparisons, conditionals, and errors are modeled. The boundary model explicitly represents the fact that raw Nat/Bool outputs lack a runtime mode witness.
8. **Emitter/runtime inventory.** Section 5 models the supported primitive table, direct saturated versus curried primitive lowering, the special saturated builtin Nat addition/monus paths, all current literal kinds, definition compilation, the major `TTerm` cases, Boolean constructor/case lowering, pattern-alternative encoding, and catchable failure branches from `ToForth.hs`. Literal alternatives are currently encoded into the constructor-like pattern path; their equality semantics are not established by this model or its tests. Section 6 models selected `FLib.fth` dispatch and mode joins; later sections model selected arithmetic, allocation, closure, and exceptional transitions. These tables are maintained by hand and are not generated from either implementation.

The historical theorem `historicalGeneratedScalarDoesNotRefineAddition` preserves the old fallback-body counterexample as historical context. It is not a claim that the current tested saturated-addition lowering still exhibits that old result.



## What remains unproved

This closes the source-expression-to-abstract-stack-program proof obligation for this four-constructor Nat fragment and makes its finite-cell representability precondition explicit. `NatCellRepresentable bound expr` is proof-carrying evidence that each literal and recursive intermediate fits the abstract bound; `bound` must be tied to the concrete runtime's cell limit before using the theorem as a machine-cell argument. The proof does **not** close the concrete implementation bridge. The instruction sequence remains a manually maintained model of the lowering/ABI word classes. The updated raw Nat operations and decimal-literal parser check input cells and overflow at runtime, but this does not prove that the Haskell emitter always emits these operations for every term in the supported grammar.

The current Agda file does **not** prove:

- that Haskell's `ToForth.hs` implements the modeled emission relation;
- that the real `data/FLib.fth` implementation refines every modeled state transition, or that concrete generated inputs dynamically satisfy the model's cell-bound precondition;
- that arbitrary compiled Agda programs preserve source denotation;
- that every source linear/modal value gains a checked runtime descriptor;
- that arbitrary emitted Forth has safe stack effects or ownership behavior;
- that all Agda builtins, literals, data types, higher-order terms, and pattern matches are supported.

A whole-backend proof needs an explicit supported source subset, a target instruction/emission relation shared by the specification and implementation, and a forward simulation that connects source meaning to generated Forth and concrete runtime state. A small Agda model and green regression tests are useful evidence, but they are not a substitute for that bridge.

## Constructive foundations and polarized-logic fragment
### Latest Library monolith synchronization

The nested `SovereignRationalSED` module in `formal/LinearModalSafety.agda` is synchronized with the latest Library artifact `SovereignRationalSED-MALLP.agda` (2026-11-05). The embedded module matches that source after removing its standalone compiler-options/header preamble, applying the enclosing-module indentation, correcting one stale “eight foundational packages” comment to “seven”, and omitting one duplicate `infix 4 _<_` declaration: the outer compiler module already declares that fixity. That fixity-only omission is required for Agda's single-module namespace; it changes no definition or theorem.

The seven nested package modules are **six earlier foundations plus constructive Laurent MALLP**, not seven postulates:

| Package | Present formal content | Exact boundary |
| --- | --- | --- |
| 1. Forster-style parametric enumerability | Typed `ParametricallyEnumerable`, typed `ProgramCode`, `universalEval`, and a definitional `forster-eval` theorem | `ProgramCode` carries an enumerator record and parameter. This is not a Gödel numbering of arbitrary programs by `Nat`. |
| 2. Markov / least witness | Unbounded `μ-search`, its true/false equations, constructive bounded search, and the least-witness/countable-choice interface | The unbounded search and arithmetical countable least-witness principle remain postulated. The false equation can unfold indefinitely when no witness exists. Bounded search does not replace the unbounded principle. |
| 3. Mac Lane coherence | Recursive flattening normalizer `tensorNF` for the free tensor-object syntax, with equations proved by `refl` | This is object-level normalization for that syntax, not the full morphism-level coherence theorem for arbitrary monoidal categories. |
| 4. Cohesive modality fragment | `Disc`, `Π`, `Γ`, `coDisc` and three object-level isomorphisms | These operators and isomorphisms are postulated. There is no constructed cohesive topos, site, sheaf semantics, or full natural adjoint quadruple. |
| 5. Hofmann-style quotient fragment | Quotient carrier/class, `canonize`, quotient-canonicalization, idempotence and relatedness interfaces; explicit relation laws | Quotient formation, class construction and canonicalization laws remain postulated. Reflexivity, symmetry and transitivity are explicit parameters, not a hidden setoid record. No full quotient eliminator/universal-property development is claimed. |
| 6. Spector-style symmetric bar recursion | Finite partial maps with unique keys, domain decisions, `omegaThread`, a branchwise bar condition, and the recursive interface | `symmetricBarRec`, `sBR-stop`, and `sBR-step` remain postulated. This is not yet an executable total Spector recursor or a termination proof. |
| 7. Laurent MALLP | Positive/negative formula grammar, De Morgan duality and involutivity, negative contexts, optional positive stoup, exchange, cut, multiplicatives, additives, units and `down`/`up` shifts | No exponentials, Seely comonad, weakening, or contraction. Cut elimination and proof-net normalization are not proved. |

There are **five postulate blocks containing twenty postulated declarations** in these six non-MALLP foundations: three μ-search equations plus the countable least-witness principle; seven cohesive operators/isomorphisms; six quotient constants/laws; and three symmetric-bar-recursion constants/equations (the remaining one is the bar-recursion recursor, giving three total in that package). Forster enumeration, Mac Lane's object normalizer, and MALLP contain no postulates. The package count and postulate count are deliberately different.

The one global rewrite registration has exactly five equations:

`μ-step-true`, `μ-step-false`, `sBR-stop`, `sBR-step`, and `lookup-tabulate`.

The first four are postulated. `lookup-tabulate` is proved by recursion on the finite bound and is an auxiliary list-computation theorem, **not an eighth foundational package**. Agda's confluence check does not establish termination; in particular, the unbounded false μ-search step is not a terminating normalizer. The MALLP constructors add no rewrite equations.

The embedded RSED code has no `Vec`, `Fin`, or custom `Index` datatype and no first-class setoid/`IsEquivalence` record. It uses ordinary lists, `Nat` labels, explicit bounds where required, and builtin intensional equality. This does not make quotient assumptions constructive: the generic quotient interface still needs an equivalence relation and its laws.


The conatural proof model follows TypeTopology's generic-convergent-sequence representation: a Boolean sequence with the decreasingness proof that once an observation is false, all later observations remain false. It is connected to the backend-compilable observation interface in `VerifiedCoreExecutable (nested module in formal/LinearModalSafety.agda)` by `finiteObservationAgrees` and `infiniteObservationAgrees`; CI compiles examples of that interface to Forth and executes them with Gforth. This tests the finite ABI projection, not arbitrary functions over conaturals or whole-backend correctness.

`VerifiedPLLCore (nested module in formal/LinearModalSafety.agda)` re-expresses a deliberately bounded subset of the ideas in TypeTopology without importing its standard-library-scale dependency graph.

- **CompactTypes/searchability:** `isSigmaCompact` is the root-or-everywhere-true decision shape for Boolean predicates. `finiteSearchCompact` proves it for types supplied with a complete finite enumeration. This is not a claim that all of `Nat` is Σ-compact/LPO.
- **Conaturals:** `CoNat` encodes `ℕ∞` as a decreasing Boolean sequence, following `TypeTopology.GenericConvergentSequence`. It permits undecided finite-versus-infinite sequences constructively. The executable ABI exposes finite and infinite observation cases, with correspondence theorems; `coNatFiniteObservationCompact` applies only to predicates explicitly factored through one fixed observation, not arbitrary predicates on `ℕ∞`.
- **Hedberg:** `hedberg` proves that decidable equality makes identity types propositions, using no `K` postulate.
- **Markov substitute:** `finiteMarkov` and `coNatFiniteObservationMarkov` eliminate double-negated root existence only when constructive finite/enumerated compactness evidence is available. They are bounded principles, not unbounded Markov's principle for arbitrary predicates on `Nat`.
- **Dyads:** `Dyad` stores an integer numerator as a pair of naturals plus a denominator exponent, with addition, multiplication, cross-multiplication equivalence, and reflexivity of that equivalence. The encoding is not normalized; ring laws, order, normalization, and their proofs remain incomplete.
- **Polarized linear logic:** The nested `LaurentPolarizedMALLP` module defines Laurent's positive/negative formula grammar, polarity duality with involutivity proofs, negative contexts, an optional positive stoup, exchange by explicit context permutations, and proof constructors for identity, cut, exchange, tensor, one, plus, par, with, bottom, top, and both polarity shifts. It has no `!`/`?`, weakening, contraction, Seely comonad, cut-elimination proof, proof-net normalization, or compiler/runtime bridge. This is a formal proof-rule system, not a certified compiler.

`hedbergReflect` is a small builtin-reflection macro: it builds a term applying the already type-checked `hedberg` theorem to an explicitly supplied decidable-equality procedure and two equality proofs. The kernel checks the resulting proof term. This is theorem instantiation, not general proof search, a reflection-based ring solver, or an implementation of dyad normalization. Rewrite support is enabled by the root module's declared Agda options; no claim of ring automation is made.

## Test and CI contract

CI checks that `ToForth.hs` is the sole Haskell divergence from pinned Agda2Scheme sources, builds the Haskell compiler, runs the configured Cabal test command, installs/runs Gforth tests, type-checks the one tracked Agda specification, and stages individual fixture sources temporarily. The relevant commands are:

```sh
cabal build all
cabal test all

gforth -e 'include data/FLib.fth' -e 'include test/gforth/abi-smoke.fs'
agda --erasure --no-libraries -i formal formal/LinearModalSafety.agda

# Fixture source is stored as .agda.src so the repository tracks only one .agda file.
(
  cp test/CheckedScalar.agda.src test/CheckedScalar.agda
  trap 'rm -f test/CheckedScalar.agda' EXIT
  cabal run agda2forth -- --erasure -i test test/CheckedScalar.agda
  gforth CheckedScalar.fth test/gforth/compiler-integration.fs
)

(
  cp test/UnsupportedNatLiteral.agda.src test/UnsupportedNatLiteral.agda
  trap 'rm -f test/UnsupportedNatLiteral.agda' EXIT
  cabal run agda2forth -- --erasure -i test test/UnsupportedNatLiteral.agda
  gforth UnsupportedNatLiteral.fth test/gforth/unsupported-nat-literal.fs
)

(
  cp test/UnsupportedLiteral.agda.src test/UnsupportedLiteral.agda
  trap 'rm -f test/UnsupportedLiteral.agda' EXIT
  cabal run agda2forth -- --erasure -i test test/UnsupportedLiteral.agda
  gforth UnsupportedLiteral.fth test/gforth/unsupported-boundary.fs
)

(
  cp test/UnsupportedAxiom.agda.src test/UnsupportedAxiom.agda
  trap 'rm -f test/UnsupportedAxiom.agda' EXIT
  cabal run agda2forth -- --erasure -i test test/UnsupportedAxiom.agda
  gforth UnsupportedAxiom.fth test/gforth/unsupported-axiom-boundary.fs
)

(
  cp test/VerifiedCoreSmoke.agda.src test/VerifiedCoreSmoke.agda
  trap 'rm -f test/VerifiedCoreSmoke.agda' EXIT
  cabal run agda2forth -- --erasure -i test test/VerifiedCoreSmoke.agda
  gforth VerifiedCoreSmoke.fth test/gforth/verified-core-smoke.fs
)

(
  cp test/TriplesFO.agda.src test/TriplesFO.agda
  trap 'rm -f test/TriplesFO.agda' EXIT
  cabal run agda2forth -- --erasure -i test test/TriplesFO.agda
)
```

At present, `cabal test all` reports that there are no package test suites to run. The meaningful executable regression coverage is in the explicit Gforth fixtures and generated-program integration test.

The 23 compiler-generated Nat/Bool witnesses cover saturated arithmetic/comparison/conditional cases and selected partial applications: curried builtin addition, `_+_ 5`, a partially applied user function, monus with either fixed operand, multiplication, equality, and less-than. The separate ABI suite tests checked and legacy paths, ownership/mode rejection, arithmetic boundaries, identity-allocation atomicity, result operations, exceptional closure cleanup, and final data-stack balance. The TriplesFO fixture is compiled as a smoke test only.

A successful CI run means these explicit commands passed at that commit. It is not a universal proof about the entire source language or arbitrary Forth programs.

## Numeric scope and possible extension

The currently tested arithmetic core is Nat operations and comparisons with Bool results. Additional numeric representations and fixed-point arithmetic are not implemented.

The current target stack model is restricted to the explicitly modeled Nat and Bool paths. Other source-level numeric representations remain outside that semantics until they have a defined target representation and corresponding machine-checked semantics.

A fixed-point value stored in data-stack cells may be a reasonable future extension; Q32.32 is only a candidate. No choice is implemented or finalized. Before claiming a fixed-point format, specify the machine-cell width and signed representation, scale/range, rounding semantics, multiplication/division behavior, overflow conditions, and a shared Agda/Forth contract. Do not claim native-integer performance or algebraic laws until the concrete representation and its correspondence have been implemented and tested.

## Status at a glance

| Area | Evidence-backed status |
| --- | --- |
| Upstream source identity | Checked by CI hashes |
| Selected saturated Nat/Bool lowering | Generated-program tests |
| Selected partial-application cases | Generated-program tests using existing `pass` path |
| Checked managed ABI | Direct Gforth tests for enumerated cases |
| Agda model | Type-checks with Agda 2.8.0.2 and `--erasure`; no `--safe` claim |
| Finite-type Σ-compactness and bounded Markov substitute | Constructive proofs in `VerifiedPLLCore`; only for an explicit finite enumeration |
| Hedberg and conatural finite-observation model | Constructive proofs; finite and infinite-observation projection is tested through generated Forth; no claim of arbitrary-function compactness of `ℕ∞` |
| Dyad laws | Representation/operations and equivalence reflexivity only; full ring laws and normalization are not proved |
| Laurent MALLP | Formula grammar, duality, negative-context/positive-stoup sequent rules, explicit exchange, cut, multiplicatives, additives, units, shifts; no exponentials or Seely structure |
| Modeled Nat-expression-to-stack-code simulation | Proven for literals, addition, multiplication, and monus with stack-tail preservation; finite-cell fit is an explicit proof precondition, not a runtime check |
| Oversized Nat literal | Generated decimal string is parsed and overflow is caught end to end |
| Unsupported String literal and referenced axiom | Catchable errors tested end to end |
| Nat literal parsing and raw arithmetic | Invalid/oversized decimal, negative input, arithmetic overflow, and zero-divisor cases tested through catchable errors |
| Exhaustive allowlist for supported source subset | Not implemented |
| Haskell-emitter correspondence to Agda model | Not proved |
| Concrete runtime refinement of Agda model | Not proved |
| Whole-backend compiler correctness | Not proved |
| General linear/modal preservation for compiled Agda | Not proved |
| Additional numeric and fixed-point arithmetic | Not implemented |

## References and further reading

These sources are background for the model and target language, not claims that the project has inherited their theorems:

- [GNU Gforth manual](https://gforth.org/manual/) for the concrete target's stack, execution-token, and exception behavior.
- [Agda 2.8.0.2 documentation](https://agda.readthedocs.io/en/latest/command-line-options.html) for current compiler options, including erasure checking.
- Henry G. Baker, [Linear Logic and Permutation Stacks: The Forth Shall Be First](https://dcreager.net/papers/Baker1994/), for the connection between linear resource use and stack permutations.
- [XDS-Agda](https://pdmosses.github.io/xds-agda/) and its [source repository](https://github.com/pdmosses/xds-agda/) for an example of organizing a language semantics in Agda.
- [Haskell Wikibooks: Denotational semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics) for compositional denotational models.
- [UPenn Software Foundations: Separation Logic Foundations](https://softwarefoundations.cis.upenn.edu/current/current/slf-current/) for heap predicates and frame reasoning. Such reasoning applies to a concrete Forth word only after its footprint and behavior have been established.
- [Stanford Encyclopedia of Philosophy: Constructive Mathematics](https://plato.stanford.edu/entries/mathematics-constructive/) for the constructive-mathematics context.
- [TypeTopology source repository](https://github.com/martinescardo/TypeTopology), especially `source/TypeTopology/CompactTypes.lagda`, `source/TypeTopology/GenericConvergentSequence.lagda`, `source/TypeTopology/GenericConvergentSequenceCompactness.lagda`, `source/CoNaturals/Type.lagda`, `source/UF/Hedberg.lagda`, `source/Taboos/MarkovsPrinciple.lagda`, and `source/Dyadics/Type.lagda`. The local module is a dependency-light re-expression of a limited subset, not a wholesale port.
- [nLab: Linear logic](https://ncatlab.org/nlab/show/linear%2Blogic) and [!-modality](https://ncatlab.org/nlab/show/%21-modality) for the intended logical interpretation of modal structural rules.
- M. Anton Ertl and Bernd Paysan, [Closures: The Forth Way](https://www.complang.tuwien.ac.at/papers/ertl%26paysan.pdf), EuroForth 2018, for Forth closure/environment design.


## CakeML and PureCake: proof architecture adopted


### What is synchronized—and what is not

This repository synchronizes a **semantic proof plan**, not CakeML's or PureCake's complete HOL4 formalization. The upstream developments use HOL4 datatypes, operational semantics, proof infrastructure, and target machines that are not definitionally interchangeable with Agda or Gforth. Their scripts are therefore references for proof decomposition; the theorems must be re-derived for this compiler's source subset and target.

| CakeML / PureCake proof layer | Required agda2forth counterpart | Status in this repository |
| --- | --- | --- |
| Source-language semantics and parser/type-inference soundness | Explicit supported Agda/Treeless grammar plus a relation from Agda checking/erasure to that grammar | Partial; no exhaustive accepted-source theorem |
| PureCake lazy PureLang semantics | Source evaluation with return, exceptions, observable effects and divergence | Partial WP model; finite outcome model does not cover arbitrary divergence |
| PureLang → thunkLang via explicit `Delay`/`Force` | A target thunk language and a proved lazy-to-thunk pass | Missing; `makeDelay = id` and variable forcing bypass mean the lazy flag is not a verified PureCake translation |
| Thunk/environment/state passes | Separate intermediate syntaxes, executable semantics and one preservation theorem per pass | Missing beyond the small hand-mirrored Nat stack fragment |
| CakeML backend correctness and installed-code premises | Typed Forth IR, Haskell lowering correspondence, exact serializer relation | Missing; `ToForth.hs` is not proved to emit the Agda instruction model |
| CakeML target-machine semantics | Complete Forth machine state and operational semantics for stacks, dictionary/code, descriptors, exceptions and I/O | Partial; selected ABI behavior and WP contracts only |
| PureCake/CakeML composed top-level theorem preserving observations | One theorem relating supported Agda observations to execution of the exact generated Forth program | Missing |

The Nat certificate is a genuine theorem about the manually defined Agda `NatExpr` and `NatStackProgram` models. It does not certify that the Haskell process emitted the same instruction list, that the text serializer preserves it, or that Gforth executes the real Forth runtime according to the model. That implementation bridge is the central remaining theorem.

CakeML and PureCake are models for the shape of a complete correctness argument, not proofs that can be imported wholesale into this repository.

CakeML separates parser correctness, type-inference soundness/completeness, backend correctness, target machine semantics, installed-code hypotheses, initial-state invariants, and resource bounds. Its top-level theorem composes those results. PureCake adds a particularly relevant pass chain for a lazy language: PureLang source semantics → explicit thunk language → environment/state representations → CakeML. Each compiler pass has its own syntax, semantics, side conditions, and preservation theorem. PureCake preserves observable behavior, including interaction and divergence, rather than only comparing returned values.

The intended proof graph here is:

```text
supported typed Agda/Treeless source
  → source semantics and erasure relation
  → canonical expression representation
  → typed Forth instruction representation
  → exact Forth serializer
  → abstract Forth machine
  → concrete Gforth execution
```

Each arrow must have a separately checked preservation theorem. The final theorem must quantify over the actual compiler output and initial runtime state, and relate source observations with concrete target observations. The observation relation must account for return values, exceptions, divergence or explicit fuel, and externally visible effects in the supported subset.

The current Nat fragment is only the first small instance of that architecture. `NatStackInstruction` has an executable semantics, `NatStackExec` relates execution traces, `natStackExecSound` connects the relation to the interpreter, and `StackSemanticPass` packages a lowering with an observation-preservation proof. `composeStackSemanticPass` composes adjacent pass proofs. `NatCompilationCertificate` packages the hand-mirrored Nat expression's meaning, linearization, abstract stack execution, and finite-cell representability evidence.

That certificate is produced by an Agda function over the *formal Nat AST*. The Haskell compiler does not currently construct or emit it. The Agda AST and target instructions are manually mirrored; no theorem establishes that `ToForth.hs` produces those instructions or that the resulting Forth text parses to them.

### Laurent MALLP scope

The nested `SovereignRationalSED` development includes Laurent-style polarized MALLP formula syntax and proof-rule constructors. Positive formulas include atoms, units, tensor, sum, and a down-shift; negative formulas include atoms, units, par, with, and an up-shift. Its sequent shape uses an ordered negative context and an optional positive stoup.

This fragment has no exponential `!`/`?` modalities, no Seely comonad, and no structural weakening or contraction rules. The additive `with` rule shares its additive context; that is part of its additive behavior, not contraction. A cut rule is present, but a complete cut-elimination proof and a proof-net normalization development are separate obligations.

MALLP is presently a formal logic development inside the one Agda file. It is **not** yet the source type system for the compiled Agda subset, does not constrain every source program compiled by `agda2forth`, and has no proved translation into the current Forth runtime. The existing compiler's linear/modal descriptor checks and the MALLP proof calculus must not be conflated. There is no Seely structure in this MALLP fragment.

### Lazy semantics remain open

PureCake's call-by-name to call-by-value translation makes delay and force explicit in each pass. This compiler currently does not do that: `makeDelay = id`, and ordinary variable references bypass the force path. Consequently, the `--lazy-evaluation` option is not backed by a semantics-preservation theorem and must not be described as a verified PureCake-style lazy compiler.

A linear one-shot thunk and a shared call-by-need thunk are different resource models. Shared memoization requires an explicit sharing discipline; it cannot be inferred from having a thunk constructor. The MALLP-only choice does not supply exponentials or shared duplication.

## End-to-end verification frontier

The work still required for a PureCake-strength result is substantial and specific:

1. Freeze an exhaustive supported source/Treeless grammar. Every unsupported constructor, primitive, literal, pattern shape, and axiom reference must fail closed.
2. Define a typed target IR whose instructions expose stack, heap, control-flow, and exception effects. The Agda operational semantics must be the specification used by the Haskell lowering, rather than a separately maintained mirror.
3. Prove source-to-IR lowering for every supported term constructor, including variables, literals, lambdas, curried application, closure environments, constructors, cases, branches, primitive calls, and error paths.
4. Prove the exact Forth serializer. Golden tests alone are evidence, not a proof that generated text parses as the certified instruction sequence.
5. Define a complete target state: data/return stacks, dictionary/code pointers, descriptor heap, metadata, execution tokens, error/throw state, and any observable I/O.
6. Prove each runtime ABI word refines its Agda state transition, with explicit footprints and exceptional atomicity.
7. Prove the generated program executes in the abstract machine with the same observations as the source semantics, and connect that machine with actual Gforth under an explicitly stated trusted computing base.

The existing WP model contains useful operation contracts and selected allocation/exception proofs. It does not yet provide the complete semantic bridge above. Do not infer a generic frame rule until concrete Forth word footprints have been established.

## Dictionary allocation and no-GC status

The current runtime is **not proved immune to dictionary exhaustion**. Runtime descriptor creation, metadata reservation, and closure-environment creation use monotone `HERE ... ALLOT` allocation. Consuming a linear handle changes ownership metadata; it does not generally return those cells to a reusable allocator. The abstract allocation model tracks cursors and preflights identity exhaustion; its `cellCount` advances the cursor without a proved arena-size bound. That does not establish memory reclamation or global storage safety in Gforth.

Compile-time `:noname` definitions are a separate issue from runtime object allocation. The runtime-growth concern is the dynamically repeated handle, metadata, and environment allocation. No general bounded slot pool, free-list, generation-tagged handle scheme, or reclamation simulation has yet been proved and connected to the Forth implementation.

Therefore the answer to “is this already a complete MALLP/PureCake compiler with no dictionary overflow or no-GC problems?” is **no**. Current CI can establish only the explicit tests and Agda files it actually runs. Even a green run would not prove unbounded memory safety, correct reclamation, or end-to-end compiler refinement.

## Verification decisions and known frontier

The intended proof API is WP over complete runtime state; generic frame reasoning should only be added after concrete footprints are proved. Existing paired obligations include identity exhaustion/failure atomicity and selected checked arithmetic/result-allocation transitions. The Gforth ABI tests include adversarial checks for selected handle liveness, arithmetic bounds, exception cleanup, and stack balance.

The selected saturated Nat/Bool regression tests cover addition, monus in both operand orders, multiplication, equality, less-than, and Boolean branches. The old `scalarAdd 20 5` generated-body counterexample was fixed for the tested path through direct lowering. This does not prove general higher-order application, closure capture, constructors, pattern matching, or modality preservation.

Still unspecified or unproved: exact complete source/Treeless semantics, complete Forth machine-state interpretation, executable code-pointer/dictionary semantics, every runtime word's footprint and exception behavior, and the treatment of divergence. Arbitrary hand-written Forth, raw memory access, unknown execution tokens, and unsupported Agda constructs remain outside any intended supported-fragment theorem; they must fail closed or be explicitly excluded.

## CakeML/PureCake and MALLP references

- CakeML complete compiler correctness: https://github.com/CakeML/cakeml/blob/master/compiler/proofs/compilerProofScript.sml
- CakeML source semantics: https://github.com/CakeML/cakeml/blob/master/semantics/semanticsScript.sml
- PureCake overall compiler correctness: https://github.com/CakeML/pure/blob/master/compiler/proofs/pure_compilerProofScript.sml
- PureLang-to-thunkLang simulation: https://github.com/CakeML/pure/blob/master/compiler/backend/passes/proofs/pure_to_thunk_1ProofScript.sml
- Thunk-language call-by-value semantics: https://github.com/CakeML/pure/blob/master/compiler/backend/languages/semantics/thunkLangScript.sml
- Olivier Laurent, polarized linear logic and MALLP: https://perso.ens-lyon.fr/olivier.laurent/fullpolgames.pdf
- Hamano and Scott, categorical semantics for polarized MALL: https://doi.org/10.1016/j.apal.2006.09.001
