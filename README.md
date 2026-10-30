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

| File | Responsibility | What currently verifies it |
| --- | --- | --- |
| `app/Main.hs` | Entry point inherited from Agda2Scheme | Exact upstream-source check in CI |
| `src/Agda/Compiler/Erase.hs` | Upstream erasure implementation | Exact upstream-source check in CI |
| `src/Main.hs` | Minimal Forth backend driver adapted for Agda 2.8 APIs | Exact driver-blob check in CI |
| `src/Agda/Compiler/ToForth.hs` | Converts Agda treeless terms into Forth forms and definitions | Haskell build and selected generated-program tests; no machine-checked proof that this Haskell code implements the Agda model |
| `data/FLib.fth` | Legacy Forth words, closure application, managed descriptors, checked ABI operations | Executed directly by Gforth tests; described by a separate manual Agda model |
| `formal/LinearModalSafety.agda` | Root model for ownership/descriptor invariants, weakest preconditions, stack effects, denotations, and selected compiler/runtime behavior; imports `VerifiedPLLCore` | Type-checks with Agda 2.8.0.2 and `--erasure`; it does not prove the concrete Haskell/Forth bridge |
| `formal/VerifiedPLLCore.agda` | Constructive finite-type search, bounded Markov substitute, conaturals, Hedberg, dyad arithmetic, and a small positive-tensor PLL fragment | Type-checks as an import of the root; its theorem scope remains intentionally limited |
| `formal/VerifiedCoreExecutable.agda` | Finite-observation projection and executable `pow2` interface imported by the proof core | Compiled to Forth and run in a small integration slice; proofs relate finite and infinite observations to the coinductive model, but this does not make arbitrary coinductive values executable |
| `test/VerifiedCoreSmoke.agda` and `test/gforth/verified-core-smoke.fs` | Generated conatural observations, dyadic scale examples, and an erased-argument call | Compiled by Agda2Forth and executed by Gforth |
| `test/CheckedScalar.agda` | Nat/Bool regression source | Compiled and executed by CI |
| `test/gforth/compiler-integration.fs` | Expected results for generated Nat/Bool programs | Executed by CI |
| `test/gforth/abi-smoke.fs` | Direct runtime ABI regressions | Executed by CI |
| `test/UnsupportedLiteral.agda` and `test/gforth/unsupported-boundary.fs` | Unsupported String literal and catchable error path | Compiled and executed by CI |
| `test/UnsupportedAxiom.agda` and `test/gforth/unsupported-axiom-boundary.fs` | Referenced Agda axiom fails closed through a catchable error | Compiled and executed by CI |
| `test/UnsupportedNatLiteral.agda` and `test/gforth/unsupported-nat-literal.fs` | Oversized Nat literal throws from generated Forth | Compiled and executed by CI |
| `test/gforth/abi-smoke.fs` | Raw Nat literal parsing, cell bounds, arithmetic overflow/domain errors, and catchable unreachable-branch boundary | Executed by CI |

### Source-provenance boundary

CI checks that:

- `app/Main.hs` and `src/Agda/Compiler/Erase.hs` are byte-identical to Agda2Scheme revision `24e02d9669f17d98ec67b8ad961cf9c3e602bf10` (the Agda 2.8 API update).
- `src/Main.hs` is the small Forth-specific Agda 2.8 driver adapter, pinned by its exact Git blob `be738fab5d26f009576e6b1a51237d4f7f2f1f9e`.
- `src/Agda/Compiler/ToForth.hs` is the only Forth-specific compiler translation module; the other shared Haskell source files must remain byte-identical to the Scheme upstream source.
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

## What `formal/LinearModalSafety.agda` establishes

The formal modules use Agda builtins rather than the standard library and declare no project-local axioms. The conatural model is a decreasing Boolean sequence. Formal checking uses Agda 2.8.0.2, `--without-K`, and the project options declared in the modules; `--safe` is intentionally not enabled. CI type-checks the root and its imports with:

```sh
agda --erasure --no-libraries -i formal formal/LinearModalSafety.agda
```

Its theorems concern explicitly defined Agda models. The module includes:

1. **Descriptor and ownership invariants.** An abstract state contains a descriptor heap, roots, and a fresh identity counter. The well-formedness predicate tracks identity uniqueness, registered references, live captures and payloads, ownership of linear resources, checked modes, and linear non-aliasing.
2. **Weakest-precondition contracts.** Commands produce a normal or exceptional outcome with state. WP uses separate normal and exceptional postconditions and includes sequencing and `CATCH` laws. This finite-outcome model is not a complete semantics for arbitrary divergence.
3. **Declarative stack effects.** `StackEffect` records allowed stack shapes for selected modeled operations. `stackTailFrame` proves a suffix-preservation property of that relation. It does not prove that the concrete Forth words obey the relation.
4. **Selected allocation, error, result, and closure contracts.** These are proofs about transitions defined in the Agda model, not automatic proofs about dictionary or metadata mutation in Gforth.
5. **Nat stack-program forward simulation and cell-bound contract.** The Nat fragment has a linear target-program representation: raw Nat-cell pushes followed by modeled `ABI-ADD-OR-LEGACY`, `ABI-MUL-OR-LEGACY`, and `ABI-MONUS-OR-LEGACY` instructions. An inductive execution relation specifies their abstract raw/raw stack behavior. `natStackExecAppend` proves sequencing, and `emissionTreeAgreesWithStackProgram` connects the tree-shaped emission mirror to the linear program. `natExpressionForwardSimulatesStackProgram` proves the expression denotation is placed above an arbitrary unchanged stack tail. Because Agda `Nat` is unbounded but a concrete Gforth cell is finite, `NatCellRepresentable` additionally requires every literal and intermediate result to fit a supplied bound. `natExpressionBoundedForwardSimulatesStackProgram` combines that witness with the stack simulation. This is an explicit proof precondition rather than an emitted proof witness; the decimal parser and raw arithmetic adapters dynamically enforce finite-cell bounds. Choosing the model bound equal to the concrete `ABI-MAX-NAT` and proving the emitter/runtime bridge remain separate obligations.
6. **Curried closure model.** Separate lemmas show that the modeled curried addition, monus, and multiplication closures preserve their corresponding arithmetic when applied.
7. **Nat/Bool and compiler-boundary models.** Selected arithmetic, comparisons, conditionals, and errors are modeled. The boundary model explicitly represents the fact that raw Nat/Bool outputs lack a runtime mode witness.
8. **Emitter/runtime inventory.** Section 5 models the supported primitive table, all current literal kinds, the major `TTerm` cases, Boolean constructor/case lowering, pattern-alternative support, and catchable failure branches from `ToForth.hs`. Section 6 models selected `FLib.fth` dispatch and mode joins; later sections model selected arithmetic, allocation, closure, and exceptional transitions. These tables are maintained by hand and are not generated from either implementation.

The historical theorem `historicalGeneratedScalarDoesNotRefineAddition` preserves the old fallback-body counterexample as historical context. It is not a claim that the current tested saturated-addition lowering still exhibits that old result.

### What remains unproved

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

The conatural proof model follows TypeTopology's generic-convergent-sequence representation: a Boolean sequence with the decreasingness proof that once an observation is false, all later observations remain false. It is connected to the backend-compilable observation interface in `formal/VerifiedCoreExecutable.agda` by `finiteObservationAgrees` and `infiniteObservationAgrees`; CI compiles examples of that interface to Forth and executes them with Gforth. This tests the finite ABI projection, not arbitrary functions over conaturals or whole-backend correctness.

`formal/VerifiedPLLCore.agda` re-expresses a deliberately bounded subset of the ideas in TypeTopology without importing its standard-library-scale dependency graph.

- **CompactTypes/searchability:** `isSigmaCompact` is the root-or-everywhere-true decision shape for Boolean predicates. `finiteSearchCompact` proves it for types supplied with a complete finite enumeration. This is not a claim that all of `Nat` is Σ-compact/LPO.
- **Conaturals:** `CoNat` encodes `ℕ∞` as a decreasing Boolean sequence, following `TypeTopology.GenericConvergentSequence`. It permits undecided finite-versus-infinite sequences constructively. The executable ABI exposes finite and infinite observation cases, with correspondence theorems; `coNatFiniteObservationCompact` applies only to predicates explicitly factored through one fixed observation, not arbitrary predicates on `ℕ∞`.
- **Hedberg:** `hedberg` proves that decidable equality makes identity types propositions, using no `K` postulate.
- **Markov substitute:** `finiteMarkov` and `coNatFiniteObservationMarkov` eliminate double-negated root existence only when constructive finite/enumerated compactness evidence is available. They are bounded principles, not unbounded Markov's principle for arbitrary predicates on `Nat`.
- **Dyads:** `Dyad` stores an integer numerator as a pair of naturals plus a denominator exponent, with addition, multiplication, cross-multiplication equivalence, and reflexivity of that equivalence. The encoding is not normalized; ring laws, order, normalization, and their proofs remain incomplete.
- **Polarized linear logic:** `PLLFragment` contains atomic identity and positive tensor introduction over ordered contexts. It is only a cut-free typing fragment, not Laurent's full calculus or proof-net normalization.

`hedbergReflect` is a small builtin-reflection macro: it builds a term applying the already type-checked `hedberg` theorem to an explicitly supplied decidable-equality procedure and two equality proofs. The kernel checks the resulting proof term. This is theorem instantiation, not general proof search, a reflection-based ring solver, or an implementation of dyad normalization. Rewrite support is enabled by the root module's declared Agda options; no claim of ring automation is made.

## Test and CI contract

CI checks source provenance, builds the Haskell compiler, runs the configured Cabal test command, installs/runs Gforth tests, type-checks the Agda specification, and compiles selected fixtures. The relevant commands are:

```sh
# Build compiler and execute Cabal's configured test command.
cabal build all
cabal test all

# Run direct runtime ABI regressions.
gforth -e 'include data/FLib.fth' -e 'include test/gforth/abi-smoke.fs'

# Type-check the Agda model.
agda --erasure --no-libraries -i formal formal/LinearModalSafety.agda

# Compile and execute generated Nat/Bool programs.
cabal run agda2forth -- --erasure -i test test/CheckedScalar.agda
gforth CheckedScalar.fth test/gforth/compiler-integration.fs

# Exercise oversized Nat literals, unsupported String literals, and axioms.
cabal run agda2forth -- -i test test/UnsupportedNatLiteral.agda
gforth UnsupportedNatLiteral.fth test/gforth/unsupported-nat-literal.fs
cabal run agda2forth -- -i test test/UnsupportedLiteral.agda
gforth UnsupportedLiteral.fth test/gforth/unsupported-boundary.fs
cabal run agda2forth -- -i test test/UnsupportedAxiom.agda
gforth UnsupportedAxiom.fth test/gforth/unsupported-axiom-boundary.fs

# Compile the first-order triples fixture (CI does not execute it).
cabal run agda2forth -- -i test test/TriplesFO.agda
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
| Laurent polarized logic | Minimal positive-tensor proof-rule fragment only; no full calculus, cut elimination, or Forth bridge |
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
