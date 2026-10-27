# agda2LinearForth

`agda2forth` translates a selected subset of Agda programs to GNU Gforth source. The repository has three distinct artifacts: a Haskell backend, a Forth runtime/ABI, and a manually maintained Agda specification. They are connected by CI checks and selected executable tests, **not by a whole-backend compiler-correctness proof**.

This README documents the implementation that exists today. Proposed target IRs, a universal `APPLY` word, statically erased runtime tags, Float replacements, and future verification milestones are not described as completed features.

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
| `src/Main.hs` | Agda backend integration inherited from Agda2Forth | Exact upstream-source check in CI |
| `src/Agda/Compiler/ToForth.hs` | Converts Agda treeless terms into Forth forms and definitions | Haskell build and selected generated-program tests; no machine-checked proof that this Haskell code implements the Agda model |
| `data/FLib.fth` | Legacy Forth words, closure application, managed descriptors, checked ABI operations | Executed directly by Gforth tests; described by a separate manual Agda model |
| `formal/LinearModalSafety.agda` | Ownership/descriptor invariants, weakest-precondition model, selected stack effects, denotations, and model-level compiler/runtime mirrors | Type-checks with `--safe`; it neither extracts nor verifies the Haskell or Forth implementation |
| `test/CheckedScalar.agda` | Nat/Bool regression source | Compiled and executed by CI |
| `test/gforth/compiler-integration.fs` | Expected results for generated Nat/Bool programs | Executed by CI |
| `test/gforth/abi-smoke.fs` | Direct runtime ABI regressions | Executed by CI |
| `test/UnsupportedLiteral.agda` and `test/gforth/unsupported-boundary.fs` | Unsupported String literal and catchable error path | Compiled and executed by CI |

### Source-provenance boundary

CI checks that:

- `app/Main.hs` and `src/Agda/Compiler/Erase.hs` match Agda2Scheme revision `6b3d975e9274448c09b5939e637b6718c2cfb10c`.
- `src/Main.hs` matches Agda2Forth revision `e83f8cc735bf220f80b3655ce2158a23818910fe`.
- `src/Agda/Compiler/ToForth.hs` is the sole Haskell source file permitted to differ from its pinned upstream boundary.
- `data/FLib.fth` matches the CI-pinned baseline blob `46ba6a5ab8c657c42c07169cf13c95a5533b41e0`.

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

- Nat literals are emitted as raw Forth cells.
- The special Boolean constructors are emitted as raw flags: `-1` for true and `0` for false.
- Not every source value is wrapped in a managed scalar/Boolean descriptor. Therefore a compiled value is not guaranteed to carry a runtime witness for its source modality.
- The shared unsupported-output path emits a diagnostic and invokes `ABI-ERROR-COMPILED-UNSUPPORTED`. That runtime word raises a catchable `THROW`; the String-literal fixture checks the error code, verifies the diagnostic, rejects a generated `BYE`, and checks stack balance.
- The same literal fallback exists for Word64, Float, String, Char, QName, and Meta literals. Only String currently has a dedicated end-to-end unsupported-literal test.
- Do not assume every unknown builtin fails closed. A definition not recognized by the direct/special mapping can fall through to generic name/application handling. An exhaustive checked allowlist for an explicitly supported source subset is still missing.

## Runtime ABI: `data/FLib.fth`

The runtime retains compatibility with raw legacy cells and also supports values represented by managed descriptors. These are distinct paths, not a guarantee that every generated source value uses the checked representation.

A managed descriptor tracks identity, kind, mode, life state, execution token, captured values, and optional result payload. Managed kinds include `THUNK`, `RESULT`, `SCALAR`, and `BOOLEAN`. Runtime modes include `MODE-UNANNOTATED`, `MODE-LINEAR`, and `MODE-MODAL`; unannotated is a runtime boundary state, not a third source modality.

The existing `pass` word handles closure application and checks metadata for managed closures/captures. `makeTHUNK`, `dethunk`, result wrappers, and capture-retirement code support closure execution and ownership transitions. Arithmetic adapters dispatch as follows:

- Two raw operands use the legacy operation.
- Two registered scalar handles use the checked operation.
- Mixing raw and managed operands throws an error.
- Registered operands of an incompatible managed kind are rejected.

The runtime tests exercise checked operand/range validation, linear consumption and alias rejection, mode behavior, Nat monus, mixed representations, arithmetic-domain errors, overflow, identity exhaustion and failure atomicity, null execution tokens, result wrapping/unwrapping, and retirement of linear captures when a closure exits exceptionally.

These safeguards apply when calls enter the corresponding checked ABI operations. Raw generated values and generic emitted Forth do not automatically inherit those guarantees. No claim is made that arbitrary Forth is sandboxed or that Girard's structural rules are preserved for every compiled Agda program.

## What `formal/LinearModalSafety.agda` establishes

The module begins with `{-# OPTIONS --safe #-}`, imports Agda builtins rather than the standard library, and contains no postulates. CI type-checks it with:

```sh
agda --safe --no-libraries -i formal formal/LinearModalSafety.agda
```

Its theorems concern explicitly defined Agda models. The module includes:

1. **Descriptor and ownership invariants.** An abstract state contains a descriptor heap, roots, and a fresh identity counter. The well-formedness predicate tracks identity uniqueness, registered references, live captures and payloads, ownership of linear resources, checked modes, and linear non-aliasing.
2. **Weakest-precondition contracts.** Commands produce a normal or exceptional outcome with state. WP uses separate normal and exceptional postconditions and includes sequencing and `CATCH` laws. This finite-outcome model is not a complete semantics for arbitrary divergence.
3. **Declarative stack effects.** `StackEffect` records allowed stack shapes for selected modeled operations. `stackTailFrame` proves a suffix-preservation property of that relation. It does not prove that the concrete Forth words obey the relation.
4. **Selected allocation, error, result, and closure contracts.** These are proofs about transitions defined in the Agda model, not automatic proofs about dictionary or metadata mutation in Gforth.
5. **A manual Nat-emission interpreter.** Its theorem proves meaning preservation for its own modeled literal/add/multiply/monus fragment. Separate lemmas show that the modeled curried addition, monus, and multiplication closures behave correctly when applied.
6. **Nat/Bool and compiler-boundary models.** Selected arithmetic, comparisons, conditionals, and errors are modeled. The boundary model explicitly represents the fact that raw Nat/Bool outputs lack a runtime mode witness.

The historical theorem `historicalGeneratedScalarDoesNotRefineAddition` preserves the old fallback-body counterexample as historical context. It is not a claim that the current tested saturated-addition lowering still exhibits that old result.

### What remains unproved

The current Agda file does **not** prove:

- that Haskell's `ToForth.hs` implements the modeled emission relation;
- that the real `data/FLib.fth` implementation refines every modeled state transition;
- that arbitrary compiled Agda programs preserve source denotation;
- that every source linear/modal value gains a checked runtime descriptor;
- that arbitrary emitted Forth has safe stack effects or ownership behavior;
- that all Agda builtins, literals, data types, higher-order terms, and pattern matches are supported.

A whole-backend proof needs an explicit supported source subset, a target instruction/emission relation shared by the specification and implementation, and a forward simulation that connects source meaning to generated Forth and concrete runtime state. A small Agda model and green regression tests are useful evidence, but they are not a substitute for that bridge.

## Test and CI contract

CI checks source provenance, builds the Haskell compiler, runs the configured Cabal test command, installs/runs Gforth tests, type-checks the Agda specification, and compiles selected fixtures. The relevant commands are:

```sh
# Build compiler and execute Cabal's configured test command.
cabal build all
cabal test all

# Run direct runtime ABI regressions.
gforth -e 'include data/FLib.fth' -e 'include test/gforth/abi-smoke.fs'

# Type-check the Agda model.
agda --safe --no-libraries -i formal formal/LinearModalSafety.agda

# Compile and execute generated Nat/Bool programs.
cabal run agda2forth -- -i test test/CheckedScalar.agda
gforth CheckedScalar.fth test/gforth/compiler-integration.fs

# Exercise the unsupported String-literal boundary.
cabal run agda2forth -- -i test test/UnsupportedLiteral.agda
gforth UnsupportedLiteral.fth test/gforth/unsupported-boundary.fs

# Compile the first-order triples fixture (CI does not execute it).
cabal run agda2forth -- -i test test/TriplesFO.agda
```

At present, `cabal test all` reports that there are no package test suites to run. The meaningful executable regression coverage is in the explicit Gforth fixtures and generated-program integration test.

The 23 compiler-generated Nat/Bool witnesses cover saturated arithmetic/comparison/conditional cases and selected partial applications: curried builtin addition, `_+_ 5`, a partially applied user function, monus with either fixed operand, multiplication, equality, and less-than. The separate ABI suite tests checked and legacy paths, ownership/mode rejection, arithmetic boundaries, identity-allocation atomicity, result operations, exceptional closure cleanup, and final data-stack balance. The TriplesFO fixture is compiled as a smoke test only.

A successful CI run means these explicit commands passed at that commit. It is not a universal proof about the entire source language or arbitrary Forth programs.

## Numeric scope and possible extension

The currently tested arithmetic core is Nat operations and comparisons with Bool results. Float arithmetic, translation to Gforth's floating-point stack, and fixed-point arithmetic are not implemented.

Agda exposes a builtin Float type, while Gforth has separate data and floating-point stacks. The current target stack model represents neither a second stack nor a complete Float semantics. Relevant primary references are the [Agda 2.6.2 built-ins documentation](https://agda.readthedocs.io/en/v2.6.2/language/built-ins.html#floats), [Gforth stack manipulation](https://gforth.org/manual/Stack-Manipulation.html), and [Gforth floating-point words](https://gforth.org/manual/Floating-Point.html).

A fixed-point value stored in data-stack cells may be a reasonable future extension; Q32.32 is only a candidate. No choice is implemented or finalized. Before claiming a fixed-point format, specify the machine-cell width and signed representation, scale/range, rounding semantics, multiplication/division behavior, overflow conditions, and a shared Agda/Forth contract. Do not claim native-integer performance or algebraic laws until the concrete representation and its correspondence have been implemented and tested.

## Status at a glance

| Area | Evidence-backed status |
| --- | --- |
| Upstream source identity | Checked by CI hashes |
| Selected saturated Nat/Bool lowering | Generated-program tests |
| Selected partial-application cases | Generated-program tests using existing `pass` path |
| Checked managed ABI | Direct Gforth tests for enumerated cases |
| Agda model | Type-checks under `--safe`; contains no postulates |
| Unsupported String literal | Catchable error tested end to end |
| Exhaustive allowlist for supported source subset | Not implemented |
| Haskell-emitter correspondence to Agda model | Not proved |
| Concrete runtime refinement of Agda model | Not proved |
| Whole-backend compiler correctness | Not proved |
| General linear/modal preservation for compiled Agda | Not proved |
| Float and fixed-point arithmetic | Not implemented |

## References and further reading

These sources are background for the model and target language, not claims that the project has inherited their theorems:

- [GNU Gforth manual](https://gforth.org/manual/) for the concrete target's stack, execution-token, and exception behavior.
- [Agda documentation](https://agda.readthedocs.io/en/v2.6.2/) for the language and the `--safe` type-checking configuration.
- Henry G. Baker, [Linear Logic and Permutation Stacks: The Forth Shall Be First](https://dcreager.net/papers/Baker1994/), for the connection between linear resource use and stack permutations.
- [XDS-Agda](https://pdmosses.github.io/xds-agda/) and its [source repository](https://github.com/pdmosses/xds-agda/) for an example of organizing a language semantics in Agda.
- [Haskell Wikibooks: Denotational semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics) for compositional denotational models.
- [UPenn Software Foundations: Separation Logic Foundations](https://softwarefoundations.cis.upenn.edu/current/current/slf-current/) for heap predicates and frame reasoning. Such reasoning applies to a concrete Forth word only after its footprint and behavior have been established.
- [Stanford Encyclopedia of Philosophy: Constructive Mathematics](https://plato.stanford.edu/entries/mathematics-constructive/) for the constructive-mathematics context.
- [nLab: Linear logic](https://ncatlab.org/nlab/show/linear%2Blogic) and [!-modality](https://ncatlab.org/nlab/show/%21-modality) for the intended logical interpretation of modal structural rules.
- M. Anton Ertl and Bernd Paysan, [Closures: The Forth Way](https://www.complang.tuwien.ac.at/papers/ertl%26paysan.pdf), EuroForth 2018, for Forth closure/environment design.
