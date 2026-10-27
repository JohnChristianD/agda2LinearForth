# agda2LinearForth

`agda2forth` translates selected Agda programs to GNU Gforth source. The repository contains an Agda formal model, a Haskell code generator, and a checked linear/modal runtime ABI. These parts are tested together, but they are **not yet connected by a whole-backend compiler-correctness proof**.

The distinction matters: an Agda theorem proves a property of the Agda model. A Gforth integration test checks a concrete generated program. Neither one alone proves that every generated Forth program preserves the source program's meaning.

## Pipeline and ownership

```text
Agda source
    |
    v
Agda 2.6.2.2 type checking and erasure
    |
    v
src/Agda/Compiler/ToForth.hs
    |
    v
generated .fth = data/FLib.fth + compiler preamble + generated definitions
    |
    v
GNU Gforth
```

| File | Responsibility | Verification status |
| --- | --- | --- |
| `app/Main.hs` | Executable entry point inherited from upstream Agda2Scheme | Pinned by CI |
| `src/Agda/Compiler/Erase.hs` | Erasure implementation inherited from upstream Agda2Scheme | Pinned by CI |
| `src/Main.hs` | Agda backend integration inherited from upstream Agda2Forth | Pinned by CI |
| `src/Agda/Compiler/ToForth.hs` | Maps the erased Agda terms to Forth words and definitions | Haskell build and selected generated-program tests; no Agda proof of this implementation |
| `data/FLib.fth` | Checked handle ABI, descriptor metadata, closure application, and compatibility arithmetic words | Direct Gforth tests plus a manually maintained Agda model |
| `formal/LinearModalSafety.agda` | Constructive model, stack effects, weakest-precondition contracts, and selected denotational results | Type-checks with `--safe`; does not inspect or extract the Haskell or Forth implementation |
| `test/CheckedScalar.agda` | Nat and Bool regression programs | Compiled and executed by CI |
| `test/gforth/abi-smoke.fs` | Direct tests of runtime ABI behavior | Executed by CI |
| `test/gforth/compiler-integration.fs` | Assertions against compiler-generated Nat and Bool values | Executed by CI |
| `test/UnsupportedLiteral.agda` | Unsupported String-literal regression | Compiled and forced under Gforth `CATCH` by CI |

### Source provenance

CI checks these exact upstream revisions:

- `app/Main.hs` and `src/Agda/Compiler/Erase.hs` must match Agda2Scheme revision `6b3d975e9274448c09b5939e637b6718c2cfb10c`.
- `src/Main.hs` must match Agda2Forth revision `e83f8cc735bf220f80b3655ce2158a23818910fe`.
- `src/Agda/Compiler/ToForth.hs` is the sole allowed Haskell-file exception.
- CI checks that `data/FLib.fth` has baseline blob `46ba6a5ab8c657c42c07169cf13c95a5533b41e0`.

A matching hash establishes source identity, not semantic equivalence between the source and the Agda model.

## Compiler lowering contract

The backend receives Agda's treeless terms and converts them to Forth forms. It does not currently compile through an Agda-defined target instruction language.

### Saturated primitives

For the exact argument shapes below, `fthDirectPrimitive` emits direct target operations rather than applying a primitive as though it were an ordinary closure.

| Agda treeless primitive | Generated Forth operation |
| --- | --- |
| `PAdd` | `ABI-ADD-OR-LEGACY` |
| `PSub` | `ABI-SUB-OR-LEGACY` |
| `PMul` | `ABI-MUL-OR-LEGACY` |
| `PQuot` | `ABI-QUOT-OR-LEGACY` |
| `PRem` | `ABI-REM-OR-LEGACY` |
| `PEqI` | `ABI-EQ-OR-LEGACY` |
| `PGeq` | `ABI-GEQ-OR-LEGACY` |
| `PLt` | `ABI-LT-OR-LEGACY` |
| `PIf` with three arguments | Inline `if ... else ... then` |

The builtin definitions for Nat addition and subtraction also have exact-arity paths. Saturated addition uses `ABI-ADD-OR-LEGACY`; saturated Nat subtraction uses `ABI-MONUS-OR-LEGACY`, which preserves zero-floor subtraction on its raw-cell path as well as on the checked path.

### Partial application and ordinary functions

Agda terms with ordinary function applications use the existing `pass` path. The compiler builds closures with the generated `makeTHUNK` protocol and the runtime stores closure metadata and captured arguments. This is not a separate word named `APPLY`; the runtime's application word is `pass`.

The backend maps under-applied builtin Nat addition to the curried `add` word and under-applied builtin Nat subtraction to `monus`. CI exercises those cases, partial multiplication, partial equality, partial less-than, and partial application of a user-defined function. These results cover those examples only. They do not establish the correctness of every higher-order function, closure, constructor, or pattern match.

### Literal and unsupported-operation boundary

`LitNat` is emitted as a raw Forth cell. The special Boolean constructors are emitted as raw Forth flags (`-1` for true and `0` for false). The current emitter does **not** wrap every source value in a checked scalar or Boolean handle.

The shared `fthError` path emits a diagnostic and calls `ABI-ERROR-COMPILED-UNSUPPORTED`. The runtime word throws `ABI-ERR-COMPILED-UNSUPPORTED`, which callers can catch. The String-literal integration test verifies that path end to end. The same literal fallback is present for Word64, Float, String, Char, QName, and Meta literals; only String currently has a dedicated integration test.

Do not assume that every unknown Agda builtin is rejected through `fthError`. A `TDef` that is not in the small direct/special-definition mappings can fall through to the generic name-and-`pass` route. An exhaustive allowlist for the supported source subset, enforced before emission, remains an open boundary task.

## Runtime ABI in `data/FLib.fth`

The runtime supports raw legacy cells and a managed representation for values that carry descriptor metadata.

- A managed descriptor records its identity, kind, mode, life state, code reference, captures, and optional result payload.
- The managed kinds include `THUNK`, `RESULT`, `SCALAR`, and `BOOLEAN`.
- Runtime modes are `MODE-UNANNOTATED`, `MODE-LINEAR`, and `MODE-MODAL`. Unannotated is an internal boundary state, not a third Agda source modality.
- Linear handles have one live identity and can be consumed. Modal handles may be reused only where the runtime checks permit it.
- `pass` checks managed closure and capture metadata. `makeTHUNK`, `dethunk`, result wrappers, and capture-retirement logic manage closure execution and ownership.
- The arithmetic adapters use a dual-entry policy. Two raw operands use the legacy word. Two registered scalar handles use the checked operation. Mixing raw and managed operands throws, and registered non-scalar operands are rejected.
- Checked operations validate operands and ranges before consuming linear inputs. Runtime tests include arithmetic-domain errors, overflow, identity exhaustion, null execution tokens, result wrapping/unwrapping, and cleanup of linear captures after exceptional closure exit.

The managed ABI is not automatically established for every compiler-generated value. Because many generated Nat and Bool values remain raw cells, this runtime alone does not prove preservation of Girard's linear and modal rules for arbitrary Agda source programs.

## What the Agda model proves

`formal/LinearModalSafety.agda` starts with `{-# OPTIONS --safe #-}` and contains no postulates. CI checks it with:

```sh
agda --safe --no-libraries -i formal formal/LinearModalSafety.agda
```

The module defines several related models. They are explicit specifications, not code extracted from `ToForth.hs` or `FLib.fth`.

1. **Descriptor and ownership model.** A machine state includes a descriptor heap, roots, and a fresh-identity counter. The well-formedness predicate records uniqueness, registered references, live captures and payloads, ownership of linear resources, and checked modes.
2. **Weakest-precondition semantics.** Commands return a state or throw an error with a state. The WP interface includes normal and exceptional postconditions, with laws for sequencing and `CATCH`. This finite outcome type does not model arbitrary divergence as success.
3. **Typed stack effects.** A declarative `StackEffect` relation describes accepted and produced stack shapes for the selected checked primitives and ABI operations. `stackTailFrame` preserves a suffix in this declarative relation. It is not a theorem that the corresponding Forth word has the same behavior.
4. **Failure and allocation contracts.** The model proves selected precondition, failure-atomicity, identity, result-payload, and closure-capture properties for its specified state transitions.
5. **Manual compiler-emission mirror.** The Nat fragment interpreter proves that its own literal, addition, multiplication, and monus AST translation preserves the Nat denotation. Separate lemmas prove application behavior for modeled curried arithmetic closures.
6. **Nat/Bool denotation and bridge models.** The closed scalar fragment models selected arithmetic, comparisons, conditional expressions, and errors. The bridge model explicitly records that raw compiler-emitted Nat and Bool cells have no runtime mode witness.

The historical `historicalGeneratedScalarDoesNotRefineAddition` theorem describes the old generated-body counterexample in the formal model. It is a historical witness, not a claim that the current saturated-addition path still returns the right operand.

### Proof boundary

The module does **not** prove any of the following:

- that Haskell's `ToForth.hs` implements the manually defined emission relation;
- that the concrete `data/FLib.fth` implementation refines every modeled state transition;
- that the generated output of arbitrary Agda programs preserves source denotation;
- that all source linear/modal values acquire managed runtime evidence;
- that arbitrary Forth words preserve stack shape or ownership;
- that the compiler handles every Agda builtin, literal, datatype, or higher-order term.

A whole-backend result needs an explicit supported source subset, a target instruction or emission relation that both the proof and implementation follow, and a forward-simulation argument connected to the emitted program and runtime behavior.

## Numeric support

The tested numeric core is Nat arithmetic and comparison, with Bool results and selected partial applications. The project does not implement Float arithmetic, a Gforth floating-point-stack translation, or a fixed-point format.

Agda has a builtin Float type and primitive operations, while Gforth maintains a separate floating-point stack. This repository's target stack-effect model does not include that second stack. See the [Agda 2.6.2 built-ins reference](https://agda.readthedocs.io/en/v2.6.2/language/built-ins.html#floats), the [Gforth stack model](https://gforth.org/manual/Stack-Manipulation.html), and [Gforth floating-point operations](https://gforth.org/manual/Floating-Point.html).

For future fractional arithmetic, a fixed-point representation on the data stack is a plausible fit for the single-data-stack model. Q32.32 with native Forth integer operations such as `*/` is a candidate, not a current feature or an agreed numeric specification. Before adding it, define the cell-width assumption, scale, range, rounding rule, multiplication and division semantics, overflow behavior, and the Agda-to-Forth correspondence. The compiler, runtime, tests, and proof model must all adopt the same contract.

## Build and test

CI currently runs with GHC 9.0.2 and Agda 2.6.2.2, installs Gforth, and executes the following checks:

```sh
# Build and run Cabal's configured test command.
cabal build all
cabal test all

# Check the runtime ABI.
gforth -e 'include data/FLib.fth' -e 'include test/gforth/abi-smoke.fs'

# Check the Agda model.
agda --safe --no-libraries -i formal formal/LinearModalSafety.agda

# Compile and execute the Nat/Bool integration fixture.
cabal run agda2forth -- -i test test/CheckedScalar.agda
gforth CheckedScalar.fth test/gforth/compiler-integration.fs

# Compile the unsupported String-literal fixture and run its CATCH test.
cabal run agda2forth -- -i test test/UnsupportedLiteral.agda
gforth UnsupportedLiteral.fth test/gforth/unsupported-boundary.fs

# Compile the first-order triples fixture.
cabal run agda2forth -- -i test test/TriplesFO.agda
```

`cabal test all` currently reports no package tests to run. The meaningful executable regressions are the explicit Gforth tests and compiler-generated integration fixture.

The 23 generated Nat/Bool witnesses cover the original saturated-result cases plus a curried builtin addition, `_+_ 5`, partial application of a user function, partial monus in both operand orders, partial multiplication, and partial equality and less-than. The ABI smoke suite separately exercises raw and checked arithmetic, mode propagation, linear consumption and alias rejection, mixed representations, division and remainder by zero, overflow, identity exhaustion, null execution tokens, result ownership, exceptional closure cleanup, and final stack balance. The first-order triples fixture is compiled as a smoke test; CI does not claim to execute it.

## Design status

| Area | Status |
| --- | --- |
| Upstream erasure and entry-point provenance | Checked by CI |
| Selected saturated Nat/Bool lowering | Generated-program regressions pass in CI |
| Selected partial-application paths | Generated-program regressions pass in CI |
| Checked runtime ABI behavior | Direct Gforth tests pass in CI |
| Agda formal model | Type-checks with `--safe`, no postulates |
| Unsupported String-literal failure | Catchable runtime boundary tested in CI |
| Exhaustive allowlist for all source terms | Not implemented |
| Haskell-to-Agda compiler-emission correspondence | Not proved |
| Concrete Gforth-to-Agda runtime refinement | Not proved |
| Whole-backend compiler correctness | Not proved |
| Float or fixed-point arithmetic | Not implemented |
