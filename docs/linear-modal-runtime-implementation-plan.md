# Closed Linear/Modal GForth ABI Implementation Plan

> Implements the design in linear-modal-runtime-abi.md.

Goal: enforce linear-resource and Girard-modal usage for compiler-generated checked code while preserving stock GForth semantics and isolating the legacy unchecked API.

Architecture: a checked ABI owns every admitted value identity and every operation that can affect its mode/ownership. The compiler emits a versioned checked module, explicit value constructors/modes, and only reviewed primitive wrappers. Existing GForth and FLib stack effects remain available as the legacy interface; they are not given a safety claim.

Tech Stack: Haskell/Agda backend, GForth runtime, F* specification interface, GitHub Actions.

## Global constraints

- No patch to the GForth interpreter.
- No mode inference by numeric threshold or pointer guess.
- No unknown/unmanaged handle may enter checked execution without explicit validation.
- THROW/CATCH must have specified state/ownership behavior; stack restoration is not state rollback.
- No unrestricted Forth safety claim.
- Every feature is test-first and every final claim is backed by a runnable test or a stated proof artifact.

## Review focus

- Aliased linear handles and use after consumption.
- Linear captures silently dropped or duplicated by closure/constructor paths.
- Unsafe modal promotion, including result wrappers and closure captures.
- Unknown numeric or unmanaged cells entering checked execution.
- THROW during allocation, capture, force, and primitive execution.

## Tasks

### 1. Freeze the semantic/runtime contract

Files: docs/linear-modal-runtime-abi.md, proof/LinearModalABI.fsti.

- [x] Specify state vocabulary, ABI operations, errors, compatibility, and proof obligations.
- [ ] Install/pin F* tooling and typecheck the interface file.
- [ ] Replace abstract predicates with a concrete state model before claiming executable verification.

### 2. Build failing runtime contract tests

Files: a dedicated GForth test script under test/, invoked by .github/workflows/haskell.yml.

- [ ] Linear handle cannot be reused through any ABI word after transfer/consumption.
- [ ] Linear captured values cannot be silently dropped or duplicated.
- [ ] Modal promotion rejects a closure with a linear, unregistered, or mode-unknown capture.
- [ ] Modal result wrapping rejects linear payloads.
- [ ] Failure injected during force/capture leaves resource accounting valid.
- [ ] Unknown/legacy raw cells are rejected by checked entry points.
- [ ] Existing supported FLib/GForth stack effects still pass compatibility tests.

Every negative test must be observed failing against the current implementation before its fix.

### 3. Make the checked ABI total

Files: data/FLib.fth and checked runtime tests.

- [ ] Introduce explicit constructors for every checked scalar, constructor, result, and closure.
- [ ] Remove MODE-UNANNOTATED from checked execution; reserve unknown only for the legacy import boundary.
- [ ] Give each checked word a stable error code and preserve invariants on error.
- [ ] Use a single authoritative handle/resource registry and explicit state transitions.

### 4. Establish compiler boundaries

Files: src/Agda/Compiler/ToForth.hs, src/Main.hs, compiler tests.

- [ ] Preserve or emit source-derived mode/type evidence before Treeless erasure loses it.
- [ ] Emit an ABI/version marker and checked constructors/application/force/primitive wrappers.
- [ ] Reject unsupported terms/primitives through compiler diagnostics, not generated Forth bye.
- [ ] For supported dynamic precondition violations, emit checked ABI calls that raise named THROW errors.
- [ ] Add golden fixtures proving every supported Treeless form emits only permitted checked words.

### 5. Specify every builtin and primitive

Files: docs/linear-modal-runtime-abi.md, primitive-contract table and compiler tests.

- [ ] Define stack/data effects, mode requirements, resource effects, memory footprint, and exception behavior.
- [ ] Route arithmetic and booleans through checked wrappers.
- [ ] Route constructors and closures through ownership-aware constructors.
- [ ] Reject unknown words from checked generated modules.

### 6. Prove and verify

- [ ] Typecheck the F* interface and implement concrete definitions/proofs.
- [ ] Prove invariant preservation for each primitive and ABI transition.
- [ ] State and prove the compiler/runtime correspondence theorem for the checked subset.
- [ ] Add explicit compatibility tests for the legacy FLib API on stock GForth.
- [ ] Run all Haskell/Agda/GForth tests and report the latest commit's CI conclusion.

## Current truthful status

The written design and contract interface are initial specification artifacts, not completed implementation or proof. Runtime negative tests, total ABI coverage, compiler instrumentation, F* checking/proofs, and refinement evidence remain open. Existing PR #6 smoke tests do not establish full linear/modal correctness.
