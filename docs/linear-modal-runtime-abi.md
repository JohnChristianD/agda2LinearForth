# Linear/modal GForth runtime ABI

Status: normative design target; not yet an implementation or proof of PR #6.
This document deliberately distinguishes the intended guarantee from behavior currently implemented and tested.

## Implementation snapshot

The current PR branch has the following incremental changes, but no end-to-end checked-code guarantee yet:

- Managed metadata now includes a scalar kind and `ABI-MAKE-SCALAR ( value mode -- handle )`; its mode parameter is a trusted compiler/loader input, not an inferred or proof-carrying mode.
- `assertModalValue` now rejects unregistered payloads and registered linear/unsafe payloads instead of unconditionally setting the result wrapper to modal. This validation covers scalar handles and the currently represented thunk/result cases; it is not a general recursive ADT/payload verifier.
- Managed ABI violations use named Gforth `exception` / `THROW` codes instead of `ABORT"` at the touched checked paths. The compiler maps unsupported target constructs to compilation failures, and unreachable Treeless code uses `ABI-ERROR-UNREACHABLE`.
- Regression steps were added for modal/linear scalar assertions, rejection codes and preservation of the wrapper mode on a caught failure, and unsupported literal compilation. The latest branch state has not been confirmed by a completed CI run; these tests were added through repository API commits and were not observed running in this session.
- The compiler still emits raw natural literals and legacy preamble/application/constructor forms for normal generated code. It does not emit ABI-versioned mode evidence and does not route all generated value operations through the checked API. Therefore this branch is still a runtime-hardening prototype, not the closed ABI specified below.

## 1. Goal and compatibility contract

The target is a dynamically enforced ABI for the Agda-to-Gforth compiler. It must account for the identity and usage of every value crossing the checked ABI, distinguish linear A from modal !A, reject invalid operations deterministically, and preserve its invariants on both success and failure.

“GForth-compatible” has two separate meanings:

1. Host compatibility: do not modify the semantics of Gforth words or require a patched interpreter. Generated checked output uses documented Gforth facilities already supported by the project's declared GForth baseline.
2. Legacy library compatibility: preserve the documented stack effects and successful behavior of the existing FLib.fth public entry points (pass, dethunk, toResult, deepDethunk, shallowPrint, and printType) where this can be done without weakening the checked ABI. New checked entry points are explicitly named and versioned. Compiler-generated checked code must not silently fall back to the legacy unchecked path.

This does not promise to make arbitrary, user-authored Forth safe. Forth programs outside the checked ABI keep normal GForth semantics and are outside the formal guarantee. Any old generated output accepted through the legacy API remains legacy/unverified unless recompiled to the checked ABI. Compatibility must be tested separately from safety.

## 2. Semantic distinction

A is a linear value: its resource identity must be consumed, transferred, or returned exactly as permitted by the language's operational rules. Merely rejecting a second use is not enough if a linear value can also be silently dropped.

!A is an exponential/modal value: the rules for duplication and weakening apply only after modal safety has been established. A modal flag alone is not evidence that the value's payload, closure code, captured environment, and relevant effects are safe to share.

Memory safety and linear/modal correctness are different properties. Linear ownership can support lifetime and aliasing guarantees, but does not prohibit every invalid address operation. Memory safety alone does not impose Girard's contraction/weakening restrictions. This ABI must state both sets of invariants where both are promised.

The ABI must not infer modes from numeric ranges such as MAXNUM, nor assume that a wrapper's mode determines its payload's mode. A value unknown to the checked ABI is rejected at entry; it is never silently classified as linear or modal.

## 3. Runtime value model

Every Agda-level value that enters checked execution has an explicit, unambiguous representation with at least:

- stable handle identity;
- representation kind: scalar, constructor/record, closure, or result;
- mode: linear or modal (no unannotated mode in checked execution);
- ownership/availability state;
- payload or closure execution token;
- captured environment, represented as managed value handles;
- any primitive/effect contract needed for safe execution.

Implementation detail may differ, but the observable invariant may not. A scalar must have the same tracked identity properties as a closure. Composite values must account for every contained resource recursively or by a formally specified shared modal reference. No pointer-vs-number heuristic is permitted.

An implementation may retain an internal “unknown” state for legacy interoperation, but that state is not a source-language type and cannot enter a checked operation without validation or explicit rejection.

### Required global invariants

I1 — Representation integrity. Each live managed handle identifies exactly one valid descriptor of the declared kind. A descriptor cannot be fabricated from an arbitrary cell, and stale/consumed handles do not become valid again by address reuse.

I2 — Resource uniqueness. Each live linear resource has exactly one logical owner: a handle, a closure environment, an in-flight operation, or an explicit result/error object. All transitions preserve this accounting.

I3 — Exact linear accounting. Every successful operation accounts for each linear input by consumption, transfer, or return as required by the semantic rule. No operation silently duplicates or loses linear ownership.

I4 — Modal validity. A value is modal only when its payload and any closure/environment/effects satisfy the modal-safety contract. Only modal values may use checked duplication or weakening operations.

I5 — Closed checked boundary. Every operation in checked code that creates, reads, duplicates, drops, captures, forces, applies, unwraps, moves, or mutates a managed value passes through the ABI. Raw Forth operations are available to legacy code but are not callable from the checked subset unless a reviewed primitive contract specifies them.

I6 — Error-state validity. Success and exception exits preserve I1–I5. Validation errors before commit leave the prior state unchanged. If arbitrary user effects have begun, the operation must follow its stated failure contract; the runtime must never pretend that CATCH rolled back dictionary writes, external effects, or metadata mutations.

## 4. ABI operation contracts

These are normative contracts, not a statement that PR #6 currently implements them.

| Operation | Preconditions | Successful postconditions | Rejection/failure |
|---|---|---|---|
| ABI-IMPORT | Explicitly trusted representation validator; no heuristic numeric/pointer guess | Fresh tracked identity and explicit mode justified by the caller's contract | Unknown/untrusted representation rejected before admission |
| ABI-MAKE-LINEAR | Payload validated; each contained linear resource transferred to the new owner | Fresh live linear handle; old owners invalidated if ownership was moved | On pre-commit failure, original ownership unchanged |
| ABI-MAKE-MODAL | Payload and all captured resources satisfy modal-safe contracts; no contained linear ownership is shared unsafely | Fresh modal handle whose duplication/weakening is justified | Reject if any payload/environment/effect is unknown or unsafe |
| ABI-PASS | Live function and argument; function's input/effect contract accepts the argument mode; all capture rules validated | Fresh closure; captured linear resources transferred exactly once; old linear handles consumed; mode derived by the specified typing rule | Reject before commit for invalid modes/aliases. After execution begins, follow explicit failure postcondition |
| ABI-FORCE | Live closure, validated code contract and environment; all captures accounted for | Result mode and resource ownership follow the closure contract; no hidden live linear capture is lost | Error path leaves every resource live, transferred, returned, or consumed exactly as specified |
| ABI-DUP | Handle is live and modal; payload supports modal sharing/copy semantics | Two usable modal references to a shared immutable/safely shared payload or two valid copies | Linear, consumed, unknown, or unsafe values rejected |
| ABI-DROP | Handle is live and modal | Modal reference released/dropped; any shared payload follows its lifetime policy | Linear or unknown value rejected |
| ABI-PROMOTE-MODAL | Closure code has a verified/trusted modal-safe contract; every captured value is modal; effects cannot consume linear resources | Same or fresh handle with modal capability, according to alias policy | Reject without changing mode if any premise is unknown/false |
| ABI-RESULT | Payload mode and result kind established | Fresh result wrapper preserving the payload's correct mode/ownership | Must not label an arbitrary payload modal solely by writing a wrapper flag |
| ABI-UNWRAP | Kind/mode contract matches the requested operation | Correct payload view and ownership transition | Representation/mode/consumption mismatch throws a defined ABI error |

The ABI must decide whether handles are linear tokens or identity-bearing references. Under the recommended token model, moving a linear resource invalidates the old token and creates a fresh token for the new owner. Modal sharing must not create mutable aliases to a payload unless the payload contract permits them.

## 5. Error boundary and compiler behavior

There are three different error classes:

1. Agda source/type error: the Agda checker rejects the program; no target program is emitted.
2. Compiler/lowering error: the compiler cannot translate a construct or cannot establish the checked-ABI contract. The compiler must return a diagnostic and non-success status; it must not emit a Forth word that prints a message and executes bye as a substitute for a compile error.
3. Dynamic ABI violation: a runtime predicate fails due to a malformed value, invalid alias/ownership transition, unsafe mode operation, unsupported boundary entry, or other stated dynamic precondition. The runtime raises a distinct named Gforth exception code with a stable diagnostic. CATCH may handle it; otherwise the normal GForth uncaught exception behavior applies.

A compiler-generated checked module must carry an explicit ABI/version marker and emit only operations in the checked subset. Missing metadata or ABI mismatch rejects module entry. Unsupported values/primitives are compile-time errors unless the source language deliberately defines a dynamic operation whose contract can be checked at run time.

Do not use ABORT" alone for machine-readable ABI errors: Gforth documents that exception handlers cannot reliably distinguish different ABORT" messages. Use reserved THROW codes and a central diagnostic mapping. CATCH restores data/return stack depths; it does not roll back arbitrary runtime-state mutations.

## 6. Primitive and builtin contract policy

Every word callable by checked code must be in a reviewed primitive table with:

- exact data-stack effect and any return-stack/locals effect;
- accepted runtime kinds and modes;
- linear resource input/output accounting;
- memory read/write footprint;
- whether it allocates, aliases, transfers, consumes or mutates;
- exception behavior and invariant-preserving failure transition;
- evidence source: formally verified, trusted audited primitive, or forbidden.

Initial policy for the current translation:

- Natural literals: emit an explicit ABI constructor with source-derived mode/type evidence; never emit an untracked numeric cell into checked execution.
- Arithmetic/comparison (+, -, *, /, mod, =, >=, <): route through ABI arithmetic/comparison words with exact scalar preconditions, payload validation and output construction. No direct primitive calls from checked terms.
- Boolean branches: use the compiler's recognized boolean representation or explicit tagged Bool values; never rely on treating arbitrary numeric cells as booleans.
- Constructor/record creation: route fields through checked captures and account for every contained linear field. A constructor is not safe merely because it allocates a cell array.
- Closures/applications/force: use explicit closure descriptors, captured-environment arrays, and the ABI's resource-transfer contracts.
- Gforth memory and execution words (@, !, +!, ALLOT, HERE, EXECUTE, dictionary/compilation words, raw pointer arithmetic, return-stack manipulation, arbitrary POSTPONE/immediate execution): forbidden from checked generated code except through a specific audited primitive wrapper with a sound contract.
- I/O or other effectful builtins: forbidden until their effect/exception contract is specified; then admitted one-by-one.

This is a policy table to implement and audit, not a claim that all words above are currently wrapped.

## 7. F*-style precondition/postcondition specification

The companion proof/LinearModalABI.fsti exposes abstract state predicates and contracts for import, pass, force, duplication, dropping, modal promotion, and result construction. A .fsti is a specification interface, not a proof of the GForth implementation. It becomes evidence only after it is typechecked with F* and connected to an implementation/model whose transitions are proved against these contracts.

A proof must establish each invariant inductively over every admitted ABI operation, including exception paths. A separate refinement/correspondence argument must show the actual GForth words implement those model transitions. A test suite is not that proof.

## 8. GForth compatibility boundary

- Do not patch Gforth or change the semantics of any Gforth word.
- Keep the checked ABI additive and namespaced; do not make arbitrary existing Forth source pass through a new checker.
- Preserve legacy entry-point stack effects and existing successful behavior where the ABI wrapper can do so.
- Make checked compilation opt-in/versioned until all generated forms and primitives are supported; after enabling it by default, old source still runs on stock GForth but regenerated code can correctly reject constructs outside the checked subset.
- No claim of safety applies to legacy unverified output or arbitrary user-defined Forth words which bypass the ABI.
- Add regression tests that run representative legacy generated outputs and direct Forth clients unchanged on the declared Gforth version, separately from negative tests for checked execution.

The word “backwards compatible” must always identify which guarantee is intended: host-language compatibility, FLib word/API compatibility, or observational compatibility of old generated Agda programs. They are not interchangeable.

## 9. Required verification obligations

The minimum proof/testing obligations are:

1. Descriptor integrity and no stale/forged handle admission.
2. Linear uniqueness, transfer, exact use, and no silent drop or duplicate.
3. Modal promotion premises, including payload, captures and effects.
4. Constructors and nested value ownership.
5. Arithmetic/boolean primitive preconditions and result modes.
6. Every closure/application/force path and partial-application stack convention.
7. Invalid-mode/alias/untracked-value diagnostics.
8. Exception safety for every transition point; no double-consumption or lost resources after THROW.
9. Compiler emits ABI marker and checked words for every supported Treeless form; unsupported forms fail compilation.
10. Compatibility tests for legacy public words and source programs on stock GForth.
11. F* specification typecheck; proof of abstract transition invariants; refinement/correspondence evidence for the GForth implementation.

Passing the current smoke test (including the addition result 30) is regression evidence only. It establishes none of the universal statements above.

## 10. References

- Henry G. Baker, “Linear Logic and Permutation Stacks—The Forth Shall Be First” (1994): https://dcreager.net/papers/Baker1994/
- nLab, “Linear logic” and “!-modality”: https://ncatlab.org/nlab/show/linear%2Blogic and https://ncatlab.org/nlab/show/%21-modality
- Jürgen Pfitzenmaier, “Type checking FORTH”, EuroForth 2005: https://www.complang.tuwien.ac.at/anton/euroforth2005/papers/proceedings.pdf
- M. Anton Ertl and Bernd Paysan, “Closures — the Forth way”, EuroForth 2018: https://www.complang.tuwien.ac.at/anton/euroforth/ef18/papers/proceedings.pdf
- Peter Knaggs, “A List Toolkit”, EuroForth 2018, same proceedings (non-refereed paper).
- M. Anton Ertl, “Memory Safety Without Tagging nor Static Type Checking”, EuroForth proceedings record: https://repositum.tuwien.at/handle/20.500.12708/193614
- GNU Gforth manual, exception handling: https://gforth.org/manual/Exception-Handling.html
- F* project and proof-oriented programming documentation: https://github.com/FStarLang/FStar
- Thomas Van Strydonck, Frank Piessens and Dominique Devriese, “Linear capabilities for fully abstract compilation of separation-logic-verified code”, JFP (2021): https://doi.org/10.1017/S0956796821000022
