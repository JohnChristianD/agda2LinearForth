# agda2LinearForth — linear/modal runtime ABI specification and verification status

`agda2forth` compiles Agda code for GNU Gforth. This document defines the intended checked subset, its error boundary, and the current proof/implementation gaps.


> **PR #6 guarantee status: NOT COMPLETE.** The Agda modules are specifications and proof ingredients, not a refinement proof for the generated Forth runtime. Generated literals and multiple execution paths still bypass the checked descriptors; caller-supplied execution-token declarations remain trusted assertions. A green CI run would validate only enumerated tests, not establish universal linear/modal memory safety.

## Upstream synchronization boundary

This repository ports the compiler backend from `jespercockx/agda2scheme` to GNU Gforth. Keep the shared frontend/erasure interface compatible with upstream: `src/Agda/Compiler/Erase.hs` is currently byte-identical to upstream. `src/Main.hs` and `src/Agda/Compiler/ToForth.hs` are intentionally target-specific: do not replace the Forth backend with Scheme-emitting code. The Cabal package name, executable name, generated file suffix, runtime assets, and GForth checks necessarily differ. Keep Agda's minimum supported version and shared dependency bounds aligned, and retain PR-triggered CI rather than copying upstream's push-only workflow verbatim.

## Goal and scope

The target is a dynamically enforced ABI for the subset of Agda programs this backend emits. Arbitrary Forth is outside the safety claim. The generated program must still be valid for GNU Gforth, and the legacy Forth words remain available with their existing stack effects; legacy callers do not automatically receive the checked-ABI guarantee. The compatibility target is the shared Agda frontend and erasure pipeline; the Forth runtime, Scheme backend, and formal proof artifacts are necessarily target-specific.

“End-to-end” means all values and all operations reachable from a generated program use the checked representation. It does not mean trying to make arbitrary interactive GForth safe.

This document deliberately distinguishes a specification, an implementation, and a refinement proof. The Agda models in `formal/LinearModalABI.agda`, `formal/LinearModalStackEffects.agda`, and `formal/LinearModalExamples.agda` are constructive and import only Agda's bundled `Agda.Builtin.Nat` and `Agda.Builtin.Equality` modules. They use no Agda standard library, no postulates and no F*. The stack-effects module gives typed normal stack-shape rules for the enumerated closed primitive subset, including numeric operations, scalar/thunk/result operations, application/force, conditional, constructor/matcher schemas and linear/modal printing. The examples provide concrete witnesses for linear, modal and mixed-mode arithmetic plus checked thunk construction and promotion. Exception transitions are specified separately from normal-return stack effects. These are specifications and proof ingredients, not yet proofs that the current Forth words implement them.

## Source modes and runtime values

The source has two relevant modalities:

- `linear`: one logical owner; the resource must be used exactly once, including transfer or return. Preventing a second use alone is insufficient because silently dropping it also violates linearity.
- `modal`: sharing and discarding are permitted only after modal safety has been established.

The runtime's `unannotated` mode is a boundary/error state, not a third source-language type. A live unannotated value is forbidden inside a fully checked machine state. Unrestricted legacy words can still handle their historical representations outside that state.

Each checked descriptor records a monotone logical identity (META-ID) distinct from its address, kind (scalar/thunk/result), runtime mode, lifecycle (live/consumed), code address, closed-code classification, capture identities and optional payload identity. Numeric payloads are not handle identities. The checked ABI must never decide “number versus pointer” using `MAXNUM` or any other magnitude heuristic.

The Agda model defines these well-formedness conditions:

1. Descriptor identities are unique.
2. Stack roots are registered and live.
3. Every descriptor reference names a registered descriptor.
4. Captures of a live closure refer to live descriptors.
5. Every live linear descriptor has an active owner reference.
6. No live linear descriptor is referenced more than once by roots, active closure captures, and live result payloads. Conditions 5 and 6 together mean exactly one active reference.
7. No live descriptor is unannotated.
8. All registered identities are strictly below the next allocation identity, and `nextIsFresh` constructively proves that the next identity cannot already occur.

A linear result wrapper owns a fresh moved payload handle. Packing transfers the resource to a fresh live descriptor and consumes the old handle; the wrapper metadata points to the fresh descriptor. Unwrapping consumes the wrapper and transfers that live payload handle back out. A modal wrapper may share a live modal payload. The heap model counts live result payload references as active references and requires the payload to remain live with a mode matching the wrapper.

## Closed code and promotion

A raw execution token is not evidence of linear or modal safety. An integrator-written `declareLinearSafeXT` / `declareModalSafeXT` declaration is a trusted assertion, not a derivation.

The formal model therefore separates `codeAddress` from `codeClass`. Modal promotion requires a constructive `ModalCode (codeClass d)` witness and proof that every captured value is live and modal. There is deliberately no modal-safety constructor for opaque user Forth code. The current implementation does not yet establish a verified correspondence from a generated XT to such a witness; this is an explicit remaining proof obligation.

For linear code, an analogous derivation must state stack/resource effects and prove that every linear input is consumed, transferred or returned exactly once. A code-class label alone cannot prove this.

## Operations and contracts

The checked ABI is intended to admit only the following families. The preconditions and exceptional postconditions are part of each operation's contract; a failed precondition must produce a named error, not silently fall through to the legacy path.

| Operation family | Preconditions | Required normal postcondition | Required exceptional postcondition |
|---|---|---|---|
| Make scalar | Payload is a supported scalar; mode comes from a compiler-produced derivation or explicit trusted boundary | Fresh unique descriptor; mode is linear or modal; payload is not mistaken for an address | No visible partial descriptor; machine remains well formed |
| Make thunk / closure | Code class is in the closed generated subset; all captures are registered and live | Fresh descriptor and environment; linear captures are moved, modal captures remain shareable | No partial ownership transfer; machine remains well formed |
| Apply / `pass` | Function is a live checked thunk; argument is checked; mode combination is defined | New closure owns transferred linear inputs; consumed aliases fail later; resulting mode follows the derivation | No alias becomes live twice; failed transfer leaves a well-formed state |
| Force / `dethunk` | Live checked thunk; code contract and capture environment valid | Linear thunk consumed; every linear capture consumed, returned, or moved exactly once; modal thunk reused only if modal-safe | Either restore the pre-state or commit a well-formed consumed/returned state; never leave orphaned live linear captures |
| Pack result | Payload is registered/live and annotated | Linear payload ownership moves to a fresh linear wrapper; modal payload remains shareable only if modal-safe | Wrapper and payload ownership remain consistent |
| Unwrap result | Wrapper is live, well-formed and annotated | Linear wrapper consumed and its contained live payload handle is transferred out; modal wrapper may return the shareable modal payload | State remains well formed and no stale alias is revived |
| Promote modal | Live closure; derivable modal-safe code witness; every capture live and modal | Closure mode becomes modal | No mode change if validation fails |
| Arithmetic / comparisons | Checked scalar operands; valid operation domain | Linear operands are accounted for once; modal operands may be reused; result mode is derived, never guessed | Division/remainder domain errors are catchable and leave a well-formed state |
| Conditional | Checked boolean condition; both branches belong to the closed ABI | Exactly the selected branch executes; unselected branch resources are not spuriously consumed | State remains well formed |
| Constructor / pattern match | Constructor tag and field layout are known; fields have checked modes | Linear fields move to selected branch bindings; modal fields may be reused; wildcard matching cannot silently drop linear fields | Malformed tag/layout raises a named error without unsafe memory access |
| Print/debug | Checked value with an explicit observation policy; the checked printer must not force-consume a linear closure by accident | Either borrow a modal value or explicitly consume/account for a linear value | Error leaves the machine well formed |
| Throw/catch | A named ABI error and a state satisfying the operation's exceptional postcondition | Catch handles the code/state pair or rethrows it | Gforth `CATCH` restores its specified stacks, but it does not roll back dictionary or metadata writes automatically; those require explicit cleanup/transaction discipline |

### Compiler-emitted vocabulary to account for

The current backend emits the following application/runtime forms; each needs an ABI rule or must be rejected before output:

- Applications: `pass` (generated repeatedly by `fthApps`).
- Closures/forcing: `makeTHUNK`, `dethunk`, `deepdethunk`, `foldThunks`, `pushArrayN`.
- Natural-number wrappers: `add`, `sub`, `mul`, `quot`, `rem`, `iff`, `eq`, `geq`, `lt`, `monus`.
- Constructor/matcher machinery: constructor tags generated through `fthDefineType`/`fthConstructor`, `obj=`, `makeWILDCARD`, `pointer` and the generated field environment.
- Literals: `LitNat` currently emits a bare numeric cell; boolean constructors currently emit `-1` and `0`. Those must become checked representations in generated code. `Word64`, float, string, character, QName and meta literals are not implemented by this backend and must produce explicit unsupported-operation boundaries.
- Locals: `fthLocal` emits Gforth locals `{ ... }`. Local binding must not create a way to alias a linear handle outside the ABI.
- `TPrim` currently maps only add/sub/mul/quot/rem/if/integer equality/geq/lt; other primitives take the `fthError` path. Supported primitive coverage must be explicit rather than inferred from a successful build.

These names describe current emitted forms, not a claim that all are already safe. The production compiler should emit a checked subset and use stable error boundaries for unsupported operations. Legacy Forth words remain for compatibility; they are outside the checked generated-program guarantee until routed through the ABI.

## Gforth compatibility boundary

The target is GNU Gforth specifically. The ABI may use Gforth-supported locals, execution tokens, `PERFORM`, and Gforth exception facilities. The compatibility requirement is:

1. Existing source programs that the backend currently supports continue to generate valid Gforth.
2. Legacy public runtime words retain their documented stack effects and representation conventions.
3. New checked output uses namespaced ABI entry points and does not silently route an invalid checked value into a legacy representation.
4. Raw memory operations, arbitrary `EXECUTE`, dictionary mutation/compilation, and caller-created XT-safety assertions are excluded from the checked subset.
5. The checked guarantee covers only code emitted/loaded through the defined boundary. It does not claim to secure arbitrary interactive Forth.
6. Any emitted unsupported/invalid operation raises a documented error instead of emitting a silent no-op or exiting the entire interpreter with `BYE`.

The runtime currently uses Gforth's `exception` to name errors and `THROW` to report them. Unsupported compiler output is emitted as a diagnostic followed by the catchable `ABI-ERROR-COMPILED-UNSUPPORTED` word, rather than using `BYE`. In `dethunk`, execution now goes through `CATCH`; on a linear closure failure, the code retires live linear descendants of its captured environment before rethrowing the original error. The Gforth smoke test checks this failure path. This cleanup relies on the closed ABI's acyclic new-descriptor/reference-order discipline, which remains a runtime invariant to enforce and prove. `CATCH` does not automatically roll back arbitrary dictionary or metadata mutations.

## Hoare and separation-logic interpretation

The Agda state model defines:

- A disjoint-identity heap split (`Sep`) for separating conjunction.
- Total Hoare triples with distinct normal and exceptional postconditions.
- A constructive preservation proof for the identity command.
- A constructive catch-preservation lemma: if an operation and each handler preserve a predicate in both normal and exceptional cases, their composition preserves it.
- Evidence-gated copy/discard operations; no evidence term exists for linear or unannotated handles.
- A modal-promotion precondition that includes a registered descriptor, thunk/live checks, all-modal captures, and a closed-code witness.

These are reusable proof ingredients, not the completed implementation theorem. The missing central theorem is that each actual ABI word refines its Agda command contract and preserves `WellFormed`. It must be proved operation by operation; a typechecked model alone is not that theorem.

## Verification stages and status

- [x] Define a stdlib-free Agda state/invariant model, copy/drop rules, and a strict identity-decrease condition for references.
- [x] Define separating conjunction and normal/exceptional Hoare contracts.
- [x] Define structured runtime-error outcomes and a catch-composition preservation lemma.
- [x] Define typed stack-shape effects and example witnesses for the enumerated closed primitive subset.
- [ ] Confirm all three Agda modules type-check in CI using Agda itself with `--no-libraries`.
- [ ] Give each emitted primitive a complete stack/mode/resource signature and derive permitted compositions.
- [ ] Route every supported generated literal, constructor, application, force, conditional and primitive through the checked ABI.
- [ ] Replace caller-asserted XT safety with compiler/loader-generated code-class derivations tied to the closed core IR.
- [ ] Prove actual Forth word implementations preserve `WellFormed`, including every exceptional path.
- [ ] Prove compiler-to-core and core-to-Gforth correspondence for the supported subset.
- [x] Add a compiler-output regression fixture requiring unsupported literals to emit a catchable ABI error instead of BYE.
- [ ] Run positive and negative Gforth tests, plus compatibility regression tests for legacy words.

Until those last obligations pass, the only justified claim is runtime hardening for explicitly managed handles—not complete end-to-end linear/modal safety.

## Research anchors

- Henry G. Baker, [Linear Logic and Permutation Stacks—The Forth Shall Be First](https://dcreager.net/papers/Baker1994/), *ACM SIGARCH Computer Architecture News* 22(1), 1994. The connection motivates linear resource stack semantics; it does not make unrestricted Forth linear automatically.
- M. Anton Ertl and Bernd Paysan, [Closures—The Forth Way](https://www.complang.tuwien.ac.at/papers/ertl%26paysan.pdf), EuroForth 2018, pp. 17–30. It supplies useful closure/environment mechanisms and explicitly leaves closure memory management to the programmer.
- M. Anton Ertl, [Memory Safety Without Tagging nor Static Type Checking](https://repositum.tuwien.at/handle/20.500.12708/193614), EuroForth 2022 proceedings. Its object-stack/value-specific-operation design is a candidate memory-safety technique, not a proof of Girard modality.
- [Gforth manual](https://gforth.org/manual/): execution, locals, exception and memory behavior determine the actual target boundary.
