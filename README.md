# agda2LinearForth — linear/modal runtime ABI specification and verification status

`agda2forth` compiles Agda code for GNU Gforth. This document defines the intended checked subset, its error boundary, and the current proof/implementation gaps.


> **Linear/modal refinement status: NOT COMPLETE.** The upstream Forth compiler still emits raw literals and legacy operations, so the checked ABI and Agda model are not yet connected by a proved end-to-end semantic refinement theorem. Component tests establish only their enumerated behaviors.

## Per-file Haskell provenance

The shared source baseline is pinned to the compatible Agda2Scheme revision `6b3d975e9274448c09b5939e637b6718c2cfb10c` (Agda 2.6.2.x API era). `app/Main.hs` and `src/Agda/Compiler/Erase.hs` are kept byte-identical to that revision. The Forth code generator, `src/Agda/Compiler/ToForth.hs`, is kept byte-identical to `LMMilliken/agda2Forth` revision `e83f8cc735bf220f80b3655ce2158a23818910fe`. The current Agda2Scheme master targets Agda 2.8, whose API no longer matches this exact Forth backend; the pinned compatible revision avoids changing the upstream Forth source or adding compatibility shims.

`src/Main.hs` is the target-specific backend adapter derived from the pinned Scheme driver's lifecycle and options flow. It calls the Forth compiler and writes the runtime preamble plus generated definitions to a `.fth` file. CI verifies the pinned shared-file identities, the exact upstream Forth backend identity, and the reviewed adapter blob. There are no source-generation helper scripts or local Haskell compatibility shims.

The build targets GHC 9.0.2 and Agda 2.6.2.2 to match the exact upstream Forth backend's API era. Source identity is provenance only; it does not prove compiler correctness or semantic refinement.

## Goal and scope

The target is a dynamically enforced ABI for the subset of Agda programs this backend emits. Arbitrary Forth is outside the safety claim. The generated program must still be valid for GNU Gforth, and the legacy Forth words remain available with their existing stack effects; legacy callers do not automatically receive the checked-ABI guarantee. The compatibility target is the shared Agda frontend and erasure pipeline; the Forth runtime, Scheme backend, and formal proof artifacts are necessarily target-specific.

“End-to-end” means all values and all operations reachable from a generated program use the checked representation. It does not mean trying to make arbitrary interactive GForth safe.

This document deliberately distinguishes a specification, an implementation, and a refinement proof. The Agda modules `formal/LinearModalABI.agda`, `formal/LinearModalStackEffects.agda`, `formal/LinearModalExamples.agda`, `formal/LinearModalPrimitiveCoverage.agda`, and `formal/LinearModalDenotation.agda` are written constructively, use only Agda's bundled `Agda.Builtin.Nat` and `Agda.Builtin.Equality` modules, and require no Agda standard library, postulates, or F*. `LinearModalStackEffects.agda` assigns normal stack signatures to numeric operations, scalar/boolean/thunk/result construction, apply/force, conditional, constructors/matchers, print, throw, and catch. `LinearModalPrimitiveCoverage.agda` adds well-typed signature witnesses for every constructor of the `Primitive` enumeration. `LinearModalDenotation.agda` gives a bounded Scott-style flat-domain observation model for the scalar/conditional fragment, including bottom, normal returns, exceptional outcomes, arithmetic bounds, and catch composition. These are proofs about the formal contracts, not yet proofs that the current emitted Forth implements them.

## Source modes and runtime values

The source has two relevant modalities:

- `linear`: one logical owner; the resource must be used exactly once, including transfer or return. Preventing a second use alone is insufficient because silently dropping it also violates linearity.
- `modal`: sharing and discarding are permitted only after modal safety has been established.

The runtime's `unannotated` mode is a boundary/error state, not a third source-language type. A live unannotated value is forbidden inside a fully checked machine state. Unrestricted legacy words can still handle their historical representations outside that state.

Each checked descriptor records a monotone logical identity (META-ID) distinct from its address, kind (scalar/thunk/result), runtime mode, lifecycle (live/consumed), code address, closed-code classification, capture identities and optional payload identity. Numeric payloads are not handle identities. The checked ABI must never decide “number versus pointer” using `MAXNUM` or any other magnitude heuristic.

The checked arithmetic preconditions are represented by `BinaryScalarPrecondition`: both operands must be registered, live scalars with checked source modes, and the machine roots must account for two operand positions. The constructive lemma `linearOperandsCannotAlias` derives from `WellFormed` that those positions cannot name the same live linear identity. This discharges the model-side alias precondition; it is not yet a theorem that compiler-emitted operands satisfy this record.

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

The stack-effect model also proves a concrete boundary fact: a raw-natural/raw-natural stack cannot inhabit the checked addition or equality signature. A raw natural becomes a checked scalar only when an explicit `pMakeScalar` operation supplies a mode token. The pinned upstream `ToForth.hs` emits natural literals as bare Forth numeric cells and does not emit this constructor/mode evidence, so this theorem identifies a real missing compiler-to-runtime precondition—not a completed compiler refinement proof.

For linear code, an analogous derivation must state stack/resource effects and prove that every linear input is consumed, transferred or returned exactly once. A code-class label alone cannot prove this.

The Agda model additionally proves two promotion-precondition consequences: for a well-formed heap, no captured identity can be both live modal and live linear, and an opaque execution-token class cannot satisfy the closed-code witness requirement. These are constructive proofs about the formal preconditions. They do not prove that the current upstream compiler emits those witnesses or that the concrete Forth `promoteModal` implementation enforces the record; that implementation correspondence remains open.

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
6. Checked runtime ABI operations raise documented, catchable errors. The unchanged compiler still emits legacy `BYE` for unsupported literals/primitives and some invalid backend cases; those compiler-emitted paths are not yet covered by the catchable-error guarantee.

The runtime defines named Gforth exception codes and uses `THROW` for checked-ABI rejection. With the Haskell sources held unchanged, `fthError` still emits a diagnostic followed by `BYE`; the runtime's `ABI-ERROR-COMPILED-UNSUPPORTED` word is available to checked Forth callers but is not emitted by the compiler. In `dethunk`, execution goes through `CATCH`; on a linear closure failure, live linear descendants of its captured environment are retired before the original error is rethrown. The smoke test exercises this failure path. This cleanup relies on the closed ABI's acyclic descriptor/reference-order discipline, which remains an invariant to enforce and prove. `CATCH` does not automatically roll back arbitrary dictionary or metadata mutations.

## Scott-style denotation and the actual refinement boundary

`LinearModalDenotation.agda` makes the scalar part compositional: a lifted flat domain distinguishes bottom from a defined value, and `Computation` distinguishes divergence, normal return, and `THROW`. Numeric meanings include addition, subtraction, multiplication, quotient/remainder, equality and order, monus, a parametric target-cell bound, and explicit division-by-zero/overflow outcomes. The conditional denotation selects only the chosen branch, propagates bottom and exceptions, and has constructive selection lemmas. The module also proves bind associativity, catch equations, a generic frame rule for a state split into local and framed components, and commutation of pure updates on disjoint components.

This is a finite, first-order Scott-style fragment, not a complete domain-theoretic semantics of arbitrary recursive GForth. It does not silently elevate an abstract semantic equation into a proof about a Forth definition. The actual Forth correspondence still needs a verified mapping from each emitted word and each runtime transition to these contracts.

The added `LinearModalPrimitiveCoverage.agda` is not limited to naturals and equality: it supplies typed witnesses for all 24 declared `Primitive` constructors, including arithmetic comparisons, construction, application, forcing, result wrapping, promotion, matching, printing, throwing, and catching. The earlier examples happened to instantiate fewer constructors; that was example coverage, not a design restriction. `rawNatsCannotEnterCheckedABI` generalizes the raw-literal mismatch proof: a pair of untagged natural cells cannot directly satisfy any checked primitive's stack signature.

There is also a constructive obstruction to the requested full end-to-end theorem under the frozen Haskell-source constraint. The upstream backend emits bare natural cells and erases source modality instead of supplying a mode witness. The denotation module formalizes the information-loss point: when linear and modal source modes share the same erased runtime representation, no decoder from that representation alone can recover both modes correctly. Updating `.fth` can improve runtime behavior or enforce contracts where evidence exists, but it cannot reconstruct source evidence that the unchanged compiler never emitted. A full proof therefore requires either the existing compiler output to carry modality/code-class evidence or a verified replacement/interposition layer that preserves that evidence. No extra Haskell shim or helper script has been added.

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
- [ ] Confirm all five Agda modules type-check in CI using Agda itself with `--no-libraries`.
- [x] Give every declared checked-ABI primitive a typed stack/mode signature and concrete witness; checked Forth correspondence remains a separate obligation.
- [x] Add bounded scalar denotations, bottom/return/throw observations, catch equations, and a separation-style frame/non-interference lemma.
- [ ] Route every supported generated literal, constructor, application, force, conditional and primitive through the checked ABI.
- [ ] Replace caller-asserted XT safety with compiler/loader-generated code-class derivations tied to the closed core IR.
- [ ] Prove actual Forth word implementations preserve `WellFormed`, including every exceptional path.
- [ ] Prove compiler-to-core and core-to-Gforth correspondence for the supported subset. The mode-erasure lemma shows why this cannot be inferred from bare literals or patched into existence by an unverified runtime guess.
- [x] Add a compiler-output regression fixture recording the unchanged unsupported-literal diagnostic and legacy `BYE` output.
- [ ] Route unsupported compiler cases through a catchable boundary without modifying the Haskell backend; this requires a verified, compatibility-preserving checked loader or runtime interception.
- [ ] Run positive and negative Gforth tests, plus compatibility regression tests for legacy words.

Until those last obligations pass, the only justified claim is runtime hardening for explicitly managed handles—not complete end-to-end linear/modal safety.

## Research anchors

- Henry G. Baker, [Linear Logic and Permutation Stacks—The Forth Shall Be First](https://dcreager.net/papers/Baker1994/), *ACM SIGARCH Computer Architecture News* 22(1), 1994. The connection motivates linear resource stack semantics; it does not make unrestricted Forth linear automatically.
- M. Anton Ertl and Bernd Paysan, [Closures—The Forth Way](https://www.complang.tuwien.ac.at/papers/ertl%26paysan.pdf), EuroForth 2018, pp. 17–30. It supplies useful closure/environment mechanisms and explicitly leaves closure memory management to the programmer.
- M. Anton Ertl, [Memory Safety Without Tagging nor Static Type Checking](https://repositum.tuwien.at/handle/20.500.12708/193614), EuroForth 2022 proceedings. Its object-stack/value-specific-operation design is a candidate memory-safety technique, not a proof of Girard modality.
- [Gforth manual](https://gforth.org/manual/): execution, locals, exception and memory behavior determine the actual target boundary.
