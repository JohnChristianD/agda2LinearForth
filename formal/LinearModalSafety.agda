{-# OPTIONS --without-K --rewriting --confluence-check --exact-split --no-projection-like #-}

-- Single-source-of-truth constructive specification for agda2LinearForth.
--
-- This module combines descriptor/ownership invariants, weakest-precondition
-- semantics, checked stack effects, allocation/exception contracts, denotational
-- models, and a semantic mirror of the compiler/runtime boundary.
-- The proof terms
-- below establish properties of this Agda model. They do not, by themselves,
-- establish that arbitrary Haskell or Forth implementations refine it.
module LinearModalSafety where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

-- Import the verified core under the same single --safe CI invocation.
import VerifiedPLLCore

-- ── 1. Descriptor heap, linear/modal invariants, and WP model ──

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

record ⊤ : Set where
  constructor tt

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

infixr 5 _::_ _++_
infix 4 _∈ₙ_ _<_

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data MaybeNat : Set where
  noPayload : MaybeNat
  hasPayload : Nat → MaybeNat

data SourceMode : Set where
  linear modal : SourceMode

-- Unannotated is a runtime boundary/error state, not a third source type.
data RuntimeMode : Set where
  unannotated linearMode modalMode : RuntimeMode

-- Checked ABI values must carry one of the two source-language modalities.
data AnnotatedMode : RuntimeMode → Set where
  checkedLinearMode : AnnotatedMode linearMode
  checkedModalMode : AnnotatedMode modalMode

sourceMode : SourceMode → RuntimeMode
sourceMode linear = linearMode
sourceMode modal = modalMode

data Life : Set where
  live consumed : Life

data Kind : Set where
  thunk result scalar boolean : Kind

data RuntimeError : Set where
  unknownHandle consumedHandle invalidMode wrongKind : RuntimeError
  aliasedLinearOperands : RuntimeError
  expectedScalar expectedBoolean invalidBoolean : RuntimeError
  linearCaptureNotAccounted modalPromotionRejected : RuntimeError
  unknownPrimitive badStackEffect : RuntimeError
  badResultPayload abiEscapeHatch : RuntimeError
  arithmeticDomainError arithmeticOverflowError identityOverflowError : RuntimeError
  nullExecutionTokenError : RuntimeError

-- CodeClass is a compiler/loader classification, not an execution-token address.
-- codeOpaque is deliberately not eligible for modal promotion.
data CodeClass : Set where
  codeOpaque : CodeClass
  codeNatAdd codeNatSub codeNatMul codeNatQuot codeNatRem : CodeClass
  codeNatEq codeNatGeq codeNatLt codeNatMonus : CodeClass

-- Witnesses exist only for explicitly audited closed primitive classes.
-- There is deliberately no constructor for opaque user Forth code.
data ModalCode : CodeClass → Set where
  modalNatAdd : ModalCode codeNatAdd
  modalNatSub : ModalCode codeNatSub
  modalNatMul : ModalCode codeNatMul
  modalNatQuot : ModalCode codeNatQuot
  modalNatRem : ModalCode codeNatRem
  modalNatEq : ModalCode codeNatEq
  modalNatGeq : ModalCode codeNatGeq
  modalNatLt : ModalCode codeNatLt
  modalNatMonus : ModalCode codeNatMonus

data _≢_ {A : Set} (x y : A) : Set where
  apart : (x ≡ y → ⊥) → x ≢ y

data _∈ₙ_ (n : Nat) : List Nat → Set where
  here : {m : Nat} {xs : List Nat} → n ≡ m → n ∈ₙ (m :: xs)
  there : {m : Nat} {xs : List Nat} → n ∈ₙ xs → n ∈ₙ (m :: xs)

NoDup : List Nat → Set
NoDup [] = ⊤
NoDup (x :: xs) = ((x ∈ₙ xs) → ⊥) × NoDup xs

data _<_ : Nat → Nat → Set where
  zeroLtSuc : {n : Nat} → zero < suc n
  sucLtSuc : {n m : Nat} → n < m → suc n < suc m

AllBelow : Nat → List Nat → Set
AllBelow bound [] = ⊤
AllBelow bound (n :: ns) = (n < bound) × AllBelow bound ns

notSelfLess : {n : Nat} → n < n → ⊥
notSelfLess {zero} ()
notSelfLess {suc n} (sucLtSuc p) = notSelfLess p

subst : {A : Set} {P : A → Set} {x y : A} → x ≡ y → P x → P y
subst refl px = px

-- If each registered identity is below nextIdentity, the next identity is fresh.
freshNotPresent :
  {next : Nat} {xs : List Nat} →
  AllBelow next xs → (next ∈ₙ xs) → ⊥
freshNotPresent {xs = []} bounded ()
freshNotPresent {next} {n :: ns} (nBelow , restBelow) (here nextEqN) =
  notSelfLess (subst {P = λ k → n < k} nextEqN nBelow)
freshNotPresent {next} {n :: ns} (nBelow , restBelow) (there occursLater) =
  freshNotPresent restBelow occursLater

record Descriptor : Set where
  constructor descriptor
  field
    key : Nat
    kind : Kind
    mode : RuntimeMode
    life : Life
    codeAddress : Nat
    codeClass : CodeClass
    captures : List Nat
    payloadRef : MaybeNat
open Descriptor public

Heap : Set
Heap = List Descriptor

keys : Heap → List Nat
keys [] = []
keys (d :: ds) = key d :: keys ds

maybeRefs : MaybeNat → List Nat
maybeRefs noPayload = []
maybeRefs (hasPayload n) = n :: []

references : Descriptor → List Nat
references d = captures d ++ maybeRefs (payloadRef d)

AllIn : List Nat → List Nat → Set
AllIn [] known = ⊤
AllIn (n :: ns) known = (n ∈ₙ known) × AllIn ns known

-- Checked descriptors point only to older identities. Since allocation identities
-- strictly increase, this rules out direct cycles and supports finite recursive
-- retirement of captured linear subtrees on exceptional exit.
ReferencesOlder : Heap → Set
ReferencesOlder [] = ⊤
ReferencesOlder (d :: ds) =
  AllBelow (key d) (references d) × ReferencesOlder ds

noDirectSelfReference :
  (d : Descriptor) →
  AllBelow (key d) (references d) →
  (key d ∈ₙ references d) → ⊥
noDirectSelfReference d = freshNotPresent

data HasDescriptor (needle : Descriptor) : Heap → Set where
  descriptorHere : {ds : Heap} → HasDescriptor needle (needle :: ds)
  descriptorThere :
    {d : Descriptor} {ds : Heap} →
    HasDescriptor needle ds → HasDescriptor needle (d :: ds)

data HasLive (n : Nat) : Heap → Set where
  liveHere :
    {d : Descriptor} {ds : Heap} →
    key d ≡ n → life d ≡ live → HasLive n (d :: ds)
  liveThere :
    {d : Descriptor} {ds : Heap} →
    HasLive n ds → HasLive n (d :: ds)

data HasLiveLinear (n : Nat) : Heap → Set where
  linearLiveHere :
    {d : Descriptor} {ds : Heap} →
    key d ≡ n → mode d ≡ linearMode → life d ≡ live →
    HasLiveLinear n (d :: ds)
  linearLiveThere :
    {d : Descriptor} {ds : Heap} →
    HasLiveLinear n ds → HasLiveLinear n (d :: ds)

data HasLiveModal (n : Nat) : Heap → Set where
  modalLiveHere :
    {d : Descriptor} {ds : Heap} →
    key d ≡ n → mode d ≡ modalMode → life d ≡ live →
    HasLiveModal n (d :: ds)
  modalLiveThere :
    {d : Descriptor} {ds : Heap} →
    HasLiveModal n ds → HasLiveModal n (d :: ds)

liveLinearAtKey :
  {d : Descriptor} {h : Heap} →
  HasDescriptor d h →
  mode d ≡ linearMode →
  life d ≡ live →
  HasLiveLinear (key d) h
liveLinearAtKey descriptorHere modeIsLinear lifeIsLive =
  linearLiveHere refl modeIsLinear lifeIsLive
liveLinearAtKey (descriptorThere registered) modeIsLinear lifeIsLive =
  linearLiveThere (liveLinearAtKey registered modeIsLinear lifeIsLive)

AllLive : List Nat → Heap → Set
AllLive [] h = ⊤
AllLive (n :: ns) h = HasLive n h × AllLive ns h

AllModal : List Nat → Heap → Set
AllModal [] h = ⊤
AllModal (n :: ns) h = HasLiveModal n h × AllModal ns h

RegisteredRefs : Heap → Heap → Set
RegisteredRefs full [] = ⊤
RegisteredRefs full (d :: ds) =
  AllIn (references d) (keys full) × RegisteredRefs full ds

LiveCaptures : Heap → Heap → Set
LiveCaptures full [] = ⊤
LiveCaptures full (d :: ds) with kind d | life d
... | thunk | live =
  AllLive (captures d) full × LiveCaptures full ds
... | _ | _ = LiveCaptures full ds

activeCaptures : Heap → List Nat
activeCaptures [] = []
activeCaptures (d :: ds) with kind d | life d
... | thunk | live = captures d ++ activeCaptures ds
... | _ | _ = activeCaptures ds

-- A live result wrapper is an active owner/reference to its contained payload.
-- This matters when the payload is a live linear thunk with captures.
activePayloads : Heap → List Nat
activePayloads [] = []
activePayloads (d :: ds) with kind d | life d | payloadRef d
... | result | live | hasPayload n = n :: activePayloads ds
... | _ | _ | _ = activePayloads ds

LivePayloads : Heap → Heap → Set
LivePayloads full [] = ⊤
LivePayloads full (d :: ds) with kind d | life d | payloadRef d
... | result | live | hasPayload n = HasLive n full × LivePayloads full ds
... | result | live | noPayload = ⊥ × LivePayloads full ds
... | _ | _ | _ = LivePayloads full ds

LiveResultPayloadModes : Heap → Heap → Set
LiveResultPayloadModes full [] = ⊤
LiveResultPayloadModes full (d :: ds) with kind d | life d | mode d | payloadRef d
... | result | live | linearMode | hasPayload n =
  HasLiveLinear n full × LiveResultPayloadModes full ds
... | result | live | modalMode | hasPayload n =
  HasLiveModal n full × LiveResultPayloadModes full ds
... | result | live | _ | noPayload =
  ⊥ × LiveResultPayloadModes full ds
... | _ | _ | _ | _ = LiveResultPayloadModes full ds

NoDupOn : (Nat → Set) → List Nat → Set
NoDupOn P [] = ⊤
NoDupOn P (n :: ns) = (P n → (n ∈ₙ ns) → ⊥) × NoDupOn P ns

-- Each live linear descriptor must occur in active references; NoDupOn enforces
-- at-most-once. Together these express exactly-one active owner reference.
LiveLinearOwned : Heap → List Nat → Set
LiveLinearOwned [] refs = ⊤
LiveLinearOwned (d :: ds) refs with mode d | life d
... | linearMode | live =
  (key d ∈ₙ refs) × LiveLinearOwned ds refs
... | _ | _ = LiveLinearOwned ds refs

AnnotatedLive : Descriptor → Set
AnnotatedLive d with mode d | life d
... | unannotated | live = ⊥
... | _ | _ = ⊤

AllAnnotated : Heap → Set
AllAnnotated [] = ⊤
AllAnnotated (d :: ds) = AnnotatedLive d × AllAnnotated ds

record Machine : Set where
  constructor machine
  field
    heap : Heap
    roots : List Nat
    nextIdentity : Nat
open Machine public

activeReferences : Machine → List Nat
activeReferences s = roots s ++ activeCaptures (heap s) ++ activePayloads (heap s)

record WellFormed (s : Machine) : Set where
  constructor wellFormed
  field
    identityUnique : NoDup (keys (heap s))
    rootsRegistered : AllIn (roots s) (keys (heap s))
    rootsLive : AllLive (roots s) (heap s)
    allReferencesRegistered : RegisteredRefs (heap s) (heap s)
    referencesDescendByIdentity : ReferencesOlder (heap s)
    activeCapturesLive : LiveCaptures (heap s) (heap s)
    liveResultPayloads : LivePayloads (heap s) (heap s)
    resultPayloadModes : LiveResultPayloadModes (heap s) (heap s)
    everyLinearResourceOwned : LiveLinearOwned (heap s) (activeReferences s)
    noLinearAliasing : NoDupOn (λ n → HasLiveLinear n (heap s)) (activeReferences s)
    noLiveUnannotated : AllAnnotated (heap s)
    nextIdentityFresh : AllBelow (nextIdentity s) (keys (heap s))
open WellFormed public

-- The operand-root list records the two inputs as separate positions.
record OperandRoots (left right : Nat) (xs : List Nat) : Set where
  constructor operandRoots
  field
    rootTail : List Nat
    rootsContainBothOperands : xs ≡ left :: right :: rootTail
open OperandRoots public

record BinaryScalarPrecondition
  (s : Machine) (left right : Descriptor) : Set where
  constructor binaryScalarPrecondition
  field
    leftRegistered : HasDescriptor left (heap s)
    rightRegistered : HasDescriptor right (heap s)
    leftIsScalar : kind left ≡ scalar
    rightIsScalar : kind right ≡ scalar
    leftIsLive : life left ≡ live
    rightIsLive : life right ≡ live
    leftHasCheckedMode : AnnotatedMode (mode left)
    rightHasCheckedMode : AnnotatedMode (mode right)
    operandRootOrder : OperandRoots (key left) (key right) (roots s)
open BinaryScalarPrecondition public

-- A well-formed machine has no linear aliasing. Because the binary-call
-- precondition records two separate operand-root positions, an aliased live
-- linear input contradicts the machine invariant constructively.
linearOperandsCannotAlias :
  (s : Machine) → WellFormed s →
  {left right : Descriptor} →
  BinaryScalarPrecondition s left right →
  key left ≡ key right →
  mode left ≡ linearMode → ⊥
linearOperandsCannotAlias s wf {left} {right} pre sameIdentity leftLinear
  with subst
    {P = λ rs →
      NoDupOn (λ n → HasLiveLinear n (heap s))
        (rs ++ activeCaptures (heap s) ++ activePayloads (heap s))}
    (rootsContainBothOperands (operandRootOrder pre))
    (noLinearAliasing wf)
... | (noRepeatedLinearRoot , _) =
  noRepeatedLinearRoot
    (liveLinearAtKey (leftRegistered pre) leftLinear (leftIsLive pre))
    (here sameIdentity)

nextIsFresh :
  (s : Machine) → WellFormed s →
  (nextIdentity s ∈ₙ keys (heap s)) → ⊥
nextIsFresh s wf = freshNotPresent (nextIdentityFresh wf)

-- The copy/drop rules are evidence-gated. No evidence constructor exists for
-- linear or unannotated handles.
data CanDuplicate : RuntimeMode → Set where
  modalCanDuplicate : CanDuplicate modalMode

data CanDiscard : RuntimeMode → Set where
  modalCanDiscard : CanDiscard modalMode

noLinearDuplication : CanDuplicate linearMode → ⊥
noLinearDuplication ()

noLinearDiscard : CanDiscard linearMode → ⊥
noLinearDiscard ()

noUnannotatedDuplication : CanDuplicate unannotated → ⊥
noUnannotatedDuplication ()

noUnannotatedDiscard : CanDiscard unannotated → ⊥
noUnannotatedDiscard ()

-- Do not model ownership with a bare indexed token. A constructor of the form
-- `token : Token identity mode life` for arbitrary indices makes each such
-- proposition trivially inhabited and proves no real consume/move transition.
-- Linear ownership is therefore expressed by the heap/root/capture invariant in
-- `WellFormed`: every live linear descriptor has exactly one active reference,
-- while `CanDuplicate` and `CanDiscard` permit those structural rules only for
-- modal values. Runtime refinement remains a separate obligation.

record PromotionPrecondition (s : Machine) (d : Descriptor) : Set where
  constructor promotionPrecondition
  field
    descriptorRegistered : HasDescriptor d (heap s)
    closureKind : kind d ≡ thunk
    closureLive : life d ≡ live
    capturedValuesModal : AllModal (captures d) (heap s)
    -- The code class must be derived from the closed compiler IR; caller-supplied
    -- XT flags are not proof witnesses.
    modalCodeWitness : ModalCode (codeClass d)
open PromotionPrecondition public

-- Equality utilities used to derive exclusivity from the machine invariants.
symEq : {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

transEq : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

modalIsNotLinear : modalMode ≡ linearMode → ⊥
modalIsNotLinear ()

modalKeyMember :
  {n : Nat} {h : Heap} → HasLiveModal n h → n ∈ₙ keys h
modalKeyMember (modalLiveHere keyEq _ _) = here (symEq keyEq)
modalKeyMember (modalLiveThere p) = there (modalKeyMember p)

linearKeyMember :
  {n : Nat} {h : Heap} → HasLiveLinear n h → n ∈ₙ keys h
linearKeyMember (linearLiveHere keyEq _ _) = here (symEq keyEq)
linearKeyMember (linearLiveThere p) = there (linearKeyMember p)

-- One identity cannot simultaneously denote live modal and live linear
-- descriptors in a heap whose descriptor identities are unique.
notBothLiveModes :
  (h : Heap) → NoDup (keys h) → {n : Nat} →
  HasLiveModal n h → HasLiveLinear n h → ⊥
notBothLiveModes [] unique () _
notBothLiveModes (d :: ds) (noDupHead , noDupTail)
  (modalLiveHere keyEq modalEq _) (linearLiveHere _ linearEq _) =
    modalIsNotLinear (transEq (symEq modalEq) linearEq)
notBothLiveModes (d :: ds) (noDupHead , noDupTail)
  (modalLiveHere keyEq _ _) (linearLiveThere linearTail) =
    noDupHead
      (subst {P = λ k → k ∈ₙ keys ds}
        (symEq keyEq) (linearKeyMember linearTail))
notBothLiveModes (d :: ds) (noDupHead , noDupTail)
  (modalLiveThere modalTail) (linearLiveHere keyEq _ _) =
    noDupHead
      (subst {P = λ k → k ∈ₙ keys ds}
        (symEq keyEq) (modalKeyMember modalTail))
notBothLiveModes (d :: ds) (noDupHead , noDupTail)
  (modalLiveThere modalTail) (linearLiveThere linearTail) =
    notBothLiveModes ds noDupTail modalTail linearTail

modalWitnessForMember :
  {h : Heap} → (ids : List Nat) → {n : Nat} →
  AllModal ids h → n ∈ₙ ids → HasLiveModal n h
modalWitnessForMember [] allModal ()
modalWitnessForMember {h = h} (x :: xs) (headModal , tailModal) (here eq) =
  subst {P = λ k → HasLiveModal k h} (symEq eq) headModal
modalWitnessForMember (x :: xs) (headModal , tailModal) (there member) =
  modalWitnessForMember xs tailModal member

-- A well-formed heap plus a promotion precondition proves that no captured
-- identity is a live linear value. This is a genuine consequence of both
-- pieces of evidence, not a trusted execution-token flag.
promotionExcludesLinearCaptures :
  (s : Machine) → WellFormed s → {d : Descriptor} →
  PromotionPrecondition s d →
  (n : Nat) → n ∈ₙ captures d → HasLiveLinear n (heap s) → ⊥
promotionExcludesLinearCaptures s wf {d} pre n captured linearWitness =
  notBothLiveModes (heap s) (identityUnique wf)
    (modalWitnessForMember (captures d) (capturedValuesModal pre) captured)
    linearWitness

-- Opaque user Forth execution tokens can never satisfy modal promotion's
-- closed-code evidence requirement.
noOpaqueModalCode : ModalCode codeOpaque → ⊥
noOpaqueModalCode ()

promotionExcludesOpaqueCode :
  {s : Machine} {d : Descriptor} →
  PromotionPrecondition s d → codeClass d ≡ codeOpaque → ⊥
promotionExcludesOpaqueCode pre codeEq =
  noOpaqueModalCode
    (subst {P = ModalCode} codeEq (modalCodeWitness pre))

-- The core-language model covers these operations; escape hatches are excluded.
data Primitive : Set where
  pNatAdd pNatSub pNatMul pNatQuot pNatRem : Primitive
  pNatEq pNatGeq pNatLt pNatMonus pIf : Primitive
  pMakeScalar pMakeBool pMakeThunk pApply pForce pMakeResult pUnwrapResult : Primitive
  pPromoteModal pAssertLinear pConstruct pMatch pPrint pThrow pCatch : Primitive


-- Complete profile table for every primitive admitted by the proposed checked
-- core ABI. This table is a specification; implementation correspondence is a
-- separate theorem and is currently an open obligation.
data Arity : Set where
  fixedArity : Nat → Arity
  constructorDefinedArity matcherDefinedArity : Arity

data OperandRule : Set where
  twoCheckedScalars : OperandRule
  threeCheckedBranches : OperandRule
  modeAndScalar modeAndBoolean : OperandRule
  checkedCode : OperandRule
  checkedClosureAndValue : OperandRule
  checkedClosure : OperandRule
  checkedResult : OperandRule
  checkedThunk : OperandRule
  checkedConstructorFields : OperandRule
  checkedMatchInputs : OperandRule
  checkedObservableValue : OperandRule
  checkedErrorAndHandler : OperandRule

data OwnershipEffect : Set where
  consumeLinearOperands : OwnershipEffect
  makeFreshScalar makeFreshBoolean : OwnershipEffect
  makeFreshClosure : OwnershipEffect
  moveCaptures : OwnershipEffect
  forceByMode : OwnershipEffect
  moveIntoResult : OwnershipEffect
  moveOutOfResult : OwnershipEffect
  promoteOnlyWithProof : OwnershipEffect
  markLinearOnlyWithProof : OwnershipEffect
  moveConstructorFields : OwnershipEffect
  accountPatternFields : OwnershipEffect
  selectBranchAndAccountResources : OwnershipEffect
  observeWithoutHiddenForce : OwnershipEffect
  raiseCheckedError : OwnershipEffect
  catchAndPreserveState : OwnershipEffect

data ResultModeRule : Set where
  joinOperandModes : ResultModeRule
  selectedBranchMode : ResultModeRule
  inputMode : ResultModeRule
  codeResultMode : ResultModeRule
  freshAnnotatedMode : ResultModeRule
  noValue : ResultModeRule

data EvidenceRequirement : Set where
  noCodeEvidence : EvidenceRequirement
  runtimeValueValidation : EvidenceRequirement
  compilerDerivedCodeProof : EvidenceRequirement
  explicitlyTrustedLegacyCode : EvidenceRequirement

record PrimitiveSpec (p : Primitive) : Set where
  constructor mkPrimitiveSpec
  field
    stackArity : Arity
    operandRule : OperandRule
    ownershipRule : OwnershipEffect
    resultModeRule : ResultModeRule
    evidenceRequirement : EvidenceRequirement
    possibleErrors : List RuntimeError
open PrimitiveSpec public

numericErrors : List RuntimeError
numericErrors = unknownHandle :: consumedHandle :: wrongKind :: expectedScalar ::
  invalidMode :: aliasedLinearOperands :: arithmeticOverflowError :: identityOverflowError :: []

booleanErrors : List RuntimeError
booleanErrors = unknownHandle :: consumedHandle :: wrongKind :: expectedBoolean :: invalidMode :: invalidBoolean :: identityOverflowError :: []

divisionErrors : List RuntimeError
divisionErrors = numericErrors ++ (arithmeticDomainError :: [])

closureErrors : List RuntimeError
closureErrors = unknownHandle :: consumedHandle :: wrongKind ::
  invalidMode :: badStackEffect :: identityOverflowError :: nullExecutionTokenError :: []

modalErrors : List RuntimeError
modalErrors = unknownHandle :: consumedHandle :: wrongKind ::
  modalPromotionRejected :: badResultPayload :: []

constructErrors : List RuntimeError
constructErrors = unknownHandle :: consumedHandle :: wrongKind ::
  badStackEffect :: abiEscapeHatch :: identityOverflowError :: []

throwErrors : List RuntimeError
throwErrors = abiEscapeHatch :: []

primitiveSpecFor : (p : Primitive) → PrimitiveSpec p
primitiveSpecFor pNatAdd = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
primitiveSpecFor pNatSub = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
primitiveSpecFor pNatMul = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
primitiveSpecFor pNatQuot = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation divisionErrors
primitiveSpecFor pNatRem = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation divisionErrors
primitiveSpecFor pNatEq = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation (numericErrors ++ (invalidBoolean :: []))
primitiveSpecFor pNatGeq = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation (numericErrors ++ (invalidBoolean :: []))
primitiveSpecFor pNatLt = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation (numericErrors ++ (invalidBoolean :: []))
primitiveSpecFor pNatMonus = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
primitiveSpecFor pIf = mkPrimitiveSpec (fixedArity 3) threeCheckedBranches selectBranchAndAccountResources selectedBranchMode runtimeValueValidation closureErrors
primitiveSpecFor pMakeScalar = mkPrimitiveSpec (fixedArity 2) modeAndScalar makeFreshScalar inputMode noCodeEvidence (invalidMode :: numericErrors)
primitiveSpecFor pMakeBool = mkPrimitiveSpec (fixedArity 2) modeAndBoolean makeFreshBoolean inputMode runtimeValueValidation booleanErrors
primitiveSpecFor pMakeThunk = mkPrimitiveSpec (fixedArity 2) checkedCode makeFreshClosure codeResultMode compilerDerivedCodeProof closureErrors
primitiveSpecFor pApply = mkPrimitiveSpec (fixedArity 2) checkedClosureAndValue moveCaptures codeResultMode compilerDerivedCodeProof closureErrors
primitiveSpecFor pForce = mkPrimitiveSpec (fixedArity 1) checkedClosure forceByMode codeResultMode compilerDerivedCodeProof closureErrors
primitiveSpecFor pMakeResult = mkPrimitiveSpec (fixedArity 1) checkedObservableValue moveIntoResult inputMode runtimeValueValidation closureErrors
primitiveSpecFor pUnwrapResult = mkPrimitiveSpec (fixedArity 1) checkedResult moveOutOfResult inputMode runtimeValueValidation closureErrors
primitiveSpecFor pPromoteModal = mkPrimitiveSpec (fixedArity 1) checkedThunk promoteOnlyWithProof inputMode compilerDerivedCodeProof modalErrors
primitiveSpecFor pAssertLinear = mkPrimitiveSpec (fixedArity 1) checkedThunk markLinearOnlyWithProof inputMode compilerDerivedCodeProof modalErrors
primitiveSpecFor pConstruct = mkPrimitiveSpec constructorDefinedArity checkedConstructorFields moveConstructorFields codeResultMode compilerDerivedCodeProof constructErrors
primitiveSpecFor pMatch = mkPrimitiveSpec matcherDefinedArity checkedMatchInputs accountPatternFields selectedBranchMode compilerDerivedCodeProof constructErrors
primitiveSpecFor pPrint = mkPrimitiveSpec (fixedArity 1) checkedObservableValue observeWithoutHiddenForce noValue runtimeValueValidation numericErrors
primitiveSpecFor pThrow = mkPrimitiveSpec (fixedArity 1) checkedErrorAndHandler raiseCheckedError noValue noCodeEvidence throwErrors
primitiveSpecFor pCatch = mkPrimitiveSpec (fixedArity 2) checkedErrorAndHandler catchAndPreserveState inputMode noCodeEvidence (unknownHandle :: badStackEffect :: [])

-- This exhaustive function is accepted by Agda only if every Primitive constructor
-- has a profile. It does not claim that each Gforth implementation satisfies it.
specifiesEveryPrimitive : (p : Primitive) → PrimitiveSpec p
specifiesEveryPrimitive = primitiveSpecFor

data EscapeHatch : Set where
  rawMemoryAccess arbitraryExecute dictionaryCompilation : EscapeHatch

data Execution (S : Set) : Set where
  returned : S → Execution S
  thrown : S → RuntimeError → Execution S

catchExecution :
  {S : Set} → Execution S → (RuntimeError → S → Execution S) → Execution S
catchExecution (returned s) handler = returned s
catchExecution (thrown s e) handler = handler e s

executionPost :
  {S : Set} →
  (normal : S → Set) →
  (exceptional : S → RuntimeError → Set) →
  Execution S → Set
executionPost normal exceptional (returned s) = normal s
executionPost normal exceptional (thrown s e) = exceptional s e

-- Weakest-precondition semantics is the authoritative contract interface.
-- A command is modeled as a total state transformer into an explicit outcome:
-- normal return or a THROW carrying both the post-state and error.  The WP
-- requires the normal postcondition on return and the exceptional postcondition
-- on every exceptional exit.  Divergence is not silently identified with
-- success: the current Execution model is total-outcome and does not model
-- divergence; finite-fuel denotation below records exhaustion explicitly.
wp :
  {S : Set} →
  (command : S → Execution S) →
  (normalPostcondition : S → Set) →
  (exceptionalPostcondition : S → RuntimeError → Set) →
  S → Set
wp command normalPostcondition exceptionalPostcondition s =
  executionPost normalPostcondition exceptionalPostcondition (command s)

-- Sequential composition propagates THROW without running the next command.
sequenceExecution :
  {S : Set} → Execution S → (S → Execution S) → Execution S
sequenceExecution (returned s) next = next s
sequenceExecution (thrown s e) next = thrown s e

sequence :
  {S : Set} →
  (first second : S → Execution S) → S → Execution S
sequence first second s = sequenceExecution (first s) second

-- Dijkstra's sequencing law: compute the later condition first, then pull it
-- backwards through the first command. Exceptional exits of the first command
-- use the final exceptional postcondition directly.
wpSequence :
  {S : Set} →
  (first second : S → Execution S) →
  (normalPostcondition : S → Set) →
  (exceptionalPostcondition : S → RuntimeError → Set) →
  (s : S) →
  wp (sequence first second) normalPostcondition exceptionalPostcondition s ≡
  wp first
    (λ s' → wp second normalPostcondition exceptionalPostcondition s')
    exceptionalPostcondition s
wpSequence first second normalPostcondition exceptionalPostcondition s
  with first s
... | returned s' = refl
... | thrown s' e = refl

-- Weakest-precondition rule for CATCH: when the protected command throws,
-- its actual post-state and error are passed to the handler's WP.  On normal
-- return, the handler is irrelevant.
wpCatch :
  {S : Set} →
  (command : S → Execution S) →
  (handler : RuntimeError → S → Execution S) →
  (normalPostcondition : S → Set) →
  (exceptionalPostcondition : S → RuntimeError → Set) →
  (s : S) →
  wp (λ state → catchExecution (command state) handler)
    normalPostcondition exceptionalPostcondition s
  ≡
  wp command normalPostcondition
    (λ state err → wp (λ state' → handler err state')
      normalPostcondition exceptionalPostcondition state) s
wpCatch command handler normalPostcondition exceptionalPostcondition s
  with command s
... | returned s' = refl
... | thrown s' e = refl

-- Operational correctness is defined directly from command outcomes.
-- There is deliberately no parallel triple API or second rule system.
SemanticTriple :
  {S : Set} →
  (precondition : S → Set) →
  (command : S → Execution S) →
  (normalPostcondition : S → Set) →
  (exceptionalPostcondition : S → RuntimeError → Set) →
  Set
SemanticTriple {S} precondition command normalPostcondition exceptionalPostcondition =
  (s : S) → precondition s →
  executionPost normalPostcondition exceptionalPostcondition (command s)

-- The WP predicate itself is a valid precondition for the requested outcomes.
wpSemanticallyAdmissible :
  {S : Set}
  (command : S → Execution S)
  (normalPostcondition : S → Set)
  (exceptionalPostcondition : S → RuntimeError → Set) →
  SemanticTriple
    (wp command normalPostcondition exceptionalPostcondition)
    command normalPostcondition exceptionalPostcondition
wpSemanticallyAdmissible command normalPostcondition exceptionalPostcondition
  s preconditionProof = preconditionProof

-- Leastness from the operational contract: any precondition which proves the
-- requested outcome entails WP. This is precondition validity/leastness for
-- the finite Execution model, not domain-theoretic admissibility over a domain.
wpLeastnessFromOperationalSemantics :
  {S : Set}
  (precondition : S → Set)
  (command : S → Execution S)
  (normalPostcondition : S → Set)
  (exceptionalPostcondition : S → RuntimeError → Set) →
  SemanticTriple precondition command normalPostcondition exceptionalPostcondition →
  (s : S) → precondition s →
  wp command normalPostcondition exceptionalPostcondition s
wpLeastnessFromOperationalSemantics precondition command normalPostcondition
  exceptionalPostcondition valid s proof = valid s proof

skip : {S : Set} → S → Execution S
skip s = returned s

wpSkip :
  {S : Set} {P : S → Set} →
  (s : S) → P s →
  wp skip P (λ state err → P state) s
wpSkip s proof = proof

-- CATCH preservation is derived directly from the WP contract of the protected
-- command and the handler's operational outcome.
wpCatchPreserves :
  {S : Set} {P : S → Set}
  (command : S → Execution S)
  (handler : RuntimeError → S → Execution S) →
  ((s : S) → P s → wp command P (λ state err → P state) s) →
  ((err : RuntimeError) (state : S) → P state →
    executionPost P (λ state' err' → P state') (handler err state)) →
  (s : S) → P s →
  wp (λ state → catchExecution (command state) handler)
    P (λ state err → P state) s
wpCatchPreserves command handler commandSafe handlerSafe s proof
  with command s | commandSafe s proof
... | returned s' | normalProof = normalProof
... | thrown s' err | exceptionalProof = handlerSafe err s' exceptionalProof


-- ── 2. Closed checked-ABI stack effects ──

infixr 5 _⇒_

data CoreTy : Set where
  naturalTy booleanTy unitTy : CoreTy
  _⇒_ : CoreTy → CoreTy → CoreTy
  !Ty : CoreTy → CoreTy

modeOfTy : CoreTy → SourceMode
modeOfTy (!Ty A) = modal
modeOfTy _ = linear

data ModalCoreTy : CoreTy → Set where
  modalCoreTy : {A : CoreTy} → ModalCoreTy (!Ty A)

data ModalCaptures : List CoreTy → Set where
  modalCapturesNil : ModalCaptures []
  modalCapturesCons : {A : CoreTy} {As : List CoreTy} →
    ModalCoreTy A → ModalCaptures As → ModalCaptures (A :: As)

-- Code signatures belong to the closed, audited vocabulary; they cannot be
-- invented by asserting an arbitrary GForth execution token is safe.
codeSignature : CodeClass → CoreTy
codeSignature codeOpaque = unitTy
codeSignature codeNatAdd = naturalTy ⇒ naturalTy ⇒ naturalTy
codeSignature codeNatSub = naturalTy ⇒ naturalTy ⇒ naturalTy
codeSignature codeNatMul = naturalTy ⇒ naturalTy ⇒ naturalTy
codeSignature codeNatQuot = naturalTy ⇒ naturalTy ⇒ naturalTy
codeSignature codeNatRem = naturalTy ⇒ naturalTy ⇒ naturalTy
codeSignature codeNatEq = naturalTy ⇒ naturalTy ⇒ booleanTy
codeSignature codeNatGeq = naturalTy ⇒ naturalTy ⇒ booleanTy
codeSignature codeNatLt = naturalTy ⇒ naturalTy ⇒ booleanTy
codeSignature codeNatMonus = naturalTy ⇒ naturalTy ⇒ naturalTy

joinSourceMode : SourceMode → SourceMode → SourceMode
joinSourceMode linear _ = linear
joinSourceMode _ linear = linear
joinSourceMode modal modal = modal

naturalTypeFor : SourceMode → CoreTy
naturalTypeFor linear = naturalTy
naturalTypeFor modal = !Ty naturalTy

booleanTypeFor : SourceMode → CoreTy
booleanTypeFor linear = booleanTy
booleanTypeFor modal = !Ty booleanTy

data NatLike : CoreTy → Set where
  naturalIsNatural : NatLike naturalTy
  boxedNaturalIsNatural : NatLike (!Ty naturalTy)

data BoolLike : CoreTy → Set where
  booleanIsBoolean : BoolLike booleanTy
  boxedBooleanIsBoolean : BoolLike (!Ty booleanTy)

data LinearCoreTy : CoreTy → Set where
  linearNatural : LinearCoreTy naturalTy
  linearBoolean : LinearCoreTy booleanTy
  linearUnit : LinearCoreTy unitTy
  linearFunction : {A B : CoreTy} → LinearCoreTy (A ⇒ B)

-- An explicit code-safety witness is required to construct a checked closure.
-- Opaque arbitrary execution tokens intentionally have no witness.
data LinearCode : CodeClass → Set where
  linearNatAdd : LinearCode codeNatAdd
  linearNatSub : LinearCode codeNatSub
  linearNatMul : LinearCode codeNatMul
  linearNatQuot : LinearCode codeNatQuot
  linearNatRem : LinearCode codeNatRem
  linearNatEq : LinearCode codeNatEq
  linearNatGeq : LinearCode codeNatGeq
  linearNatLt : LinearCode codeNatLt
  linearNatMonus : LinearCode codeNatMonus

data CodeSafe : SourceMode → CodeClass → Set where
  linearCodeSafe : {c : CodeClass} → LinearCode c → CodeSafe linear c
  modalCodeSafe : {c : CodeClass} → ModalCode c → CodeSafe modal c

record ConstructorSignature : Set where
  constructor constructorSignature
  field
    constructorTag : Nat
    constructorFields : List CoreTy
    constructorResult : CoreTy
open ConstructorSignature public

record MatcherSignature : Set where
  constructor matcherSignature
  field
    matcherInput : CoreTy
    matcherOutput : CoreTy
open MatcherSignature public

data StackItem : Set where
  rawNatItem : StackItem
  rawBoolItem : StackItem
  modeTokenItem : SourceMode → StackItem
  valueItem : CoreTy → StackItem
  thunkItem : SourceMode → CodeClass → List CoreTy → CoreTy → StackItem
  resultItem : CoreTy → StackItem
  codeItem : CodeClass → StackItem
  constructorTokenItem : Nat → StackItem
  matcherTokenItem : MatcherSignature → StackItem
  errorTokenItem : RuntimeError → StackItem
  handlerTokenItem : StackItem

StackShape : Set
StackShape = List StackItem

valuesOf : List CoreTy → StackShape
valuesOf [] = []
valuesOf (A :: As) = valueItem A :: valuesOf As

-- Stack shapes are listed top-first. The state/ownership contracts live in
-- LinearModalSafety; these effects say which well-typed shapes an operation accepts.
data StackEffect : Primitive → StackShape → StackShape → Set where
  natAddEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatAdd
      (valueItem B :: valueItem A :: tail)
      (valueItem (naturalTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natSubEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatSub
      (valueItem B :: valueItem A :: tail)
      (valueItem (naturalTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natMulEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatMul
      (valueItem B :: valueItem A :: tail)
      (valueItem (naturalTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natQuotEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatQuot
      (valueItem B :: valueItem A :: tail)
      (valueItem (naturalTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natRemEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatRem
      (valueItem B :: valueItem A :: tail)
      (valueItem (naturalTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natEqEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatEq
      (valueItem B :: valueItem A :: tail)
      (valueItem (booleanTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natGeqEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatGeq
      (valueItem B :: valueItem A :: tail)
      (valueItem (booleanTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natLtEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatLt
      (valueItem B :: valueItem A :: tail)
      (valueItem (booleanTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  natMonusEffect : {A B : CoreTy} {tail : StackShape} →
    NatLike A → NatLike B →
    StackEffect pNatMonus
      (valueItem B :: valueItem A :: tail)
      (valueItem (naturalTypeFor (joinSourceMode (modeOfTy A) (modeOfTy B))) :: tail)

  makeScalarEffect : {m : SourceMode} {tail : StackShape} →
    StackEffect pMakeScalar
      (modeTokenItem m :: rawNatItem :: tail)
      (valueItem (naturalTypeFor m) :: tail)

  makeBooleanEffect : {m : SourceMode} {tail : StackShape} →
    StackEffect pMakeBool
      (modeTokenItem m :: rawBoolItem :: tail)
      (valueItem (booleanTypeFor m) :: tail)

  makeLinearThunkEffect : {c : CodeClass} {tail : StackShape} →
    LinearCode c →
    StackEffect pMakeThunk
      (modeTokenItem linear :: codeItem c :: tail)
      (thunkItem linear c [] (codeSignature c) :: tail)

  makeModalThunkEffect : {c : CodeClass} {tail : StackShape} →
    ModalCode c →
    StackEffect pMakeThunk
      (modeTokenItem modal :: codeItem c :: tail)
      (thunkItem modal c [] (codeSignature c) :: tail)

  applyLinearEffect : {m : SourceMode} {c : CodeClass}
    {captures : List CoreTy} {A B : CoreTy} {tail : StackShape} →
    CodeSafe (joinSourceMode m (modeOfTy A)) c →
    StackEffect pApply
      (thunkItem m c captures (A ⇒ B) :: valueItem A :: tail)
      (thunkItem (joinSourceMode m (modeOfTy A)) c
        (captures ++ (A :: [])) B :: tail)

  forceLinearEffect : {c : CodeClass} {captures : List CoreTy}
    {A : CoreTy} {tail : StackShape} →
    LinearCode c →
    StackEffect pForce
      (thunkItem linear c captures A :: tail)
      (valueItem A :: tail)

  forceModalEffect : {c : CodeClass} {captures : List CoreTy}
    {A : CoreTy} {tail : StackShape} →
    ModalCode c →
    ModalCaptures captures →
    StackEffect pForce
      (thunkItem modal c captures A :: tail)
      (valueItem A :: tail)

  makeResultEffect : {A : CoreTy} {tail : StackShape} →
    StackEffect pMakeResult
      (valueItem A :: tail)
      (resultItem A :: tail)

  unwrapResultEffect : {A : CoreTy} {tail : StackShape} →
    StackEffect pUnwrapResult
      (resultItem A :: tail)
      (valueItem A :: tail)

  promoteModalEffect : {c : CodeClass} {captures : List CoreTy}
    {A : CoreTy} {tail : StackShape} →
    ModalCode c →
    ModalCaptures captures →
    StackEffect pPromoteModal
      (thunkItem linear c captures A :: tail)
      (thunkItem modal c captures A :: tail)

  assertLinearEffect : {c : CodeClass} {captures : List CoreTy}
    {A : CoreTy} {tail : StackShape} {m : SourceMode} →
    LinearCode c →
    StackEffect pAssertLinear
      (thunkItem m c captures A :: tail)
      (thunkItem linear c captures A :: tail)

  ifModalBranchesEffect : {C A : CoreTy}
    {c1 c2 : CodeClass} {captures1 captures2 : List CoreTy}
    {tail : StackShape} →
    BoolLike C → ModalCode c1 → ModalCode c2 →
    ModalCaptures captures1 → ModalCaptures captures2 →
    StackEffect pIf
      (thunkItem modal c2 captures2 A ::
       thunkItem modal c1 captures1 A :: valueItem C :: tail)
      (valueItem A :: tail)

  constructEffect : (sig : ConstructorSignature) {tail : StackShape} →
    StackEffect pConstruct
      (valuesOf (constructorFields sig) ++
       (constructorTokenItem (constructorTag sig) :: tail))
      (valueItem (constructorResult sig) :: tail)

  matchEffect : (sig : MatcherSignature) {tail : StackShape} →
    StackEffect pMatch
      (matcherTokenItem sig :: valueItem (matcherInput sig) :: tail)
      (valueItem (matcherOutput sig) :: tail)

  printLinearEffect : {A : CoreTy} {tail : StackShape} →
    LinearCoreTy A →
    StackEffect pPrint (valueItem A :: tail) tail

  printModalEffect : {A : CoreTy} {tail : StackShape} →
    StackEffect pPrint (valueItem (!Ty A) :: tail) (valueItem (!Ty A) :: tail)

-- A stack-tail frame law for the declarative stack-effect semantics.
-- It is stronger than testing a primitive at an empty stack: any framed suffix
-- remains unchanged by the specified effect. This is a theorem about StackEffect,
-- not yet the implementation-correspondence theorem for the Forth word.
stackAppendAssoc :
  {A : Set} (xs ys zs : List A) →
  ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
stackAppendAssoc [] ys zs = refl
stackAppendAssoc (x :: xs) ys zs rewrite stackAppendAssoc xs ys zs = refl

stackTailFrame :
  {p : Primitive} {input output : StackShape} →
  StackEffect p input output →
  (frame : StackShape) →
  StackEffect p (input ++ frame) (output ++ frame)
stackTailFrame (natAddEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natAddEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natSubEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natSubEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natMulEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natMulEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natQuotEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natQuotEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natRemEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natRemEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natEqEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natEqEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natGeqEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natGeqEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natLtEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natLtEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (natMonusEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
  natMonusEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
stackTailFrame (makeScalarEffect {m = m} {tail = tail}) frame =
  makeScalarEffect {m = m} {tail = tail ++ frame}
stackTailFrame (makeBooleanEffect {m = m} {tail = tail}) frame =
  makeBooleanEffect {m = m} {tail = tail ++ frame}
stackTailFrame (makeLinearThunkEffect {c = c} {tail = tail} safeCode) frame =
  makeLinearThunkEffect {c = c} {tail = tail ++ frame} safeCode
stackTailFrame (makeModalThunkEffect {c = c} {tail = tail} safeCode) frame =
  makeModalThunkEffect {c = c} {tail = tail ++ frame} safeCode
stackTailFrame (applyLinearEffect {m = m} {c = c} {captures = captures}
  {A = A} {B = B} {tail = tail} safeCode) frame =
  applyLinearEffect {m = m} {c = c} {captures = captures} {A = A} {B = B}
    {tail = tail ++ frame} safeCode
stackTailFrame (forceLinearEffect {c = c} {captures = captures}
  {A = A} {tail = tail} safeCode) frame =
  forceLinearEffect {c = c} {captures = captures} {A = A} {tail = tail ++ frame} safeCode
stackTailFrame (forceModalEffect {c = c} {captures = captures}
  {A = A} {tail = tail} safeCode modalCaptures) frame =
  forceModalEffect {c = c} {captures = captures} {A = A} {tail = tail ++ frame}
    safeCode modalCaptures
stackTailFrame (makeResultEffect {A = A} {tail = tail}) frame =
  makeResultEffect {A = A} {tail = tail ++ frame}
stackTailFrame (unwrapResultEffect {A = A} {tail = tail}) frame =
  unwrapResultEffect {A = A} {tail = tail ++ frame}
stackTailFrame (promoteModalEffect {c = c} {captures = captures}
  {A = A} {tail = tail} safeCode modalCaptures) frame =
  promoteModalEffect {c = c} {captures = captures} {A = A} {tail = tail ++ frame}
    safeCode modalCaptures
stackTailFrame (assertLinearEffect {c = c} {captures = captures}
  {A = A} {tail = tail} {m = m} safeCode) frame =
  assertLinearEffect {c = c} {captures = captures} {A = A}
    {tail = tail ++ frame} {m = m} safeCode
stackTailFrame (ifModalBranchesEffect {C = C} {A = A} {c1 = c1} {c2 = c2}
  {captures1 = captures1} {captures2 = captures2} {tail = tail}
  condition modalCode1 modalCode2 capturesSafe1 capturesSafe2) frame =
  ifModalBranchesEffect {C = C} {A = A} {c1 = c1} {c2 = c2}
    {captures1 = captures1} {captures2 = captures2} {tail = tail ++ frame}
    condition modalCode1 modalCode2 capturesSafe1 capturesSafe2
stackTailFrame (constructEffect sig {tail = tail}) frame =
  subst
    {P = λ input → StackEffect pConstruct input
      (valueItem (constructorResult sig) :: (tail ++ frame))}
    (symEq (stackAppendAssoc (valuesOf (constructorFields sig))
      (constructorTokenItem (constructorTag sig) :: tail) frame))
    (constructEffect sig {tail = tail ++ frame})
stackTailFrame (matchEffect sig {tail = tail}) frame =
  matchEffect sig {tail = tail ++ frame}
stackTailFrame (printLinearEffect {A = A} {tail = tail} linearTy) frame =
  printLinearEffect {A = A} {tail = tail ++ frame} linearTy
stackTailFrame (printModalEffect {A = A} {tail = tail}) frame =
  printModalEffect {A = A} {tail = tail ++ frame}

-- These are error transitions, not ordinary stack-returning effects. The
-- state/error payload is modeled by Execution and the WP contracts.
data ErrorEffect : Primitive → StackShape → RuntimeError → Set where
  throwEffect : {e : RuntimeError} {tail : StackShape} →
    ErrorEffect pThrow (errorTokenItem e :: tail) e

-- Every primitive with an ordinary return path must have a stack-effect derivation
-- for the specific input/output shape. Dynamic constructor/matcher effects carry
-- explicit schemas; throws use ErrorEffect instead.

-- A bare emitted natural literal is not a checked ABI scalar. The only way to
-- turn a raw natural into a checked scalar is the explicit pMakeScalar effect,
-- which requires a source-mode token. In particular, raw/raw arithmetic does
-- not inhabit the checked numeric primitive signature.
rawLiteralCannotUseCheckedAddition :
  {tail output : StackShape} →
  StackEffect pNatAdd
    (rawNatItem :: rawNatItem :: tail)
    output →
  ⊥
rawLiteralCannotUseCheckedAddition ()

rawLiteralCannotUseCheckedEquality :
  {tail output : StackShape} →
  StackEffect pNatEq
    (rawNatItem :: rawNatItem :: tail)
    output →
  ⊥
rawLiteralCannotUseCheckedEquality ()

-- The checked constructor has the missing witness explicitly: it takes a
-- runtime mode token and a raw natural, producing a mode-indexed value.
rawLiteralNeedsModeWitness :
  {m : SourceMode} {tail : StackShape} →
  StackEffect pMakeScalar
    (modeTokenItem m :: rawNatItem :: tail)
    (valueItem (naturalTypeFor m) :: tail)
rawLiteralNeedsModeWitness = makeScalarEffect


-- ── 3. Concrete witnesses for selected checked-ABI compositions ──

linearNatAddition :
  {tail : StackShape} →
  StackEffect pNatAdd
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatAddition = natAddEffect naturalIsNatural naturalIsNatural

modalNatAddition :
  {tail : StackShape} →
  StackEffect pNatAdd
    (valueItem (!Ty naturalTy) :: valueItem (!Ty naturalTy) :: tail)
    (valueItem (!Ty naturalTy) :: tail)
modalNatAddition = natAddEffect boxedNaturalIsNatural boxedNaturalIsNatural

mixedNatAddition :
  {tail : StackShape} →
  StackEffect pNatAdd
    (valueItem (!Ty naturalTy) :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
mixedNatAddition = natAddEffect naturalIsNatural boxedNaturalIsNatural

linearNatEquality :
  {tail : StackShape} →
  StackEffect pNatEq
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
linearNatEquality = natEqEffect naturalIsNatural naturalIsNatural

modalNatEquality :
  {tail : StackShape} →
  StackEffect pNatEq
    (valueItem (!Ty naturalTy) :: valueItem (!Ty naturalTy) :: tail)
    (valueItem (!Ty booleanTy) :: tail)
modalNatEquality = natEqEffect boxedNaturalIsNatural boxedNaturalIsNatural

mixedNatEquality :
  {tail : StackShape} →
  StackEffect pNatEq
    (valueItem (!Ty naturalTy) :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
mixedNatEquality = natEqEffect naturalIsNatural boxedNaturalIsNatural

checkedModalBooleanConstruction :
  StackEffect pMakeBool
    (modeTokenItem modal :: rawBoolItem :: [])
    (valueItem (!Ty booleanTy) :: [])
checkedModalBooleanConstruction = makeBooleanEffect

checkedModalAddClosure :
  StackEffect pMakeThunk
    (modeTokenItem modal :: codeItem codeNatAdd :: [])
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
checkedModalAddClosure = makeModalThunkEffect modalNatAdd

checkedLinearAddClosure :
  StackEffect pMakeThunk
    (modeTokenItem linear :: codeItem codeNatAdd :: [])
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
checkedLinearAddClosure = makeLinearThunkEffect linearNatAdd

modalPromotionEffect :
  StackEffect pPromoteModal
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
modalPromotionEffect = promoteModalEffect modalNatAdd modalCapturesNil


-- ── 4. Compiler emission boundary mirrored from ToForth.hs ──

data NatExpr : Set where
  natLiteral : Nat → NatExpr
  natAddition : NatExpr → NatExpr → NatExpr
  natMultiplication : NatExpr → NatExpr → NatExpr
  natMonus : NatExpr → NatExpr → NatExpr

-- These constructors distinguish raw literals, saturated primitive calls routed
-- through the checked-or-legacy ABI adapters, and checked result constructors.
-- The checked constructors are included so the predicate below can state, and prove, their absence.
data EmittedFragment : Set where
  rawNaturalCell : Nat → EmittedFragment
  rawTrueCell rawFalseCell : EmittedFragment
  abiAddAdapterCode : EmittedFragment → EmittedFragment → EmittedFragment
  abiMulAdapterCode : EmittedFragment → EmittedFragment → EmittedFragment
  abiMonusAdapterCode : EmittedFragment → EmittedFragment → EmittedFragment
  checkedScalarCode : SourceMode → Nat → EmittedFragment
  checkedBooleanCode : SourceMode → EmittedFragment

-- Mirrors the selected ToForth.hs emission paths: Nat literals are emitted
-- as decimal text and parsed by ABI-PARSE-NAT into raw cells only when they fit
-- the target cell bound; saturated addition, multiplication, and builtin Nat
-- subtraction use ABI-ADD-OR-LEGACY, ABI-MUL-OR-LEGACY, and
-- ABI-MONUS-OR-LEGACY. The result remains a raw cell without source-mode evidence.
-- This is a manual semantic mirror, not extraction from the Haskell emitter.
compileNatFragment : NatExpr → EmittedFragment
compileNatFragment (natLiteral n) = rawNaturalCell n
compileNatFragment (natAddition left right) =
  abiAddAdapterCode (compileNatFragment left) (compileNatFragment right)
compileNatFragment (natMultiplication left right) =
  abiMulAdapterCode (compileNatFragment left) (compileNatFragment right)
compileNatFragment (natMonus left right) =
  abiMonusAdapterCode (compileNatFragment left) (compileNatFragment right)

compiledNatMultiplicationUsesAdapter :
  (left right : NatExpr) →
  compileNatFragment (natMultiplication left right) ≡
    abiMulAdapterCode (compileNatFragment left) (compileNatFragment right)
compiledNatMultiplicationUsesAdapter left right = refl

compiledNatMonusUsesAdapter :
  (left right : NatExpr) →
  compileNatFragment (natMonus left right) ≡
    abiMonusAdapterCode (compileNatFragment left) (compileNatFragment right)
compiledNatMonusUsesAdapter left right = refl

-- A small interpreter for the selected emitted Nat fragment. It deliberately
-- treats booleans and checked handles as outside this Nat-only observation model.
data NatFragmentObservation : Set where
  observedNat : Nat → NatFragmentObservation
  notObservedNat : NatFragmentObservation

modelNatMonus : Nat → Nat → Nat
modelNatMonus n zero = n
modelNatMonus zero (suc m) = zero
modelNatMonus (suc n) (suc m) = modelNatMonus n m

natExprMeaning : NatExpr → Nat
natExprMeaning (natLiteral n) = n
natExprMeaning (natAddition left right) =
  natExprMeaning left + natExprMeaning right
natExprMeaning (natMultiplication left right) =
  natExprMeaning left * natExprMeaning right
natExprMeaning (natMonus left right) =
  modelNatMonus (natExprMeaning left) (natExprMeaning right)

observeNatFragment : EmittedFragment → NatFragmentObservation
observeNatFragment (rawNaturalCell n) = observedNat n
observeNatFragment rawTrueCell = notObservedNat
observeNatFragment rawFalseCell = notObservedNat
observeNatFragment (abiAddAdapterCode left right)
  with observeNatFragment left | observeNatFragment right
... | observedNat x | observedNat y = observedNat (x + y)
... | _ | _ = notObservedNat
observeNatFragment (abiMulAdapterCode left right)
  with observeNatFragment left | observeNatFragment right
... | observedNat x | observedNat y = observedNat (x * y)
... | _ | _ = notObservedNat
observeNatFragment (abiMonusAdapterCode left right)
  with observeNatFragment left | observeNatFragment right
... | observedNat x | observedNat y = observedNat (modelNatMonus x y)
... | _ | _ = notObservedNat
observeNatFragment (checkedScalarCode mode n) = notObservedNat
observeNatFragment (checkedBooleanCode mode) = notObservedNat

-- This is an induction theorem about the two explicit ASTs above. It does not
-- infer anything about the Haskell emitter or the concrete Gforth interpreter.
compiledNatFragmentPreservesMeaning :
  (expr : NatExpr) →
  observeNatFragment (compileNatFragment expr) ≡
    observedNat (natExprMeaning expr)
compiledNatFragmentPreservesMeaning (natLiteral n) = refl
compiledNatFragmentPreservesMeaning (natAddition left right)
  rewrite compiledNatFragmentPreservesMeaning left
        | compiledNatFragmentPreservesMeaning right = refl
compiledNatFragmentPreservesMeaning (natMultiplication left right)
  rewrite compiledNatFragmentPreservesMeaning left
        | compiledNatFragmentPreservesMeaning right = refl
compiledNatFragmentPreservesMeaning (natMonus left right)
  rewrite compiledNatFragmentPreservesMeaning left
        | compiledNatFragmentPreservesMeaning right = refl

-- ── 4a. Forward simulation for the Nat stack-code fragment ──
--
-- This target program is a linear sequence of the exact operation classes used
-- by the current raw-cell path: literal cells followed by ABI-ADD-OR-LEGACY,
-- ABI-MUL-OR-LEGACY, or ABI-MONUS-OR-LEGACY. The execution relation below
-- specifies their raw/raw stack behavior, with the top cell first. It is a
-- target-language specification; it is not an interpreter for arbitrary Forth.

data NatStackInstruction : Set where
  pushNatCellInstruction : Nat → NatStackInstruction
  abiAddOrLegacyInstruction : NatStackInstruction
  abiMulOrLegacyInstruction : NatStackInstruction
  abiMonusOrLegacyInstruction : NatStackInstruction

NatStackProgram : Set
NatStackProgram = List NatStackInstruction

compileNatStackProgram : NatExpr → NatStackProgram
compileNatStackProgram (natLiteral n) = pushNatCellInstruction n :: []
compileNatStackProgram (natAddition left right) =
  compileNatStackProgram left ++
    (compileNatStackProgram right ++ (abiAddOrLegacyInstruction :: []))
compileNatStackProgram (natMultiplication left right) =
  compileNatStackProgram left ++
    (compileNatStackProgram right ++ (abiMulOrLegacyInstruction :: []))
compileNatStackProgram (natMonus left right) =
  compileNatStackProgram left ++
    (compileNatStackProgram right ++ (abiMonusOrLegacyInstruction :: []))

-- A successful execution derivation describes the whole remaining program.
-- Binary instructions consume right :: left :: tail and push their result.
-- Consequently the source-to-target theorem also proves that an arbitrary
-- suffix of the caller's stack is framed unchanged.
data NatStackExec : NatStackProgram → List Nat → List Nat → Set where
  natStackDone :
    {stack : List Nat} →
    NatStackExec [] stack stack
  natStackPush :
    {n : Nat} {program : NatStackProgram}
    {initial final : List Nat} →
    NatStackExec program (n :: initial) final →
    NatStackExec (pushNatCellInstruction n :: program) initial final
  natStackAdd :
    {program : NatStackProgram} {left right : Nat}
    {initial final : List Nat} →
    NatStackExec program ((left + right) :: initial) final →
    NatStackExec (abiAddOrLegacyInstruction :: program)
      (right :: left :: initial) final
  natStackMultiply :
    {program : NatStackProgram} {left right : Nat}
    {initial final : List Nat} →
    NatStackExec program ((left * right) :: initial) final →
    NatStackExec (abiMulOrLegacyInstruction :: program)
      (right :: left :: initial) final
  natStackMonus :
    {program : NatStackProgram} {left right : Nat}
    {initial final : List Nat} →
    NatStackExec program (modelNatMonus left right :: initial) final →
    NatStackExec (abiMonusOrLegacyInstruction :: program)
      (right :: left :: initial) final

-- Append is composition: run the first program, then the second. This lemma is
-- the sequencing fact used by the compiler simulation, not an assumed axiom.
natStackExecAppend :
  {first second : NatStackProgram}
  {initial middle final : List Nat} →
  NatStackExec first initial middle →
  NatStackExec second middle final →
  NatStackExec (first ++ second) initial final
natStackExecAppend natStackDone secondRun = secondRun
natStackExecAppend (natStackPush firstRun) secondRun =
  natStackPush (natStackExecAppend firstRun secondRun)
natStackExecAppend (natStackAdd firstRun) secondRun =
  natStackAdd (natStackExecAppend firstRun secondRun)
natStackExecAppend (natStackMultiply firstRun) secondRun =
  natStackMultiply (natStackExecAppend firstRun secondRun)
natStackExecAppend (natStackMonus firstRun) secondRun =
  natStackMonus (natStackExecAppend firstRun secondRun)

-- The tree-shaped emission mirror linearizes to exactly the instruction
-- sequence used above. Unsupported/non-Nat fragments are explicitly outside
-- this projection instead of being assigned fabricated numeric semantics.
data NatStackProjection : Set where
  outsideNatStackProjection : NatStackProjection
  projectedNatStackProgram : NatStackProgram → NatStackProjection

projectNatStackFragment : EmittedFragment → NatStackProjection
projectNatStackFragment (rawNaturalCell n) =
  projectedNatStackProgram (pushNatCellInstruction n :: [])
projectNatStackFragment rawTrueCell = outsideNatStackProjection
projectNatStackFragment rawFalseCell = outsideNatStackProjection
projectNatStackFragment (abiAddAdapterCode left right)
  with projectNatStackFragment left | projectNatStackFragment right
... | projectedNatStackProgram leftCode | projectedNatStackProgram rightCode =
  projectedNatStackProgram
    (leftCode ++ (rightCode ++ (abiAddOrLegacyInstruction :: [])))
... | _ | _ = outsideNatStackProjection
projectNatStackFragment (abiMulAdapterCode left right)
  with projectNatStackFragment left | projectNatStackFragment right
... | projectedNatStackProgram leftCode | projectedNatStackProgram rightCode =
  projectedNatStackProgram
    (leftCode ++ (rightCode ++ (abiMulOrLegacyInstruction :: [])))
... | _ | _ = outsideNatStackProjection
projectNatStackFragment (abiMonusAdapterCode left right)
  with projectNatStackFragment left | projectNatStackFragment right
... | projectedNatStackProgram leftCode | projectedNatStackProgram rightCode =
  projectedNatStackProgram
    (leftCode ++ (rightCode ++ (abiMonusOrLegacyInstruction :: [])))
... | _ | _ = outsideNatStackProjection
projectNatStackFragment (checkedScalarCode mode n) = outsideNatStackProjection
projectNatStackFragment (checkedBooleanCode mode) = outsideNatStackProjection

emissionTreeAgreesWithStackProgram :
  (expr : NatExpr) →
  projectNatStackFragment (compileNatFragment expr) ≡
    projectedNatStackProgram (compileNatStackProgram expr)
emissionTreeAgreesWithStackProgram (natLiteral n) = refl
emissionTreeAgreesWithStackProgram (natAddition left right)
  rewrite emissionTreeAgreesWithStackProgram left
        | emissionTreeAgreesWithStackProgram right = refl
emissionTreeAgreesWithStackProgram (natMultiplication left right)
  rewrite emissionTreeAgreesWithStackProgram left
        | emissionTreeAgreesWithStackProgram right = refl
emissionTreeAgreesWithStackProgram (natMonus left right)
  rewrite emissionTreeAgreesWithStackProgram left
        | emissionTreeAgreesWithStackProgram right = refl

-- Forward simulation theorem:
--   executing compileNatStackProgram e on any tail yields
--   natExprMeaning e :: tail.
-- The tail is preserved by every derivation; this rules out modeled stack
-- underflow for these compiled expressions. The proof covers this explicit
-- Nat expression grammar, not all Agda terms or concrete Gforth internals.
natExpressionForwardSimulatesStackProgram :
  (expr : NatExpr) (tail : List Nat) →
  NatStackExec (compileNatStackProgram expr) tail
    (natExprMeaning expr :: tail)
natExpressionForwardSimulatesStackProgram (natLiteral n) tail =
  natStackPush natStackDone
natExpressionForwardSimulatesStackProgram (natAddition left right) tail =
  natStackExecAppend
    (natExpressionForwardSimulatesStackProgram left tail)
    (natStackExecAppend
      (natExpressionForwardSimulatesStackProgram right
        (natExprMeaning left :: tail))
      (natStackAdd natStackDone))
natExpressionForwardSimulatesStackProgram (natMultiplication left right) tail =
  natStackExecAppend
    (natExpressionForwardSimulatesStackProgram left tail)
    (natStackExecAppend
      (natExpressionForwardSimulatesStackProgram right
        (natExprMeaning left :: tail))
      (natStackMultiply natStackDone))
natExpressionForwardSimulatesStackProgram (natMonus left right) tail =
  natStackExecAppend
    (natExpressionForwardSimulatesStackProgram left tail)
    (natStackExecAppend
      (natExpressionForwardSimulatesStackProgram right
        (natExprMeaning left :: tail))
      (natStackMonus natStackDone))

-- A raw Gforth cell is finite, unlike Agda's mathematical Nat. Representability
-- therefore belongs in the theorem's input contract, not hidden in a claim that
-- arbitrary natural-number arithmetic is machine arithmetic. The bound is a
-- parameter: a concrete bridge must instantiate it from the selected runtime.
-- Every literal and every recursively computed intermediate result must fit.
data NatCellRepresentable (bound : Nat) : NatExpr → Set where
  natLiteralCellFits : {n : Nat} →
    n < suc bound →
    NatCellRepresentable bound (natLiteral n)
  natAdditionCellFits : {left right : NatExpr} →
    NatCellRepresentable bound left →
    NatCellRepresentable bound right →
    (natExprMeaning left + natExprMeaning right) < suc bound →
    NatCellRepresentable bound (natAddition left right)
  natMultiplicationCellFits : {left right : NatExpr} →
    NatCellRepresentable bound left →
    NatCellRepresentable bound right →
    (natExprMeaning left * natExprMeaning right) < suc bound →
    NatCellRepresentable bound (natMultiplication left right)
  natMonusCellFits : {left right : NatExpr} →
    NatCellRepresentable bound left →
    NatCellRepresentable bound right →
    modelNatMonus (natExprMeaning left) (natExprMeaning right) < suc bound →
    NatCellRepresentable bound (natMonus left right)

natExprValueFitsCellBound :
  (bound : Nat) (expr : NatExpr) →
  NatCellRepresentable bound expr →
  natExprMeaning expr < suc bound
natExprValueFitsCellBound bound (natLiteral n) (natLiteralCellFits fits) = fits
natExprValueFitsCellBound bound (natAddition left right)
  (natAdditionCellFits leftFits rightFits resultFits) = resultFits
natExprValueFitsCellBound bound (natMultiplication left right)
  (natMultiplicationCellFits leftFits rightFits resultFits) = resultFits
natExprValueFitsCellBound bound (natMonus left right)
  (natMonusCellFits leftFits rightFits resultFits) = resultFits

-- The pair theorem makes the machine-cell side condition visible at the same
-- call site as source-to-target simulation. The recursive witness carries the
-- bound for every intermediate node, while the stack theorem preserves any tail.
-- This remains a parameterized mathematical model, not an overflow check in Forth.
natExpressionBoundedForwardSimulatesStackProgram :
  (bound : Nat) (expr : NatExpr) (tail : List Nat) →
  NatCellRepresentable bound expr →
  NatStackExec (compileNatStackProgram expr) tail
    (natExprMeaning expr :: tail) ×
  (natExprMeaning expr < suc bound)
natExpressionBoundedForwardSimulatesStackProgram bound expr tail representable =
  natExpressionForwardSimulatesStackProgram expr tail ,
  natExprValueFitsCellBound bound expr representable

-- Model the runtime contract of a curried arithmetic word: the first pass
-- captures its left operand; the next application supplies the right operand.
-- The names correspond to the selected Forth preamble words, not extracted code.
data CurriedNatWord : Set where
  natAddWord natMonusWord natMultiplyWord : CurriedNatWord

data CurriedNatClosure : Set where
  pendingNatClosure : CurriedNatWord → Nat → CurriedNatClosure

lowerPartialNatAddition : Nat → CurriedNatClosure
lowerPartialNatAddition left = pendingNatClosure natAddWord left

lowerPartialNatMonus : Nat → CurriedNatClosure
lowerPartialNatMonus left = pendingNatClosure natMonusWord left

lowerPartialNatMultiplication : Nat → CurriedNatClosure
lowerPartialNatMultiplication left = pendingNatClosure natMultiplyWord left

applyCurriedNatClosure : CurriedNatClosure → Nat → Nat
applyCurriedNatClosure (pendingNatClosure natAddWord left) right = left + right
applyCurriedNatClosure (pendingNatClosure natMonusWord left) right =
  modelNatMonus left right
applyCurriedNatClosure (pendingNatClosure natMultiplyWord left) right =
  left * right

curriedNatAdditionPreservesMeaning :
  (left right : Nat) →
  applyCurriedNatClosure (lowerPartialNatAddition left) right ≡ left + right
curriedNatAdditionPreservesMeaning left right = refl

curriedNatMonusPreservesMeaning :
  (left right : Nat) →
  applyCurriedNatClosure (lowerPartialNatMonus left) right ≡
    modelNatMonus left right
curriedNatMonusPreservesMeaning left right = refl

curriedNatMultiplicationPreservesMeaning :
  (left right : Nat) →
  applyCurriedNatClosure (lowerPartialNatMultiplication left) right ≡ left * right
curriedNatMultiplicationPreservesMeaning left right = refl

-- Historical counterexample for the pre-fix curried-application path. The
-- earlier generated fixture emitted a lambda body `a c pass`; the raw/non-thunk
-- branch of `pass { x h -- result }` returns h unchanged. This witness is kept
-- as a regression specification, not a claim about the current output after
-- saturated primitive/builtin lowering was routed through ABI adapters. It is
-- a model of the observed body, not a proof extracted from the Haskell emitter.
historicalPassRawFallback : Nat → Nat → Nat
historicalPassRawFallback x h = h

historicalGeneratedScalarAddBody : Nat → Nat → Nat
historicalGeneratedScalarAddBody left right = historicalPassRawFallback left right

historicalGeneratedBodyReturnsRightArgument :
  (left right : Nat) → historicalGeneratedScalarAddBody left right ≡ right
historicalGeneratedBodyReturnsRightArgument left right = refl

historicalGeneratedScalarBodyAt20And5 :
  historicalGeneratedScalarAddBody 20 5 ≡ 5
historicalGeneratedScalarBodyAt20And5 = refl

sourceAdditionAt20And5 : 20 + 5 ≡ 25
sourceAdditionAt20And5 = refl

fiveIsNotTwentyFive : 5 ≡ 25 → ⊥
fiveIsNotTwentyFive ()

historicalGeneratedBodyCannotRefineAddition :
  (historicalGeneratedScalarAddBody 20 5 ≡ 20 + 5) → ⊥
historicalGeneratedBodyCannotRefineAddition bodyRefinement =
  fiveIsNotTwentyFive
    (transEq
      (transEq (symEq historicalGeneratedScalarBodyAt20And5) bodyRefinement)
      sourceAdditionAt20And5)

HistoricalGeneratedScalarRefinesAddition : Set
HistoricalGeneratedScalarRefinesAddition =
  (left right : Nat) →
  historicalGeneratedScalarAddBody left right ≡ left + right

historicalGeneratedScalarDoesNotRefineAddition :
  HistoricalGeneratedScalarRefinesAddition → ⊥
historicalGeneratedScalarDoesNotRefineAddition refinement =
  historicalGeneratedBodyCannotRefineAddition (refinement 20 5)

NoCheckedRepresentation : EmittedFragment → Set
NoCheckedRepresentation (rawNaturalCell n) = ⊤
NoCheckedRepresentation rawTrueCell = ⊤
NoCheckedRepresentation rawFalseCell = ⊤
NoCheckedRepresentation (abiAddAdapterCode left right) =
  NoCheckedRepresentation left × NoCheckedRepresentation right
NoCheckedRepresentation (abiMulAdapterCode left right) =
  NoCheckedRepresentation left × NoCheckedRepresentation right
NoCheckedRepresentation (abiMonusAdapterCode left right) =
  NoCheckedRepresentation left × NoCheckedRepresentation right
NoCheckedRepresentation (checkedScalarCode mode n) = ⊥
NoCheckedRepresentation (checkedBooleanCode mode) = ⊥

compilerNatFragmentHasNoCheckedRepresentation :
  (expr : NatExpr) → NoCheckedRepresentation (compileNatFragment expr)
compilerNatFragmentHasNoCheckedRepresentation (natLiteral n) = tt
compilerNatFragmentHasNoCheckedRepresentation (natAddition left right) =
  compilerNatFragmentHasNoCheckedRepresentation left ,
  compilerNatFragmentHasNoCheckedRepresentation right
compilerNatFragmentHasNoCheckedRepresentation (natMultiplication left right) =
  compilerNatFragmentHasNoCheckedRepresentation left ,
  compilerNatFragmentHasNoCheckedRepresentation right
compilerNatFragmentHasNoCheckedRepresentation (natMonus left right) =
  compilerNatFragmentHasNoCheckedRepresentation left ,
  compilerNatFragmentHasNoCheckedRepresentation right

-- Literal booleans in the pinned source are output as raw -1/0 cells, not as
-- ABI boolean handles; the separate constructors record their source meaning,
-- not runtime type tags.
data BoolLiteral : Set where
  trueLiteral falseLiteral : BoolLiteral

compileBoolFragment : BoolLiteral → EmittedFragment
compileBoolFragment trueLiteral = rawTrueCell
compileBoolFragment falseLiteral = rawFalseCell

compilerBoolLiteralHasNoCheckedRepresentation :
  (literal : BoolLiteral) → NoCheckedRepresentation (compileBoolFragment literal)
compilerBoolLiteralHasNoCheckedRepresentation trueLiteral = tt
compilerBoolLiteralHasNoCheckedRepresentation falseLiteral = tt

data CheckedABIValue : StackItem → Set where
  checkedLinearNatural : CheckedABIValue (valueItem naturalTy)
  checkedModalNatural : CheckedABIValue (valueItem (!Ty naturalTy))
  checkedLinearBoolean : CheckedABIValue (valueItem booleanTy)
  checkedModalBoolean : CheckedABIValue (valueItem (!Ty booleanTy))

rawNaturalCannotBeCheckedABIValue :
  CheckedABIValue rawNatItem → ⊥
rawNaturalCannotBeCheckedABIValue ()

rawBooleanCannotBeCheckedABIValue :
  CheckedABIValue rawBoolItem → ⊥
rawBooleanCannotBeCheckedABIValue ()

-- Every natural-literal/addition expression in this fragment leaves a raw
-- natural cell as its result. It cannot carry the mode-indexed descriptor
-- witness required by a checked ABI operand.
compiledNatResultShape : NatExpr → StackItem
compiledNatResultShape _ = rawNatItem

compiledNatResultCannotBeChecked :
  (expr : NatExpr) →
  CheckedABIValue (compiledNatResultShape expr) → ⊥
compiledNatResultCannotBeChecked expr = rawNaturalCannotBeCheckedABIValue

compiledBooleanResultShape : BoolLiteral → StackItem
compiledBooleanResultShape _ = rawBoolItem

compiledBoolResultCannotBeChecked :
  (literal : BoolLiteral) →
  CheckedABIValue (compiledBooleanResultShape literal) → ⊥
compiledBoolResultCannotBeChecked literal = rawBooleanCannotBeCheckedABIValue

-- Import and reuse the closed stack-effect lemmas rather than assuming that
-- raw output is accepted by checked operations.
rawCompilerOperandsCannotUseCheckedAddition :
  {tail output : StackShape} →
  StackEffect pNatAdd (rawNatItem :: rawNatItem :: tail) output → ⊥
rawCompilerOperandsCannotUseCheckedAddition =
  rawLiteralCannotUseCheckedAddition

rawCompilerOperandsCannotUseCheckedEquality :
  {tail output : StackShape} →
  StackEffect pNatEq (rawNatItem :: rawNatItem :: tail) output → ⊥
rawCompilerOperandsCannotUseCheckedEquality =
  rawLiteralCannotUseCheckedEquality

-- For a checked scalar to be introduced from a raw literal, the compiler must
-- emit a pMakeScalar effect with a source-mode token. The theorem's type makes
-- the missing evidence explicit; the upstream lowering above does not supply it.
checkedScalarRequiresModeWitness :
  {m : SourceMode} {tail : StackShape} →
  StackEffect pMakeScalar
    (modeTokenItem m :: rawNatItem :: tail)
    (valueItem (naturalTypeFor m) :: tail)
checkedScalarRequiresModeWitness = rawLiteralNeedsModeWitness


-- ── 5. Explicit compiler-emission table ──
--
-- This table mirrors the current ToForth.hs TPrim case and literal translation.
-- The supported primitive vocabulary is narrower than Agda's full primitive
-- vocabulary. Unsupported operations go through fthError, which emits a
-- diagnostic followed by ABI-ERR-COMPILED-UNSUPPORTED (a catchable THROW).
--
-- This is a manually maintained semantic mirror, not a generated proof about
-- Haskell. The per-file provenance check pins the source; it does not prove
-- semantic equivalence between this table and the Haskell implementation.

data SupportedBackendPrimitive : Set where
  backendAdd backendSub backendMul backendQuot backendRem : SupportedBackendPrimitive
  backendIf backendIntegerEq backendGeq backendLt : SupportedBackendPrimitive

data BackendPrimitive : Set where
  backendSupported : SupportedBackendPrimitive → BackendPrimitive
  backendUnsupported : BackendPrimitive

data BackendEmission : Set where
  emitBinaryAdapterAdd emitBinaryAdapterSub emitBinaryAdapterMul emitBinaryAdapterQuot emitBinaryAdapterRem : BackendEmission
  emitInlineIf emitBinaryAdapterEq emitBinaryAdapterGeq emitBinaryAdapterLt : BackendEmission
  emitDiagnosticThrow : BackendEmission

emitSupportedPrimitive : SupportedBackendPrimitive → BackendEmission
emitSupportedPrimitive backendAdd = emitBinaryAdapterAdd
emitSupportedPrimitive backendSub = emitBinaryAdapterSub
emitSupportedPrimitive backendMul = emitBinaryAdapterMul
emitSupportedPrimitive backendQuot = emitBinaryAdapterQuot
emitSupportedPrimitive backendRem = emitBinaryAdapterRem
emitSupportedPrimitive backendIf = emitInlineIf
emitSupportedPrimitive backendIntegerEq = emitBinaryAdapterEq
emitSupportedPrimitive backendGeq = emitBinaryAdapterGeq
emitSupportedPrimitive backendLt = emitBinaryAdapterLt

emitBackendPrimitive : BackendPrimitive → BackendEmission
emitBackendPrimitive (backendSupported p) = emitSupportedPrimitive p
emitBackendPrimitive backendUnsupported = emitDiagnosticThrow

data SupportedEmission : BackendEmission → Set where
  adapterAddEmission : SupportedEmission emitBinaryAdapterAdd
  adapterSubEmission : SupportedEmission emitBinaryAdapterSub
  adapterMulEmission : SupportedEmission emitBinaryAdapterMul
  adapterQuotEmission : SupportedEmission emitBinaryAdapterQuot
  adapterRemEmission : SupportedEmission emitBinaryAdapterRem
  inlineIfEmission : SupportedEmission emitInlineIf
  adapterEqEmission : SupportedEmission emitBinaryAdapterEq
  adapterGeqEmission : SupportedEmission emitBinaryAdapterGeq
  adapterLtEmission : SupportedEmission emitBinaryAdapterLt

-- Every supported primitive maps to a typed ABI adapter or an inline conditional.
supportedPrimitiveEmissionIsSpecified :
  (p : SupportedBackendPrimitive) → SupportedEmission (emitSupportedPrimitive p)
supportedPrimitiveEmissionIsSpecified backendAdd = adapterAddEmission
supportedPrimitiveEmissionIsSpecified backendSub = adapterSubEmission
supportedPrimitiveEmissionIsSpecified backendMul = adapterMulEmission
supportedPrimitiveEmissionIsSpecified backendQuot = adapterQuotEmission
supportedPrimitiveEmissionIsSpecified backendRem = adapterRemEmission
supportedPrimitiveEmissionIsSpecified backendIf = inlineIfEmission
supportedPrimitiveEmissionIsSpecified backendIntegerEq = adapterEqEmission
supportedPrimitiveEmissionIsSpecified backendGeq = adapterGeqEmission
supportedPrimitiveEmissionIsSpecified backendLt = adapterLtEmission

unsupportedPrimitiveUsesCatchableDiagnostic :
  emitBackendPrimitive backendUnsupported ≡ emitDiagnosticThrow
unsupportedPrimitiveUsesCatchableDiagnostic = refl

-- Literal support mirrors ToForth.hs's Literal case. Nat becomes decimal
-- text consumed by ABI-PARSE-NAT; unsupported literal forms use fthError,
-- which emits ABI-ERROR-COMPILED-UNSUPPORTED and throws catchably.
data UnsupportedLiteralKind : Set where
  unsupportedWord64 unsupportedFloat unsupportedString unsupportedChar
    unsupportedQName unsupportedMeta : UnsupportedLiteralKind

data BackendLiteral : Set where
  backendNatLiteral : Nat → BackendLiteral
  backendTrueLiteral backendFalseLiteral : BackendLiteral
  backendUnsupportedLiteral : UnsupportedLiteralKind → BackendLiteral

data LiteralEmission : Set where
  emitNaturalCell emitTrueCell emitFalseCell : LiteralEmission
  emitLiteralDiagnosticThrow : UnsupportedLiteralKind → LiteralEmission

emitBackendLiteral : BackendLiteral → LiteralEmission
emitBackendLiteral (backendNatLiteral n) = emitNaturalCell
emitBackendLiteral backendTrueLiteral = emitTrueCell
emitBackendLiteral backendFalseLiteral = emitFalseCell
emitBackendLiteral (backendUnsupportedLiteral kind) =
  emitLiteralDiagnosticThrow kind

unsupportedLiteralUsesCatchableDiagnostic :
  (kind : UnsupportedLiteralKind) →
  emitBackendLiteral (backendUnsupportedLiteral kind) ≡
    emitLiteralDiagnosticThrow kind
unsupportedLiteralUsesCatchableDiagnostic kind = refl

unsupportedStringLiteralUsesCatchableDiagnostic :
  emitBackendLiteral (backendUnsupportedLiteral unsupportedString) ≡
    emitLiteralDiagnosticThrow unsupportedString
unsupportedStringLiteralUsesCatchableDiagnostic = refl

-- The term-level cases below record additional concrete ToForth.hs branches.
-- Unit, sorts and erased terms emit the Forth zero value; Boolean constructors
-- emit -1/0; Boolean cases become IF/ELSE/THEN; coercions are transparent.
-- TError TUnreachable and TMeta use fthError (the generic catchable diagnostic),
-- while a missing fthPatternMatch fallback uses ABI-ERROR-UNREACHABLE.
data BackendTermCase : Set where
  backendUnitTerm backendSortTerm backendErasedTerm : BackendTermCase
  backendTrueConstructor backendFalseConstructor : BackendTermCase
  backendBooleanCase backendCoerceTerm : BackendTermCase
  backendPanicTerm backendUnsolvedMetaTerm backendUnmatchedPatternFallback
    : BackendTermCase

data TermEmission : Set where
  emitZeroCell emitTrueFlag emitFalseFlag emitInlineConditional
    emitTransparentTerm emitDiagnosticThrow emitUnreachableErrorThrow
    : TermEmission

emitBackendTermCase : BackendTermCase → TermEmission
emitBackendTermCase backendUnitTerm = emitZeroCell
emitBackendTermCase backendSortTerm = emitZeroCell
emitBackendTermCase backendErasedTerm = emitZeroCell
emitBackendTermCase backendTrueConstructor = emitTrueFlag
emitBackendTermCase backendFalseConstructor = emitFalseFlag
emitBackendTermCase backendBooleanCase = emitInlineConditional
emitBackendTermCase backendCoerceTerm = emitTransparentTerm
emitBackendTermCase backendPanicTerm = emitDiagnosticThrow
emitBackendTermCase backendUnsolvedMetaTerm = emitDiagnosticThrow
emitBackendTermCase backendUnmatchedPatternFallback = emitUnreachableErrorThrow

panicTermUsesCatchableDiagnostic :
  emitBackendTermCase backendPanicTerm ≡ emitDiagnosticThrow
panicTermUsesCatchableDiagnostic = refl

unsolvedMetaUsesCatchableDiagnostic :
  emitBackendTermCase backendUnsolvedMetaTerm ≡ emitDiagnosticThrow
unsolvedMetaUsesCatchableDiagnostic = refl

unmatchedPatternUsesCatchableUnreachableError :
  emitBackendTermCase backendUnmatchedPatternFallback ≡
    emitUnreachableErrorThrow
unmatchedPatternUsesCatchableUnreachableError = refl

-- ── 6. Runtime dispatch table mirrored from data/FLib.fth ──
--
-- ABI-DISPATCH-BINARY's branch structure is:
--   * two unregistered cells -> legacy operation;
--   * two registered scalar handles -> checked operation;
--   * one registered and one unregistered value -> reject mixed representation;
--   * two registered values where either is not a scalar -> reject wrong kind.
--
-- The Agda function below makes that decision table explicit and proves its
-- equations. It is a model of inspected Forth behavior, not extraction from it.

data RuntimeOperandClass : Set where
  rawUnregistered trackedScalar trackedNonScalar : RuntimeOperandClass

data BinaryDispatchRoute : Set where
  dispatchCheckedABI dispatchLegacy dispatchRejectMixed dispatchRejectWrongKind : BinaryDispatchRoute

runtimeBinaryRoute : RuntimeOperandClass → RuntimeOperandClass → BinaryDispatchRoute
runtimeBinaryRoute rawUnregistered rawUnregistered = dispatchLegacy
runtimeBinaryRoute trackedScalar trackedScalar = dispatchCheckedABI
runtimeBinaryRoute trackedScalar rawUnregistered = dispatchRejectMixed
runtimeBinaryRoute trackedNonScalar rawUnregistered = dispatchRejectMixed
runtimeBinaryRoute rawUnregistered trackedScalar = dispatchRejectMixed
runtimeBinaryRoute rawUnregistered trackedNonScalar = dispatchRejectMixed
runtimeBinaryRoute trackedNonScalar trackedScalar = dispatchRejectWrongKind
runtimeBinaryRoute trackedNonScalar trackedNonScalar = dispatchRejectWrongKind
runtimeBinaryRoute trackedScalar trackedNonScalar = dispatchRejectWrongKind

rawPairUsesLegacyRoute :
  runtimeBinaryRoute rawUnregistered rawUnregistered ≡ dispatchLegacy
rawPairUsesLegacyRoute = refl

checkedScalarPairUsesCheckedRoute :
  runtimeBinaryRoute trackedScalar trackedScalar ≡ dispatchCheckedABI
checkedScalarPairUsesCheckedRoute = refl

trackedScalarPlusRawFailsClosed :
  runtimeBinaryRoute trackedScalar rawUnregistered ≡ dispatchRejectMixed
trackedScalarPlusRawFailsClosed = refl

rawPlusTrackedScalarFailsClosed :
  runtimeBinaryRoute rawUnregistered trackedScalar ≡ dispatchRejectMixed
rawPlusTrackedScalarFailsClosed = refl

trackedNonScalarPlusRawFailsClosed :
  runtimeBinaryRoute trackedNonScalar rawUnregistered ≡ dispatchRejectMixed
trackedNonScalarPlusRawFailsClosed = refl

rawPlusTrackedNonScalarFailsClosed :
  runtimeBinaryRoute rawUnregistered trackedNonScalar ≡ dispatchRejectMixed
rawPlusTrackedNonScalarFailsClosed = refl


-- The concrete runtime's combineModes has one extra state: unannotated.
-- Model the exact rule implemented by data/FLib.fth: unannotated is absorbing,
-- linear is absorbing over annotated modes, and only modal/modal joins to modal.
runtimeCombineModes : RuntimeMode → RuntimeMode → RuntimeMode
runtimeCombineModes unannotated _ = unannotated
runtimeCombineModes _ unannotated = unannotated
runtimeCombineModes linearMode linearMode = linearMode
runtimeCombineModes linearMode modalMode = linearMode
runtimeCombineModes modalMode linearMode = linearMode
runtimeCombineModes modalMode modalMode = modalMode

unannotatedIsAbsorbingLeft :
  (m : RuntimeMode) → runtimeCombineModes unannotated m ≡ unannotated
unannotatedIsAbsorbingLeft m = refl

unannotatedIsAbsorbingRight :
  (m : RuntimeMode) → runtimeCombineModes m unannotated ≡ unannotated
unannotatedIsAbsorbingRight unannotated = refl
unannotatedIsAbsorbingRight linearMode = refl
unannotatedIsAbsorbingRight modalMode = refl

linearWithAnnotatedRight :
  (m : RuntimeMode) → AnnotatedMode m →
  runtimeCombineModes linearMode m ≡ linearMode
linearWithAnnotatedRight linearMode checkedLinearMode = refl
linearWithAnnotatedRight modalMode checkedModalMode = refl

linearWithAnnotatedLeft :
  (m : RuntimeMode) → AnnotatedMode m →
  runtimeCombineModes m linearMode ≡ linearMode
linearWithAnnotatedLeft linearMode checkedLinearMode = refl
linearWithAnnotatedLeft modalMode checkedModalMode = refl

modalOnlyJoinsToModal :
  runtimeCombineModes modalMode modalMode ≡ modalMode
modalOnlyJoinsToModal = refl

-- ── 7. Constructive transaction contract for ABI-BINARY ──
--
-- This models the order in data/FLib.fth's ABI-BINARY:
--   1. validate both handles as live checked scalars (precondition here);
--   2. reject aliased linear operands;
--   3. evaluate the raw arithmetic/comparison operator;
--   4. allocate the result with the joined operand mode;
--   5. consume linear inputs only after result allocation succeeds.
--
-- The runtime blob checked by CI is the exact source examined for this contract.
-- These are proofs of the following explicit transition model, not a proof
-- extracted from the concrete Forth implementation.

data BinaryAliasStatus : Set where
  noLinearAlias linearAliasDetected : BinaryAliasStatus

data OperationOutcome (A : Set) : Set where
  operationReturned : A → OperationOutcome A
  operationThrew : RuntimeError → OperationOutcome A

data BinaryCommitResult (leftMode rightMode : SourceMode) : Set where
  binaryFailure :
    RuntimeError → Life → Life → BinaryCommitResult leftMode rightMode
  binarySuccess :
    Nat → SourceMode → Life → Life → BinaryCommitResult leftMode rightMode

lifeAfterBinarySuccess : SourceMode → Life
lifeAfterBinarySuccess linear = consumed
lifeAfterBinarySuccess modal = live

checkedBinaryTransaction :
  {leftMode rightMode : SourceMode} →
  BinaryAliasStatus →
  OperationOutcome Nat →
  (Nat → SourceMode → OperationOutcome Nat) →
  BinaryCommitResult leftMode rightMode
checkedBinaryTransaction {leftMode} {rightMode} linearAliasDetected operation makeResult =
  binaryFailure aliasedLinearOperands live live
checkedBinaryTransaction {leftMode} {rightMode} noLinearAlias
    (operationThrew err) makeResult =
  binaryFailure err live live
checkedBinaryTransaction {leftMode} {rightMode} noLinearAlias
    (operationReturned rawValue) makeResult
  with makeResult rawValue (joinSourceMode leftMode rightMode)
... | operationThrew err = binaryFailure err live live
... | operationReturned resultHandle =
  binarySuccess resultHandle (joinSourceMode leftMode rightMode)
    (lifeAfterBinarySuccess leftMode) (lifeAfterBinarySuccess rightMode)

-- These equations prove that no failure before the ownership-commit writes
-- consumes either logical operand.
linearAliasRejectedBeforeOperation :
  {leftMode rightMode : SourceMode} →
  (operation : OperationOutcome Nat) →
  (makeResult : Nat → SourceMode → OperationOutcome Nat) →
  checkedBinaryTransaction {leftMode} {rightMode}
    linearAliasDetected operation makeResult ≡
  binaryFailure aliasedLinearOperands live live
linearAliasRejectedBeforeOperation operation makeResult = refl

operationFailurePreservesOperands :
  {leftMode rightMode : SourceMode} →
  (err : RuntimeError) →
  (makeResult : Nat → SourceMode → OperationOutcome Nat) →
  checkedBinaryTransaction {leftMode} {rightMode}
    noLinearAlias (operationThrew err) makeResult ≡
  binaryFailure err live live
operationFailurePreservesOperands err makeResult = refl

resultAllocationFailurePreservesOperands :
  {leftMode rightMode : SourceMode} →
  (rawValue : Nat) →
  (err : RuntimeError) →
  checkedBinaryTransaction {leftMode} {rightMode}
    noLinearAlias (operationReturned rawValue)
    (λ _ _ → operationThrew err) ≡
  binaryFailure err live live
resultAllocationFailurePreservesOperands rawValue err = refl

successfulBinaryCommitsJoinedModeAndOwnership :
  {leftMode rightMode : SourceMode} →
  (rawValue resultHandle : Nat) →
  checkedBinaryTransaction {leftMode} {rightMode}
    noLinearAlias (operationReturned rawValue)
    (λ _ _ → operationReturned resultHandle) ≡
  binarySuccess resultHandle (joinSourceMode leftMode rightMode)
    (lifeAfterBinarySuccess leftMode) (lifeAfterBinarySuccess rightMode)
successfulBinaryCommitsJoinedModeAndOwnership rawValue resultHandle = refl

-- WP for the checked binary transaction, with normal and exceptional postconditions.
-- The failure postcondition observes both input ownership states.
BinaryWPPost :
  {leftMode rightMode : SourceMode} →
  (normal : Nat → SourceMode → Life → Life → Set) →
  (exceptional : RuntimeError → Life → Life → Set) →
  BinaryCommitResult leftMode rightMode → Set
BinaryWPPost normal exceptional (binaryFailure err leftLife rightLife) =
  exceptional err leftLife rightLife
BinaryWPPost normal exceptional (binarySuccess value mode leftLife rightLife) =
  normal value mode leftLife rightLife

checkedBinaryWP :
  {leftMode rightMode : SourceMode} →
  BinaryAliasStatus →
  OperationOutcome Nat →
  (Nat → SourceMode → OperationOutcome Nat) →
  (normal : Nat → SourceMode → Life → Life → Set) →
  (exceptional : RuntimeError → Life → Life → Set) → Set
checkedBinaryWP {leftMode} {rightMode} alias operation makeResult normal exceptional =
  BinaryWPPost {leftMode = leftMode} {rightMode = rightMode} normal exceptional
    (checkedBinaryTransaction {leftMode = leftMode} {rightMode = rightMode}
      alias operation makeResult)

-- A primitive THROW happens before the linear-ownership commit writes.
checkedBinaryWPArithmeticFailurePreservesOperands :
  {leftMode rightMode : SourceMode} →
  (err : RuntimeError) →
  (makeResult : Nat → SourceMode → OperationOutcome Nat) →
  (normal : Nat → SourceMode → Life → Life → Set) →
  (exceptional : RuntimeError → Life → Life → Set) →
  exceptional err live live →
  checkedBinaryWP {leftMode = leftMode} {rightMode = rightMode}
    noLinearAlias (operationThrew err) makeResult normal exceptional
checkedBinaryWPArithmeticFailurePreservesOperands err makeResult normal exceptional proof = proof

-- Result-allocation failure also occurs before either operand is consumed.
checkedBinaryWPResultAllocationFailurePreservesOperands :
  {leftMode rightMode : SourceMode} →
  (rawValue : Nat) →
  (err : RuntimeError) →
  (normal : Nat → SourceMode → Life → Life → Set) →
  (exceptional : RuntimeError → Life → Life → Set) →
  exceptional err live live →
  checkedBinaryWP {leftMode = leftMode} {rightMode = rightMode}
    noLinearAlias (operationReturned rawValue)
    (λ value mode → operationThrew err) normal exceptional
checkedBinaryWPResultAllocationFailurePreservesOperands rawValue err normal exceptional proof = proof

linearInputConsumedOnSuccessfulCommit :
  lifeAfterBinarySuccess linear ≡ consumed
linearInputConsumedOnSuccessfulCommit = refl

modalInputRemainsLiveOnSuccessfulCommit :
  lifeAfterBinarySuccess modal ≡ live
modalInputRemainsLiveOnSuccessfulCommit = refl

-- ── 8. Verification boundary ──
--
-- To close end-to-end refinement, future work must prove that:
-- (1) each supported compiler translation corresponds to the stated emission;
-- (2) every generated application/closure/constructor/conditional routes through
--     a specified ABI path;
-- (3) each concrete Forth word preserves WellFormed on normal and exceptional
--     exits; and
-- (4) unsupported cases fail through a specified, catchable error boundary.
-- These obligations remain open while the Haskell backend emits raw literals
-- and legacy operator forms.


-- Full-state WP is the contract mechanism: stack, descriptor heap, roots,
-- metadata identities and exception state belong in S. The former generic frame
-- theorem merely threaded an unrelated F value unchanged by construction; it did
-- not prove footprint locality for any Forth word, so it was removed. Reintroduce
-- a frame theorem only with concrete read/write-footprint evidence for a runtime
-- operation, not a stack-tail product that is untouched by definition.


-- ── Scalar bridge correspondence for the opt-in runtime gate ──
--
-- This bridge has two deliberately distinct views:
--   * bridgeNormalizeNat/Bool are source-semantic views; a closed literal has a
--     modal interpretation because it has no linear dependencies.
--   * bridgeRuntimeModeNat/Bool model the actual representation boundary:
--     FLib.fth's raw/raw dispatch leaves raw cells unannotated, while only checked
--     handles carry MODE-LINEAR or MODE-MODAL metadata.
-- Thus source-level modal interpretation is NOT itself evidence of a runtime !.
-- This mismatch is a proved limitation of the current emitter, not a hidden
-- assumption in the Girard-preservation claim.
data BridgeNatCell : Set where
  bridgeRawNat : Nat → BridgeNatCell
  bridgeCheckedNat : Nat → SourceMode → BridgeNatCell

bridgeNatPayload : BridgeNatCell → Nat
bridgeNatPayload (bridgeRawNat n) = n
bridgeNatPayload (bridgeCheckedNat n m) = n

bridgeNormalizeNat : BridgeNatCell → Nat × SourceMode
bridgeNormalizeNat (bridgeRawNat n) = n , modal
bridgeNormalizeNat (bridgeCheckedNat n m) = n , m

bridgeNatPayloadPreserved :
  (v : BridgeNatCell) → fst (bridgeNormalizeNat v) ≡ bridgeNatPayload v
bridgeNatPayloadPreserved (bridgeRawNat n) = refl
bridgeNatPayloadPreserved (bridgeCheckedNat n m) = refl

bridgeRawNatIsModal :
  (n : Nat) → snd (bridgeNormalizeNat (bridgeRawNat n)) ≡ modal
bridgeRawNatIsModal n = refl

bridgeCheckedModePreserved :
  (n : Nat) (m : SourceMode) →
  snd (bridgeNormalizeNat (bridgeCheckedNat n m)) ≡ m
bridgeCheckedModePreserved n m = refl

-- Runtime tags are distinct from the logical source interpretation above.
-- Raw Nat cells emitted by ToForth.hs contain no descriptor/mode witness.
bridgeRuntimeModeNat : BridgeNatCell → RuntimeMode
bridgeRuntimeModeNat (bridgeRawNat n) = unannotated
bridgeRuntimeModeNat (bridgeCheckedNat n m) = sourceMode m

rawNatRuntimeModeIsUnannotated :
  (n : Nat) → bridgeRuntimeModeNat (bridgeRawNat n) ≡ unannotated
rawNatRuntimeModeIsUnannotated n = refl

checkedNatRuntimeModePreserved :
  (n : Nat) (m : SourceMode) →
  bridgeRuntimeModeNat (bridgeCheckedNat n m) ≡ sourceMode m
checkedNatRuntimeModePreserved n m = refl

unannotatedCannotBeModal : unannotated ≡ modalMode → ⊥
unannotatedCannotBeModal ()

unannotatedCannotBeLinear : unannotated ≡ linearMode → ⊥
unannotatedCannotBeLinear ()

rawNatCannotEstablishModalSourceMode :
  (n : Nat) →
  bridgeRuntimeModeNat (bridgeRawNat n) ≡ sourceMode modal → ⊥
rawNatCannotEstablishModalSourceMode n ()

rawNatCannotEstablishLinearSourceMode :
  (n : Nat) →
  bridgeRuntimeModeNat (bridgeRawNat n) ≡ sourceMode linear → ⊥
rawNatCannotEstablishLinearSourceMode n ()

data BridgeBoolCell : Set where
  bridgeRawBool : Bool → BridgeBoolCell
  bridgeCheckedBool : Bool → SourceMode → BridgeBoolCell

bridgeBoolPayload : BridgeBoolCell → Bool
bridgeBoolPayload (bridgeRawBool b) = b
bridgeBoolPayload (bridgeCheckedBool b m) = b

bridgeNormalizeBool : BridgeBoolCell → Bool × SourceMode
bridgeNormalizeBool (bridgeRawBool b) = b , modal
bridgeNormalizeBool (bridgeCheckedBool b m) = b , m

bridgeBoolPayloadPreserved :
  (v : BridgeBoolCell) → fst (bridgeNormalizeBool v) ≡ bridgeBoolPayload v
bridgeBoolPayloadPreserved (bridgeRawBool b) = refl
bridgeBoolPayloadPreserved (bridgeCheckedBool b m) = refl

bridgeRawBoolIsModal :
  (b : Bool) → snd (bridgeNormalizeBool (bridgeRawBool b)) ≡ modal
bridgeRawBoolIsModal b = refl

bridgeRuntimeModeBool : BridgeBoolCell → RuntimeMode
bridgeRuntimeModeBool (bridgeRawBool b) = unannotated
bridgeRuntimeModeBool (bridgeCheckedBool b m) = sourceMode m

rawBoolRuntimeModeIsUnannotated :
  (b : Bool) → bridgeRuntimeModeBool (bridgeRawBool b) ≡ unannotated
rawBoolRuntimeModeIsUnannotated b = refl

checkedBoolRuntimeModePreserved :
  (b : Bool) (m : SourceMode) →
  bridgeRuntimeModeBool (bridgeCheckedBool b m) ≡ sourceMode m
checkedBoolRuntimeModePreserved b m = refl

rawBoolCannotEstablishModalSourceMode :
  (b : Bool) →
  bridgeRuntimeModeBool (bridgeRawBool b) ≡ sourceMode modal → ⊥
rawBoolCannotEstablishModalSourceMode b ()

rawBoolCannotEstablishLinearSourceMode :
  (b : Bool) →
  bridgeRuntimeModeBool (bridgeRawBool b) ≡ sourceMode linear → ⊥
rawBoolCannotEstablishLinearSourceMode b ()

bridgeNatSub : Nat → Nat → Nat
bridgeNatSub n zero = n
bridgeNatSub zero (suc m) = zero
bridgeNatSub (suc n) (suc m) = bridgeNatSub n m

bridgeNatEq : Nat → Nat → Bool
bridgeNatEq zero zero = true
bridgeNatEq zero (suc m) = false
bridgeNatEq (suc n) zero = false
bridgeNatEq (suc n) (suc m) = bridgeNatEq n m

bridgeEvalAdd : BridgeNatCell → BridgeNatCell → Nat × SourceMode
bridgeEvalAdd left right =
  (fst (bridgeNormalizeNat left) + fst (bridgeNormalizeNat right)) ,
  joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))

bridgeEvalSub : BridgeNatCell → BridgeNatCell → Nat × SourceMode
bridgeEvalSub left right =
  bridgeNatSub (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
  joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))

bridgeEvalEq : BridgeNatCell → BridgeNatCell → Bool × SourceMode
bridgeEvalEq left right =
  bridgeNatEq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
  joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))

bridgeAddPayloadCorrespondence :
  (left right : BridgeNatCell) →
  fst (bridgeEvalAdd left right) ≡
    fst (bridgeNormalizeNat left) + fst (bridgeNormalizeNat right)
bridgeAddPayloadCorrespondence left right = refl

bridgeSubPayloadCorrespondence :
  (left right : BridgeNatCell) →
  fst (bridgeEvalSub left right) ≡
    bridgeNatSub (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
bridgeSubPayloadCorrespondence left right = refl

bridgeEqualityPayloadCorrespondence :
  (left right : BridgeNatCell) →
  fst (bridgeEvalEq left right) ≡
    bridgeNatEq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
bridgeEqualityPayloadCorrespondence left right = refl

bridgeSelect : Bool → BridgeNatCell → BridgeNatCell → BridgeNatCell
bridgeSelect true yes no = yes
bridgeSelect false yes no = no

bridgeTrueSelectsLeft :
  (yes no : BridgeNatCell) → bridgeSelect true yes no ≡ yes
bridgeTrueSelectsLeft yes no = refl

bridgeFalseSelectsRight :
  (yes no : BridgeNatCell) → bridgeSelect false yes no ≡ no
bridgeFalseSelectsRight yes no = refl


-- Model the rest of the checked scalar ABI vocabulary, including the domain
-- error for quotient/remainder by zero and the operation-specific joined mode.
bridgeNatMul : Nat → Nat → Nat
bridgeNatMul left right = left * right

bridgeNatLt : Nat → Nat → Bool
bridgeNatLt zero zero = false
bridgeNatLt zero (suc right) = true
bridgeNatLt (suc left) zero = false
bridgeNatLt (suc left) (suc right) = bridgeNatLt left right

bridgeNatGeq : Nat → Nat → Bool
bridgeNatGeq zero zero = true
bridgeNatGeq zero (suc right) = false
bridgeNatGeq (suc left) zero = true
bridgeNatGeq (suc left) (suc right) = bridgeNatGeq left right

bridgeEvalMul : BridgeNatCell → BridgeNatCell → Nat × SourceMode
bridgeEvalMul left right =
  bridgeNatMul (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
  joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))

bridgeEvalGeq : BridgeNatCell → BridgeNatCell → Bool × SourceMode
bridgeEvalGeq left right =
  bridgeNatGeq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
  joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))

bridgeEvalLt : BridgeNatCell → BridgeNatCell → Bool × SourceMode
bridgeEvalLt left right =
  bridgeNatLt (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
  joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))

bridgeMulPayloadCorrespondence :
  (left right : BridgeNatCell) →
  fst (bridgeEvalMul left right) ≡
    fst (bridgeNormalizeNat left) * fst (bridgeNormalizeNat right)
bridgeMulPayloadCorrespondence left right = refl

bridgeGeqPayloadCorrespondence :
  (left right : BridgeNatCell) →
  fst (bridgeEvalGeq left right) ≡
    bridgeNatGeq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
bridgeGeqPayloadCorrespondence left right = refl

bridgeLtPayloadCorrespondence :
  (left right : BridgeNatCell) →
  fst (bridgeEvalLt left right) ≡
    bridgeNatLt (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
bridgeLtPayloadCorrespondence left right = refl

bridgeNatDivModFuel : Nat → Nat → Nat → Nat → Nat × Nat
bridgeNatDivModFuel zero dividend divisor quotient = quotient , dividend
bridgeNatDivModFuel (suc fuel) dividend divisor quotient
  with bridgeNatLt dividend divisor
... | true = quotient , dividend
... | false =
  bridgeNatDivModFuel fuel (bridgeNatSub dividend divisor) divisor (suc quotient)

data BridgeDivision : Set where
  bridgeDivisionByZero : BridgeDivision
  bridgeDivisionResult : Nat → Nat → BridgeDivision

bridgeNatDivMod : Nat → Nat → BridgeDivision
bridgeNatDivMod dividend zero = bridgeDivisionByZero
bridgeNatDivMod dividend (suc divisor)
  with bridgeNatDivModFuel dividend dividend (suc divisor) zero
... | quotient , remainder = bridgeDivisionResult quotient remainder

data BridgeNatEval : Set where
  bridgeNatFailure : RuntimeError → BridgeNatEval
  bridgeNatSuccess : Nat → SourceMode → BridgeNatEval

bridgeEvalQuot : BridgeNatCell → BridgeNatCell → BridgeNatEval
bridgeEvalQuot left right
  with bridgeNatDivMod (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
... | bridgeDivisionByZero = bridgeNatFailure arithmeticDomainError
... | bridgeDivisionResult quotient remainder =
  bridgeNatSuccess quotient
    (joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right)))

bridgeEvalRem : BridgeNatCell → BridgeNatCell → BridgeNatEval
bridgeEvalRem left right
  with bridgeNatDivMod (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
... | bridgeDivisionByZero = bridgeNatFailure arithmeticDomainError
... | bridgeDivisionResult quotient remainder =
  bridgeNatSuccess remainder
    (joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right)))

bridgeQuotZeroIsDomainError :
  (left : BridgeNatCell) →
  bridgeEvalQuot left (bridgeRawNat zero) ≡ bridgeNatFailure arithmeticDomainError
bridgeQuotZeroIsDomainError left = refl

bridgeRemainderZeroIsDomainError :
  (left : BridgeNatCell) →
  bridgeEvalRem left (bridgeRawNat zero) ≡ bridgeNatFailure arithmeticDomainError
bridgeRemainderZeroIsDomainError left = refl

-- ── 10. Compositional denotation for the closed Nat/Bool scalar fragment ──
--
-- This is a Scott-Strachey-style denotation for a finite, total expression
-- fragment with explicit runtime errors. Syntax maps compositionally to values
-- and errors. It deliberately does not claim to model arbitrary Forth, mutable
-- dictionary operations, untrusted execution tokens, or nontermination.

data ScalarTerm : CoreTy → Set where
  sNatLiteral : Nat → ScalarTerm naturalTy
  sCheckedNat : Nat → SourceMode → ScalarTerm naturalTy
  sBoolLiteral : Bool → SourceMode → ScalarTerm booleanTy
  sAdd : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
  sSub : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
  sMul : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
  sQuot : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
  sRem : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
  sMonus : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
  sEq : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm booleanTy
  sGeq : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm booleanTy
  sLt : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm booleanTy
  sIfNat :
    ScalarTerm booleanTy →
    ScalarTerm naturalTy →
    ScalarTerm naturalTy →
    ScalarTerm naturalTy

data ScalarValue : CoreTy → Set where
  scalarNat : Nat → SourceMode → ScalarValue naturalTy
  scalarBool : Bool → SourceMode → ScalarValue booleanTy

data ScalarResult (A : Set) : Set where
  scalarRaised : RuntimeError → ScalarResult A
  scalarReturned : A → ScalarResult A

scalarQuotDenotation :
  Nat → SourceMode → Nat → SourceMode →
  ScalarResult (ScalarValue naturalTy)
scalarQuotDenotation left leftMode right rightMode
  with bridgeNatDivMod left right
... | bridgeDivisionByZero = scalarRaised arithmeticDomainError
... | bridgeDivisionResult quotient remainder =
  scalarReturned (scalarNat quotient (joinSourceMode leftMode rightMode))

scalarRemDenotation :
  Nat → SourceMode → Nat → SourceMode →
  ScalarResult (ScalarValue naturalTy)
scalarRemDenotation left leftMode right rightMode
  with bridgeNatDivMod left right
... | bridgeDivisionByZero = scalarRaised arithmeticDomainError
... | bridgeDivisionResult quotient remainder =
  scalarReturned (scalarNat remainder (joinSourceMode leftMode rightMode))

denoteScalar :
  {A : CoreTy} → ScalarTerm A → ScalarResult (ScalarValue A)
denoteScalar (sNatLiteral n) = scalarReturned (scalarNat n modal)
denoteScalar (sCheckedNat n mode) = scalarReturned (scalarNat n mode)
denoteScalar (sBoolLiteral b mode) = scalarReturned (scalarBool b mode)
denoteScalar (sAdd left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarReturned (scalarNat (x + y) (joinSourceMode leftMode rightMode))
denoteScalar (sSub left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarReturned (scalarNat (bridgeNatSub x y) (joinSourceMode leftMode rightMode))
denoteScalar (sMul left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarReturned (scalarNat (bridgeNatMul x y) (joinSourceMode leftMode rightMode))
denoteScalar (sQuot left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarQuotDenotation x leftMode y rightMode
denoteScalar (sRem left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarRemDenotation x leftMode y rightMode
denoteScalar (sMonus left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarReturned (scalarNat (bridgeNatSub x y) (joinSourceMode leftMode rightMode))
denoteScalar (sEq left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarReturned (scalarBool (bridgeNatEq x y) (joinSourceMode leftMode rightMode))
denoteScalar (sGeq left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarReturned (scalarBool (bridgeNatGeq x y) (joinSourceMode leftMode rightMode))
denoteScalar (sLt left right) with denoteScalar left | denoteScalar right
... | scalarRaised err | _ = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
  scalarReturned (scalarBool (bridgeNatLt x y) (joinSourceMode leftMode rightMode))
denoteScalar (sIfNat condition yes no) with denoteScalar condition
... | scalarRaised err = scalarRaised err
... | scalarReturned (scalarBool true conditionMode) = denoteScalar yes
... | scalarReturned (scalarBool false conditionMode) = denoteScalar no

scalarFromCell : BridgeNatCell → ScalarTerm naturalTy
scalarFromCell (bridgeRawNat n) = sNatLiteral n
scalarFromCell (bridgeCheckedNat n mode) = sCheckedNat n mode

scalarCellIsModal :
  (n : Nat) →
  denoteScalar (scalarFromCell (bridgeRawNat n)) ≡
    scalarReturned (scalarNat n modal)
scalarCellIsModal n = refl

scalarCheckedCellPreservesMode :
  (n : Nat) (mode : SourceMode) →
  denoteScalar (scalarFromCell (bridgeCheckedNat n mode)) ≡
    scalarReturned (scalarNat n mode)
scalarCheckedCellPreservesMode n mode = refl

scalarAdditionCompositional :
  (left right : Nat) →
  denoteScalar (sAdd (sNatLiteral left) (sNatLiteral right)) ≡
    scalarReturned (scalarNat (left + right) modal)
scalarAdditionCompositional left right = refl

scalarMixedAdditionCompositional :
  (left right : Nat) (mode : SourceMode) →
  denoteScalar (sAdd (sCheckedNat left mode) (sNatLiteral right)) ≡
    scalarReturned (scalarNat (left + right) (joinSourceMode mode modal))
scalarMixedAdditionCompositional left right mode = refl

scalarEqualityCompositional :
  (left right : Nat) →
  denoteScalar (sEq (sNatLiteral left) (sNatLiteral right)) ≡
    scalarReturned (scalarBool (bridgeNatEq left right) modal)
scalarEqualityCompositional left right = refl

scalarTrueChoosesThenBranch :
  (yes no : ScalarTerm naturalTy) →
  denoteScalar (sIfNat (sBoolLiteral true modal) yes no) ≡ denoteScalar yes
scalarTrueChoosesThenBranch yes no = refl

scalarFalseChoosesElseBranch :
  (yes no : ScalarTerm naturalTy) →
  denoteScalar (sIfNat (sBoolLiteral false modal) yes no) ≡ denoteScalar no
scalarFalseChoosesElseBranch yes no = refl

scalarQuotientByZeroRaises :
  (numerator : Nat) →
  denoteScalar (sQuot (sNatLiteral numerator) (sNatLiteral zero)) ≡
    scalarRaised arithmeticDomainError
scalarQuotientByZeroRaises numerator = refl

scalarRemainderByZeroRaises :
  (numerator : Nat) →
  denoteScalar (sRem (sNatLiteral numerator) (sNatLiteral zero)) ≡
    scalarRaised arithmeticDomainError
scalarRemainderByZeroRaises numerator = refl

scalarNatEvalToResult : BridgeNatEval → ScalarResult (ScalarValue naturalTy)
scalarNatEvalToResult (bridgeNatFailure err) = scalarRaised err
scalarNatEvalToResult (bridgeNatSuccess n mode) = scalarReturned (scalarNat n mode)

scalarAdditionMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sAdd (scalarFromCell left) (scalarFromCell right)) ≡
    scalarReturned (scalarNat (fst (bridgeEvalAdd left right)) (snd (bridgeEvalAdd left right)))
scalarAdditionMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarAdditionMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarAdditionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarAdditionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl

scalarSubtractionMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sSub (scalarFromCell left) (scalarFromCell right)) ≡
    scalarReturned (scalarNat (fst (bridgeEvalSub left right)) (snd (bridgeEvalSub left right)))
scalarSubtractionMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarSubtractionMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarSubtractionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarSubtractionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl

scalarMultiplicationMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sMul (scalarFromCell left) (scalarFromCell right)) ≡
    scalarReturned (scalarNat (fst (bridgeEvalMul left right)) (snd (bridgeEvalMul left right)))
scalarMultiplicationMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarMultiplicationMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarMultiplicationMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarMultiplicationMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl

scalarEqualityMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sEq (scalarFromCell left) (scalarFromCell right)) ≡
    scalarReturned (scalarBool (fst (bridgeEvalEq left right)) (snd (bridgeEvalEq left right)))
scalarEqualityMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarEqualityMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarEqualityMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarEqualityMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl

scalarGreaterEqualMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sGeq (scalarFromCell left) (scalarFromCell right)) ≡
    scalarReturned (scalarBool (fst (bridgeEvalGeq left right)) (snd (bridgeEvalGeq left right)))
scalarGreaterEqualMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarGreaterEqualMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarGreaterEqualMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarGreaterEqualMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl

scalarLessThanMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sLt (scalarFromCell left) (scalarFromCell right)) ≡
    scalarReturned (scalarBool (fst (bridgeEvalLt left right)) (snd (bridgeEvalLt left right)))
scalarLessThanMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarLessThanMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarLessThanMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarLessThanMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl

scalarQuotientMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sQuot (scalarFromCell left) (scalarFromCell right)) ≡
    scalarNatEvalToResult (bridgeEvalQuot left right)
scalarQuotientMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y)
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl
scalarQuotientMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode)
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl
scalarQuotientMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y)
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl
scalarQuotientMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode')
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl

scalarRemainderMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sRem (scalarFromCell left) (scalarFromCell right)) ≡
    scalarNatEvalToResult (bridgeEvalRem left right)
scalarRemainderMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y)
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl
scalarRemainderMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode)
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl
scalarRemainderMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y)
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl
scalarRemainderMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode')
  with bridgeNatDivMod x y
... | bridgeDivisionByZero = refl
... | bridgeDivisionResult quotient remainder = refl

-- Recovered compositional semantics from the formerly separate denotation
-- module. Kept nested here so there is one authoritative Agda specification.
module CoreDenotation where
  data DList (A : Set) : Set where
    dnil : DList A
    dcons : A → DList A → DList A
  
  appendD : {A : Set} → DList A → DList A → DList A
  appendD dnil ys = ys
  appendD (dcons x xs) ys = dcons x (appendD xs ys)
  
  lengthD : {A : Set} → DList A → Nat
  lengthD dnil = zero
  lengthD (dcons x xs) = suc (lengthD xs)
  
  natEq : Nat → Nat → Bool
  natEq zero zero = true
  natEq zero (suc y) = false
  natEq (suc x) zero = false
  natEq (suc x) (suc y) = natEq x y
  
  mutual
    data Term : Set where
      tNat : Nat → Term
      tBool : Bool → SourceMode → Term
      tUnit : Term
      tVar : Nat → Term
      tLambda : Term → Term
      tApply : Term → Term → Term
      tAdd : Term → Term → Term
      tSub : Term → Term → Term
      tMul : Term → Term → Term
      tQuot : Term → Term → Term
      tRem : Term → Term → Term
      tMonus : Term → Term → Term
      tEqual : Term → Term → Term
      tGeq : Term → Term → Term
      tLt : Term → Term → Term
      tIf : Term → Term → Term → Term
      tConstruct : Nat → DList Term → Term
      tMatch : Term → Nat → Nat → Term → Term → Term
      tRaise : RuntimeError → Term
      tCatch : Term → Term → Term
      tPackResult : Term → Term
      tUnpackResult : Term → Term
      tPrint : Term → Term
  
    data Value : Set where
      vNat : Nat → SourceMode → Value
      vBool : Bool → SourceMode → Value
      vUnit : Value
      vClosure : DList Value → Term → Value
      vConstructed : Nat → DList Value → Value
      vResult : Value → Value
      vError : RuntimeError → Value
  
  Env : Set
  Env = DList Value
  
  data Event : Set where
    observed : Value → Event
  
  -- The denotation preserves observable output and distinguishes normal return,
  -- a language-level exception, and exhaustion of the evaluator's finite fuel.
  data Outcome : Set where
    returned : Value → DList Event → Outcome
    raised : RuntimeError → DList Event → Outcome
    outOfFuel : DList Event → Outcome
  
  data ValuesOutcome : Set where
    valuesReturned : DList Value → DList Event → ValuesOutcome
    valuesRaised : RuntimeError → DList Event → ValuesOutcome
    valuesOutOfFuel : DList Event → ValuesOutcome
  
  prefixOutcome : DList Event → Outcome → Outcome
  prefixOutcome trace (returned value later) =
    returned value (appendD trace later)
  prefixOutcome trace (raised err later) =
    raised err (appendD trace later)
  prefixOutcome trace (outOfFuel later) = outOfFuel (appendD trace later)
  
  prefixValues : DList Event → ValuesOutcome → ValuesOutcome
  prefixValues trace (valuesReturned values later) =
    valuesReturned values (appendD trace later)
  prefixValues trace (valuesRaised err later) =
    valuesRaised err (appendD trace later)
  prefixValues trace (valuesOutOfFuel later) =
    valuesOutOfFuel (appendD trace later)
  
  bindOutcome : Outcome → (Value → Outcome) → Outcome
  bindOutcome (returned value trace) next =
    prefixOutcome trace (next value)
  bindOutcome (raised err trace) next = raised err trace
  bindOutcome (outOfFuel trace) next = outOfFuel trace
  
  combineOutcome :
    Outcome → Outcome → (Value → Value → Outcome) → Outcome
  combineOutcome (returned left leftTrace) second operation with second
  ... | returned right rightTrace =
    prefixOutcome (appendD leftTrace rightTrace) (operation left right)
  ... | raised err rightTrace = raised err (appendD leftTrace rightTrace)
  ... | outOfFuel rightTrace = outOfFuel (appendD leftTrace rightTrace)
  combineOutcome (raised err trace) second operation = raised err trace
  combineOutcome (outOfFuel trace) second operation = outOfFuel trace
  
  data MaybeValue : Set where
    missing : MaybeValue
    found : Value → MaybeValue
  
  lookupEnv : Nat → Env → MaybeValue
  lookupEnv zero dnil = missing
  lookupEnv zero (dcons value rest) = found value
  lookupEnv (suc index) dnil = missing
  lookupEnv (suc index) (dcons value rest) = lookupEnv index rest
  
  addValues : Value → Value → Outcome
  addValues (vNat x leftMode) (vNat y rightMode) =
    returned (vNat (x + y) (joinSourceMode leftMode rightMode)) dnil
  addValues _ _ = raised wrongKind dnil
  
  subValues : Value → Value → Outcome
  subValues (vNat x leftMode) (vNat y rightMode) =
    returned (vNat (bridgeNatSub x y) (joinSourceMode leftMode rightMode)) dnil
  subValues _ _ = raised wrongKind dnil
  
  mulValues : Value → Value → Outcome
  mulValues (vNat x leftMode) (vNat y rightMode) =
    returned (vNat (bridgeNatMul x y) (joinSourceMode leftMode rightMode)) dnil
  mulValues _ _ = raised wrongKind dnil
  
  quotValues : Value → Value → Outcome
  quotValues (vNat x leftMode) (vNat y rightMode)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = raised arithmeticDomainError dnil
  ... | bridgeDivisionResult quotient remainder =
    returned (vNat quotient (joinSourceMode leftMode rightMode)) dnil
  quotValues _ _ = raised wrongKind dnil
  
  remValues : Value → Value → Outcome
  remValues (vNat x leftMode) (vNat y rightMode)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = raised arithmeticDomainError dnil
  ... | bridgeDivisionResult quotient remainder =
    returned (vNat remainder (joinSourceMode leftMode rightMode)) dnil
  remValues _ _ = raised wrongKind dnil
  
  equalValues : Value → Value → Outcome
  equalValues (vNat x leftMode) (vNat y rightMode) =
    returned (vBool (natEq x y) (joinSourceMode leftMode rightMode)) dnil
  equalValues _ _ = raised wrongKind dnil
  
  geqValues : Value → Value → Outcome
  geqValues (vNat x leftMode) (vNat y rightMode) =
    returned (vBool (bridgeNatGeq x y) (joinSourceMode leftMode rightMode)) dnil
  geqValues _ _ = raised wrongKind dnil
  
  ltValues : Value → Value → Outcome
  ltValues (vNat x leftMode) (vNat y rightMode) =
    returned (vBool (bridgeNatLt x y) (joinSourceMode leftMode rightMode)) dnil
  ltValues _ _ = raised wrongKind dnil
  
  monusValues : Value → Value → Outcome
  monusValues = subValues
  
  unwrapValue : Value → Outcome
  unwrapValue (vResult value) = returned value dnil
  unwrapValue _ = raised wrongKind dnil
  
  mutual
    -- Fuel bounds recursive evaluation depth. It makes the denotation total
    -- without assuming normalization for arbitrary recursive or user Forth code.
    eval : Nat → Env → Term → Outcome
    evalList : Nat → Env → DList Term → ValuesOutcome
    matchOutcome : Nat → Env → Nat → Nat → Term → Term → Outcome → Outcome
    catchOutcome : Nat → Env → Term → Outcome → Outcome
  
    eval zero env term = outOfFuel dnil
    eval (suc fuel) env (tNat n) = returned (vNat n modal) dnil
    eval (suc fuel) env (tBool b mode) = returned (vBool b mode) dnil
    eval (suc fuel) env tUnit = returned vUnit dnil
    eval (suc fuel) env (tVar index) with lookupEnv index env
    ... | missing = raised unknownPrimitive dnil
    ... | found value = returned value dnil
    eval (suc fuel) env (tLambda body) = returned (vClosure env body) dnil
  
    eval (suc fuel) env (tApply function argument)
      with eval fuel env function | eval fuel env argument
    ... | returned (vClosure captured body) functionTrace
        | returned value argumentTrace =
      prefixOutcome (appendD functionTrace argumentTrace)
        (eval fuel (dcons value captured) body)
    ... | raised err trace | _ = raised err trace
    ... | outOfFuel trace | _ = outOfFuel trace
    ... | returned _ functionTrace | raised err argumentTrace =
      raised err (appendD functionTrace argumentTrace)
    ... | returned _ functionTrace | outOfFuel argumentTrace =
      outOfFuel (appendD functionTrace argumentTrace)
    ... | returned _ functionTrace | returned _ argumentTrace =
      raised wrongKind (appendD functionTrace argumentTrace)
  
    eval (suc fuel) env (tAdd left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) addValues
    eval (suc fuel) env (tSub left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) subValues
    eval (suc fuel) env (tMul left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) mulValues
    eval (suc fuel) env (tQuot left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) quotValues
    eval (suc fuel) env (tRem left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) remValues
    eval (suc fuel) env (tMonus left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) monusValues
    eval (suc fuel) env (tEqual left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) equalValues
    eval (suc fuel) env (tGeq left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) geqValues
    eval (suc fuel) env (tLt left right) =
      combineOutcome (eval fuel env left) (eval fuel env right) ltValues
  
    eval (suc fuel) env (tIf condition yes no) with eval fuel env condition
    ... | returned (vBool true mode) trace = prefixOutcome trace (eval fuel env yes)
    ... | returned (vBool false mode) trace = prefixOutcome trace (eval fuel env no)
    ... | returned value trace = raised wrongKind trace
    ... | raised err trace = raised err trace
    ... | outOfFuel trace = outOfFuel trace
  
    eval (suc fuel) env (tConstruct tag fields) with evalList fuel env fields
    ... | valuesReturned values trace = returned (vConstructed tag values) trace
    ... | valuesRaised err trace = raised err trace
    ... | valuesOutOfFuel trace = outOfFuel trace
  
    eval (suc fuel) env (tMatch scrutinee expectedTag expectedArity matched fallback) =
      matchOutcome fuel env expectedTag expectedArity matched fallback
        (eval fuel env scrutinee)
  
    eval (suc fuel) env (tRaise err) = raised err dnil
    eval (suc fuel) env (tCatch body handler) =
      catchOutcome fuel env handler (eval fuel env body)
  
    eval (suc fuel) env (tPackResult term) =
      bindOutcome (eval fuel env term) (λ value → returned (vResult value) dnil)
    eval (suc fuel) env (tUnpackResult term) =
      bindOutcome (eval fuel env term) unwrapValue
  
    eval (suc fuel) env (tPrint term) with eval fuel env term
    ... | returned value trace =
      returned value (appendD trace (dcons (observed value) dnil))
    ... | raised err trace = raised err trace
    ... | outOfFuel trace = outOfFuel trace
  
    evalList zero env terms = valuesOutOfFuel dnil
    evalList (suc fuel) env dnil = valuesReturned dnil dnil
    evalList (suc fuel) env (dcons term terms) with eval fuel env term
    ... | raised err trace = valuesRaised err trace
    ... | outOfFuel trace = valuesOutOfFuel trace
    ... | returned value trace with evalList fuel env terms
    ...   | valuesReturned values later =
      valuesReturned (dcons value values) (appendD trace later)
    ...   | valuesRaised err later = valuesRaised err (appendD trace later)
    ...   | valuesOutOfFuel later = valuesOutOfFuel (appendD trace later)
  
    matchOutcome fuel env expectedTag expectedArity matched fallback
      (returned (vConstructed actualTag fields) trace)
      with natEq actualTag expectedTag | natEq (lengthD fields) expectedArity
    ... | true | true =
      prefixOutcome trace (eval fuel (appendD fields env) matched)
    ... | _ | _ = prefixOutcome trace (eval fuel env fallback)
    matchOutcome fuel env expectedTag expectedArity matched fallback
      (returned value trace) = prefixOutcome trace (eval fuel env fallback)
    matchOutcome fuel env expectedTag expectedArity matched fallback
      (raised err trace) = raised err trace
    matchOutcome fuel env expectedTag expectedArity matched fallback
      (outOfFuel trace) = outOfFuel trace
  
    catchOutcome fuel env handler (returned value trace) = returned value trace
    catchOutcome fuel env handler (outOfFuel trace) = outOfFuel trace
    catchOutcome fuel env handler (raised err trace) =
      prefixOutcome trace (eval fuel (dcons (vError err) env) handler)
  
  -- Constructive equations for representative backend forms. These prove the
  -- denotation's equations; concrete compiler/runtime refinement is a separate
  -- simulation obligation and is not implied by these equations.
  
  naturalLiteralDenotesItsValue :
    (n fuel : Nat) (env : Env) →
    eval (suc fuel) env (tNat n) ≡ returned (vNat n modal) dnil
  naturalLiteralDenotesItsValue n fuel env = refl
  
  additionIsCompositional :
    (left right : Nat) →
    eval (suc (suc zero)) dnil (tAdd (tNat left) (tNat right)) ≡
    returned (vNat (left + right) modal) dnil
  additionIsCompositional left right = refl
  
  -- The evaluator prefixes the selected branch's trace. Prove the neutral-trace
  -- law explicitly rather than assuming it is definitional for an unknown outcome.
  prefixOutcomeIdentity : (outcome : Outcome) → prefixOutcome dnil outcome ≡ outcome
  prefixOutcomeIdentity (returned value trace) = refl
  prefixOutcomeIdentity (raised err trace) = refl
  prefixOutcomeIdentity (outOfFuel trace) = refl
  
  conditionalSelectsItsTrueBranch :
    (yes no : Term) →
    eval (suc (suc zero)) dnil (tIf (tBool true modal) yes no) ≡ eval (suc zero) dnil yes
  conditionalSelectsItsTrueBranch yes no =
    prefixOutcomeIdentity (eval (suc zero) dnil yes)
  
  quotientByZeroRaises :
    (numerator : Nat) →
    eval (suc (suc zero)) dnil (tQuot (tNat numerator) (tNat zero)) ≡
    raised arithmeticDomainError dnil
  quotientByZeroRaises numerator = refl
  
  betaReductionForIdentity :
    (n : Nat) →
    eval (suc (suc (suc zero))) dnil
      (tApply (tLambda (tVar zero)) (tNat n)) ≡ returned (vNat n modal) dnil
  betaReductionForIdentity n = refl
  
  constructorMatcherSelectsAndBindsFields :
    eval (suc (suc (suc (suc zero)))) dnil
      (tMatch (tConstruct 3 (dcons (tNat 42) dnil)) 3 1 (tVar zero) (tNat zero)) ≡
    returned (vNat 42 modal) dnil
  constructorMatcherSelectsAndBindsFields = refl
  
  resultPackUnpackRoundTrips :
    (n : Nat) →
    eval (suc (suc (suc zero))) dnil (tUnpackResult (tPackResult (tNat n))) ≡
    returned (vNat n modal) dnil
  resultPackUnpackRoundTrips n = refl
  
  printPreservesTheValueAndRecordsAnEvent :
    (n : Nat) →
    eval (suc (suc zero)) dnil (tPrint (tNat n)) ≡
    returned (vNat n modal) (dcons (observed (vNat n modal)) dnil)
  printPreservesTheValueAndRecordsAnEvent n = refl
  
  catchRunsItsHandlerWithTheErrorValue :
    eval (suc (suc zero)) dnil
      (tCatch (tRaise arithmeticDomainError) (tVar zero)) ≡
    returned (vError arithmeticDomainError) dnil
  catchRunsItsHandlerWithTheErrorValue = refl
  


-- Recovered from PR #7: scalar denotation with explicit bottom and errors.
-- Kept separate from CoreDenotation because finite fuel exhaustion and
-- denotational divergence are different observations. The flat preorder is a
-- Scott-style partial-order ingredient; this module does not claim to build
-- a complete domain for unrestricted Forth.
module ScottScalarDenotation where

  data FlatDomain (A : Set) : Set where
    bottom : FlatDomain A
    defined : A → FlatDomain A

  infix 4 _⊑_

  data _⊑_ {A : Set} : FlatDomain A → FlatDomain A → Set where
    bottomLeast : {x : FlatDomain A} → bottom ⊑ x
    definedSame : {x y : A} → x ≡ y → defined x ⊑ defined y

  flatRefl : {A : Set} → (x : FlatDomain A) → x ⊑ x
  flatRefl bottom = bottomLeast
  flatRefl (defined x) = definedSame refl

  flatTrans :
    {A : Set} {x y z : FlatDomain A} →
    x ⊑ y → y ⊑ z → x ⊑ z
  flatTrans bottomLeast yz = bottomLeast
  flatTrans (definedSame refl) yz = yz

  -- Three observable outcomes: divergence, successful return, and THROW.
  data Computation (A : Set) : Set where
    diverges : Computation A
    returns : A → Computation A
    throws : RuntimeError → Computation A

  mapComputation :
    {A B : Set} → (A → B) → Computation A → Computation B
  mapComputation f diverges = diverges
  mapComputation f (returns a) = returns (f a)
  mapComputation f (throws e) = throws e

  bindComputation :
    {A B : Set} → Computation A → (A → Computation B) → Computation B
  bindComputation diverges k = diverges
  bindComputation (returns a) k = k a
  bindComputation (throws e) k = throws e

  catchComputation :
    {A : Set} → Computation A → (RuntimeError → Computation A) → Computation A
  catchComputation diverges h = diverges
  catchComputation (returns a) h = returns a
  catchComputation (throws e) h = h e

  bindAssoc :
    {A B C : Set}
    (c : Computation A)
    (f : A → Computation B)
    (g : B → Computation C) →
    bindComputation (bindComputation c f) g ≡
    bindComputation c (λ a → bindComputation (f a) g)
  bindAssoc diverges f g = refl
  bindAssoc (throws e) f g = refl
  bindAssoc (returns a) f g = refl

  catchReturn :
    {A : Set} (a : A) (h : RuntimeError → Computation A) →
    catchComputation (returns a) h ≡ returns a
  catchReturn a h = refl

  catchThrow :
    {A : Set} (e : RuntimeError) (h : RuntimeError → Computation A) →
    catchComputation (throws e) h ≡ h e
  catchThrow e h = refl

  catchBottom :
    {A : Set} (h : RuntimeError → Computation A) →
    catchComputation (diverges {A}) h ≡ diverges
  catchBottom h = refl

  data Truth : Set where
    yes no : Truth

  truthOr : Truth → Truth → Truth
  truthOr yes _ = yes
  truthOr no y = y

  truthNot : Truth → Truth
  truthNot yes = no
  truthNot no = yes

  natEq : Nat → Nat → Truth
  natEq zero zero = yes
  natEq zero (suc y) = no
  natEq (suc x) zero = no
  natEq (suc x) (suc y) = natEq x y

  natLt : Nat → Nat → Truth
  natLt zero zero = no
  natLt zero (suc y) = yes
  natLt (suc x) zero = no
  natLt (suc x) (suc y) = natLt x y

  natLe : Nat → Nat → Truth
  natLe x y = truthOr (natLt x y) (natEq x y)

  natMinus : Nat → Nat → Nat
  natMinus x zero = x
  natMinus zero (suc y) = zero
  natMinus (suc x) (suc y) = natMinus x y

  -- Fuel bounds repeated subtraction, avoiding axioms about division.
  natDivFuel : Nat → Nat → Nat → Nat
  natDivFuel zero n d = zero
  natDivFuel (suc fuel) n d with natLt n d
  ... | yes = zero
  ... | no = suc (natDivFuel fuel (natMinus n d) d)

  natRemFuel : Nat → Nat → Nat → Nat
  natRemFuel zero n d = n
  natRemFuel (suc fuel) n d with natLt n d
  ... | yes = n
  ... | no = natRemFuel fuel (natMinus n d) d

  data ScalarMeaning : Set where
    numberMeaning : Nat → ScalarMeaning
    booleanMeaning : Truth → ScalarMeaning

  data NumericOp : Set where
    addOp subOp mulOp quotientOp remainderOp : NumericOp
    equalOp greaterEqualOp lessThanOp monusOp : NumericOp

  fitNatural : Nat → Nat → Computation ScalarMeaning
  fitNatural bound n with natLe n bound
  ... | yes = returns (numberMeaning n)
  ... | no = throws arithmeticOverflowError

  numericMeaning : Nat → NumericOp → Nat → Nat → Computation ScalarMeaning
  numericMeaning bound addOp x y = fitNatural bound (x + y)
  numericMeaning bound subOp x y = fitNatural bound (natMinus x y)
  numericMeaning bound mulOp x y = fitNatural bound (x * y)
  numericMeaning bound quotientOp x zero = throws arithmeticDomainError
  numericMeaning bound quotientOp x (suc y) =
    fitNatural bound (natDivFuel x x (suc y))
  numericMeaning bound remainderOp x zero = throws arithmeticDomainError
  numericMeaning bound remainderOp x (suc y) =
    fitNatural bound (natRemFuel x x (suc y))
  numericMeaning bound equalOp x y = returns (booleanMeaning (natEq x y))
  numericMeaning bound greaterEqualOp x y = returns (booleanMeaning (natLe y x))
  numericMeaning bound lessThanOp x y = returns (booleanMeaning (natLt x y))
  numericMeaning bound monusOp x y = fitNatural bound (natMinus x y)

  data Value : Set where
    natValue : Nat → SourceMode → Value
    boolValue : Truth → SourceMode → Value
    unitValue : Value

  valueMode : Value → SourceMode
  valueMode (natValue n m) = m
  valueMode (boolValue b m) = m
  valueMode unitValue = modal

  meaningValue : SourceMode → ScalarMeaning → Value
  meaningValue m (numberMeaning n) = natValue n m
  meaningValue m (booleanMeaning b) = boolValue b m

  -- The target cell bound is a parameter, not a hard-coded machine width.
  denoteBinary :
    Nat → NumericOp → Value → Value → Computation Value
  denoteBinary bound op (natValue x mx) (natValue y my)
    with natLe x bound | natLe y bound
  ... | yes | yes =
    mapComputation (meaningValue (joinSourceMode mx my))
      (numericMeaning bound op x y)
  ... | _ | _ = throws arithmeticOverflowError
  denoteBinary bound op _ _ = throws wrongKind

  denoteIf :
    Computation Value → Computation Value → Computation Value → Computation Value
  denoteIf diverges yesBranch noBranch = diverges
  denoteIf (throws e) yesBranch noBranch = throws e
  denoteIf (returns (boolValue yes mode)) yesBranch noBranch = yesBranch
  denoteIf (returns (boolValue no mode)) yesBranch noBranch = noBranch
  denoteIf (returns value) yesBranch noBranch = throws wrongKind

  ifChoosesTrue :
    {yesBranch noBranch : Computation Value} →
    denoteIf (returns (boolValue yes linear)) yesBranch noBranch ≡ yesBranch
  ifChoosesTrue = refl

  ifChoosesFalse :
    {yesBranch noBranch : Computation Value} →
    denoteIf (returns (boolValue no modal)) yesBranch noBranch ≡ noBranch
  ifChoosesFalse = refl

  ifPropagatesBottom :
    {yesBranch noBranch : Computation Value} →
    denoteIf diverges yesBranch noBranch ≡ diverges
  ifPropagatesBottom = refl

  ifPropagatesException :
    (e : RuntimeError) (yesBranch noBranch : Computation Value) →
    denoteIf (throws e) yesBranch noBranch ≡ throws e
  ifPropagatesException e yesBranch noBranch = refl

  everyPrimitiveHasProfile : (p : Primitive) → PrimitiveSpec p
  everyPrimitiveHasProfile = specifiesEveryPrimitive

  -- The fixed emitter erases the source mode. Both modalities map to the same
  -- cell, so a decoder cannot reconstruct both original modes correctly.
  erasedModeCell : SourceMode → Nat
  erasedModeCell _ = zero

  symDenotation : {A : Set} {x y : A} → x ≡ y → y ≡ x
  symDenotation refl = refl

  transDenotation : {A : Set} {x y z : A} →
    x ≡ y → y ≡ z → x ≡ z
  transDenotation refl q = q

  linearIsNotModal : linear ≡ modal → ⊥
  linearIsNotModal ()

  noRuntimeModeDecoder :
    (decode : Nat → SourceMode) →
    decode (erasedModeCell linear) ≡ linear →
    decode (erasedModeCell modal) ≡ modal →
    ⊥
  noRuntimeModeDecoder decode linearCorrect modalCorrect =
    linearIsNotModal
      (transDenotation (symDenotation linearCorrect) modalCorrect)

 
-- Abstract account of the checked allocator's identity-exhaustion boundary.
-- arenaCursor and metadataCount abstract HERE and the metadata-list mutation.
module ABIAllocationWP where

  natLessBool : Nat → Nat → Bool
  natLessBool zero zero = false
  natLessBool zero (suc y) = true
  natLessBool (suc x) zero = false
  natLessBool (suc x) (suc y) = natLessBool x y

  natAtMost : Nat → Nat → Bool
  natAtMost n bound = natLessBool n (suc bound)

  natLessThanZero : (n : Nat) → natLessBool n zero ≡ false
  natLessThanZero zero = refl
  natLessThanZero (suc n) = refl

  natLessThanAfterPositiveAddition :
    (n k : Nat) → natLessBool (n + suc k) (suc n) ≡ false
  natLessThanAfterPositiveAddition zero k = natLessThanZero k
  natLessThanAfterPositiveAddition (suc n) k =
    natLessThanAfterPositiveAddition n k

  natAtMostAfterPositiveAddition :
    (n k : Nat) → natAtMost (n + suc k) n ≡ false
  natAtMostAfterPositiveAddition n k =
    natLessThanAfterPositiveAddition n k

  record AllocationState : Set where
    constructor allocationState
    field
      arenaCursor : Nat
      nextIdentity : Nat
      metadataCount : Nat
  open AllocationState public

  data AllocationOutcome : Set where
    allocationFailed : RuntimeError → AllocationState → AllocationOutcome
    allocationSucceeded : AllocationState → AllocationOutcome

  -- identityBound is ABI-MAX-NAT. identityCount/cellCount describe the
  -- complete preflighted allocation group. Failure leaves state untouched.
  allocationAfterCapacityCheck :
    Bool → Nat → Nat → Nat → AllocationState → AllocationOutcome
  allocationAfterCapacityCheck false identityBound identityCount cellCount state =
    allocationFailed identityOverflowError state
  allocationAfterCapacityCheck true identityBound identityCount cellCount state =
    allocationSucceeded
      (allocationState
        (arenaCursor state + cellCount)
        (nextIdentity state + identityCount)
        (metadataCount state + identityCount))

  allocateBlock :
    Nat → Nat → Nat → AllocationState → AllocationOutcome
  allocateBlock identityBound identityCount cellCount state =
    allocationAfterCapacityCheck
      (natAtMost (nextIdentity state + identityCount) identityBound)
      identityBound identityCount cellCount state

  AllocationPost :
    (normal : AllocationState → Set) →
    (exceptional : RuntimeError → AllocationState → Set) →
    AllocationOutcome → Set
  AllocationPost normal exceptional (allocationFailed err state) =
    exceptional err state
  AllocationPost normal exceptional (allocationSucceeded state) =
    normal state

  wpAllocateBlock :
    (identityBound identityCount cellCount : Nat) →
    (state : AllocationState) →
    (normal : AllocationState → Set) →
    (exceptional : RuntimeError → AllocationState → Set) → Set
  wpAllocateBlock identityBound identityCount cellCount state normal exceptional =
    AllocationPost normal exceptional
      (allocateBlock identityBound identityCount cellCount state)

  identityExhaustionIsAtomic :
    (identityBound remainingIds cellCount : Nat) →
    {state : AllocationState} →
    nextIdentity state ≡ identityBound →
    allocateBlock identityBound (suc remainingIds) cellCount state ≡
      allocationFailed identityOverflowError state
  identityExhaustionIsAtomic identityBound remainingIds cellCount {state}
    identityAtLimit
    rewrite identityAtLimit
          | natAtMostAfterPositiveAddition identityBound remainingIds = refl

  identityExhaustionSatisfiesWP :
    (identityBound remainingIds cellCount : Nat) →
    (state : AllocationState) →
    nextIdentity state ≡ identityBound →
    (normal : AllocationState → Set) →
    (exceptional : RuntimeError → AllocationState → Set) →
    exceptional identityOverflowError state →
    wpAllocateBlock identityBound (suc remainingIds) cellCount state
      normal exceptional
  identityExhaustionSatisfiesWP identityBound remainingIds cellCount state
    identityAtLimit normal exceptional exceptionalProof
    rewrite identityAtLimit
          | natAtMostAfterPositiveAddition identityBound remainingIds = exceptionalProof

  -- The runtime's makeTHUNK rejects a null execution token before allocating
  -- the handle or metadata cells. This is the Agda counterpart of the zero-page
  -- trap guard, separate from identity exhaustion.
  data ExecutionToken : Set where
    nullExecutionToken : ExecutionToken
    nonNullExecutionToken : Nat → ExecutionToken

  allocateThunk :
    ExecutionToken → Nat → Nat → Nat → AllocationState → AllocationOutcome
  allocateThunk nullExecutionToken identityBound identityCount cellCount state =
    allocationFailed nullExecutionTokenError state
  allocateThunk (nonNullExecutionToken token) identityBound identityCount cellCount state =
    allocateBlock identityBound identityCount cellCount state

  wpAllocateThunk :
    ExecutionToken → Nat → Nat → Nat → AllocationState →
    (normal : AllocationState → Set) →
    (exceptional : RuntimeError → AllocationState → Set) → Set
  wpAllocateThunk token identityBound identityCount cellCount state normal exceptional =
    AllocationPost normal exceptional
      (allocateThunk token identityBound identityCount cellCount state)

  nullExecutionTokenRejectedAtomically :
    (identityBound identityCount cellCount : Nat) →
    (state : AllocationState) →
    allocateThunk nullExecutionToken identityBound identityCount cellCount state ≡
      allocationFailed nullExecutionTokenError state
  nullExecutionTokenRejectedAtomically identityBound identityCount cellCount state = refl

  nullExecutionTokenSatisfiesWP :
    (identityBound identityCount cellCount : Nat) →
    (state : AllocationState) →
    (normal : AllocationState → Set) →
    (exceptional : RuntimeError → AllocationState → Set) →
    exceptional nullExecutionTokenError state →
    wpAllocateThunk nullExecutionToken identityBound identityCount cellCount
      state normal exceptional
  nullExecutionTokenSatisfiesWP identityBound identityCount cellCount state
    normal exceptional exceptionalProof = exceptionalProof
