{-# OPTIONS --safe #-}

-- Single-source-of-truth constructive specification for agda2LinearForth.
--
-- This module combines the descriptor/ownership model, Hoare and separation
-- contracts, checked primitive stack effects, concrete witnesses, and a small
-- semantic mirror of the pinned compiler/runtime boundary. The proof terms
-- below establish properties of this Agda model. They do not, by themselves,
-- establish that arbitrary Haskell or Forth implementations refine it.
module LinearModalSafety where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_ )
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

-- ── 1. Descriptor heap, linear/modal invariants, Hoare and separation model ──

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
  arithmeticDomainError : RuntimeError

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

-- Separation conjunction over disjoint descriptor identities.
Disjoint : List Nat → List Nat → Set
Disjoint [] ys = ⊤
Disjoint (x :: xs) ys = ((x ∈ₙ ys) → ⊥) × Disjoint xs ys

record Sep (P Q : Heap → Set) (whole : Heap) : Set where
  constructor splitHeap
  field
    leftHeap : Heap
    rightHeap : Heap
    heapDecomposition : whole ≡ leftHeap ++ rightHeap
    leftPredicate : P leftHeap
    rightPredicate : Q rightHeap
    disjointIdentities : Disjoint (keys leftHeap) (keys rightHeap)
open Sep public

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
  invalidMode :: aliasedLinearOperands :: []

booleanErrors : List RuntimeError
booleanErrors = unknownHandle :: consumedHandle :: wrongKind :: expectedBoolean :: invalidMode :: invalidBoolean :: []

divisionErrors : List RuntimeError
divisionErrors = numericErrors ++ (arithmeticDomainError :: [])

closureErrors : List RuntimeError
closureErrors = unknownHandle :: consumedHandle :: wrongKind ::
  invalidMode :: badStackEffect :: []

modalErrors : List RuntimeError
modalErrors = unknownHandle :: consumedHandle :: wrongKind ::
  modalPromotionRejected :: badResultPayload :: []

constructErrors : List RuntimeError
constructErrors = unknownHandle :: consumedHandle :: wrongKind ::
  badStackEffect :: abiEscapeHatch :: []

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

-- Total, constructive Hoare triple with distinct normal/exceptional postconditions.
Hoare :
  {S : Set} →
  (precondition : S → Set) →
  (command : S → Execution S) →
  (normalPostcondition : S → Set) →
  (exceptionalPostcondition : S → RuntimeError → Set) →
  Set
Hoare {S = S} precondition command normalPostcondition exceptionalPostcondition =
  (s : S) → precondition s →
  executionPost normalPostcondition exceptionalPostcondition (command s)

skip : {S : Set} → S → Execution S
skip s = returned s

skipPreserves :
  {S : Set} {P : S → Set} →
  Hoare P skip P (λ s e → P s)
skipPreserves s proof = proof

catchPreserves :
  {S : Set} {P : S → Set}
  (command : S → Execution S)
  (handler : RuntimeError → S → Execution S) →
  Hoare P command P (λ s e → P s) →
  ((e : RuntimeError) (s : S) → P s →
    executionPost P (λ s' e' → P s') (handler e s)) →
  Hoare P (λ s → catchExecution (command s) handler) P (λ s e → P s)
catchPreserves command handler commandSafe handlerSafe s proof
  with command s | commandSafe s proof
... | returned s' | normalProof = normalProof
... | thrown s' e | exceptionalProof = handlerSafe e s' exceptionalProof


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

-- These are error transitions, not ordinary stack-returning effects. The
-- state/error payload is modeled by Execution and the Hoare contracts.
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

-- These constructors distinguish the compiler's legacy/raw representation
-- from the representation required by the checked ABI. The checked constructors
-- are included so the predicate below can state, and prove, their absence.
data EmittedFragment : Set where
  rawNaturalCell : Nat → EmittedFragment
  rawTrueCell rawFalseCell : EmittedFragment
  legacyAddCode : EmittedFragment → EmittedFragment → EmittedFragment
  checkedScalarCode : SourceMode → Nat → EmittedFragment
  checkedBooleanCode : SourceMode → EmittedFragment

-- Mirrors ToForth.hs's LitNat and PAdd cases at the value/operator-footprint
-- level: a numeric literal is a raw cell; integer addition uses legacy "add".
compileNatFragment : NatExpr → EmittedFragment
compileNatFragment (natLiteral n) = rawNaturalCell n
compileNatFragment (natAddition left right) =
  legacyAddCode (compileNatFragment left) (compileNatFragment right)

NoCheckedRepresentation : EmittedFragment → Set
NoCheckedRepresentation (rawNaturalCell n) = ⊤
NoCheckedRepresentation rawTrueCell = ⊤
NoCheckedRepresentation rawFalseCell = ⊤
NoCheckedRepresentation (legacyAddCode left right) =
  NoCheckedRepresentation left × NoCheckedRepresentation right
NoCheckedRepresentation (checkedScalarCode mode n) = ⊥
NoCheckedRepresentation (checkedBooleanCode mode) = ⊥

compilerNatFragmentHasNoCheckedRepresentation :
  (expr : NatExpr) → NoCheckedRepresentation (compileNatFragment expr)
compilerNatFragmentHasNoCheckedRepresentation (natLiteral n) = tt
compilerNatFragmentHasNoCheckedRepresentation (natAddition left right) =
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
-- vocabulary. Unsupported operations currently go through fthError, which
-- emits a diagnostic followed by BYE; that is not a checked THROW boundary.
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
  emitLegacyAdd emitLegacySub emitLegacyMul emitLegacyQuot emitLegacyRem : BackendEmission
  emitLegacyIf emitLegacyEq emitLegacyGeq emitLegacyLt : BackendEmission
  emitDiagnosticBye : BackendEmission

emitSupportedPrimitive : SupportedBackendPrimitive → BackendEmission
emitSupportedPrimitive backendAdd = emitLegacyAdd
emitSupportedPrimitive backendSub = emitLegacySub
emitSupportedPrimitive backendMul = emitLegacyMul
emitSupportedPrimitive backendQuot = emitLegacyQuot
emitSupportedPrimitive backendRem = emitLegacyRem
emitSupportedPrimitive backendIf = emitLegacyIf
emitSupportedPrimitive backendIntegerEq = emitLegacyEq
emitSupportedPrimitive backendGeq = emitLegacyGeq
emitSupportedPrimitive backendLt = emitLegacyLt

emitBackendPrimitive : BackendPrimitive → BackendEmission
emitBackendPrimitive (backendSupported p) = emitSupportedPrimitive p
emitBackendPrimitive backendUnsupported = emitDiagnosticBye

data LegacyEmission : BackendEmission → Set where
  legacyAddEmission : LegacyEmission emitLegacyAdd
  legacySubEmission : LegacyEmission emitLegacySub
  legacyMulEmission : LegacyEmission emitLegacyMul
  legacyQuotEmission : LegacyEmission emitLegacyQuot
  legacyRemEmission : LegacyEmission emitLegacyRem
  legacyIfEmission : LegacyEmission emitLegacyIf
  legacyEqEmission : LegacyEmission emitLegacyEq
  legacyGeqEmission : LegacyEmission emitLegacyGeq
  legacyLtEmission : LegacyEmission emitLegacyLt

-- Every currently supported primitive has a typed legacy-emission witness.
-- Unlike an unindexed "success" proposition, the result type cannot inhabit
-- this claim for emitDiagnosticBye.
supportedPrimitiveEmissionIsLegacy :
  (p : SupportedBackendPrimitive) → LegacyEmission (emitSupportedPrimitive p)
supportedPrimitiveEmissionIsLegacy backendAdd = legacyAddEmission
supportedPrimitiveEmissionIsLegacy backendSub = legacySubEmission
supportedPrimitiveEmissionIsLegacy backendMul = legacyMulEmission
supportedPrimitiveEmissionIsLegacy backendQuot = legacyQuotEmission
supportedPrimitiveEmissionIsLegacy backendRem = legacyRemEmission
supportedPrimitiveEmissionIsLegacy backendIf = legacyIfEmission
supportedPrimitiveEmissionIsLegacy backendIntegerEq = legacyEqEmission
supportedPrimitiveEmissionIsLegacy backendGeq = legacyGeqEmission
supportedPrimitiveEmissionIsLegacy backendLt = legacyLtEmission

unsupportedPrimitiveUsesDiagnosticBye :
  emitBackendPrimitive backendUnsupported ≡ emitDiagnosticBye
unsupportedPrimitiveUsesDiagnosticBye = refl

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

linearInputConsumedOnSuccessfulCommit :
  lifeAfterBinarySuccess linear ≡ consumed
linearInputConsumedOnSuccessfulCommit = refl

modalInputRemainsLiveOnSuccessfulCommit :
  lifeAfterBinarySuccess modal ≡ live
modalInputRemainsLiveOnSuccessfulCommit = refl


-- Broader witnesses: the catalogue's scalar fragment was not intended to be
-- limited to addition/equality. These prove the remaining enumerated operations.
linearNatSubtraction :
  {tail : StackShape} →
  StackEffect pNatSub
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatSubtraction = natSubEffect naturalIsNatural naturalIsNatural

linearNatMultiplication :
  {tail : StackShape} →
  StackEffect pNatMul
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatMultiplication = natMulEffect naturalIsNatural naturalIsNatural

linearNatQuotient :
  {tail : StackShape} →
  StackEffect pNatQuot
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatQuotient = natQuotEffect naturalIsNatural naturalIsNatural

linearNatRemainder :
  {tail : StackShape} →
  StackEffect pNatRem
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatRemainder = natRemEffect naturalIsNatural naturalIsNatural

linearNatGreaterEqual :
  {tail : StackShape} →
  StackEffect pNatGeq
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
linearNatGreaterEqual = natGeqEffect naturalIsNatural naturalIsNatural

linearNatLessThan :
  {tail : StackShape} →
  StackEffect pNatLt
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
linearNatLessThan = natLtEffect naturalIsNatural naturalIsNatural

linearNatMonusStackEffect :
  {tail : StackShape} →
  StackEffect pNatMonus
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatMonusStackEffect = natMonusEffect naturalIsNatural naturalIsNatural

modalAdditionWitness :
  StackEffect pNatAdd
    (valueItem (!Ty naturalTy) :: valueItem (!Ty naturalTy) :: [])
    (valueItem (!Ty naturalTy) :: [])
modalAdditionWitness = natAddEffect boxedNaturalIsNatural boxedNaturalIsNatural

mixedModeMultiplicationWitness :
  StackEffect pNatMul
    (valueItem (!Ty naturalTy) :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
mixedModeMultiplicationWitness = natMulEffect naturalIsNatural boxedNaturalIsNatural

orderComparisonReturnsBoolean :
  StackEffect pNatGeq
    (valueItem (!Ty naturalTy) :: valueItem naturalTy :: [])
    (valueItem booleanTy :: [])
orderComparisonReturnsBoolean = natGeqEffect naturalIsNatural boxedNaturalIsNatural

remainderStackEffect :
  StackEffect pNatRem
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
remainderStackEffect = natRemEffect naturalIsNatural naturalIsNatural

modalNaturalConditional :
  StackEffect pIf
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) ::
     thunkItem modal codeNatSub [] (codeSignature codeNatSub) ::
     valueItem (!Ty booleanTy) :: [])
    (valueItem (codeSignature codeNatAdd) :: [])
modalNaturalConditional =
  ifModalBranchesEffect boxedBooleanIsBoolean modalNatSub modalNatAdd
    modalCapturesNil modalCapturesNil

natConstructorSignature : ConstructorSignature
natConstructorSignature = constructorSignature 0 (naturalTy :: []) naturalTy

natConstructorStackEffect :
  StackEffect pConstruct
    (valueItem naturalTy :: constructorTokenItem 0 :: [])
    (valueItem naturalTy :: [])
natConstructorStackEffect = constructEffect natConstructorSignature

natMatcherSignature : MatcherSignature
natMatcherSignature = matcherSignature naturalTy naturalTy

natMatcherStackEffect :
  StackEffect pMatch
    (matcherTokenItem natMatcherSignature :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natMatcherStackEffect = matchEffect natMatcherSignature

linearResultPackEffect :
  StackEffect pMakeResult (valueItem naturalTy :: []) (resultItem naturalTy :: [])
linearResultPackEffect = makeResultEffect

linearResultUnpackEffect :
  StackEffect pUnwrapResult (resultItem naturalTy :: []) (valueItem naturalTy :: [])
linearResultUnpackEffect = unwrapResultEffect

linearNaturalPrintEffect :
  StackEffect pPrint (valueItem naturalTy :: []) []
linearNaturalPrintEffect = printLinearEffect linearNatural

modalNaturalPrintEffect :
  StackEffect pPrint (valueItem (!Ty naturalTy) :: [])
    (valueItem (!Ty naturalTy) :: [])
modalNaturalPrintEffect = printModalEffect


-- ── Scalar bridge correspondence for the opt-in runtime gate ──
--
-- The concrete Forth bridge maps a bare Nat cell to a modal scalar and preserves
-- an explicitly checked handle's mode. The source compiler's erased boolean/Nat
-- overlap at raw 0 is handled by a caller-selected Nat/Bool result adapter.
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


-- ── 9. Frame rule and disjoint concurrent updates ──
--
-- A framed command receives and returns an untouched resource component.
-- This makes the locality premise explicit: a real Forth word may use the
-- frame rule only after its actual reads and writes have been shown confined
-- to the command-owned component. The lemma below does not assume arbitrary
-- EXECUTE, dictionary mutation, or global metadata updates are local.

data FramedExecution (S F : Set) : Set where
  framedReturned : S → F → FramedExecution S F
  framedThrown : S → F → RuntimeError → FramedExecution S F

frameCommand :
  {S F : Set} →
  (command : S → Execution S) →
  S → F → FramedExecution S F
frameCommand command s f with command s
... | returned s' = framedReturned s' f
... | thrown s' err = framedThrown s' f err

FramedPost :
  {S F : Set} →
  (normal : S → Set) →
  (exceptional : S → RuntimeError → Set) →
  (frameInvariant : F → Set) →
  FramedExecution S F → Set
FramedPost normal exceptional frameInvariant (framedReturned s f) =
  normal s × frameInvariant f
FramedPost normal exceptional frameInvariant (framedThrown s f err) =
  exceptional s err × frameInvariant f

FramedHoare :
  {S F : Set} →
  (precondition : S → Set) →
  (command : S → F → FramedExecution S F) →
  (normalPostcondition : S → Set) →
  (exceptionalPostcondition : S → RuntimeError → Set) →
  (frameInvariant : F → Set) → Set
FramedHoare {S} {F} precondition command normalPostcondition
  exceptionalPostcondition frameInvariant =
  (s : S) → (f : F) → precondition s → frameInvariant f →
  FramedPost normalPostcondition exceptionalPostcondition frameInvariant
    (command s f)

frameRule :
  {S F : Set} →
  {P Q : S → Set} →
  {E : S → RuntimeError → Set} →
  {R : F → Set} →
  {command : S → Execution S} →
  Hoare P command Q E →
  FramedHoare P (frameCommand command) Q E R
frameRule {command = command} safe s f preconditionProof frameProof
  with command s | safe s preconditionProof
... | returned s' | postProof = postProof , frameProof
... | thrown s' err | postProof = postProof , frameProof

-- Transitions that update separate components of a product state commute.
-- This is an elementary interference-freedom law, not a locality theorem for
-- the concrete Forth words.
leftUpdate : {L R : Set} → (L → L) → L × R → L × R
leftUpdate update (left , right) = update left , right

rightUpdate : {L R : Set} → (R → R) → L × R → L × R
rightUpdate update (left , right) = left , update right

disjointUpdatesCommute :
  {L R : Set} →
  (updateL : L → L) →
  (updateR : R → R) →
  (state : L × R) →
  rightUpdate updateR (leftUpdate updateL state) ≡
  leftUpdate updateL (rightUpdate updateR state)
disjointUpdatesCommute updateL updateR (left , right) = refl

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
scalarQuotientMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarQuotientMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarQuotientMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarQuotientMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl

scalarRemainderMatchesRuntimeBridge :
  (left right : BridgeNatCell) →
  denoteScalar (sRem (scalarFromCell left) (scalarFromCell right)) ≡
    scalarNatEvalToResult (bridgeEvalRem left right)
scalarRemainderMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
scalarRemainderMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
scalarRemainderMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
scalarRemainderMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl
