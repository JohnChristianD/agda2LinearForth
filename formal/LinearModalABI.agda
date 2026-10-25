{-# OPTIONS --safe #-}

-- Constructive, standard-library-free contract model for the checked GForth ABI.
-- This module imports only Agda's bundled primitive Nat and equality definitions.
-- It is a specification, not yet a proof that FLib.fth refines the model.
module LinearModalABI where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

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

data Life : Set where
  live consumed : Life

data Kind : Set where
  scalar thunk result : Kind

data RuntimeError : Set where
  unknownHandle consumedHandle invalidMode wrongKind : RuntimeError
  linearCaptureNotAccounted modalPromotionRejected : RuntimeError
  unknownPrimitive badStackEffect : RuntimeError
  badResultPayload abiEscapeHatch : RuntimeError
  arithmeticDomainError : RuntimeError

data _∈ₙ_ (n : Nat) : List Nat → Set where
  here : {m : Nat} {xs : List Nat} → n ≡ m → n ∈ₙ (m :: xs)
  there : {m : Nat} {xs : List Nat} → n ∈ₙ xs → n ∈ₙ (m :: xs)

NoDup : List Nat → Set
NoDup [] = ⊤
NoDup (x :: xs) = ((x ∈ₙ xs) → ⊥) × NoDup xs

record Descriptor : Set where
  constructor descriptor
  field
    key : Nat
    kind : Kind
    mode : RuntimeMode
    life : Life
    code : Nat
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

AllBelow : Nat → List Nat → Set
AllBelow bound [] = ⊤
AllBelow bound (n :: ns) = (n < bound) × AllBelow bound ns

data _<_ : Nat → Nat → Set where
  zeroLtSuc : {n : Nat} → zero < suc n
  sucLtSuc : {n m : Nat} → n < m → suc n < suc m

notSelfLess : {n : Nat} → n < n → ⊥
notSelfLess {zero} ()
notSelfLess {suc n} (sucLtSuc p) = notSelfLess p

subst : {A : Set} {P : A → Set} {x y : A} → x ≡ y → P x → P y
subst refl px = px

-- If every registered identity is below nextIdentity, the next identity is fresh.
freshNotPresent :
  {next : Nat} {xs : List Nat} →
  AllBelow next xs → (next ∈ₙ xs) → ⊥
freshNotPresent {xs = []} bounded ()
freshNotPresent {next} {n :: ns} (nBelow , restBelow) (here nextEqN) =
  notSelfLess (subst (λ k → n < k) nextEqN nBelow)
freshNotPresent {next} {n :: ns} (nBelow , restBelow) (there occursLater) =
  freshNotPresent restBelow occursLater

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

NoDupOn : (Nat → Set) → List Nat → Set
NoDupOn P [] = ⊤
NoDupOn P (n :: ns) = (P n → (n ∈ₙ ns) → ⊥) × NoDupOn P ns

-- Every live linear descriptor must have exactly one active owner reference:
-- presence is LiveLinearOwned; at-most-once is NoDupOn below.
LiveLinearOwned : Heap → List Nat → Set
LiveLinearOwned [] refs = ⊤
LiveLinearOwned (d :: ds) refs with mode d | life d
... | linearMode | live =
  (key d ∈ₙ refs) × LiveLinearOwned ds refs
... | _ | _ = LiveLinearOwned ds refs

AllAnnotated : Heap → Set
AllAnnotated [] = ⊤
AllAnnotated (d :: ds) = AnnotatedLive d × AllAnnotated ds
  where
  AnnotatedLive : Descriptor → Set
  AnnotatedLive d with mode d | life d
  ... | unannotated | live = ⊥
  ... | _ | _ = ⊤

record Machine : Set where
  constructor machine
  field
    heap : Heap
    roots : List Nat
    nextIdentity : Nat
open Machine public

activeReferences : Machine → List Nat
activeReferences s = roots s ++ activeCaptures (heap s)

record WellFormed (s : Machine) : Set where
  constructor wellFormed
  field
    identityUnique : NoDup (keys (heap s))
    rootsRegistered : AllIn (roots s) (keys (heap s))
    rootsLive : AllLive (roots s) (heap s)
    allReferencesRegistered : RegisteredRefs (heap s) (heap s)
    activeCapturesLive : LiveCaptures (heap s) (heap s)
    everyLinearResourceOwned : LiveLinearOwned (heap s) (activeReferences s)
    noLinearAliasing : NoDupOn (λ n → HasLiveLinear n (heap s)) (activeReferences s)
    noLiveUnannotated : AllAnnotated (heap s)
    nextIdentityFresh : AllBelow (nextIdentity s) (keys (heap s))
open WellFormed public

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

-- The permitted copy/drop evidence follows Girard's modality, not handle tags.
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

data Token (m : RuntimeMode) (l : Life) : Set where
  token : Nat → Token m l

consumeLinear : Token linearMode live → Token linearMode consumed
consumeLinear (token n) = token n

moveLinear :
  Token linearMode live →
  (freshIdentity : Nat) →
  (freshProof : (oldIdentity : Nat) → oldIdentity ≡ freshIdentity → ⊥) →
  Token linearMode consumed × Token linearMode live
moveLinear (token old) fresh distinct = token old , token fresh

duplicateModal :
  Token modalMode live → Token modalMode live × Token modalMode live
duplicateModal (token n) = token n , token n

discardModal : Token modalMode live → ⊤
discardModal (token n) = tt

record PromotionPrecondition (s : Machine) (d : Descriptor) : Set where
  constructor promotionPrecondition
  field
    registered : key d ∈ₙ keys (heap s)
    closureKind : kind d ≡ thunk
    closureLive : life d ≡ live
    capturedValuesModal : AllModal (captures d) (heap s)
    -- This is a constructive witness supplied by derivation of closed code.
    -- A caller-provided XT flag is not such a witness.
    modalCodeWitness : ModalCode (code d)
open PromotionPrecondition public

data ModalCode : Nat → Set where
  auditedPurePrimitive : (codeId : Nat) → ModalCode codeId
  composedModalCode :
    {outer inner : Nat} → ModalCode outer → ModalCode inner →
    ModalCode (outer + inner)

-- These predicates describe the preconditions a runtime implementation must check.
-- They do not imply that the current Forth words already check them.
CanPromote :
  (s : Machine) → (d : Descriptor) → PromotionPrecondition s d → Set
CanPromote s d p = ⊤

data Primitive : Set where
  pNatAdd pNatSub pNatMul pNatQuot pNatRem : Primitive
  pNatEq pNatGeq pNatLt pNatMonus pIf : Primitive
  pMakeScalar pMakeThunk pApply pForce pMakeResult pUnwrapResult : Primitive
  pPromoteModal pAssertLinear pConstruct pMatch pPrint pThrow pCatch : Primitive

-- The checked ABI deliberately does not admit these as ordinary value operations.
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

-- Total, constructive Hoare triple with a separate exceptional postcondition.
Hoare :
  {S : Set} →
  (precondition : S → Set) →
  (command : S → Execution S) →
  (normalPostcondition : S → Set) →
  (exceptionalPostcondition : S → RuntimeError → Set) →
  Set
Hoare precondition command normalPostcondition exceptionalPostcondition =
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

-- Source-level boundary classifications. Every unsupported construct must become
-- a type-checking diagnostic or an explicit runtime error, never a silent no-op.
data BoundaryDecision : Set where
  sourceRejected runtimeChecked legacyCompatible : BoundaryDecision

record PrimitiveBoundary (p : Primitive) : Set where
  constructor primitiveBoundary
  field
    preconditionChecked : BoundaryDecision
    effectAccountedFor : BoundaryDecision
    exceptionalPathSpecified : BoundaryDecision
open PrimitiveBoundary public
