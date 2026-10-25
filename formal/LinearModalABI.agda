{-# OPTIONS --safe #-}

-- Constructive, standard-library-free contract model for the checked GForth ABI.
-- Imports only Agda's bundled primitive Nat and equality definitions.
-- This file specifies invariants; it is not by itself a refinement proof for FLib.fth.
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

sourceMode : SourceMode → RuntimeMode
sourceMode linear = linearMode
sourceMode modal = modalMode

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
  notSelfLess (subst (λ k → n < k) nextEqN nBelow)
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

data Token (identity : Nat) (m : RuntimeMode) (l : Life) : Set where
  token : Token identity m l

consumeLinear :
  {identity : Nat} →
  Token identity linearMode live → Token identity linearMode consumed
consumeLinear token = token

moveLinear :
  {oldIdentity freshIdentity : Nat} →
  oldIdentity ≢ freshIdentity →
  Token oldIdentity linearMode live →
  Token oldIdentity linearMode consumed × Token freshIdentity linearMode live
moveLinear (apart distinct) token = token , token

duplicateModal :
  {identity : Nat} →
  Token identity modalMode live →
  Token identity modalMode live × Token identity modalMode live
duplicateModal token = token , token

discardModal : {identity : Nat} → Token identity modalMode live → ⊤
discardModal token = tt

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

-- The core-language model covers these operations; escape hatches are excluded.
data Primitive : Set where
  pNatAdd pNatSub pNatMul pNatQuot pNatRem : Primitive
  pNatEq pNatGeq pNatLt pNatMonus pIf : Primitive
  pMakeScalar pMakeThunk pApply pForce pMakeResult pUnwrapResult : Primitive
  pPromoteModal pAssertLinear pConstruct pMatch pPrint pThrow pCatch : Primitive

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
