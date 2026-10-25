{-# OPTIONS --safe #-}

-- Explicit stack signatures for the checked ABI subset.
-- Imports the project's constructive model and no Agda standard library.
module LinearModalStackEffects where

open import Agda.Builtin.Nat using (Nat)
open import LinearModalABI

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
-- LinearModalABI; these effects say which well-typed shapes an operation accepts.
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
