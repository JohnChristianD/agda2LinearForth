{-# OPTIONS --safe #-}

-- Constructive correspondence model for the opt-in checked scalar gate in
-- data/FLib.fth. This uses only Agda builtins and the project's own model.
-- The lemmas prove the bridge semantics; runtime tests exercise the Forth words.
module LinearModalRuntimeRefinement where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import LinearModalABI using (SourceMode; linear; modal; _×_; _,_; fst; snd)
open import LinearModalStackEffects using (joinSourceMode)

data NatCell : Set where
  rawNatCell : Nat → NatCell
  checkedNatCell : Nat → SourceMode → NatCell

natPayload : NatCell → Nat
natPayload (rawNatCell n) = n
natPayload (checkedNatCell n m) = n

natMode : NatCell → SourceMode
natMode (rawNatCell n) = modal
natMode (checkedNatCell n m) = m

-- Raw immutable Nat literals are boxed modal; an explicitly checked handle
-- retains its mode. This rule is not a type classifier for arbitrary Forth cells.
normalizeNat : NatCell → Nat × SourceMode
normalizeNat (rawNatCell n) = n , modal
normalizeNat (checkedNatCell n m) = n , m

normalizeNatPreservesPayload :
  (v : NatCell) → fst (normalizeNat v) ≡ natPayload v
normalizeNatPreservesPayload (rawNatCell n) = refl
normalizeNatPreservesPayload (checkedNatCell n m) = refl

rawNaturalsBecomeModal :
  (n : Nat) → snd (normalizeNat (rawNatCell n)) ≡ modal
rawNaturalsBecomeModal n = refl

checkedModeIsPreserved :
  (n : Nat) (m : SourceMode) →
  snd (normalizeNat (checkedNatCell n m)) ≡ m
checkedModeIsPreserved n m = refl

data BoolCell : Set where
  rawBoolCell : Bool → BoolCell
  checkedBoolCell : Bool → SourceMode → BoolCell

boolPayload : BoolCell → Bool
boolPayload (rawBoolCell b) = b
boolPayload (checkedBoolCell b m) = b

normalizeBool : BoolCell → Bool × SourceMode
normalizeBool (rawBoolCell b) = b , modal
normalizeBool (checkedBoolCell b m) = b , m

normalizeBoolPreservesPayload :
  (v : BoolCell) → fst (normalizeBool v) ≡ boolPayload v
normalizeBoolPreservesPayload (rawBoolCell b) = refl
normalizeBoolPreservesPayload (checkedBoolCell b m) = refl

rawBooleansBecomeModal :
  (b : Bool) → snd (normalizeBool (rawBoolCell b)) ≡ modal
rawBooleansBecomeModal b = refl

natSub : Nat → Nat → Nat
natSub n zero = n
natSub zero (suc m) = zero
natSub (suc n) (suc m) = natSub n m

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc m) = false
natEq (suc n) zero = false
natEq (suc n) (suc m) = natEq n m

evalAdd : NatCell → NatCell → Nat × SourceMode
evalAdd left right =
  (fst (normalizeNat left) + fst (normalizeNat right)) ,
  joinSourceMode (snd (normalizeNat left)) (snd (normalizeNat right))

evalSub : NatCell → NatCell → Nat × SourceMode
evalSub left right =
  natSub (fst (normalizeNat left)) (fst (normalizeNat right)) ,
  joinSourceMode (snd (normalizeNat left)) (snd (normalizeNat right))

evalEq : NatCell → NatCell → Bool × SourceMode
evalEq left right =
  natEq (fst (normalizeNat left)) (fst (normalizeNat right)) ,
  joinSourceMode (snd (normalizeNat left)) (snd (normalizeNat right))

addCorrespondence :
  (left right : NatCell) →
  fst (evalAdd left right) ≡ fst (normalizeNat left) + fst (normalizeNat right)
addCorrespondence left right = refl

subCorrespondence :
  (left right : NatCell) →
  fst (evalSub left right) ≡
    natSub (fst (normalizeNat left)) (fst (normalizeNat right))
subCorrespondence left right = refl

equalityCorrespondence :
  (left right : NatCell) →
  fst (evalEq left right) ≡ natEq (fst (normalizeNat left)) (fst (normalizeNat right))
equalityCorrespondence left right = refl

selectNat : Bool → NatCell → NatCell → NatCell
selectNat true yes no = yes
selectNat false yes no = no

trueSelectsLeft :
  (yes no : NatCell) → selectNat true yes no ≡ yes
trueSelectsLeft yes no = refl

falseSelectsRight :
  (yes no : NatCell) → selectNat false yes no ≡ no
falseSelectsRight yes no = refl

-- A typed Nat/Bool result API resolves the erased 0/false ambiguity at return.
natResultTagPreserved :
  (n : Nat) → natPayload (rawNatCell n) ≡ n
natResultTagPreserved n = refl

boolResultTagPreserved :
  (b : Bool) → boolPayload (rawBoolCell b) ≡ b
boolResultTagPreserved b = refl
