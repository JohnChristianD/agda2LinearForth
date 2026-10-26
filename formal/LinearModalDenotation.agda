{-# OPTIONS --safe #-}

-- A constructive Scott-style denotation for the first-order checked ABI
-- fragment.  The lifted flat domain makes divergence explicit; RuntimeError
-- is a separate observable outcome, not confused with bottom.
module LinearModalDenotation where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import LinearModalABI using
  ( SourceMode; linear; modal; RuntimeError; wrongKind
  ; arithmeticDomainError; arithmeticOverflowError
  )
open import LinearModalStackEffects using (joinSourceMode)

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

-- Runtime observations distinguish non-termination, normal return, and THROW.
-- The error branch carries no claim that machine state is rolled back.
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

-- Truncated natural subtraction, as required by natural-number monus.
natMinus : Nat → Nat → Nat
natMinus x zero = x
natMinus zero (suc y) = zero
natMinus (suc x) (suc y) = natMinus x y

-- Fuel makes the mathematical meaning total. For a positive divisor, at most
-- n repeated subtractions are needed for quotient/remainder of n by d.
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

-- A finite, compositional denotation for the backend's scalar primitive
-- fragment.  The bound parameter represents the target cell's admitted
-- natural range; the concrete Gforth cell limit is not hard-coded in Agda.
denoteBinary :
  Nat → NumericOp → Value → Value → Computation Value
denoteBinary bound op (natValue x mx) (natValue y my)
  with natLe x bound | natLe y bound
... | yes | yes =
  mapComputation (meaningValue (joinSourceMode mx my))
    (numericMeaning bound op x y)
... | _ | _ = throws arithmeticOverflowError
denoteBinary bound op _ _ = throws wrongKind

-- Conditionals evaluate only the selected denotation. A bottom or exception
-- in an unselected branch does not affect the result.
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

-- The source-to-ABI proof surface is exhaustive over Primitive. This theorem
-- establishes that every declared checked primitive has a formal profile;
-- it intentionally does not identify that profile with the bytes of FLib.fth.
open import LinearModalABI using (Primitive; PrimitiveSpec; specifiesEveryPrimitive)

everyPrimitiveHasProfile : (p : Primitive) → PrimitiveSpec p
everyPrimitiveHasProfile = specifiesEveryPrimitive
