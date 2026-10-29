{-# OPTIONS --safe --without-K --guardedness #-}

-- Constructive core for the verified polarized-logic work.
-- No standard library, postulates, classical principles, or rewrite rules.
module VerifiedPLLCore where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Coinduction using (∞; ♯_; ♭)

-- Small path algebra, kept local so this module has no library dependency.
symmetry : {A : Set} {x y : A} → x ≡ y → y ≡ x
symmetry refl = refl

transitivity : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitivity refl q = q

congruence : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
congruence f refl = refl

leftInverse : {A : Set} {x y : A} (p : x ≡ y) →
              transitivity (symmetry p) p ≡ refl
leftInverse refl = refl

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- Hedberg's theorem: decidable equality makes every identity type a
-- proposition. This proof is generic and assumes no K axiom.
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

choosePath : {A : Set} → ((x y : A) → Dec (x ≡ y)) →
             {x y : A} → x ≡ y → x ≡ y
choosePath dec {x} {y} p with dec x y
... | yes q = q
... | no refute = ⊥-elim (refute p)

choosePathConstant :
  {A : Set} (dec : (x y : A) → Dec (x ≡ y)) →
  {x y : A} (p q : x ≡ y) → choosePath dec p ≡ choosePath dec q
choosePathConstant dec {x} {y} p q with dec x y
... | yes r = refl
... | no refute = ⊥-elim (refute p)

pathNormalForm :
  {A : Set} (dec : (x y : A) → Dec (x ≡ y)) →
  {x y : A} (p : x ≡ y) →
  p ≡ transitivity (symmetry (choosePath dec refl)) (choosePath dec p)
pathNormalForm dec {x} refl =
  symmetry (leftInverse (choosePath dec refl))

hedberg :
  {A : Set} (dec : (x y : A) → Dec (x ≡ y)) →
  {x y : A} (p q : x ≡ y) → p ≡ q
hedberg dec {x} {y} p q =
  transitivity (pathNormalForm dec p)
    (transitivity
      (congruence
        (λ r → transitivity (symmetry (choosePath dec refl)) r)
        (choosePathConstant dec p q))
      (symmetry (pathNormalForm dec q)))

-- A conatural is a finite chain of successors or an infinite chain.
-- observe c n decides whether c has at least n+1 successors. Any finite
-- observation of the infinite element reduces productively.
data CoNat : Set where
  coZero : CoNat
  coSucc : ∞ CoNat → CoNat

coInfinity : CoNat
coInfinity = coSucc (♯ coInfinity)

finiteCoNat : Nat → CoNat
finiteCoNat zero = coZero
finiteCoNat (suc n) = coSucc (♯ finiteCoNat n)

observe : CoNat → Nat → Bool
observe coZero n = false
observe (coSucc next) zero = true
observe (coSucc next) (suc n) = observe (♭ next) n

coInfinityAtEveryDepth : (n : Nat) → observe coInfinity n ≡ true
coInfinityAtEveryDepth zero = refl
coInfinityAtEveryDepth (suc n) = coInfinityAtEveryDepth n

finiteZeroObservation : observe (finiteCoNat zero) zero ≡ false
finiteZeroObservation = refl

finiteOneObservation : observe (finiteCoNat (suc zero)) zero ≡ true
finiteOneObservation = refl

finiteOneStops : observe (finiteCoNat (suc zero)) (suc zero) ≡ false
finiteOneStops = refl

-- A finite list is exhaustibly searchable. A negative result carries proof
-- that every member fails; a positive result carries a member and its proof.
-- This is a constructive bounded-search substitute, not unbounded Markov
-- principle for arbitrary predicates over Nat.
data Member {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → Member x (x ∷ xs)
  there : {y : A} {xs : List A} → Member x xs → Member x (y ∷ xs)

data SearchResult {A : Set} (xs : List A) (p : A → Bool) : Set where
  allTrue : ((x : A) → Member x xs → p x ≡ true) → SearchResult xs p
  foundFalse : (x : A) → Member x xs → p x ≡ false → SearchResult xs p

consAllTrue :
  {A : Set} {xs : List A} {p : A → Bool} (x : A) →
  p x ≡ true →
  ((y : A) → Member y xs → p y ≡ true) →
  (y : A) → Member y (x ∷ xs) → p y ≡ true
consAllTrue x px rest .x here = px
consAllTrue x px rest y (there member) = rest y member

finiteSearch : {A : Set} (xs : List A) (p : A → Bool) → SearchResult xs p
finiteSearch [] p = allTrue (λ x ())
finiteSearch (x ∷ xs) p with p x in px | finiteSearch xs p
... | false | rest = foundFalse x here px
... | true  | foundFalse y member evidence = foundFalse y (there member) evidence
... | true  | allTrue everyTail = allTrue (consAllTrue x px everyTail)

-- CompactTypes' Σ-compactness, specialized to Bool-valued predicates.
-- The two branches carry either a root or evidence that the predicate is
-- true everywhere. This is a definition, not an LPO/MP postulate.
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record Witness {A : Set} (P : A → Set) : Set where
  constructor witness
  field
    witnessValue : A
    witnessEvidence : P witnessValue
open Witness public

record ForAll {A : Set} (P : A → Set) : Set where
  constructor forAll
  field
    everywhereEvidence : (x : A) → P x
open ForAll public

isSigmaCompact : Set → Set
isSigmaCompact X =
  (p : X → Bool) →
  Witness (λ x → p x ≡ false) ⊎ ForAll (λ x → p x ≡ true)

record Enumeration (X : Set) : Set where
  constructor enumeration
  field
    elements : List X
    enumerates : (x : X) → Member x elements
open Enumeration public

finiteSearchCompact : {X : Set} → Enumeration X → isSigmaCompact X
finiteSearchCompact (enumeration xs covers) p with finiteSearch xs p
... | foundFalse x member evidence = inj₁ (witness x evidence)
... | allTrue allRoots = inj₂ (forAll (λ x → allRoots x (covers x)))

-- Exact dyadics without normalization. An integer is represented as the
-- difference of two naturals; this avoids a non-canonical negative-zero
-- constructor. A dyadic denotes (positivePart - negativePart) / 2^scale.
record IntegerPair : Set where
  constructor integerPair
  field
    positivePart : Nat
    negativePart : Nat
open IntegerPair public

record Dyad : Set where
  constructor dyad
  field
    numerator : IntegerPair
    scale : Nat
open Dyad public

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc n) = pow2 n * suc (suc zero)

dyadAdd : Dyad → Dyad → Dyad
dyadAdd (dyad (integerPair p n) e) (dyad (integerPair q m) f) =
  dyad
    (integerPair
      (p * pow2 f + q * pow2 e)
      (n * pow2 f + m * pow2 e))
    (e + f)

dyadMultiply : Dyad → Dyad → Dyad
dyadMultiply (dyad (integerPair p n) e) (dyad (integerPair q m) f) =
  dyad
    (integerPair
      (p * q + n * m)
      (p * m + n * q))
    (e + f)

-- Equality of denoted dyadic values, by cross-multiplication. This is a
-- semantic relation, not structural equality of the non-normalized record.
dyadEquivalent : Dyad → Dyad → Set
dyadEquivalent
  (dyad (integerPair p n) e)
  (dyad (integerPair q m) f) =
  (p * pow2 f + m * pow2 e) ≡ (q * pow2 e + n * pow2 f)

dyadEquivalentRefl : (d : Dyad) → dyadEquivalent d d
dyadEquivalentRefl (dyad (integerPair p n) e) = refl

-- Minimal cut-free polarized multiplicative fragment:
-- atomic identity and positive tensor introduction. Contexts are ordered
-- lists and tensor-right concatenates disjoint contexts, so contraction and
-- weakening are not available as constructors.
data Polarity : Set where
  positive negative : Polarity

data Formula : Polarity → Set where
  positiveAtom : Nat → Formula positive
  negativeAtom : Nat → Formula negative
  positiveTensor : Formula positive → Formula positive → Formula positive

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

data PLLFragment : List (Formula negative) → Formula positive → Set where
  pllAxiom :
    {a : Nat} → PLLFragment (negativeAtom a ∷ []) (positiveAtom a)
  pllTensorRight :
    {Γ Δ : List (Formula negative)} {A B : Formula positive} →
    PLLFragment Γ A →
    PLLFragment Δ B →
    PLLFragment (append Γ Δ) (positiveTensor A B)

-- Limits are intentional: this module does not yet provide Laurent's full
-- grammar/cut elimination, a Forth code generator for tensor values, or the
-- Haskell-emitter/concrete-Gforth simulation theorem. The current Agda2Forth
-- runtime has no verified tensor ABI. Also, builtin-reflection ring tactics
-- and user rewrite rules are excluded: --allow-exec/--rewriting conflict with
-- the repository's single --safe verification configuration.
