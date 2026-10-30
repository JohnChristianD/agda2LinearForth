{ OPTIONS --without-K #-}


-- Constructive core for the verified polarized-logic work.
-- No project-defined axioms, classical principles, or rewrite rules.
module VerifiedPLLCore where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Reflection using
  ( Term ; TC ; Arg ; arg ; arg-info ; visible
  ; modality ; relevant ; quantity-ω ; def ; unify
  )
open import VerifiedCoreExecutable using (finiteObservation; infiniteObservation; pow2)

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

-- Reflection frontend: instantiate the checked Hedberg theorem from an
-- explicit decidable-equality procedure and two path terms. The macro emits
-- an ordinary proof term; the kernel still type-checks that term.
private
  visibleTerm : Term → Arg Term
  visibleTerm t = arg (arg-info visible (modality relevant quantity-ω)) t

macro
  hedbergReflect : Term → Term → Term → Term → TC ⊤
  hedbergReflect dec p q hole =
    unify hole
      (def (quote hedberg)
        (visibleTerm dec ∷ visibleTerm p ∷ visibleTerm q ∷ []))

-- This fixture exercises the reflected proof path with a concrete decidable
-- equality instance for Bool.
boolEqualityDec : (x y : Bool) → Dec (x ≡ y)
boolEqualityDec false false = yes refl
boolEqualityDec false true = no (λ ())
boolEqualityDec true false = no (λ ())
boolEqualityDec true true = yes refl

reflectedHedbergBool :
  {x y : Bool} (p q : x ≡ y) → p ≡ q
reflectedHedbergBool {x} {y} p q =
  hedbergReflect boolEqualityDec p q


-- TypeTopology's generic-convergent-sequence representation of ℕ∞:
-- a decreasing Boolean sequence (the 1s form an initial segment, possibly
-- infinite). This allows undecided finite-vs-infinite sequences constructively.
record CoNat : Set where
  constructor conat
  field
    observe : Nat → Bool
    decreasing : (n : Nat) → observe (suc n) ≡ true → observe n ≡ true
open CoNat public

coZero : CoNat
coZero = conat (λ n → false) (λ n ())

successorObservation : CoNat → Nat → Bool
successorObservation c zero = true
successorObservation c (suc n) = observe c n

successorObservationDecreasing :
  (c : CoNat) (n : Nat) →
  successorObservation c (suc n) ≡ true →
  successorObservation c n ≡ true
successorObservationDecreasing c zero p = refl
successorObservationDecreasing c (suc n) p = decreasing c n p

coSucc : CoNat → CoNat
coSucc c = conat (successorObservation c) (successorObservationDecreasing c)

coInfinity : CoNat
coInfinity = conat (λ n → true) (λ n p → refl)

finiteCoNat : Nat → CoNat
finiteCoNat zero = coZero
finiteCoNat (suc n) = coSucc (finiteCoNat n)

coInfinityAtEveryDepth : (n : Nat) → observe coInfinity n ≡ true
coInfinityAtEveryDepth n = refl

finiteZeroObservation : observe (finiteCoNat zero) zero ≡ false
finiteZeroObservation = refl

finiteOneObservation : observe (finiteCoNat (suc zero)) zero ≡ true
finiteOneObservation = refl

finiteOneStops : observe (finiteCoNat (suc zero)) (suc zero) ≡ false
finiteOneStops = refl

-- Correctness of the finite-observation interface used by the Forth slice.
finiteObservationAgrees :
  (available depth : Nat) →
  observe (finiteCoNat available) depth ≡ finiteObservation available depth
finiteObservationAgrees zero depth = refl
finiteObservationAgrees (suc available) zero = refl
finiteObservationAgrees (suc available) (suc depth) =
  finiteObservationAgrees available depth

infiniteObservationAgrees :
  (depth : Nat) → observe coInfinity depth ≡ infiniteObservation depth
infiniteObservationAgrees depth = coInfinityAtEveryDepth depth

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

-- A constructive compactness result for the conatural approximation model:
-- every predicate that factors through one finite-depth Bool observation has
-- either an observed root or is true everywhere. This deliberately makes no
-- claim that arbitrary functions CoNat → Bool are compact/searchable.
record ObservationFactor (p : CoNat → Bool) : Set where
  constructor observationFactor
  field
    obsDepth : Nat
    classifier : Bool → Bool
    factorsAt : (c : CoNat) → p c ≡ classifier (observe c obsDepth)
open ObservationFactor public

classifierAllTrue :
  (q : Bool → Bool) → q false ≡ true → q true ≡ true →
  (b : Bool) → q b ≡ true
classifierAllTrue q onFalse onTrue false = onFalse
classifierAllTrue q onFalse onTrue true = onTrue

coNatFiniteObservationCompact :
  (p : CoNat → Bool) → ObservationFactor p →
  Witness (λ c → p c ≡ false) ⊎ ForAll (λ c → p c ≡ true)
coNatFiniteObservationCompact p (observationFactor n q factor)
  with q false in q0 | q true in q1
... | false | false =
  inj₁ (witness coZero (transitivity (factor coZero) q0))
... | false | true =
  inj₁ (witness coZero (transitivity (factor coZero) q0))
... | true | false =
  inj₁ (witness coInfinity
    (transitivity (factor coInfinity)
      (transitivity (congruence q (coInfinityAtEveryDepth n)) q1)))
... | true | true =
  inj₂ (forAll (λ c → transitivity (factor c)
    (classifierAllTrue q q0 q1 (observe c n))))

-- A bounded, constructive Markov principle: on an explicitly finite type,
-- double-negated existence of a root can be eliminated by finite search.
-- This does not assert unbounded Markov's principle for predicates on Nat.
falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

-- The exact constructive implication behind the finite substitute:
-- a proof of root-or-everywhere-true searchability turns ¬¬root into root.
markovFromSigmaCompactness :
  {X : Set} (p : X → Bool) →
  (Witness (λ x → p x ≡ false) ⊎ ForAll (λ x → p x ≡ true)) →
  ((Witness (λ x → p x ≡ false) → ⊥) → ⊥) →
  Witness (λ x → p x ≡ false)
markovFromSigmaCompactness p (inj₁ root) doubleNegation = root
markovFromSigmaCompactness p (inj₂ (forAll allAt)) doubleNegation =
  ⊥-elim
    (doubleNegation
      (λ root →
        falseNotTrue
          (transitivity
            (symmetry (witnessEvidence root))
            (allAt (witnessValue root)))))

-- Bounded Markov elimination for an explicitly enumerated finite type.
-- It does not assert unbounded Markov's principle for predicates on Nat.
finiteMarkov :
  {X : Set} (enum : Enumeration X) (p : X → Bool) →
  ((Witness (λ x → p x ≡ false) → ⊥) → ⊥) →
  Witness (λ x → p x ≡ false)
finiteMarkov enum p doubleNegation =
  markovFromSigmaCompactness p (finiteSearchCompact enum p) doubleNegation

-- The same bounded substitute holds for conatural predicates that factor
-- through the finite-depth observation specified by ObservationFactor.
coNatFiniteObservationMarkov :
  (p : CoNat → Bool) → (factor : ObservationFactor p) →
  ((Witness (λ c → p c ≡ false) → ⊥) → ⊥) →
  Witness (λ c → p c ≡ false)
coNatFiniteObservationMarkov p factor doubleNegation =
  markovFromSigmaCompactness p
    (coNatFiniteObservationCompact p factor)
    doubleNegation

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
