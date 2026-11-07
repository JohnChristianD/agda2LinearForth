{-# OPTIONS --with-K --rewriting --confluence-check --polarity --lossy-unification --exact-split --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections #-}

------------------------------------------------------------------------
-- SovereignRationalSED
--
-- Six original foundational packages plus Laurent's constructive MALLP
-- calculus, without exponentials or Seely structure.  Finite-list computation
-- remains a separate helper witness.  Rewrite rules are registered once
-- at the outer module so Agda checks the combined rewrite system together.
-- The physical modules do not treat logical rewrite equations as physical
-- laws; they expose explicit finite data and proof obligations.
------------------------------------------------------------------------

module MALLPForth where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
-- Agda 2.8 has no Agda.Builtin.Empty module; define the empty type locally.
data ⊥ : Set where

------------------------------------------------------------------------
-- Small utilities
------------------------------------------------------------------------

infixr 3 _×_
infixr 9 _∘ᶠ_

¬_ : Set → Set
¬ P = P → ⊥

record _×_ (A B : Set) : Set where
  constructor pair
  field
    fst : A
    snd : B
open _×_ public

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {a a′ : A} {b b′ : B} →
        a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
cong₂ f refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

idᶠ : {A : Set} → A → A
idᶠ x = x

_∘ᶠ_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ᶠ f) x = g (f x)

record Iso (A B : Set) : Set where
  constructor iso
  field
    to       : A → B
    from     : B → A
    from-to  : (x : A) → from (to x) ≡ x
    to-from  : (y : B) → to (from y) ≡ y
open Iso public

------------------------------------------------------------------------
-- FINITE LIST COMPUTATION
--
-- Auxiliary constructive witness; separate from the six foundational
-- packages and the Laurent MALLP calculus. Finite coordinates are represented
-- by ordinary Lists and Nat labels.
-- No bounded-index container is introduced. Finite prefixes
-- are enumerated by tabulateList; lookupPrefix records bounded lookup as
-- Maybe, while lookupListOr supplies an explicit default for sparse tails.
------------------------------------------------------------------------

infix 4 _<_

data _<_ : Nat → Nat → Set where
  zero<successor : {n : Nat} → zero < suc n
  successor<successor : {m n : Nat} → m < n → suc m < suc n

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

replicateList : {A : Set} → Nat → A → List A
replicateList zero x = []
replicateList (suc n) x = x ∷ replicateList n x

tabulateList : {A : Set} → (n : Nat) → (Nat → A) → List A
tabulateList zero f = []
tabulateList (suc n) f = f zero ∷ tabulateList n (λ i → f (suc i))

lookupPrefix : {A : Set} → (n : Nat) → List A →
               (i : Nat) → i < n → Maybe A
lookupPrefix zero xs i ()
lookupPrefix (suc n) [] i bound = nothing
lookupPrefix (suc n) (x ∷ xs) zero zero<successor = just x
lookupPrefix (suc n) (x ∷ xs) (suc i) (successor<successor bound) =
  lookupPrefix n xs i bound

lookupListOr : {A : Set} → A → Nat → List A → A
lookupListOr fallback zero [] = fallback
lookupListOr fallback zero (x ∷ xs) = x
lookupListOr fallback (suc i) [] = fallback
lookupListOr fallback (suc i) (x ∷ xs) = lookupListOr fallback i xs

------------------------------------------------------------------------
-- FINITE LIST COMPUTATION: AUXILIARY CONSTRUCTIVE WITNESS
--
-- This theorem remains available to finite-prefix code, separate from the
-- six foundational packages and Laurent MALLP.
------------------------------------------------------------------------

module FiniteListComputation where

  lookup-tabulate :
    {A : Set} → (n : Nat) → (f : Nat → A) →
    (i : Nat) → (bound : i < n) →
    lookupPrefix n (tabulateList n f) i bound ≡ just (f i)
  lookup-tabulate zero f i ()
  lookup-tabulate (suc n) f zero zero<successor = refl
  lookup-tabulate (suc n) f (suc i) (successor<successor bound) =
    lookup-tabulate n (λ j → f (suc j)) i bound

open FiniteListComputation public

------------------------------------------------------------------------
-- CONATURALS: CONSTRUCTIVE COINDUCTIVE TIME HORIZONS
------------------------------------------------------------------------

record Conat : Set where
  coinductive
  field
    observeConat : Maybe Conat
open Conat public

zero∞ : Conat
observeConat zero∞ = nothing

suc∞ : Conat → Conat
observeConat (suc∞ n) = just n

infinity : Conat
observeConat infinity = just infinity

fromNat : Nat → Conat
fromNat zero = zero∞
fromNat (suc n) = suc∞ (fromNat n)

-- A bounded observation: after k observations, an infinite value is
-- represented by the cutoff k.  This always terminates by recursion on k.
finiteApproximation : Nat → Conat → Nat
finiteApproximation zero n = zero
finiteApproximation (suc k) n with observeConat n
... | nothing = zero
... | just predecessor = suc (finiteApproximation k predecessor)

finiteApproximation-fromNat :
  (n : Nat) → finiteApproximation n (fromNat n) ≡ n
finiteApproximation-fromNat zero = refl
finiteApproximation-fromNat (suc n) =
  cong suc (finiteApproximation-fromNat n)

finiteApproximation-infinity :
  (n : Nat) → finiteApproximation n infinity ≡ n
finiteApproximation-infinity zero = refl
finiteApproximation-infinity (suc n) =
  cong suc (finiteApproximation-infinity n)

-- Addition is productive: the left argument is inspected once, and every
-- recursive call is guarded under the successor observation constructor.
_+∞_ : Conat → Conat → Conat
(a +∞ b) .observeConat with observeConat a
... | nothing = observeConat b
... | just predecessor = just (predecessor +∞ b)

------------------------------------------------------------------------
-- CONATURAL STREAMS AND A NEGATIVE OBSERVATION VIEW
------------------------------------------------------------------------

-- A stream whose length is a conatural.  Its finite prefixes are always
-- computable; an infinite horizon is observed one constructor at a time.
record ConatStream (A : Set) : Set where
  coinductive
  field
    observeStream : Maybe (A × ConatStream A)
open ConatStream public

iterateConat : {A : Set} → (A → A) → Conat → A → ConatStream A
observeStream (iterateConat step horizon state) with observeConat horizon
... | nothing = nothing
... | just remaining = just (pair state (iterateConat step remaining (step state)))

mapConatStream : {A B : Set} → (A → B) → ConatStream A → ConatStream B
observeStream (mapConatStream f stream) with observeStream stream
... | nothing = nothing
... | just (pair value rest) = just (pair (f value) (mapConatStream f rest))

-- The bound, rather than the stream, controls recursion.  This evaluator is
-- total even for an infinite stream and is the executable observation API.
foldConatPrefix : {A R : Set} → (A → R → R) → R → Nat → ConatStream A → R
foldConatPrefix step initial zero stream = initial
foldConatPrefix step initial (suc n) stream with observeStream stream
... | nothing = initial
... | just (pair value rest) =
      step value (foldConatPrefix step initial n rest)

-- Continuation/negative view of one observation.  This is a polarized
-- consumer interface, not a claim that the entire Conat type is a Laurent
-- MALLP formula.  Encoding and decoding the observation are definitionally
-- adequate and require no extensionality axiom.
ConatObservationNegative : Set₁
ConatObservationNegative = {R : Set} → (Maybe Conat → R) → R

encodeConatObservationNegative : Conat → ConatObservationNegative
encodeConatObservationNegative n consume = consume (observeConat n)

decodeConatObservationNegative : ConatObservationNegative → Maybe Conat
decodeConatObservationNegative observation = observation (λ value → value)

negativeObservation-decode-encode : (n : Conat) →
  decodeConatObservationNegative (encodeConatObservationNegative n) ≡
  observeConat n
negativeObservation-decode-encode n = refl

negativeObservation-run-adequate : (n : Conat) {R : Set} →
  (consume : Maybe Conat → R) →
  encodeConatObservationNegative n consume ≡ consume (observeConat n)
negativeObservation-run-adequate n consume = refl

------------------------------------------------------------------------
-- MODULE 1: SIX FOUNDATIONAL PACKAGES AND LAURENT MALLP
------------------------------------------------------------------------

module Foundations where

  ----------------------------------------------------------------------
  -- 1. Forster-style parametric enumerability.
  --
  -- ProgramCode is a typed semantic code tree carrying an enumerable
  -- family and its numeric parameter.  It is deliberately NOT claimed to
  -- be a Gödel-numbering into Nat.  A concrete effective coding layer may
  -- replace it later without changing the evaluator equation.
  ----------------------------------------------------------------------

  module ForsterEnumerability where

    record ParametricallyEnumerable : Set₁ where
      field
        Predicate : Nat → Nat → Set
        emit : Nat → Nat → Maybe Nat
        emit-sound :
          (i stage value : Nat) →
          emit i stage ≡ just value → Predicate i value
        emit-complete :
          (i value : Nat) →
          Predicate i value →
          Σ Nat (λ stage → emit i stage ≡ just value)

    open ParametricallyEnumerable public

    data ProgramCode : Set₁ where
      familyCode : ParametricallyEnumerable → Nat → ProgramCode

    universalEval : ProgramCode → Nat → Maybe Nat
    universalEval (familyCode F i) stage = emit F i stage

    forster-eval :
      (F : ParametricallyEnumerable) →
      (i stage : Nat) →
      universalEval (familyCode F i) stage ≡ emit F i stage
    forster-eval F i stage = refl

  ----------------------------------------------------------------------
  -- 2. Markov principle plus deterministic least-witness minimization.
  --
  -- μ-search is an intentionally unbounded rewrite computation.  For a
  -- predicate with a witness it advances in natural order and returns the
  -- first witness.  With no witness it keeps reducing forever.
  -- ArithmeticalCountableChoiceLeastWitness is the stated logical choice
  -- principle, tied to μ-search.  The step equations alone do not prove
  -- Markov's principle or termination when no witness exists.
  ----------------------------------------------------------------------

  module MarkovLeastWitness where

    BooleanWitness : (Nat → Bool) → Set
    BooleanWitness P = Σ Nat (λ n → P n ≡ true)

    data AllFalseBefore (P : Nat → Bool) : Nat → Set where
      before-zero : AllFalseBefore P zero
      before-suc :
        {n : Nat} →
        AllFalseBefore P n →
        P n ≡ false →
        AllFalseBefore P (suc n)

    record LeastWitness (P : Nat → Bool) (n : Nat) : Set where
      field
        witness-holds : P n ≡ true
        all-earlier-false : AllFalseBefore P n

    open LeastWitness public

    postulate
      μ-search : (Nat → Bool) → Nat → Bool → Nat
      μ-step-true :
        (P : Nat → Bool) → (n : Nat) →
        μ-search P n true ≡ n
      μ-step-false :
        (P : Nat → Bool) → (n : Nat) →
        μ-search P n false ≡ μ-search P (suc n) (P (suc n))

    leastSearch : (Nat → Bool) → Nat
    leastSearch P = μ-search P zero (P zero)

    -- The intended arithmetical countable least-witness principle.
    -- The choice function is not hidden behind an existential: it is
    -- definitionally i ↦ leastSearch (P i).  The postulate says that, under
    -- pointwise double-negated existence, each such search returns its
    -- least witness.  This packages the countable family of Markov steps
    -- with the deterministic μ-minimizer.  It is stronger than MP_B alone.
    ArithmeticalCountableChoiceLeastWitness : Set
    ArithmeticalCountableChoiceLeastWitness =
      (P : Nat → Nat → Bool) →
      ((i : Nat) → ¬ (¬ BooleanWitness (P i))) →
      (i : Nat) → LeastWitness (P i) (leastSearch (P i))

    postulate
      arithmeticalCountableChoiceLeastWitness :
        ArithmeticalCountableChoiceLeastWitness

    leastWitnessChoice :
      (P : Nat → Nat → Bool) →
      ((i : Nat) → ¬ (¬ BooleanWitness (P i))) → Nat → Nat
    leastWitnessChoice P double-negated i = leastSearch (P i)

    leastWitnessChoice-correct :
      (P : Nat → Nat → Bool) →
      (double-negated : (i : Nat) → ¬ (¬ BooleanWitness (P i))) →
      (i : Nat) → LeastWitness (P i) (leastWitnessChoice P double-negated i)
    leastWitnessChoice-correct P double-negated i =
      arithmeticalCountableChoiceLeastWitness P double-negated i

    boundedSearch : Nat → (Nat → Bool) → Maybe Nat
    boundedSearch zero P = nothing
    boundedSearch (suc fuel) P with P zero
    ... | true = just zero
    ... | false with boundedSearch fuel (λ n → P (suc n))
    ...   | nothing = nothing
    ...   | just n = just (suc n)

    boundedSearch-sound :
      (fuel : Nat) (P : Nat → Bool) (n : Nat) →
      boundedSearch fuel P ≡ just n → P n ≡ true
    maybeNothingNotJust : {A : Set} {x : A} → nothing ≡ just x → ⊥
    maybeNothingNotJust ()

    just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    just-injective refl = refl

    zeroNotSuc : {n : Nat} → zero ≡ suc n → ⊥
    zeroNotSuc ()

    sucNotZero : {n : Nat} → suc n ≡ zero → ⊥
    sucNotZero ()

    suc-injective : {m n : Nat} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

    absurd : {A : Set} → ⊥ → A
    absurd ()

    boundedSearch-sound zero P n ()
    boundedSearch-sound (suc fuel) P zero result with P zero
    ... | true = refl
    ... | false with boundedSearch fuel (λ i → P (suc i)) in smaller
    ...   | nothing = absurd (maybeNothingNotJust result)
    ...   | just k = absurd (sucNotZero (just-injective result))
    boundedSearch-sound (suc fuel) P (suc n) result with P zero
    ... | true = absurd (zeroNotSuc (just-injective result))
    ... | false with boundedSearch fuel (λ i → P (suc i)) in smaller
    ...   | nothing = absurd (maybeNothingNotJust result)
    ...   | just k =
      boundedSearch-sound fuel (λ i → P (suc i)) n
        (trans smaller (cong just (suc-injective (just-injective result))))

    MarkovPrinciple : Set
    MarkovPrinciple =
      (P : Nat → Bool) →
      ¬ (¬ BooleanWitness P) →
      BooleanWitness P

    markovPrinciple : MarkovPrinciple
    markovPrinciple P double-negated =
      leastSearch P ,
      witness-holds
        (leastWitnessChoice-correct
          (λ i → P) (λ i → double-negated) zero)

  ----------------------------------------------------------------------
  -- 3. Mac Lane monoidal coherence as canonical object normalization.
  --
  -- Every parenthesized tensor tree flattens to the same ordered list of
  -- atoms. The three tensorNF equations have disjoint constructor patterns.
  ----------------------------------------------------------------------

  module MacLaneCoherence where

    data TensorExpr : Set where
      atom : Nat → TensorExpr
      unitₑ : TensorExpr
      tensor : TensorExpr → TensorExpr → TensorExpr

    _++_ : List Nat → List Nat → List Nat
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

    -- Flatten every tensor tree into the unique ordered list of atoms.
    -- This is a terminating normalizer whose equations implement unit and
    -- associativity coherence for the free strict monoidal object syntax.
    tensorNF : TensorExpr → List Nat
    tensorNF (atom n) = n ∷ []
    tensorNF unitₑ = []
    tensorNF (tensor A B) = tensorNF A ++ tensorNF B

    tensor-atom : (n : Nat) → tensorNF (atom n) ≡ n ∷ []
    tensor-atom n = refl

    tensor-unit : tensorNF unitₑ ≡ []
    tensor-unit = refl

    tensor-product : (A B : TensorExpr) →
      tensorNF (tensor A B) ≡ tensorNF A ++ tensorNF B
    tensor-product A B = refl

  ----------------------------------------------------------------------
  -- 4. Abstract modality compatibility fragment.
  --
  -- These are the original object-level rewrite commitments.  They specify
  -- only the equations registered below; no topos, sheaf site, or additional
  -- continuity structure is assumed by this finite physical development.
  ----------------------------------------------------------------------

  module CohesiveRetractions where

    -- Abstract modalities retained by foundational package four.  Their
    -- equations are exactly the original rewrite commitments.
    postulate
      Disc Π Γ coDisc : Set → Set
      gammaDiscIso : (X : Set) → Iso (Γ (Disc X)) X
      piDiscIso : (X : Set) → Iso (Π (Disc X)) X
      gammaCodiscIso : (X : Set) → Iso (Γ (coDisc X)) X

    -- A small expression language makes the reduction patterns legal Agda
    -- rewrite patterns.  Modality applications are represented by constructors.
    data CohesiveExpr : Set₁ where
      objectₑ : Set → CohesiveExpr
      discₑ : CohesiveExpr → CohesiveExpr
      piₑ : CohesiveExpr → CohesiveExpr
      gammaₑ : CohesiveExpr → CohesiveExpr
      codiscₑ : CohesiveExpr → CohesiveExpr

    denoteCohesive : CohesiveExpr → Set
    denoteCohesive (objectₑ X) = X
    denoteCohesive (discₑ X) = Disc (denoteCohesive X)
    denoteCohesive (piₑ X) = Π (denoteCohesive X)
    denoteCohesive (gammaₑ X) = Γ (denoteCohesive X)
    denoteCohesive (codiscₑ X) = coDisc (denoteCohesive X)

    gamma-disc-semantics : (X : CohesiveExpr) →
      Iso
        (denoteCohesive (gammaₑ (discₑ X)))
        (denoteCohesive X)
    gamma-disc-semantics X = gammaDiscIso (denoteCohesive X)

    pi-disc-semantics : (X : CohesiveExpr) →
      Iso
        (denoteCohesive (piₑ (discₑ X)))
        (denoteCohesive X)
    pi-disc-semantics X = piDiscIso (denoteCohesive X)

    gamma-codisc-semantics : (X : CohesiveExpr) →
      Iso
        (denoteCohesive (gammaₑ (codiscₑ X)))
        (denoteCohesive X)
    gamma-codisc-semantics X = gammaCodiscIso (denoteCohesive X)

    normalizeCohesive : CohesiveExpr → CohesiveExpr
    normalizeCohesive (objectₑ X) = objectₑ X
    normalizeCohesive (discₑ X) = discₑ (normalizeCohesive X)
    normalizeCohesive (piₑ X) with X
    ... | objectₑ A = piₑ (objectₑ A)
    ... | discₑ Y = normalizeCohesive Y
    ... | piₑ Y = piₑ (normalizeCohesive (piₑ Y))
    ... | gammaₑ Y = piₑ (normalizeCohesive (gammaₑ Y))
    ... | codiscₑ Y = piₑ (normalizeCohesive (codiscₑ Y))
    normalizeCohesive (gammaₑ X) with X
    ... | objectₑ A = gammaₑ (objectₑ A)
    ... | discₑ Y = normalizeCohesive Y
    ... | piₑ Y = gammaₑ (normalizeCohesive (piₑ Y))
    ... | gammaₑ Y = gammaₑ (normalizeCohesive (gammaₑ Y))
    ... | codiscₑ Y = normalizeCohesive Y
    normalizeCohesive (codiscₑ X) = codiscₑ (normalizeCohesive X)

    gamma-disc : (X : CohesiveExpr) →
      normalizeCohesive (gammaₑ (discₑ X)) ≡ normalizeCohesive X
    gamma-disc X = refl

    pi-disc : (X : CohesiveExpr) →
      normalizeCohesive (piₑ (discₑ X)) ≡ normalizeCohesive X
    pi-disc X = refl

    gamma-codisc : (X : CohesiveExpr) →
      normalizeCohesive (gammaₑ (codiscₑ X)) ≡ normalizeCohesive X
    gamma-codisc X = refl

  ----------------------------------------------------------------------
  -- 5. Hofmann-style quotient reflection on quotient-expression syntax.
  --
  -- Quotients are indexed by an explicit equivalence-relation certificate.
  -- Raw and canonicalized representatives denote equal quotient classes.
  -- The rewrite layer normalizes expression syntax; canonicalization laws
  -- remain explicit assumptions about the chosen representative function.
  ----------------------------------------------------------------------

  module QuotientReflection where

    -- Equivalence laws are explicit arguments to the quotient completion.
    -- There is no first-class setoid carrier/record: the relation and its
    -- three laws are passed directly.  This preserves the quotient package's
    -- mathematical requirements without adding another equality structure.
    postulate
      Quotient : (A : Set) →
                 (R : A → A → Set) →
                 ((x : A) → R x x) →
                 ({x y : A} → R x y → R y x) →
                 ({x y z : A} → R x y → R y z → R x z) → Set
      quotientClass : {A : Set} {R : A → A → Set}
                      {rflR : (x : A) → R x x}
                      {symR : {x y : A} → R x y → R y x}
                      {transR : {x y z : A} → R x y → R y z → R x z} →
                      A → Quotient A R rflR symR transR
      canonize : {A : Set} {R : A → A → Set}
                 {rflR : (x : A) → R x x}
                 {symR : {x y : A} → R x y → R y x}
                 {transR : {x y z : A} → R x y → R y z → R x z} →
                 A → A
      quotient-canon :
        {A : Set} {R : A → A → Set}
        {rflR : (x : A) → R x x}
        {symR : {x y : A} → R x y → R y x}
        {transR : {x y z : A} → R x y → R y z → R x z} →
        (x : A) →
        quotientClass {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR}
          (canonize {A} {R} {rflR} {symR} {transR} x) ≡
        quotientClass {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} x
      canonical-idempotent :
        {A : Set} {R : A → A → Set}
        {rflR : (x : A) → R x x}
        {symR : {x y : A} → R x y → R y x}
        {transR : {x y z : A} → R x y → R y z → R x z} →
        (x : A) →
        canonize {A} {R} {rflR} {symR} {transR}
          (canonize {A} {R} {rflR} {symR} {transR} x) ≡
        canonize {A} {R} {rflR} {symR} {transR} x
      canonical-related :
        {A : Set} {R : A → A → Set}
        {rflR : (x : A) → R x x}
        {symR : {x y : A} → R x y → R y x}
        {transR : {x y z : A} → R x y → R y z → R x z} →
        (x : A) → R (canonize {A} {R} {rflR} {symR} {transR} x) x

    -- Syntax for quotient normalization.  `canonicalizedₑ x` denotes the
    -- canonical representative; the quotient relation remains explicit.
    data QuotientExpr (A : Set) : Set where
      rawₑ : A → QuotientExpr A
      canonicalizedₑ : A → QuotientExpr A
      classₑ : QuotientExpr A → QuotientExpr A

    denoteQuotient :
      {A : Set} {R : A → A → Set}
      {rflR : (x : A) → R x x}
      {symR : {x y : A} → R x y → R y x}
      {transR : {x y z : A} → R x y → R y z → R x z} →
      QuotientExpr A → Quotient A R rflR symR transR
    denoteQuotient {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} (rawₑ x) =
      quotientClass {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} x
    denoteQuotient {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} (canonicalizedₑ x) =
      quotientClass {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR}
        (canonize {A} {R} {rflR} {symR} {transR} x)
    denoteQuotient (classₑ expression) = denoteQuotient expression

    normalizeQuotient : {A : Set} → QuotientExpr A → QuotientExpr A
    normalizeQuotient (rawₑ x) = canonicalizedₑ x
    normalizeQuotient (canonicalizedₑ x) = canonicalizedₑ x
    normalizeQuotient (classₑ expression) =
      classₑ (normalizeQuotient expression)

    quotient-raw :
      {A : Set} → (x : A) →
      normalizeQuotient (rawₑ x) ≡ normalizeQuotient (canonicalizedₑ x)
    quotient-raw x = refl

    quotient-class-canon :
      {A : Set} → (x : A) →
      normalizeQuotient (classₑ (canonicalizedₑ x)) ≡
      normalizeQuotient (classₑ (rawₑ x))
    quotient-class-canon x = refl

    quotient-raw-sound :
      {A : Set} {R : A → A → Set}
      {rflR : (x : A) → R x x}
      {symR : {x y : A} → R x y → R y x}
      {transR : {x y z : A} → R x y → R y z → R x z} →
      (x : A) →
      denoteQuotient (rawₑ x) ≡ denoteQuotient (canonicalizedₑ x)
    quotient-raw-sound {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} x =
      sym (quotient-canon {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} x)

    quotient-class-canon-sound :
      {A : Set} {R : A → A → Set}
      {rflR : (x : A) → R x x}
      {symR : {x y : A} → R x y → R y x}
      {transR : {x y z : A} → R x y → R y z → R x z} →
      (x : A) →
      denoteQuotient (classₑ (canonicalizedₑ x)) ≡
      denoteQuotient (classₑ (rawₑ x))
    quotient-class-canon-sound {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} x =
      quotient-canon {A = A} {R = R} {rflR = rflR} {symR = symR} {transR = transR} x

  ----------------------------------------------------------------------
  -- 6. Spector-style symmetric bar recursion over finite partial maps.
  --
  -- The control functional chooses the next key.  A present key hits the
  -- bar; an absent key is extended with a value supplied by the step
  -- functional.  SymmetricBarCondition supplies branchwise bar coverage.
  ----------------------------------------------------------------------

  module SymmetricBarRecursion where

    FiniteEntries : Set → Set
    FiniteEntries X = List (Nat × X)

    natEq : Nat → Nat → Bool
    natEq zero zero = true
    natEq zero (suc n) = false
    natEq (suc n) zero = false
    natEq (suc m) (suc n) = natEq m n

    memberKey : {X : Set} → Nat → FiniteEntries X → Bool
    memberKey n [] = false
    memberKey n ((pair k value) ∷ entries) with natEq n k
    ... | true = true
    ... | false = memberKey n entries

    lookupKey : {X : Set} → Nat → FiniteEntries X → Maybe X
    lookupKey n [] = nothing
    lookupKey n ((pair k value) ∷ entries) with natEq n k
    ... | true = just value
    ... | false = lookupKey n entries

    -- A finite partial map carries a proof that its key list has no
    -- duplicates.  This prevents the association-list representation from
    -- silently making lookup order part of the mathematical object.
    data UniqueKeys {X : Set} : FiniteEntries X → Set where
      unique-empty : UniqueKeys []
      unique-cons :
        {key : Nat} {value : X} {entries : FiniteEntries X} →
        memberKey key entries ≡ false →
        UniqueKeys entries →
        UniqueKeys (pair key value ∷ entries)

    record PartialMap (X : Set) : Set where
      constructor partialMap
      field
        mapEntries : FiniteEntries X
        keys-unique : UniqueKeys mapEntries
    open PartialMap public

    emptyMap : {X : Set} → PartialMap X
    emptyMap = partialMap [] unique-empty

    streamOf : {X : Set} → FiniteEntries X → X → Nat → X
    streamOf entries default n with lookupKey n entries
    ... | just value = value
    ... | nothing = default

    extendFresh :
      {X : Set} →
      (entries : PartialMap X) →
      (key : Nat) →
      memberKey key (mapEntries entries) ≡ false →
      X → PartialMap X
    extendFresh entries key fresh value =
      partialMap
        (pair key value ∷ mapEntries entries)
        (unique-cons fresh (keys-unique entries))

    data DomainDecision {X : Set}
      (entries : PartialMap X) (key : Nat) : Set where
      inDomain :
        memberKey key (mapEntries entries) ≡ true → DomainDecision entries key
      outDomain :
        memberKey key (mapEntries entries) ≡ false → DomainDecision entries key

    decideDomain :
      {X : Set} →
      (entries : PartialMap X) →
      (key : Nat) →
      DomainDecision entries key
    decideDomain entries key
      with memberKey key (mapEntries entries) in membership
    ... | true = inDomain membership
    ... | false = outDomain membership

    omegaThread :
      {X : Set} →
      (omega : (Nat → X) → Nat) →
      (default : X) →
      (alpha : Nat → X) →
      (initial : PartialMap X) →
      Nat → PartialMap X
    omegaThread omega default alpha initial zero = initial
    omegaThread omega default alpha initial (suc n) with
      omegaThread omega default alpha initial n
    ... | entries with memberKey
      (omega (streamOf (mapEntries entries) default))
      (mapEntries entries) in membership
    ...   | true = entries
    ...   | false =
      extendFresh entries
        (omega (streamOf (mapEntries entries) default))
        membership
        (alpha (omega (streamOf (mapEntries entries) default)))

    SymmetricBarCondition :
      {X : Set} →
      (omega : (Nat → X) → Nat) →
      X → Set
    SymmetricBarCondition {X} omega default =
      (initial : PartialMap X) →
      (alpha : Nat → X) →
      Σ Nat
        (λ n →
          memberKey
            (omega (streamOf
              (mapEntries (omegaThread omega default alpha initial n)) default))
            (mapEntries (omegaThread omega default alpha initial n)) ≡ true)

    postulate
      symmetricBarRec :
        {X R : Set} →
        (omega : (Nat → X) → Nat) →
        (default : X) →
        SymmetricBarCondition omega default →
        (base : PartialMap X → R) →
        (step : PartialMap X → (X → R) → R) →
        (entries : PartialMap X) →
        (key : Nat) →
        DomainDecision entries key → R

      sBR-stop :
        {X R : Set} →
        (omega : (Nat → X) → Nat) →
        (default : X) →
        (condition : SymmetricBarCondition omega default) →
        (base : PartialMap X → R) →
        (step : PartialMap X → (X → R) → R) →
        (entries : PartialMap X) →
        (key : Nat) →
        (present : memberKey key (mapEntries entries) ≡ true) →
        symmetricBarRec omega default condition base step entries key
          (inDomain present) ≡ base entries

      sBR-step :
        {X R : Set} →
        (omega : (Nat → X) → Nat) →
        (default : X) →
        (condition : SymmetricBarCondition omega default) →
        (base : PartialMap X → R) →
        (step : PartialMap X → (X → R) → R) →
        (entries : PartialMap X) →
        (key : Nat) →
        (absent : memberKey key (mapEntries entries) ≡ false) →
        symmetricBarRec omega default condition base step entries key
          (outDomain absent) ≡
        step entries
          (λ value →
            let nextEntries = extendFresh entries key absent value
                nextKey = omega (streamOf (mapEntries nextEntries) default)
            in symmetricBarRec omega default condition base step
                 nextEntries nextKey (decideDomain nextEntries nextKey))

    symmetricBarRecAt :
      {X R : Set} →
      (omega : (Nat → X) → Nat) →
      (default : X) →
      SymmetricBarCondition omega default →
      (base : PartialMap X → R) →
      (step : PartialMap X → (X → R) → R) →
      PartialMap X → R
    symmetricBarRecAt omega default condition base step entries =
      symmetricBarRec omega default condition base step entries
        (omega (streamOf (mapEntries entries) default))
        (decideDomain entries (omega (streamOf (mapEntries entries) default)))

  ----------------------------------------------------------------------
  -- 7. LAURENT'S MULTIPLICATIVE-ADDITIVE POLARIZED LINEAR LOGIC (MALLP)
  --
  -- This is Laurent's polarized linear fragment WITHOUT exponentials.
  -- Positive and negative formulas are separated by polarity; down/up
  -- are polarity shifts, not Seely modalities and not an adjoint pair
  -- asserted to be inverse.  Contexts contain only negative formulas and
  -- a stoup contains at most one positive formula.
  --
  -- No weakening or contraction constructors occur here.  Tensor splits
  -- resources between premises; with has the usual additive shared-context
  -- rule (one branch is selected by additive observation), not contraction.
  -- Cut is included as a derivation rule; cut elimination is not asserted.
  --
  -- Categorical semantics is intentionally not smuggled in via a Seely
  -- comonad.  Hamano-Scott's MALLP model uses an adjunction between
  -- reflective/coreflective full subcategories of a *-autonomous category
  -- with products.  That categorical model is a separate obligation; this
  -- module specifies formulas, duality, and proof-relevant rules only.
  -- Rule reference: Laurent, "Polarized games", section 3.1 (MALLP).
  ----------------------------------------------------------------------

  module LaurentPolarizedMALLP where

    data Polarity : Set where
      posPolarity negPolarity : Polarity

    infixr 7 _⊗⁺_ _⅋⁻_
    infixr 6 _⊕⁺_ _&⁻_

    -- Laurent's MALLP grammar:
    --   P ::= X⊥ | 1 | 0 | P ⊗ P | P ⊕ P | ↓N
    --   N ::= X  | ⊥ | ⊤ | N ⅋ N | N & N | ↑P
    data PolType : Polarity → Set where
      atom⁺ : Nat → PolType posPolarity
      atom⁻ : Nat → PolType negPolarity

      one⁺ zero⁺ : PolType posPolarity
      _⊗⁺_ _⊕⁺_ :
        PolType posPolarity → PolType posPolarity → PolType posPolarity
      down⁺ : PolType negPolarity → PolType posPolarity

      bot⁻ top⁻ : PolType negPolarity
      _⅋⁻_ _&⁻_ :
        PolType negPolarity → PolType negPolarity → PolType negPolarity
      up⁻ : PolType posPolarity → PolType negPolarity

    DownPol : PolType negPolarity → PolType posPolarity
    DownPol = down⁺

    UpPol : PolType posPolarity → PolType negPolarity
    UpPol = up⁻

    mutual
      dualPos : PolType posPolarity → PolType negPolarity
      dualPos (atom⁺ n) = atom⁻ n
      dualPos one⁺ = bot⁻
      dualPos zero⁺ = top⁻
      dualPos (A ⊗⁺ B) = dualPos A ⅋⁻ dualPos B
      dualPos (A ⊕⁺ B) = dualPos A &⁻ dualPos B
      dualPos (down⁺ N) = up⁻ (dualNeg N)

      dualNeg : PolType negPolarity → PolType posPolarity
      dualNeg (atom⁻ n) = atom⁺ n
      dualNeg bot⁻ = one⁺
      dualNeg top⁻ = zero⁺
      dualNeg (A ⅋⁻ B) = dualNeg A ⊗⁺ dualNeg B
      dualNeg (A &⁻ B) = dualNeg A ⊕⁺ dualNeg B
      dualNeg (up⁻ P) = down⁺ (dualPos P)

    mutual
      dualPos-involutive : (P : PolType posPolarity) →
        dualNeg (dualPos P) ≡ P
      dualPos-involutive (atom⁺ n) = refl
      dualPos-involutive one⁺ = refl
      dualPos-involutive zero⁺ = refl
      dualPos-involutive (A ⊗⁺ B) =
        cong₂ _⊗⁺_ (dualPos-involutive A) (dualPos-involutive B)
      dualPos-involutive (A ⊕⁺ B) =
        cong₂ _⊕⁺_ (dualPos-involutive A) (dualPos-involutive B)
      dualPos-involutive (down⁺ N) =
        cong down⁺ (dualNeg-involutive N)

      dualNeg-involutive : (N : PolType negPolarity) →
        dualPos (dualNeg N) ≡ N
      dualNeg-involutive (atom⁻ n) = refl
      dualNeg-involutive bot⁻ = refl
      dualNeg-involutive top⁻ = refl
      dualNeg-involutive (A ⅋⁻ B) =
        cong₂ _⅋⁻_ (dualNeg-involutive A) (dualNeg-involutive B)
      dualNeg-involutive (A &⁻ B) =
        cong₂ _&⁻_ (dualNeg-involutive A) (dualNeg-involutive B)
      dualNeg-involutive (up⁻ P) =
        cong up⁻ (dualPos-involutive P)

    Context : Set
    Context = List (PolType negPolarity)

    Stoup : Set
    Stoup = Maybe (PolType posPolarity)

    infixr 5 _++ᴸ_
    _++ᴸ_ : Context → Context → Context
    [] ++ᴸ ys = ys
    (x ∷ xs) ++ᴸ ys = x ∷ (xs ++ᴸ ys)

    -- Lists are a concrete presentation of finite contexts; exchange is
    -- witnessed explicitly, without quotient equality or setoids.  The
    -- negative context plus optional positive stoup enforces Laurent's
    -- at-most-one-positive-formula invariant by construction.
    data ContextPermutation {A : Set} : List A → List A → Set where
      permutation-nil : ContextPermutation [] []
      permutation-cons :
        {x : A} {xs ys : List A} →
        ContextPermutation xs ys →
        ContextPermutation (x ∷ xs) (x ∷ ys)
      permutation-swap :
        {x y : A} {xs : List A} →
        ContextPermutation (x ∷ y ∷ xs) (y ∷ x ∷ xs)
      permutation-trans :
        {xs ys zs : List A} →
        ContextPermutation xs ys →
        ContextPermutation ys zs →
        ContextPermutation xs zs

    contextPermutation-refl : {A : Set} (xs : List A) →
      ContextPermutation xs xs
    contextPermutation-refl [] = permutation-nil
    contextPermutation-refl (x ∷ xs) =
      permutation-cons (contextPermutation-refl xs)

    contextPermutation-sym : {A : Set} {xs ys : List A} →
      ContextPermutation xs ys → ContextPermutation ys xs
    contextPermutation-sym permutation-nil = permutation-nil
    contextPermutation-sym (permutation-cons permutation) =
      permutation-cons (contextPermutation-sym permutation)
    contextPermutation-sym permutation-swap = permutation-swap
    contextPermutation-sym (permutation-trans first second) =
      permutation-trans (contextPermutation-sym second)
        (contextPermutation-sym first)

    -- The indices enforce negative context / optional positive stoup.
    -- There are no constructors for weakening, contraction, !, or ?.
    data MALLP : Context → Stoup → Set where
      mallp-ax :
        {P : PolType posPolarity} →
        MALLP (dualPos P ∷ []) (just P)

      mallp-cut :
        {Γ Δ : Context} {P : PolType posPolarity} {S : Stoup} →
        MALLP Γ (just P) →
        MALLP (dualPos P ∷ Δ) S →
        MALLP (Γ ++ᴸ Δ) S

      mallp-exchange :
        {Γ Δ : Context} {S : Stoup} →
        ContextPermutation Γ Δ →
        MALLP Γ S →
        MALLP Δ S

      -- Positive multiplicatives and additives.
      mallp-tensor :
        {Γ Δ : Context} {P Q : PolType posPolarity} →
        MALLP Γ (just P) →
        MALLP Δ (just Q) →
        MALLP (Γ ++ᴸ Δ) (just (P ⊗⁺ Q))

      mallp-one : MALLP [] (just one⁺)

      mallp-plus-left :
        {Γ : Context} {P Q : PolType posPolarity} →
        MALLP Γ (just P) →
        MALLP Γ (just (P ⊕⁺ Q))

      mallp-plus-right :
        {Γ : Context} {P Q : PolType posPolarity} →
        MALLP Γ (just Q) →
        MALLP Γ (just (P ⊕⁺ Q))

      -- Negative multiplicatives and additives.
      mallp-par :
        {Γ : Context} {M N : PolType negPolarity} {S : Stoup} →
        MALLP (M ∷ N ∷ Γ) S →
        MALLP ((M ⅋⁻ N) ∷ Γ) S

      mallp-with :
        {Γ : Context} {M N : PolType negPolarity} {S : Stoup} →
        MALLP (M ∷ Γ) S →
        MALLP (N ∷ Γ) S →
        MALLP ((M &⁻ N) ∷ Γ) S

      mallp-bottom :
        {Γ : Context} {S : Stoup} →
        MALLP Γ S →
        MALLP (bot⁻ ∷ Γ) S

      mallp-top :
        {Γ : Context} {S : Stoup} →
        MALLP (top⁻ ∷ Γ) S

      -- Polarity shifts.  Down moves a negative formula into the positive
      -- stoup, with the remaining context negative; up moves the positive
      -- stoup into the negative context.
      mallp-down :
        {Γ : Context} {N : PolType negPolarity} →
        MALLP (N ∷ Γ) nothing →
        MALLP Γ (just (down⁺ N))

      mallp-up :
        {Γ : Context} {P : PolType posPolarity} →
        MALLP Γ (just P) →
        MALLP (up⁻ P ∷ Γ) nothing

    _+ᴺ_ : Nat → Nat → Nat
    zero +ᴺ n = n
    suc m +ᴺ n = suc (m +ᴺ n)

    derivationSize : {Γ : Context} {S : Stoup} → MALLP Γ S → Nat
    derivationSize mallp-ax = suc zero
    derivationSize (mallp-cut p q) = suc (derivationSize p +ᴺ derivationSize q)
    derivationSize (mallp-exchange permutation p) = suc (derivationSize p)
    derivationSize (mallp-tensor p q) = suc (derivationSize p +ᴺ derivationSize q)
    derivationSize mallp-one = suc zero
    derivationSize (mallp-plus-left p) = suc (derivationSize p)
    derivationSize (mallp-plus-right p) = suc (derivationSize p)
    derivationSize (mallp-par p) = suc (derivationSize p)
    derivationSize (mallp-with p q) = suc (derivationSize p +ᴺ derivationSize q)
    derivationSize (mallp-bottom p) = suc (derivationSize p)
    derivationSize mallp-top = suc zero
    derivationSize (mallp-down p) = suc (derivationSize p)
    derivationSize (mallp-up p) = suc (derivationSize p)

    orBool : Bool → Bool → Bool
    orBool true y = true
    orBool false y = y

    hasCut : {Γ : Context} {S : Stoup} → MALLP Γ S → Bool
    hasCut mallp-ax = false
    hasCut (mallp-cut p q) = true
    hasCut (mallp-exchange permutation p) = hasCut p
    hasCut (mallp-tensor p q) = orBool (hasCut p) (hasCut q)
    hasCut mallp-one = false
    hasCut (mallp-plus-left p) = hasCut p
    hasCut (mallp-plus-right p) = hasCut p
    hasCut (mallp-par p) = hasCut p
    hasCut (mallp-with p q) = orBool (hasCut p) (hasCut q)
    hasCut (mallp-bottom p) = hasCut p
    hasCut mallp-top = false
    hasCut (mallp-down p) = hasCut p
    hasCut (mallp-up p) = hasCut p

  ----------------------------------------------------------------------
  -- Publicly expose the six foundational packages and the Laurent MALLP
  -- calculus.  No Seely / exponential structure is part of this interface.
  ----------------------------------------------------------------------

  open ForsterEnumerability public
  open MarkovLeastWitness public
  open MacLaneCoherence public
  open CohesiveRetractions public
  open QuotientReflection public
  open SymmetricBarRecursion public
  open LaurentPolarizedMALLP public

open Foundations.ForsterEnumerability public
open Foundations.MarkovLeastWitness public
open Foundations.MacLaneCoherence public
open Foundations.CohesiveRetractions public
open Foundations.QuotientReflection public
open Foundations.SymmetricBarRecursion public
open Foundations.LaurentPolarizedMALLP public

{-# REWRITE
  μ-step-true
  μ-step-false
  sBR-stop
  sBR-step
#-}

------------------------------------------------------------------------
-- Rewrite computation smoke witnesses
------------------------------------------------------------------------

alwaysTrue : Nat → Bool
alwaysTrue n = true

falseThenTrue : Nat → Bool
falseThenTrue zero = false
falseThenTrue (suc n) = true

leastSearch-zero-computes :
  Foundations.MarkovLeastWitness.leastSearch alwaysTrue ≡ zero
leastSearch-zero-computes = refl

leastSearch-successor-computes :
  Foundations.MarkovLeastWitness.leastSearch falseThenTrue ≡ suc zero
leastSearch-successor-computes = refl

------------------------------------------------------------------------
-- Strict closed-Nat Forth combinator semantics
--
-- This compiler fragment has no variables, closures, heap, implicit copy,
-- implicit drop, exponentials, or garbage collector.  Each syntax child is
-- visited once; each combinator returns exactly one Nat and preserves the
-- caller's residual stack.
------------------------------------------------------------------------

module StrictNatCompiler where

  -- A single value type is enough for this initial strict fragment.
  -- Each stack transition consumes precisely its indexed input resources.
  data StackType : Set where
    natCell : StackType

  data Stack : List StackType → Set where
    emptyStack : Stack []
    pushCell : {Γ : List StackType} → Nat → Stack Γ → Stack (natCell ∷ Γ)

  -- A depth witness makes ROLL stack-safe: the selected resource exists.
  data StackAt : Nat → List StackType → Set where
    stackAtHere : {Γ : List StackType} → StackAt zero (natCell ∷ Γ)
    stackAtThere :
      {depth : Nat} {Γ : List StackType} →
      StackAt depth Γ →
      StackAt (suc depth) (natCell ∷ Γ)

  stackAtDepth : {depth : Nat} {Γ : List StackType} →
    StackAt depth Γ → Nat
  stackAtDepth stackAtHere = zero
  stackAtDepth (stackAtThere proof) = suc (stackAtDepth proof)

  rollStack :
    {depth : Nat} {Γ : List StackType} →
    StackAt depth Γ → Stack Γ → Stack Γ
  rollStack stackAtHere stack = stack
  rollStack (stackAtThere proof) (pushCell head rest)
    with rollStack proof rest
  ... | pushCell selected remaining =
    pushCell selected (pushCell head remaining)

  data NatOp : Set where
    addOp monusOp multiplyOp : NatOp

  applyNatOp : NatOp → Nat → Nat → Nat
  applyNatOp addOp x y = x + y
  applyNatOp monusOp zero y = zero
  applyNatOp monusOp (suc x) zero = suc x
  applyNatOp monusOp (suc x) (suc y) = applyNatOp monusOp x y
  applyNatOp multiplyOp x y = x * y

  data NatExpr : Set where
    literal : Nat → NatExpr
    binary : NatOp → NatExpr → NatExpr → NatExpr

  evalNatExpr : NatExpr → Nat
  evalNatExpr (literal n) = n
  evalNatExpr (binary op left right) =
    applyNatOp op (evalNatExpr left) (evalNatExpr right)

  -- A unary function consumes exactly one live Nat input. All other operands
  -- are closed derivations. Separate constructors make duplication and
  -- discard of the live assumption unrepresentable.
  data NatLinearExpr : Set where
    natArgument : NatLinearExpr
    natLinearLeft :
      NatOp →
      NatLinearExpr →
      NatExpr →
      NatLinearExpr
    natLinearRight :
      NatOp →
      NatExpr →
      NatLinearExpr →
      NatLinearExpr

  evalNatLinearExpr : NatLinearExpr → Nat → Nat
  evalNatLinearExpr natArgument argument = argument
  evalNatLinearExpr (natLinearLeft operation input right) argument =
    applyNatOp operation
      (evalNatLinearExpr input argument)
      (evalNatExpr right)
  evalNatLinearExpr (natLinearRight operation left input) argument =
    applyNatOp operation
      (evalNatExpr left)
      (evalNatLinearExpr input argument)

  -- Indexed postfix code. SWAP is an exchange, not duplication or discard.
  data ForthCode : List StackType → List StackType → Set where
    identityNat :
      {Γ : List StackType} →
      ForthCode Γ Γ
    pushNat :
      {Γ : List StackType} →
      Nat →
      ForthCode Γ (natCell ∷ Γ)
    swapNat :
      {Γ : List StackType} →
      ForthCode (natCell ∷ natCell ∷ Γ) (natCell ∷ natCell ∷ Γ)
    rollNat :
      {depth : Nat} {Γ : List StackType} →
      StackAt depth Γ →
      ForthCode Γ Γ
    binaryWord :
      {Γ : List StackType} →
      NatOp →
      ForthCode (natCell ∷ natCell ∷ Γ) (natCell ∷ Γ)
    sequence :
      {Γ Δ Ε : List StackType} →
      ForthCode Γ Δ →
      ForthCode Δ Ε →
      ForthCode Γ Ε
  compileNat : {Γ : List StackType} → NatExpr → ForthCode Γ (natCell ∷ Γ)
  compileNat (literal n) = pushNat n
  compileNat (binary op left right) =
    sequence (compileNat left)
      (sequence (compileNat right) (binaryWord op))

  -- Compile a Nat expression with exactly one live input. Any closed
  -- subexpression may be computed independently; the live input itself
  -- is consumed exactly once. The right-input case uses exchange only.
  compileNatLinear :
    {Γ : List StackType} →
    NatLinearExpr →
    ForthCode (natCell ∷ Γ) (natCell ∷ Γ)
  compileNatLinear natArgument = identityNat
  compileNatLinear (natLinearLeft operation input right) =
    sequence (compileNatLinear input)
      (sequence (compileNat right) (binaryWord operation))
  compileNatLinear (natLinearRight operation left input) =
    sequence (compileNat left)
      (sequence swapNat
        (sequence (compileNatLinear input) (binaryWord operation)))

  execForthCode : {Γ Δ : List StackType} → ForthCode Γ Δ → Stack Γ → Stack Δ
  execForthCode identityNat stack = stack
  execForthCode (pushNat n) stack = pushCell n stack
  execForthCode swapNat (pushCell top (pushCell next stack)) =
    pushCell next (pushCell top stack)
  execForthCode (rollNat proof) stack = rollStack proof stack
  execForthCode (binaryWord addOp) (pushCell right (pushCell left stack)) =
    pushCell (left + right) stack
  execForthCode (binaryWord monusOp) (pushCell right (pushCell left stack)) =
    pushCell (applyNatOp monusOp left right) stack
  execForthCode (binaryWord multiplyOp) (pushCell right (pushCell left stack)) =
    pushCell (left * right) stack
  execForthCode (sequence first second) stack =
    execForthCode second (execForthCode first stack)

  execForthCode-correct :
    {Γ : List StackType} (e : NatExpr) (stack : Stack Γ) →
    execForthCode (compileNat e) stack ≡ pushCell (evalNatExpr e) stack
  execForthCode-binary-correct :
    (op : NatOp) (left right : Nat) {Γ : List StackType} →
    (stack : Stack Γ) →
    execForthCode (binaryWord op) (pushCell right (pushCell left stack)) ≡
    pushCell (applyNatOp op left right) stack
  execForthCode-binary-correct addOp left right stack = refl
  execForthCode-binary-correct monusOp left right stack = refl
  execForthCode-binary-correct multiplyOp left right stack = refl

  execForthCode-correct (literal n) stack = refl
  execForthCode-correct (binary op left right) stack
    rewrite execForthCode-correct left stack
          | execForthCode-correct right (pushCell (evalNatExpr left) stack) =
      execForthCode-binary-correct op (evalNatExpr left) (evalNatExpr right) stack

  execNatLinear-correct :
    (expression : NatLinearExpr) →
    (argument : Nat) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execForthCode (compileNatLinear expression) (pushCell argument stack) ≡
    pushCell (evalNatLinearExpr expression argument) stack
  execNatLinear-correct natArgument argument stack = refl
  execNatLinear-correct
    (natLinearLeft operation input right) argument stack
      rewrite execNatLinear-correct input argument stack
            | execForthCode-correct right
                (pushCell (evalNatLinearExpr input argument) stack) =
        execForthCode-binary-correct operation
          (evalNatLinearExpr input argument) (evalNatExpr right) stack
  execNatLinear-correct
    (natLinearRight operation left input) argument stack
      rewrite execForthCode-correct left (pushCell argument stack)
            | execNatLinear-correct input argument
                (pushCell (evalNatExpr left) stack) =
        execForthCode-binary-correct operation
          (evalNatExpr left) (evalNatLinearExpr input argument) stack

  data ForthToken : Set where
    pushLiteral : Nat → ForthToken
    addWord monusWord multiplyWord swapWord : ForthToken
    rollWord : Nat → ForthToken

  _++ᴳ_ : {A : Set} → List A → List A → List A
  [] ++ᴳ ys = ys
  (x ∷ xs) ++ᴳ ys = x ∷ (xs ++ᴳ ys)

  renderNatOp : NatOp → ForthToken
  renderNatOp addOp = addWord
  renderNatOp monusOp = monusWord
  renderNatOp multiplyOp = multiplyWord

  renderForth : {Γ Δ : List StackType} → ForthCode Γ Δ → List ForthToken
  renderForth identityNat = []
  renderForth (pushNat n) = pushLiteral n ∷ []
  renderForth swapNat = swapWord ∷ []
  renderForth (rollNat proof) = rollWord (stackAtDepth proof) ∷ []
  renderForth (binaryWord op) = renderNatOp op ∷ []
  renderForth (sequence first second) =
    renderForth first ++ᴳ renderForth second

  -- Interpret the actual postfix token list produced by renderForth.
  forgetStack : {Γ : List StackType} → Stack Γ → List Nat
  forgetStack emptyStack = []
  forgetStack (pushCell n stack) = n ∷ forgetStack stack

  rollList : Nat → List Nat → Maybe (List Nat)
  rollList zero [] = nothing
  rollList zero (x ∷ xs) = just (x ∷ xs)
  rollList (suc depth) [] = nothing
  rollList (suc depth) (x ∷ xs) with rollList depth xs
  ... | nothing = nothing
  ... | just [] = nothing
  ... | just (selected ∷ rest) = just (selected ∷ x ∷ rest)

  rollList-correct :
    {depth : Nat} {Γ : List StackType} →
    (proof : StackAt depth Γ) →
    (stack : Stack Γ) →
    rollList (stackAtDepth proof) (forgetStack stack) ≡
    just (forgetStack (rollStack proof stack))
  rollList-correct stackAtHere (pushCell value stack) = refl
  rollList-correct (stackAtThere proof) (pushCell head rest)
    with rollList (stackAtDepth proof) (forgetStack rest)
       | rollStack proof rest
       | rollList-correct proof rest
  ... | nothing | _ | ()
  ... | just [] | _ | ()
  ... | just (selected ∷ restValues) | pushCell selected′ remaining | refl = refl

  execToken : ForthToken → List Nat → Maybe (List Nat)
  execToken (pushLiteral n) stack = just (n ∷ stack)
  execToken addWord (right ∷ left ∷ stack) = just ((left + right) ∷ stack)
  execToken addWord _ = nothing
  execToken monusWord (right ∷ left ∷ stack) =
    just (applyNatOp monusOp left right ∷ stack)
  execToken monusWord _ = nothing
  execToken multiplyWord (right ∷ left ∷ stack) =
    just (left * right ∷ stack)
  execToken multiplyWord _ = nothing

  execToken swapWord (top ∷ next ∷ stack) = just (next ∷ top ∷ stack)
  execToken swapWord _ = nothing
  execToken (rollWord depth) stack = rollList depth stack

  maybeBind : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  maybeBind nothing continuation = nothing
  maybeBind (just value) continuation = continuation value

  execTokens : List ForthToken → List Nat → Maybe (List Nat)
  execTokens [] stack = just stack
  execTokens (pushLiteral value ∷ tokens) stack
    with execToken (pushLiteral value) stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack
  execTokens (addWord ∷ tokens) stack
    with execToken addWord stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack
  execTokens (monusWord ∷ tokens) stack
    with execToken monusWord stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack
  execTokens (multiplyWord ∷ tokens) stack
    with execToken multiplyWord stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack
  execTokens (swapWord ∷ tokens) stack
    with execToken swapWord stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack
  execTokens (rollWord depth ∷ tokens) stack with rollList depth stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack

  execTokens-append :
    (first second : List ForthToken) (stack : List Nat) →
    execTokens (first ++ᴳ second) stack ≡
    maybeBind (execTokens first stack) (λ nextStack → execTokens second nextStack)
  execTokens-append [] second stack = refl
  execTokens-append (pushLiteral value ∷ first) second stack =
    execTokens-append first second (value ∷ stack)
  execTokens-append (addWord ∷ first) second (right ∷ left ∷ stack) =
    execTokens-append first second ((left + right) ∷ stack)
  execTokens-append (addWord ∷ first) second [] = refl
  execTokens-append (addWord ∷ first) second (value ∷ []) = refl
  execTokens-append (monusWord ∷ first) second (right ∷ left ∷ stack) =
    execTokens-append first second (applyNatOp monusOp left right ∷ stack)
  execTokens-append (monusWord ∷ first) second [] = refl
  execTokens-append (monusWord ∷ first) second (value ∷ []) = refl
  execTokens-append (multiplyWord ∷ first) second (right ∷ left ∷ stack) =
    execTokens-append first second ((left * right) ∷ stack)
  execTokens-append (multiplyWord ∷ first) second [] = refl
  execTokens-append (multiplyWord ∷ first) second (value ∷ []) = refl
  execTokens-append (swapWord ∷ first) second (top ∷ next ∷ stack) =
    execTokens-append first second (next ∷ top ∷ stack)
  execTokens-append (swapWord ∷ first) second [] = refl
  execTokens-append (swapWord ∷ first) second (value ∷ []) = refl
  execTokens-append (rollWord depth ∷ first) second stack
    with rollList depth stack
  ... | nothing = refl
  ... | just nextStack = execTokens-append first second nextStack

  renderForth-sound :
    {Γ Δ : List StackType} (code : ForthCode Γ Δ) (stack : Stack Γ) →
    execTokens (renderForth code) (forgetStack stack) ≡
    just (forgetStack (execForthCode code stack))
  renderForth-sound identityNat stack = refl
  renderForth-sound (pushNat n) stack = refl
  renderForth-sound swapNat (pushCell top (pushCell next stack)) = refl
  renderForth-sound (rollNat proof) stack
    with rollList (stackAtDepth proof) (forgetStack stack)
       | rollList-correct proof stack
  ... | nothing | ()
  ... | just result | refl = refl
  renderForth-sound (binaryWord addOp) (pushCell right (pushCell left stack)) = refl
  renderForth-sound (binaryWord monusOp) (pushCell right (pushCell left stack)) = refl
  renderForth-sound (binaryWord multiplyOp) (pushCell right (pushCell left stack)) = refl
  renderForth-sound (sequence first second) stack
    rewrite execTokens-append (renderForth first) (renderForth second) (forgetStack stack)
          | renderForth-sound first stack
          | renderForth-sound second (execForthCode first stack) = refl

  ----------------------------------------------------------------------
  -- A closed, proof-carrying MALLP theory for the implemented Nat slice.
  --
  -- Numerals are nullary constants. Each arithmetic primitive is a linear
  -- axiom Nat- ⊗ Nat- ⊢ Nat+, and composition is MALLP cut. Thus every
  -- source subterm is consumed once; this is a theory over MALLP, with an
  -- explicit primitive signature, rather than bare proof-tree syntax.
  ----------------------------------------------------------------------

  natFormula : PolType posPolarity
  natFormula = atom⁺ zero

  natAssumption : PolType negPolarity
  natAssumption = dualPos natFormula

  data MALLPNatTheory : Context → Stoup → Set where
    mallp-nat-literal :
      Nat → MALLPNatTheory [] (just natFormula)

    mallp-nat-primitive :
      NatOp →
      MALLPNatTheory
        (natAssumption ∷ natAssumption ∷ [])
        (just natFormula)

    mallp-nat-cut :
      {Γ Δ : Context} →
      MALLPNatTheory Γ (just natFormula) →
      MALLPNatTheory (natAssumption ∷ Δ) (just natFormula) →
      MALLPNatTheory (Γ ++ᴸ Δ) (just natFormula)

    mallp-nat-exchange :
      {Γ Δ : Context} →
      ContextPermutation Γ Δ →
      MALLPNatTheory Γ (just natFormula) →
      MALLPNatTheory Δ (just natFormula)

    mallp-nat-transport :
      {Γ Δ : Context} →
      Γ ≡ Δ →
      MALLPNatTheory Γ (just natFormula) →
      MALLPNatTheory Δ (just natFormula)

    mallp-nat-logical :
      {Γ : Context} {S : Stoup} →
      MALLP Γ S →
      MALLPNatTheory Γ S

  -- The focused proof-term language records only the number of linear Nat
  -- assumptions. Its constructors are exactly the two signature axioms and cut.
  data MALLPNatProof : Nat → Set where
    natLiteralProof :
      Nat → MALLPNatProof zero

    natPrimitiveProof :
      NatOp → MALLPNatProof (suc (suc zero))

    natArgumentProof :
      MALLPNatProof (suc zero)

    natExchangeProof :
      MALLPNatProof (suc (suc zero)) →
      MALLPNatProof (suc (suc zero))

    -- Move the first live Nat assumption behind the remaining n resources.
    -- This is a finite sequence of Laurent MALLP exchanges, not contraction.
    natRotateHeadToLastProof :
      {n : Nat} →
      MALLPNatProof (suc n) →
      MALLPNatProof (suc n)

    natCutProof :
      {n m : Nat} →
      MALLPNatProof n →
      MALLPNatProof (suc m) →
      MALLPNatProof (n + m)

  natContext : Nat → Context
  natContext zero = []
  natContext (suc n) = natAssumption ∷ natContext n

  natRotateHeadToLastPermutation :
    (n : Nat) →
    ContextPermutation (natContext (suc n)) (natContext (suc n))
  natRotateHeadToLastPermutation zero =
    contextPermutation-refl (natContext (suc zero))
  natRotateHeadToLastPermutation (suc n) =
    permutation-trans permutation-swap
      (permutation-cons (natRotateHeadToLastPermutation n))

  natContext-append :
    (n m : Nat) →
    natContext (n + m) ≡ natContext n ++ᴸ natContext m
  natContext-append zero m = refl
  natContext-append (suc n) m =
    cong (natAssumption ∷_) (natContext-append n m)

  embedNatProof :
    {n : Nat} →
    MALLPNatProof n →
    MALLPNatTheory (natContext n) (just natFormula)
  embedNatProof (natLiteralProof value) = mallp-nat-literal value
  embedNatProof (natPrimitiveProof operation) =
    mallp-nat-primitive operation
  embedNatProof natArgumentProof =
    mallp-nat-logical mallp-ax
  embedNatProof (natExchangeProof proof) =
    mallp-nat-exchange permutation-swap (embedNatProof proof)
  embedNatProof (natRotateHeadToLastProof {n = n} proof) =
    mallp-nat-exchange
      (natRotateHeadToLastPermutation n)
      (embedNatProof proof)
  embedNatProof (natCutProof {n = n} {m = m} first second) =
    mallp-nat-transport
      (sym (natContext-append n m))
      (mallp-nat-cut (embedNatProof first) (embedNatProof second))

  data NatEnvironment : Nat → Set where
    natEnvironmentNil : NatEnvironment zero
    natEnvironmentCons :
      {n : Nat} →
      Nat →
      NatEnvironment n →
      NatEnvironment (suc n)

  splitNatEnvironment :
    (n m : Nat) →
    NatEnvironment (n + m) →
    NatEnvironment n × NatEnvironment m
  splitNatEnvironment zero m environment =
    pair natEnvironmentNil environment
  splitNatEnvironment (suc n) m (natEnvironmentCons value rest)
    with splitNatEnvironment n m rest
  ... | pair prefix suffix =
    pair (natEnvironmentCons value prefix) suffix

  appendNatEnvironment :
    {n : Nat} →
    NatEnvironment n →
    Nat →
    NatEnvironment (suc n)
  appendNatEnvironment natEnvironmentNil value =
    natEnvironmentCons value natEnvironmentNil
  appendNatEnvironment (natEnvironmentCons head rest) value =
    natEnvironmentCons head (appendNatEnvironment rest value)

  rotateHeadToLastEnvironment :
    {n : Nat} →
    NatEnvironment (suc n) →
    NatEnvironment (suc n)
  rotateHeadToLastEnvironment (natEnvironmentCons head rest) =
    appendNatEnvironment rest head

  splitNatEnvironment-append :
    (n : Nat) →
    (environment : NatEnvironment n) →
    (value : Nat) →
    splitNatEnvironment n (suc zero)
      (appendNatEnvironment environment value) ≡
    pair environment (natEnvironmentCons value natEnvironmentNil)
  splitNatEnvironment-append zero natEnvironmentNil value = refl
  splitNatEnvironment-append (suc n)
    (natEnvironmentCons head rest) value
    rewrite splitNatEnvironment-append n rest value = refl

  -- Environments are ordered like the target stack, with its top first.
  -- A primitive therefore sees right above left and computes left op right.
  interpretMALLPNatProof :
    {n : Nat} →
    MALLPNatProof n →
    NatEnvironment n →
    Nat
  interpretMALLPNatProof (natLiteralProof value) natEnvironmentNil = value
  interpretMALLPNatProof (natPrimitiveProof operation)
    (natEnvironmentCons right
      (natEnvironmentCons left natEnvironmentNil)) =
        applyNatOp operation left right
  interpretMALLPNatProof natArgumentProof
    (natEnvironmentCons argument natEnvironmentNil) = argument
  interpretMALLPNatProof (natExchangeProof proof)
    (natEnvironmentCons first (natEnvironmentCons second natEnvironmentNil)) =
      interpretMALLPNatProof proof
        (natEnvironmentCons second (natEnvironmentCons first natEnvironmentNil))
  interpretMALLPNatProof
    (natRotateHeadToLastProof proof) environment =
      interpretMALLPNatProof proof
        (rotateHeadToLastEnvironment environment)
  interpretMALLPNatProof
    (natCutProof {n = n} {m = m} first second) environment
    with splitNatEnvironment n m environment
  ... | pair prefix suffix =
    interpretMALLPNatProof second
      (natEnvironmentCons (interpretMALLPNatProof first prefix) suffix)

  natExprProof : NatExpr → MALLPNatProof zero
  natExprProof (literal value) = natLiteralProof value
  natExprProof (binary operation left right) =
    natCutProof (natExprProof left)
      (natCutProof (natExprProof right) (natPrimitiveProof operation))

  natExpr-proof-derivation :
    (expression : NatExpr) →
    MALLPNatTheory [] (just natFormula)
  natExpr-proof-derivation expression = embedNatProof (natExprProof expression)

  natExprProof-adequate :
    (expression : NatExpr) →
    interpretMALLPNatProof (natExprProof expression) natEnvironmentNil ≡
    evalNatExpr expression
  natExprProof-adequate (literal value) = refl
  natExprProof-adequate (binary operation left right)
    rewrite natExprProof-adequate left
          | natExprProof-adequate right = refl

  ----------------------------------------------------------------------
  -- General finite linear Nat trees.
  --
  -- The index n counts live Nat assumptions. Literal leaves consume zero
  -- resources; an argument leaf consumes exactly one; binary composition
  -- partitions n+m assumptions between its two premises. This makes
  -- duplication and discard unrepresentable in this source core.
  ----------------------------------------------------------------------

  data NatResourceExpr : Nat → Set where
    resourceLiteral :
      Nat →
      NatResourceExpr zero

    resourceArgument :
      NatResourceExpr (suc zero)

    resourceBinary :
      {n m : Nat} →
      NatOp →
      NatResourceExpr n →
      NatResourceExpr m →
      NatResourceExpr (n + m)

  evalNatResourceExpr :
    {n : Nat} →
    NatResourceExpr n →
    NatEnvironment n →
    Nat
  evalNatResourceExpr (resourceLiteral value) natEnvironmentNil = value
  evalNatResourceExpr resourceArgument
    (natEnvironmentCons value natEnvironmentNil) = value
  evalNatResourceExpr
    (resourceBinary {n = n} {m = m} operation left right) environment
    with splitNatEnvironment n m environment
  ... | pair leftEnvironment rightEnvironment =
    applyNatOp operation
      (evalNatResourceExpr left leftEnvironment)
      (evalNatResourceExpr right rightEnvironment)

  natResourceProof :
    {n : Nat} →
    NatResourceExpr n →
    MALLPNatProof n
  natResourceProof (resourceLiteral value) = natLiteralProof value
  natResourceProof resourceArgument = natArgumentProof
  natResourceProof
    (resourceBinary {n = n} {m = m} operation left right) =
      natCutProof
        (natResourceProof left)
        (natRotateHeadToLastProof
          (natCutProof (natResourceProof right)
            (natPrimitiveProof operation)))

  natResource-proof-derivation :
    {n : Nat} →
    (expression : NatResourceExpr n) →
    MALLPNatTheory (natContext n) (just natFormula)
  natResource-proof-derivation expression =
    embedNatProof (natResourceProof expression)

  natResourceProof-adequate :
    {n : Nat} →
    (expression : NatResourceExpr n) →
    (environment : NatEnvironment n) →
    interpretMALLPNatProof (natResourceProof expression) environment ≡
    evalNatResourceExpr expression environment
  natResourceProof-adequate (resourceLiteral value) natEnvironmentNil = refl
  natResourceProof-adequate resourceArgument
    (natEnvironmentCons value natEnvironmentNil) = refl
  natResourceProof-adequate
    (resourceBinary {n = n} {m = m} operation left right) environment
    with splitNatEnvironment n m environment
  ... | pair leftEnvironment rightEnvironment
    rewrite natResourceProof-adequate left leftEnvironment
          | splitNatEnvironment-append m rightEnvironment
              (evalNatResourceExpr left leftEnvironment)
          | natResourceProof-adequate right rightEnvironment = refl

  -- A unary source function is linear when its sole argument occurs once.
  -- Its proof term is an MALLP derivation with exactly one Nat assumption.
  natLinearProof : NatLinearExpr → MALLPNatProof (suc zero)
  natLinearProof natArgument = natArgumentProof
  natLinearProof (natLinearLeft operation input right) =
    natCutProof
      (natLinearProof input)
      (natCutProof (natExprProof right) (natPrimitiveProof operation))
  natLinearProof (natLinearRight operation left input) =
    natCutProof
      (natLinearProof input)
      (natCutProof (natExprProof left)
        (natExchangeProof (natPrimitiveProof operation)))

  natLinear-proof-derivation :
    (expression : NatLinearExpr) →
    MALLPNatTheory (natContext (suc zero)) (just natFormula)
  natLinear-proof-derivation expression =
    embedNatProof (natLinearProof expression)

  natLinearProof-adequate :
    (expression : NatLinearExpr) →
    (argument : Nat) →
    interpretMALLPNatProof (natLinearProof expression)
      (natEnvironmentCons argument natEnvironmentNil) ≡
    evalNatLinearExpr expression argument
  natLinearProof-adequate natArgument argument = refl
  natLinearProof-adequate
    (natLinearLeft operation input right) argument
      rewrite natLinearProof-adequate input argument
            | natExprProof-adequate right = refl
  natLinearProof-adequate
    (natLinearRight operation left input) argument
      rewrite natExprProof-adequate left
            | natLinearProof-adequate input argument = refl

  -- Composition of the proof-term interpretation, the typed Forth stack
  -- machine, and the rendered postfix-token interpreter. This theorem is for
  -- the mathematical token machine, not yet the Haskell printer or real Gforth.
  natMALLP-forth-sound :
    {Γ : List StackType} →
    (expression : NatExpr) →
    (stack : Stack Γ) →
    execTokens
      (renderForth (compileNat expression))
      (forgetStack stack) ≡
    just
      (interpretMALLPNatProof (natExprProof expression) natEnvironmentNil
        ∷ forgetStack stack)
  natMALLP-forth-sound expression stack =
    trans
      (renderForth-sound (compileNat expression) stack)
      (trans
        (cong (λ values → just values)
          (cong forgetStack (execForthCode-correct expression stack)))
        (cong (λ value → just (value ∷ forgetStack stack))
          (sym (natExprProof-adequate expression))))

  natLinear-forth-sound :
    (expression : NatLinearExpr) →
    (argument : Nat) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execTokens
      (renderForth (compileNatLinear expression))
      (forgetStack (pushCell argument stack)) ≡
    just (evalNatLinearExpr expression argument ∷ forgetStack stack)
  natLinear-forth-sound expression argument stack =
    trans
      (renderForth-sound
        (compileNatLinear expression)
        (pushCell argument stack))
      (cong (λ values → just values)
        (cong forgetStack (execNatLinear-correct expression argument stack)))

  natLinearMALLP-forth-sound :
    (expression : NatLinearExpr) →
    (argument : Nat) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execTokens
      (renderForth (compileNatLinear expression))
      (forgetStack (pushCell argument stack)) ≡
    just
      (interpretMALLPNatProof (natLinearProof expression)
        (natEnvironmentCons argument natEnvironmentNil) ∷
        forgetStack stack)
  natLinearMALLP-forth-sound expression argument stack =
    trans
      (natLinear-forth-sound expression argument stack)
      (cong
        (λ value → just (value ∷ forgetStack stack))
        (sym (natLinearProof-adequate expression argument)))

  ----------------------------------------------------------------------
  -- Binary linear Nat primitives.
  --
  -- The two source arguments are each consumed once.  The incoming stack
  -- has the second argument at its head, matching the environment order
  -- used by the MALLP primitive signature.  Exchange is explicit.
  ----------------------------------------------------------------------

  data NatBinaryLinearExpr : Set where
    natBinaryArguments : NatOp → NatBinaryLinearExpr
    natBinaryArgumentsExchanged : NatOp → NatBinaryLinearExpr

  evalNatBinaryLinearExpr : NatBinaryLinearExpr → Nat → Nat → Nat
  evalNatBinaryLinearExpr (natBinaryArguments operation) first second =
    applyNatOp operation first second
  evalNatBinaryLinearExpr
    (natBinaryArgumentsExchanged operation) first second =
      applyNatOp operation second first

  compileNatBinaryLinear :
    {Γ : List StackType} →
    NatBinaryLinearExpr →
    ForthCode (natCell ∷ natCell ∷ Γ) (natCell ∷ Γ)
  compileNatBinaryLinear (natBinaryArguments operation) =
    binaryWord operation
  compileNatBinaryLinear (natBinaryArgumentsExchanged operation) =
    sequence swapNat (binaryWord operation)

  execNatBinaryLinear-correct :
    (expression : NatBinaryLinearExpr) →
    (first second : Nat) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execForthCode (compileNatBinaryLinear expression)
      (pushCell second (pushCell first stack)) ≡
    pushCell (evalNatBinaryLinearExpr expression first second) stack
  execNatBinaryLinear-correct
    (natBinaryArguments operation) first second stack =
      execForthCode-binary-correct operation first second stack
  execNatBinaryLinear-correct
    (natBinaryArgumentsExchanged operation) first second stack =
      execForthCode-binary-correct operation second first stack

  natBinary-forth-sound :
    (expression : NatBinaryLinearExpr) →
    (first second : Nat) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execTokens
      (renderForth (compileNatBinaryLinear expression))
      (forgetStack (pushCell second (pushCell first stack))) ≡
    just (evalNatBinaryLinearExpr expression first second ∷ forgetStack stack)
  natBinary-forth-sound expression first second stack =
    trans
      (renderForth-sound
        (compileNatBinaryLinear expression)
        (pushCell second (pushCell first stack)))
      (cong (λ values → just values)
        (cong forgetStack
          (execNatBinaryLinear-correct expression first second stack)))

  natBinaryProof : NatBinaryLinearExpr → MALLPNatProof (suc (suc zero))
  natBinaryProof (natBinaryArguments operation) =
    natPrimitiveProof operation
  natBinaryProof (natBinaryArgumentsExchanged operation) =
    natExchangeProof (natPrimitiveProof operation)

  natBinary-proof-derivation :
    (expression : NatBinaryLinearExpr) →
    MALLPNatTheory (natContext (suc (suc zero))) (just natFormula)
  natBinary-proof-derivation expression =
    embedNatProof (natBinaryProof expression)

  natBinaryProof-adequate :
    (expression : NatBinaryLinearExpr) →
    (first second : Nat) →
    interpretMALLPNatProof (natBinaryProof expression)
      (natEnvironmentCons second
        (natEnvironmentCons first natEnvironmentNil)) ≡
    evalNatBinaryLinearExpr expression first second
  natBinaryProof-adequate (natBinaryArguments operation) first second = refl
  natBinaryProof-adequate
    (natBinaryArgumentsExchanged operation) first second = refl

  natBinaryMALLP-forth-sound :
    (expression : NatBinaryLinearExpr) →
    (first second : Nat) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execTokens
      (renderForth (compileNatBinaryLinear expression))
      (forgetStack (pushCell second (pushCell first stack))) ≡
    just
      (interpretMALLPNatProof (natBinaryProof expression)
        (natEnvironmentCons second
          (natEnvironmentCons first natEnvironmentNil)) ∷
        forgetStack stack)
  natBinaryMALLP-forth-sound expression first second stack =
    trans
      (natBinary-forth-sound expression first second stack)
      (cong
        (λ value → just (value ∷ forgetStack stack))
        (sym (natBinaryProof-adequate expression first second)))

  ----------------------------------------------------------------------
  -- Closed PureLang lets: substitution without weakening or contraction.
  --
  -- A closed binding owns no MALLP assumptions.  A zero-use binding may be
  -- skipped, and a multi-use binding may be inlined into independent copies
  -- of its closed proof.  This is distinct from copying or discarding a live
  -- linear resource.  The theorem is intentionally restricted to a closed
  -- Nat term; open environments need the resource-indexed judgement below
  -- this compiler layer before analogous transformations are admitted.
  ----------------------------------------------------------------------

  data NatLocalIndex : Nat → Set where
    local-zero : {n : Nat} → NatLocalIndex (suc n)
    local-suc :
      {n : Nat} →
      NatLocalIndex n →
      NatLocalIndex (suc n)

  data NatLocalExpr : Nat → Set where
    local-literal :
      {n : Nat} →
      Nat →
      NatLocalExpr n

    local-variable :
      {n : Nat} →
      NatLocalIndex n →
      NatLocalExpr n

    local-binary :
      {n : Nat} →
      NatOp →
      NatLocalExpr n →
      NatLocalExpr n →
      NatLocalExpr n

    local-let :
      {n : Nat} →
      NatLocalExpr n →
      NatLocalExpr (suc n) →
      NatLocalExpr n

  data NatExprEnvironment : Nat → Set where
    natExprEnvironmentNil : NatExprEnvironment zero
    natExprEnvironmentCons :
      {n : Nat} →
      NatExpr →
      NatExprEnvironment n →
      NatExprEnvironment (suc n)

  lookupNatExpr :
    {n : Nat} →
    NatLocalIndex n →
    NatExprEnvironment n →
    NatExpr
  lookupNatExpr local-zero (natExprEnvironmentCons expression environment) =
    expression
  lookupNatExpr (local-suc index)
    (natExprEnvironmentCons expression environment) =
      lookupNatExpr index environment

  evalNatExprEnvironment :
    {n : Nat} →
    NatExprEnvironment n →
    NatEnvironment n
  evalNatExprEnvironment natExprEnvironmentNil = natEnvironmentNil
  evalNatExprEnvironment
    (natExprEnvironmentCons expression environment) =
      natEnvironmentCons (evalNatExpr expression)
        (evalNatExprEnvironment environment)

  lookupNatValue :
    {n : Nat} →
    NatLocalIndex n →
    NatEnvironment n →
    Nat
  lookupNatValue local-zero (natEnvironmentCons value environment) = value
  lookupNatValue (local-suc index)
    (natEnvironmentCons value environment) =
      lookupNatValue index environment

  evalNatLocalExpr :
    {n : Nat} →
    NatLocalExpr n →
    NatEnvironment n →
    Nat
  evalNatLocalExpr (local-literal value) environment = value
  evalNatLocalExpr (local-variable index) environment =
    lookupNatValue index environment
  evalNatLocalExpr (local-binary operation left right) environment =
    applyNatOp operation
      (evalNatLocalExpr left environment)
      (evalNatLocalExpr right environment)
  evalNatLocalExpr (local-let bound body) environment =
    evalNatLocalExpr body
      (natEnvironmentCons (evalNatLocalExpr bound environment) environment)

  inlineNatLocalExpr :
    {n : Nat} →
    NatLocalExpr n →
    NatExprEnvironment n →
    NatExpr
  inlineNatLocalExpr (local-literal value) environment = literal value
  inlineNatLocalExpr (local-variable index) environment =
    lookupNatExpr index environment
  inlineNatLocalExpr (local-binary operation left right) environment =
    binary operation
      (inlineNatLocalExpr left environment)
      (inlineNatLocalExpr right environment)
  inlineNatLocalExpr (local-let bound body) environment =
    inlineNatLocalExpr body
      (natExprEnvironmentCons
        (inlineNatLocalExpr bound environment)
        environment)

  lookupNatExpr-adequate :
    {n : Nat} →
    (index : NatLocalIndex n) →
    (environment : NatExprEnvironment n) →
    evalNatExpr (lookupNatExpr index environment) ≡
    lookupNatValue index (evalNatExprEnvironment environment)
  lookupNatExpr-adequate local-zero
    (natExprEnvironmentCons expression environment) = refl
  lookupNatExpr-adequate (local-suc index)
    (natExprEnvironmentCons expression environment) =
      lookupNatExpr-adequate index environment

  inlineNatLocalExpr-adequate :
    {n : Nat} →
    (expression : NatLocalExpr n) →
    (environment : NatExprEnvironment n) →
    evalNatExpr (inlineNatLocalExpr expression environment) ≡
    evalNatLocalExpr expression (evalNatExprEnvironment environment)
  inlineNatLocalExpr-adequate (local-literal value) environment = refl
  inlineNatLocalExpr-adequate (local-variable index) environment =
    lookupNatExpr-adequate index environment
  inlineNatLocalExpr-adequate
    (local-binary operation left right) environment
      rewrite inlineNatLocalExpr-adequate left environment
            | inlineNatLocalExpr-adequate right environment = refl
  inlineNatLocalExpr-adequate (local-let bound body) environment
      rewrite inlineNatLocalExpr-adequate body
                (natExprEnvironmentCons
                  (inlineNatLocalExpr bound environment)
                  environment)
            | inlineNatLocalExpr-adequate bound environment = refl

  closedNatLocal-proof :
    (expression : NatLocalExpr zero) →
    MALLPNatTheory [] (just natFormula)
  closedNatLocal-proof expression =
    natExpr-proof-derivation
      (inlineNatLocalExpr expression natExprEnvironmentNil)

  closedNatLocal-proof-adequate :
    (expression : NatLocalExpr zero) →
    interpretMALLPNatProof
      (natExprProof
        (inlineNatLocalExpr expression natExprEnvironmentNil))
      natEnvironmentNil ≡
    evalNatLocalExpr expression natEnvironmentNil
  closedNatLocal-proof-adequate expression =
    trans
      (natExprProof-adequate
        (inlineNatLocalExpr expression natExprEnvironmentNil))
      (inlineNatLocalExpr-adequate expression natExprEnvironmentNil)

  closedNatLocal-forth-sound :
    {Γ : List StackType} →
    (expression : NatLocalExpr zero) →
    (stack : Stack Γ) →
    execTokens
      (renderForth
        (compileNat
          (inlineNatLocalExpr expression natExprEnvironmentNil)))
      (forgetStack stack) ≡
    just
      (evalNatLocalExpr expression natEnvironmentNil ∷
        forgetStack stack)
  closedNatLocal-forth-sound expression stack =
    trans
      (natMALLP-forth-sound
        (inlineNatLocalExpr expression natExprEnvironmentNil)
        stack)
      (cong
        (λ value → just (value ∷ forgetStack stack))
        (closedNatLocal-proof-adequate expression))

  maxNat : Nat → Nat → Nat
  maxNat zero y = y
  maxNat (suc x) zero = suc x
  maxNat (suc x) (suc y) = suc (maxNat x y)

  stackPeak : NatExpr → Nat
  stackPeak (literal n) = suc zero
  stackPeak (binary op left right) =
    maxNat (stackPeak left) (suc (stackPeak right))

  record StackContract : Set where
    constructor stackContract
    field
      requiredInputCells : Nat
      resultCells : Nat
      peakAdditionalCells : Nat
  open StackContract public

  stackContractOf : NatExpr → StackContract
  stackContractOf expression =
    stackContract zero (suc zero) (stackPeak expression)

  compiledNat-contract :
    (e : NatExpr) →
    requiredInputCells (stackContractOf e) ≡ zero
  compiledNat-contract e = refl

  compiledNat-result :
    (e : NatExpr) →
    resultCells (stackContractOf e) ≡ suc zero
  compiledNat-result e = refl

------------------------------------------------------------------------
-- Pure Boolean values as additive MALLP proofs
--
-- Bool = 1 ⊕ 1.  True and False are the two additive introductions; their
-- proofs consume no linear assumptions.  The target uses Forth's canonical
-- TRUE/FALSE values and preserves any caller-owned residual stack.
------------------------------------------------------------------------

module StrictBoolCompiler where

  boolFormula : PolType posPolarity
  boolFormula = one⁺ ⊕⁺ one⁺

  data BoolProof : Set where
    boolTrueProof boolFalseProof : BoolProof

  boolProofDerivation : BoolProof → MALLP [] (just boolFormula)
  boolProofDerivation boolTrueProof = mallp-plus-left mallp-one
  boolProofDerivation boolFalseProof = mallp-plus-right mallp-one

  interpretBoolProof : BoolProof → Bool
  interpretBoolProof boolTrueProof = true
  interpretBoolProof boolFalseProof = false

  data BoolStackType : Set where
    boolCell : BoolStackType

  data BoolStack : List BoolStackType → Set where
    emptyBoolStack : BoolStack []
    pushBooleanValue :
      {Γ : List BoolStackType} →
      Bool →
      BoolStack Γ →
      BoolStack (boolCell ∷ Γ)

  forgetBoolStack : {Γ : List BoolStackType} → BoolStack Γ → List Bool
  forgetBoolStack emptyBoolStack = []
  forgetBoolStack (pushBooleanValue value stack) =
    value ∷ forgetBoolStack stack

  data BoolForthCode :
    List BoolStackType → List BoolStackType → Set where
    pushBoolean :
      {Γ : List BoolStackType} →
      Bool →
      BoolForthCode Γ (boolCell ∷ Γ)

  execBoolCode :
    {Γ Δ : List BoolStackType} →
    BoolForthCode Γ Δ →
    BoolStack Γ →
    BoolStack Δ
  execBoolCode (pushBoolean value) stack =
    pushBooleanValue value stack

  data BoolForthToken : Set where
    pushTrueToken pushFalseToken : BoolForthToken

  renderBoolCode :
    {Γ Δ : List BoolStackType} →
    BoolForthCode Γ Δ →
    List BoolForthToken
  renderBoolCode (pushBoolean true) = pushTrueToken ∷ []
  renderBoolCode (pushBoolean false) = pushFalseToken ∷ []

  execBoolToken :
    BoolForthToken →
    List Bool →
    List Bool
  execBoolToken pushTrueToken stack = true ∷ stack
  execBoolToken pushFalseToken stack = false ∷ stack

  execBoolTokens :
    List BoolForthToken →
    List Bool →
    Maybe (List Bool)
  execBoolTokens [] stack = just stack
  execBoolTokens (token ∷ tokens) stack =
    execBoolTokens tokens (execBoolToken token stack)

  renderBoolCode-sound :
    {Γ Δ : List BoolStackType} →
    (code : BoolForthCode Γ Δ) →
    (stack : BoolStack Γ) →
    execBoolTokens (renderBoolCode code) (forgetBoolStack stack) ≡
    just (forgetBoolStack (execBoolCode code stack))
  renderBoolCode-sound (pushBoolean true) stack = refl
  renderBoolCode-sound (pushBoolean false) stack = refl

  compileBoolProof :
    BoolProof →
    BoolForthCode [] (boolCell ∷ [])
  compileBoolProof boolTrueProof = pushBoolean true
  compileBoolProof boolFalseProof = pushBoolean false

  boolMALLP-forth-sound :
    (proof : BoolProof) →
    execBoolTokens
      (renderBoolCode (compileBoolProof proof))
      [] ≡ just (interpretBoolProof proof ∷ [])
  boolMALLP-forth-sound boolTrueProof = refl
  boolMALLP-forth-sound boolFalseProof = refl

open StrictBoolCompiler public

open StrictNatCompiler public

------------------------------------------------------------------------
-- Pure Unit as the MALLP multiplicative unit
--
-- Unit is the formula 1.  Its unique source value carries no target cell;
-- compiling its proof is the identity stack transition, with no emitted
-- Forth tokens and no consumption of the caller's residual stack.
------------------------------------------------------------------------

module StrictUnitCompiler where

  unitOneProof : MALLP [] (just one⁺)
  unitOneProof = mallp-one

  -- Unit contributes no runtime cell. Its proof lowers to the empty token
  -- sequence, whose formal execution preserves the caller's entire stack.
  compileUnitProof :
    MALLP [] (just one⁺) →
    List ForthToken
  compileUnitProof derivation = []

  unitMALLP-forth-sound :
    (derivation : MALLP [] (just one⁺)) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execTokens
      (compileUnitProof derivation)
      (forgetStack stack) ≡
    just (forgetStack stack)
  unitMALLP-forth-sound derivation stack = refl

open StrictUnitCompiler public


