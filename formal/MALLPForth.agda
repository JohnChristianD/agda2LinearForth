{-# OPTIONS --with-K --rewriting --confluence-check --polarity --lossy-unification --exact-split --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections #-}

------------------------------------------------------------------------
-- SovereignRationalSED
--
-- Five original foundational packages plus Laurent's constructive MALLP
-- calculus, without exponentials or Seely structure.  Finite-list computation
-- remains a separate helper witness.  Rewrite rules are registered once
-- at the outer module so Agda checks the combined rewrite system together.
-- The physical modules do not treat logical rewrite equations as physical
-- laws; they expose explicit finite data and proof obligations.
------------------------------------------------------------------------

module MALLPForth where

--Required for Polymorphism:
open import Agda.Primitive using (Level; lsuc; _⊔_) public
open import Agda.Builtin.Nat public hiding (_<_)
open import Agda.Builtin.Bool public
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Agda.Builtin.String public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Word using (Word64; primWord64ToNat; primWord64FromNat) public
open import Agda.Builtin.Word.Properties using (primWord64ToNatInjective) public
-- Agda 2.8.0.2 has no Agda.Builtin.Tuple module; the product record _×_ below
-- is the explicit project-owned pair, while Sigma supplies dependent pairs.
open import Agda.Builtin.Unit public
open import Agda.Builtin.Strict public
open import Agda.Builtin.Coinduction public
import Agda.Builtin.Reflection as Reflection
-- Agda 2.8 has no Agda.Builtin.Empty module; define the empty type locally.
data ⊥ : Set where

-- Word64 equality is reflected exactly by its unsigned Nat interpretation.
record Equivalence (A B : Set) : Set where
  constructor equivalence
  field
    toForward : A → B
    toBackward : B → A
open Equivalence public

word64EqualityCong :
  {A B : Set} {left right : A} →
  (function : A → B) →
  left ≡ right → function left ≡ function right
word64EqualityCong function refl = refl

word64EqualityByNat :
  {left right : Word64} →
  Equivalence
    (left ≡ right)
    (primWord64ToNat left ≡ primWord64ToNat right)
word64EqualityByNat =
  equivalence
    (word64EqualityCong primWord64ToNat)
    (primWord64ToNatInjective _ _)

-- Proof-carrying Forth instruction vocabulary and canonical renderer.
-- Kept here so generated compiler witnesses and MALLP derivations share
-- one source-level interface.
data ForthTextToken : Set where
  textPushLiteral : Nat → ForthTextToken
  textPushWord64 : Nat → Nat → ForthTextToken
  textAddWord textMonusWord textMultiplyWord textSwapWord : ForthTextToken
  textRollWord : Nat → ForthTextToken
  textTrueWord textFalseWord : ForthTextToken
  textIf : List ForthTextToken → List ForthTextToken → ForthTextToken

mutual
  renderForthTokenText : ForthTextToken → String
  renderForthTokenText (textPushLiteral value) =
    primStringAppend "s\" "
      (primStringAppend (primShowNat value) "\" MALLP-PARSE-NAT ")
  renderForthTokenText (textPushWord64 high low) =
    primStringAppend
      (renderForthTokenText (textPushLiteral high))
      (renderForthTokenText (textPushLiteral low))
  renderForthTokenText textAddWord = "MALLP-NAT-ADD "
  renderForthTokenText textMonusWord = "MALLP-NAT-MONUS "
  renderForthTokenText textMultiplyWord = "MALLP-NAT-MUL "
  renderForthTokenText textSwapWord = "SWAP "
  renderForthTokenText (textRollWord depth) =
    primStringAppend (primShowNat depth) " ROLL "
  renderForthTokenText textTrueWord = "TRUE "
  renderForthTokenText textFalseWord = "FALSE "
  renderForthTokenText (textIf whenTrue whenFalse) =
    primStringAppend "IF "
      (primStringAppend (renderForthTokensText whenTrue)
        (primStringAppend "ELSE "
          (primStringAppend (renderForthTokensText whenFalse) "THEN ")))

  renderForthTokensText : List ForthTextToken → String
  renderForthTokensText [] = ""
  renderForthTokensText (token ∷ tokens) =
    primStringAppend (renderForthTokenText token)
      (renderForthTokensText tokens)

renderForthWordText : String → List ForthTextToken → String
renderForthWordText name tokens =
  primStringAppend ": "
    (primStringAppend name
      (primStringAppend " "
        (primStringAppend (renderForthTokensText tokens) ";")))


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

subst :
  {A : Set} →
  (P : A → Set) →
  {x y : A} →
  x ≡ y →
  P x →
  P y
subst P refl value = value

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
-- five foundational packages and Laurent MALLP.
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
  -- 5. Spector-style symmetric bar recursion over finite partial maps.
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
  -- 6. LAURENT'S MULTIPLICATIVE-ADDITIVE POLARIZED LINEAR LOGIC (MALLP)
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
  -- Publicly expose the five foundational packages and the Laurent MALLP
  -- calculus.  No Seely / exponential structure is part of this interface.
  ----------------------------------------------------------------------

  open ForsterEnumerability public
  open MarkovLeastWitness public
  open MacLaneCoherence public
  open CohesiveRetractions public
  open SymmetricBarRecursion public
  open LaurentPolarizedMALLP public

open Foundations.ForsterEnumerability public
open Foundations.MarkovLeastWitness public
open Foundations.MacLaneCoherence public
open Foundations.CohesiveRetractions public
open Foundations.SymmetricBarRecursion public
open Foundations.LaurentPolarizedMALLP public

------------------------------------------------------------------------
-- A relational denotation for every Laurent MALLP proof constructor.
--
-- Atoms are interpreted parametrically. Positive/negative tensor and
-- par are paired resources; plus/with are tagged alternatives; one/bottom
-- and zero/top are dual unit/empty objects. Polarity shifts exchange the
-- two value interpretations. Cut is relational composition (an explicit
-- intermediate witness), exchange reindexes the environment, and additive
-- branches inspect one tagged alternative.
--
-- This is a concrete Rel-style sound interpretation of the proof rules.
-- It is deliberately not labelled as the full Hamano-Scott categorical
-- model: that stronger result needs the reflective/coreflective adjunction
-- and its *-autonomous coherence data as explicit Agda structures.
------------------------------------------------------------------------

module MALLPRelationalDenotation (Atom : Nat → Set) where

  data DenotationSum (A B : Set) : Set where
    denLeft : A → DenotationSum A B
    denRight : B → DenotationSum A B

  record DenotationWitness (A : Set) (P : A → Set) : Set where
    constructor denotationWitness
    field
      witnessValue : A
      witnessEvidence : P witnessValue
  open DenotationWitness public

  mutual
    PosValue : PolType posPolarity → Set
    PosValue (atom⁺ index) = Atom index
    PosValue one⁺ = ⊤
    PosValue zero⁺ = ⊥
    PosValue (left ⊗⁺ right) = PosValue left × PosValue right
    PosValue (left ⊕⁺ right) = DenotationSum (PosValue left) (PosValue right)
    PosValue (down⁺ negative) = NegValue negative

    NegValue : PolType negPolarity → Set
    NegValue (atom⁻ index) = Atom index
    NegValue bot⁻ = ⊤
    NegValue top⁻ = ⊥
    NegValue (left ⅋⁻ right) = NegValue left × NegValue right
    NegValue (left &⁻ right) = DenotationSum (NegValue left) (NegValue right)
    NegValue (up⁻ positive) = PosValue positive

  mutual
    dualPositiveValue :
      (positive : PolType posPolarity) →
      PosValue positive → NegValue (dualPos positive)
    dualNegativeValue :
      (negative : PolType negPolarity) →
      NegValue negative → PosValue (dualNeg negative)
  
    dualPositiveValue (atom⁺ index) value = value
    dualPositiveValue one⁺ value = value
    dualPositiveValue zero⁺ ()
    dualPositiveValue (left ⊗⁺ right) (pair leftValue rightValue) =
      pair (dualPositiveValue left leftValue) (dualPositiveValue right rightValue)
    dualPositiveValue (left ⊕⁺ right) (denLeft value) =
      denLeft (dualPositiveValue left value)
    dualPositiveValue (left ⊕⁺ right) (denRight value) =
      denRight (dualPositiveValue right value)
    dualPositiveValue (down⁺ negative) value =
      dualNegativeValue negative value
  
    dualNegativeValue (atom⁻ index) value = value
    dualNegativeValue bot⁻ value = value
    dualNegativeValue top⁻ ()
    dualNegativeValue (left ⅋⁻ right) (pair leftValue rightValue) =
      pair (dualNegativeValue left leftValue) (dualNegativeValue right rightValue)
    dualNegativeValue (left &⁻ right) (denLeft value) =
      denLeft (dualNegativeValue left value)
    dualNegativeValue (left &⁻ right) (denRight value) =
      denRight (dualNegativeValue right value)
    dualNegativeValue (up⁻ positive) value =
      dualPositiveValue positive value
  
  mutual
    recoverPositiveValue :
      (positive : PolType posPolarity) →
      NegValue (dualPos positive) → PosValue positive
    recoverPositiveValue (atom⁺ index) value = value
    recoverPositiveValue one⁺ value = value
    recoverPositiveValue zero⁺ ()
    recoverPositiveValue (left ⊗⁺ right) (pair leftValue rightValue) =
      pair (recoverPositiveValue left leftValue)
        (recoverPositiveValue right rightValue)
    recoverPositiveValue (left ⊕⁺ right) (denLeft value) =
      denLeft (recoverPositiveValue left value)
    recoverPositiveValue (left ⊕⁺ right) (denRight value) =
      denRight (recoverPositiveValue right value)
    recoverPositiveValue (down⁺ negative) value =
      recoverNegativeValue negative value

    recoverNegativeValue :
      (negative : PolType negPolarity) →
      PosValue (dualNeg negative) → NegValue negative
    recoverNegativeValue (atom⁻ index) value = value
    recoverNegativeValue bot⁻ value = value
    recoverNegativeValue top⁻ ()
    recoverNegativeValue (left ⅋⁻ right) (pair leftValue rightValue) =
      pair (recoverNegativeValue left leftValue)
        (recoverNegativeValue right rightValue)
    recoverNegativeValue (left &⁻ right) (denLeft value) =
      denLeft (recoverNegativeValue left value)
    recoverNegativeValue (left &⁻ right) (denRight value) =
      denRight (recoverNegativeValue right value)
    recoverNegativeValue (up⁻ positive) value =
      recoverPositiveValue positive value

    recoverPositive-dualPositive :
      (positive : PolType posPolarity) →
      (value : PosValue positive) →
      recoverPositiveValue positive (dualPositiveValue positive value) ≡ value
    recoverPositive-dualPositive (atom⁺ index) value = refl
    recoverPositive-dualPositive one⁺ value = refl
    recoverPositive-dualPositive zero⁺ ()
    recoverPositive-dualPositive (left ⊗⁺ right)
      (pair leftValue rightValue) =
      cong₂ pair
        (recoverPositive-dualPositive left leftValue)
        (recoverPositive-dualPositive right rightValue)
    recoverPositive-dualPositive (left ⊕⁺ right) (denLeft value) =
      cong denLeft (recoverPositive-dualPositive left value)
    recoverPositive-dualPositive (left ⊕⁺ right) (denRight value) =
      cong denRight (recoverPositive-dualPositive right value)
    recoverPositive-dualPositive (down⁺ negative) value =
      recoverNegative-dualNegative negative value

    recoverNegative-dualNegative :
      (negative : PolType negPolarity) →
      (value : NegValue negative) →
      recoverNegativeValue negative (dualNegativeValue negative value) ≡ value
    recoverNegative-dualNegative (atom⁻ index) value = refl
    recoverNegative-dualNegative bot⁻ value = refl
    recoverNegative-dualNegative top⁻ ()
    recoverNegative-dualNegative (left ⅋⁻ right)
      (pair leftValue rightValue) =
      cong₂ pair
        (recoverNegative-dualNegative left leftValue)
        (recoverNegative-dualNegative right rightValue)
    recoverNegative-dualNegative (left &⁻ right) (denLeft value) =
      cong denLeft (recoverNegative-dualNegative left value)
    recoverNegative-dualNegative (left &⁻ right) (denRight value) =
      cong denRight (recoverNegative-dualNegative right value)
    recoverNegative-dualNegative (up⁻ positive) value =
      recoverPositive-dualPositive positive value

  ContextValues : Context → Set
  ContextValues [] = ⊤
  ContextValues (negative ∷ Γ) = NegValue negative × ContextValues Γ

  StoupValue : Stoup → Set
  StoupValue nothing = ⊤
  StoupValue (just positive) = PosValue positive

  splitContextValues :
    {Γ Δ : Context} →
    ContextValues (Γ ++ᴸ Δ) →
    ContextValues Γ × ContextValues Δ
  splitContextValues {Γ = []} {Δ} values = pair tt values
  splitContextValues {Γ = negative ∷ Γ} {Δ} (pair head tail)
    with splitContextValues {Γ = Γ} {Δ = Δ} tail
  ... | pair prefix suffix = pair (pair head prefix) suffix

  permuteContextValues :
    {Γ Δ : Context} →
    ContextPermutation Γ Δ →
    ContextValues Γ → ContextValues Δ
  permuteContextValues permutation-nil tt = tt
  permuteContextValues (permutation-cons permutation) (pair head tail) =
    pair head (permuteContextValues permutation tail)
  permuteContextValues permutation-swap (pair first (pair second tail)) =
    pair second (pair first tail)
  permuteContextValues (permutation-trans first second) values =
    permuteContextValues second (permuteContextValues first values)

  MALLPRelation :
    {Γ : Context} {S : Stoup} →
    MALLP Γ S → ContextValues Γ → StoupValue S → Set

  MALLPRelation {S = just positive} mallp-ax (pair source tt) result =
    result ≡ recoverPositiveValue positive source

  MALLPRelation
    (mallp-cut {Γ = Γ} {Δ = Δ} {P = positive} producer consumer)
    environment result
    with splitContextValues {Γ = Γ} {Δ = Δ} environment
  ... | pair producerEnvironment consumerEnvironment =
    DenotationWitness (PosValue positive)
      (λ intermediate →
        MALLPRelation producer producerEnvironment intermediate ×
        MALLPRelation consumer
          (pair (dualPositiveValue positive intermediate) consumerEnvironment)
          result)

  MALLPRelation (mallp-exchange permutation proof) environment result =
    MALLPRelation proof
      (permuteContextValues (contextPermutation-sym permutation) environment)
      result

  MALLPRelation
    (mallp-tensor {Γ = Γ} {Δ = Δ} left right)
    environment (pair leftValue rightValue)
    with splitContextValues {Γ = Γ} {Δ = Δ} environment
  ... | pair leftEnvironment rightEnvironment =
    MALLPRelation left leftEnvironment leftValue ×
    MALLPRelation right rightEnvironment rightValue

  MALLPRelation mallp-one tt tt = ⊤

  MALLPRelation (mallp-plus-left proof) environment (denLeft value) =
    MALLPRelation proof environment value
  MALLPRelation (mallp-plus-left proof) environment (denRight value) = ⊥

  MALLPRelation (mallp-plus-right proof) environment (denLeft value) = ⊥
  MALLPRelation (mallp-plus-right proof) environment (denRight value) =
    MALLPRelation proof environment value

  MALLPRelation (mallp-par proof) (pair (pair leftValue rightValue) rest) result =
    MALLPRelation proof (pair leftValue (pair rightValue rest)) result

  MALLPRelation (mallp-with left right) (pair (denLeft value) rest) result =
    MALLPRelation left (pair value rest) result
  MALLPRelation (mallp-with left right) (pair (denRight value) rest) result =
    MALLPRelation right (pair value rest) result

  MALLPRelation (mallp-bottom proof) (pair tt rest) result =
    MALLPRelation proof rest result

  MALLPRelation mallp-top (pair () rest) result

  MALLPRelation (mallp-down proof) environment result =
    MALLPRelation proof (pair result environment) tt

  MALLPRelation (mallp-up proof) (pair result environment) tt =
    MALLPRelation proof environment result


------------------------------------------------------------------------
-- GENERIC LINEAR SOURCE TERMS: STRUCTURAL MALLP DERIVATION
--
-- This small, reusable source core indexes every term by its exact live
-- context and result type. Its interpretation is a Laurent MALLP proof.
-- Tensor elimination is par on the negative context; sum elimination is
-- with over a shared branch context; cut is linear substitution; and
-- lambda introduction uses the existing up/par/down rules.
--
-- A closure stores its environment once and its code expects that same
-- environment paired with its explicit argument. No captured resource is
-- copied into code or silently discarded at closure creation.
------------------------------------------------------------------------

data LinearSourceType : Set where
  linearNatType linearIntType linearWord64Type linearBoolType linearUnitType : LinearSourceType
  linearTensorType linearSumType linearArrowType :
    LinearSourceType → LinearSourceType → LinearSourceType

linearSourceFormula : LinearSourceType → PolType posPolarity
linearSourceFormula linearNatType = atom⁺ zero
linearSourceFormula linearIntType = atom⁺ (suc zero)
linearSourceFormula linearWord64Type = atom⁺ (suc (suc zero))
linearSourceFormula linearBoolType = one⁺ ⊕⁺ one⁺
linearSourceFormula linearUnitType = one⁺
linearSourceFormula (linearTensorType A B) =
  linearSourceFormula A ⊗⁺ linearSourceFormula B
linearSourceFormula (linearSumType A B) =
  linearSourceFormula A ⊕⁺ linearSourceFormula B
linearSourceFormula (linearArrowType A B) =
  down⁺ (dualPos (linearSourceFormula A) ⅋⁻ up⁻ (linearSourceFormula B))

linearSourceContext : List LinearSourceType → Context
linearSourceContext [] = []
linearSourceContext (A ∷ Γ) =
  dualPos (linearSourceFormula A) ∷ linearSourceContext Γ

appendLinearContext : List LinearSourceType → List LinearSourceType →
  List LinearSourceType
appendLinearContext [] Δ = Δ
appendLinearContext (A ∷ Γ) Δ = A ∷ appendLinearContext Γ Δ

linearSourceContext-append :
  (Γ Δ : List LinearSourceType) →
  linearSourceContext (appendLinearContext Γ Δ) ≡
  (linearSourceContext Γ ++ᴸ linearSourceContext Δ)
linearSourceContext-append [] Δ = refl
linearSourceContext-append (A ∷ Γ) Δ =
  cong (λ context → dualPos (linearSourceFormula A) ∷ context)
    (linearSourceContext-append Γ Δ)

appendLinearContext-right-unit :
  (Γ : List LinearSourceType) →
  appendLinearContext Γ [] ≡ Γ
appendLinearContext-right-unit [] = refl
appendLinearContext-right-unit (A ∷ Γ) =
  cong (A ∷_) (appendLinearContext-right-unit Γ)

linearSourceContext-right-unit :
  (Γ : List LinearSourceType) →
  linearSourceContext Γ ≡ (linearSourceContext Γ ++ᴸ [])
linearSourceContext-right-unit Γ =
  trans
    (sym (cong linearSourceContext (appendLinearContext-right-unit Γ)))
    (linearSourceContext-append Γ [])

linearContextPermutation :
  {Γ Δ : List LinearSourceType} →
  ContextPermutation Γ Δ →
  ContextPermutation (linearSourceContext Γ) (linearSourceContext Δ)
linearContextPermutation permutation-nil = permutation-nil
linearContextPermutation (permutation-cons permutation) =
  permutation-cons (linearContextPermutation permutation)
linearContextPermutation permutation-swap = permutation-swap
linearContextPermutation (permutation-trans first second) =
  permutation-trans
    (linearContextPermutation first)
    (linearContextPermutation second)

data LinearTerm : List LinearSourceType → LinearSourceType → Set where
  linearVariable :
    {A : LinearSourceType} →
    LinearTerm (A ∷ []) A

  linearExchange :
    {Γ Δ : List LinearSourceType} {A : LinearSourceType} →
    ContextPermutation Γ Δ →
    LinearTerm Γ A →
    LinearTerm Δ A

  linearTensor :
    {Γ Δ : List LinearSourceType} {A B : LinearSourceType} →
    LinearTerm Γ A →
    LinearTerm Δ B →
    LinearTerm (appendLinearContext Γ Δ) (linearTensorType A B)

  linearUnit :
    LinearTerm [] linearUnitType

  -- Eliminating the unique Unit value consumes its linear assumption by
  -- MALLP bottom-left; the residual context and result are preserved.
  linearUnitCaseTerm :
    {Γ : List LinearSourceType} {A : LinearSourceType} →
    LinearTerm Γ A →
    LinearTerm (linearUnitType ∷ Γ) A

  linearInl :
    {Γ : List LinearSourceType} {A B : LinearSourceType} →
    LinearTerm Γ A →
    LinearTerm Γ (linearSumType A B)

  linearInr :
    {Γ : List LinearSourceType} {A B : LinearSourceType} →
    LinearTerm Γ B →
    LinearTerm Γ (linearSumType A B)

  linearTensorElim :
    {Γ : List LinearSourceType} {A B C : LinearSourceType} →
    LinearTerm (A ∷ B ∷ Γ) C →
    LinearTerm (linearTensorType A B ∷ Γ) C

  linearSumCaseTerm :
    {Γ : List LinearSourceType} {A B C : LinearSourceType} →
    LinearTerm (A ∷ Γ) C →
    LinearTerm (B ∷ Γ) C →
    LinearTerm (linearSumType A B ∷ Γ) C

  linearCut :
    {Γ Δ : List LinearSourceType} {A B : LinearSourceType} →
    LinearTerm Γ A →
    LinearTerm (A ∷ Δ) B →
    LinearTerm (appendLinearContext Γ Δ) B

  linearLambda :
    {Γ : List LinearSourceType} {A B : LinearSourceType} →
    LinearTerm (A ∷ Γ) B →
    LinearTerm Γ (linearArrowType A B)

  -- A closure owns one environment value. Its code receives that environment
  -- explicitly paired with its argument, so captured fields stay linear.
  linearClosureTerm :
    {Γ : List LinearSourceType} {Environment Argument Result : LinearSourceType} →
    LinearTerm Γ Environment →
    LinearTerm
      (linearTensorType Environment Argument ∷ [])
      Result →
    LinearTerm Γ
      (linearTensorType Environment
        (linearArrowType (linearTensorType Environment Argument) Result))

-- Proof-level lambda introduction. Keeping this transformation separate
-- lets closure introduction reuse a body derivation without recursively
-- asking deriveMALLP to inspect a newly constructed source term.
deriveLinearLambda :
  {Γ : List LinearSourceType} {A B : LinearSourceType} →
  MALLP
    (dualPos (linearSourceFormula A) ∷ linearSourceContext Γ)
    (just (linearSourceFormula B)) →
  MALLP
    (linearSourceContext Γ)
    (just (linearSourceFormula (linearArrowType A B)))
deriveLinearLambda bodyProof =
  mallp-down
    (mallp-par
      (mallp-exchange permutation-swap
        (mallp-up bodyProof)))

deriveMALLP :
  {Γ : List LinearSourceType} {A : LinearSourceType} →
  LinearTerm Γ A →
  MALLP (linearSourceContext Γ) (just (linearSourceFormula A))
deriveMALLP linearVariable = mallp-ax
deriveMALLP (linearExchange permutation term) =
  mallp-exchange (linearContextPermutation permutation) (deriveMALLP term)
deriveMALLP
  (linearTensor {Γ = Γ} {Δ = Δ} {A = A} {B = B} left right) =
  subst
    (λ context → MALLP context
      (just (linearSourceFormula (linearTensorType A B))))
    (sym (linearSourceContext-append Γ Δ))
    (mallp-tensor (deriveMALLP left) (deriveMALLP right))
deriveMALLP linearUnit = mallp-one
deriveMALLP (linearUnitCaseTerm body) =
  mallp-bottom (deriveMALLP body)
deriveMALLP (linearInl term) = mallp-plus-left (deriveMALLP term)
deriveMALLP (linearInr term) = mallp-plus-right (deriveMALLP term)
deriveMALLP (linearTensorElim body) = mallp-par (deriveMALLP body)
deriveMALLP (linearSumCaseTerm whenLeft whenRight) =
  mallp-with (deriveMALLP whenLeft) (deriveMALLP whenRight)
deriveMALLP (linearCut {Γ = Γ} {Δ = Δ} {B = B} producer consumer) =
  subst
    (λ context → MALLP context (just (linearSourceFormula B)))
    (sym (linearSourceContext-append Γ Δ))
    (mallp-cut (deriveMALLP producer) (deriveMALLP consumer))
deriveMALLP (linearLambda body) =
  deriveLinearLambda (deriveMALLP body)
deriveMALLP
  (linearClosureTerm
    {Γ = Γ}
    {Environment = Environment}
    {Argument = Argument}
    {Result = Result}
    environment body) =
  subst
    (λ context → MALLP context
      (just (linearSourceFormula
        (linearTensorType Environment
          (linearArrowType (linearTensorType Environment Argument) Result)))))
    (sym (linearSourceContext-right-unit Γ))
    (mallp-tensor
      {Γ = linearSourceContext Γ}
      {Δ = []}
      (deriveMALLP environment)
      (deriveLinearLambda (deriveMALLP body)))

-- General tensor permutation is a derived source term, not a special rule.
linearTensorSwap :
  {A B : LinearSourceType} →
  LinearTerm
    (linearTensorType A B ∷ [])
    (linearTensorType B A)
linearTensorSwap =
  linearTensorElim
    (linearExchange permutation-swap
      (linearTensor linearVariable linearVariable))

linearTensorSwapMALLP :
  {A B : LinearSourceType} →
  MALLP
    (linearSourceContext (linearTensorType A B ∷ []))
    (just (linearSourceFormula (linearTensorType B A)))
linearTensorSwapMALLP = deriveMALLP linearTensorSwap

-- Word64 is one source-level resource, even though its current target
-- representation is two 32-bit limbs.
linearWord64Identity :
  LinearTerm (linearWord64Type ∷ []) linearWord64Type
linearWord64Identity = linearVariable

linearWord64IdentityMALLP :
  MALLP
    (linearSourceContext (linearWord64Type ∷ []))
    (just (linearSourceFormula linearWord64Type))
linearWord64IdentityMALLP = deriveMALLP linearWord64Identity


-- A finite Maybe-like ADT is the additive sum 1 ⊕ A. Both branches
-- consume the same residual context; the absent branch consumes its Unit
-- payload and the present branch consumes its A payload.
linearMaybeType : LinearSourceType → LinearSourceType
linearMaybeType A = linearSumType linearUnitType A

linearMaybeIdentity :
  {A : LinearSourceType} →
  LinearTerm (linearMaybeType A ∷ []) (linearMaybeType A)
linearMaybeIdentity =
  linearSumCaseTerm
    (linearUnitCaseTerm (linearInl linearUnit))
    (linearInr linearVariable)

linearMaybeIdentityMALLP :
  {A : LinearSourceType} →
  MALLP
    (linearSourceContext (linearMaybeType A ∷ []))
    (just (linearSourceFormula (linearMaybeType A)))
linearMaybeIdentityMALLP = deriveMALLP linearMaybeIdentity

------------------------------------------------------------------------
-- REFLECTION-GENERATED ADT SHAPES
--
-- Reflection inspects the kernel-resolved datatype declaration and its
-- constructor Pi telescopes, then emits a quoted description. This is
-- compile-time metadata only: it does not decide linearity, runtime layout,
-- or a MALLP derivation. Those are checked by the typed source core above.
------------------------------------------------------------------------

record ReflectedConstructorShape : Set where
  constructor reflectedConstructorShape
  field
    reflectedConstructorName : Reflection.Name
    reflectedConstructorArity : Nat
open ReflectedConstructorShape public

record ReflectedDataShape : Set where
  constructor reflectedDataShape
  field
    reflectedParameterCount : Nat
    reflectedIndexCount : Nat
    reflectedConstructors : List ReflectedConstructorShape
open ReflectedDataShape public

reflectedConstructorArities :
  List ReflectedConstructorShape → List Nat
reflectedConstructorArities [] = []
reflectedConstructorArities (entry ∷ entries) =
  reflectedConstructorArity entry ∷
    reflectedConstructorArities entries

reflectionPiArity : Reflection.Term → Nat
reflectionPiArity (Reflection.pi _ (Reflection.abs _ body)) =
  suc (reflectionPiArity body)
reflectionPiArity _ = zero

reflectionNatDifference : Nat → Nat → Nat
reflectionNatDifference n zero = n
reflectionNatDifference zero (suc m) = zero
reflectionNatDifference (suc n) (suc m) =
  reflectionNatDifference n m

reflectConstructorShapes :
  Nat →
  List Reflection.Name →
  Reflection.TC (List ReflectedConstructorShape)
reflectConstructorShapes parameters [] =
  Reflection.returnTC []
reflectConstructorShapes parameters (entry ∷ entries) =
  Reflection.bindTC (Reflection.getType entry)
    (λ entryType →
      Reflection.bindTC
        (reflectConstructorShapes parameters entries)
        (λ rest →
          Reflection.returnTC
            (reflectedConstructorShape entry
              (reflectionNatDifference
                (reflectionPiArity entryType) parameters)
              ∷ rest)))

reflectDataShapeImpl :
  Reflection.Name →
  Reflection.Term →
  Reflection.Definition →
  Reflection.TC ⊤
reflectDataShapeImpl name hole (Reflection.data-type parameters constructors) =
  Reflection.bindTC (Reflection.getType name)
    (λ datatypeType →
      Reflection.bindTC
        (reflectConstructorShapes parameters constructors)
        (λ constructorShapes →
          Reflection.bindTC
            (Reflection.quoteTC
              (reflectedDataShape
                parameters
                (reflectionNatDifference
                  (reflectionPiArity datatypeType) parameters)
                constructorShapes))
            (λ witness → Reflection.unify hole witness)))
reflectDataShapeImpl name hole _ =
  Reflection.typeError
    (Reflection.strErr
      "reflectDataShape: expected the name of an Agda data type" ∷ [])

macro
  reflectDataShape : Reflection.Name → Reflection.Term → Reflection.TC ⊤
  reflectDataShape name hole =
    Reflection.bindTC (Reflection.getDefinition name)
      (reflectDataShapeImpl name hole)

-- Kernel-checked examples: the pair has two post-parameter constructor
-- binders; the parameterized box has one parameter and one additional binder.
data ReflectionPair : Set where
  reflectionPair : Nat → Bool → ReflectionPair

reflectedPairShape : ReflectedDataShape
reflectedPairShape = reflectDataShape ReflectionPair

reflectedPairArityWitness :
  reflectedParameterCount reflectedPairShape ≡ zero ×
  reflectedIndexCount reflectedPairShape ≡ zero ×
  reflectedConstructorArities
    (reflectedConstructors reflectedPairShape) ≡ (suc (suc zero) ∷ [])
reflectedPairArityWitness = pair refl (pair refl refl)

data ReflectionBox (A : Set) : Set where
  reflectionBox : A → ReflectionBox A

reflectedBoxShape : ReflectedDataShape
reflectedBoxShape = reflectDataShape ReflectionBox

reflectedBoxArityWitness :
  reflectedParameterCount reflectedBoxShape ≡ suc zero ×
  reflectedIndexCount reflectedBoxShape ≡ zero ×
  reflectedConstructorArities
    (reflectedConstructors reflectedBoxShape) ≡ (suc zero ∷ [])
reflectedBoxArityWitness = pair refl (pair refl refl)

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

  -- Word64 is represented at the current Gforth boundary by two unsigned
  -- 32-bit cells (high, low). The source resource remains indivisible.
  word64StackShape : List StackType
  word64StackShape = natCell ∷ natCell ∷ []

  word64IdentityCode :
    ForthCode word64StackShape word64StackShape
  word64IdentityCode = identityNat

  word64IdentityCode-correct :
    (stack : Stack word64StackShape) →
    execForthCode word64IdentityCode stack ≡ stack
  word64IdentityCode-correct stack = refl

  -- Text tokens are deliberately separate from the Nat execution machine:
  -- TRUE/FALSE have Gforth's Bool representation, not a Nat stack meaning.
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
  ... | just [] | pushCell selected′ remaining | ()
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
      MALLPNatProof (n + suc zero) →
      MALLPNatProof (n + suc zero)

    natCutProof :
      {n m : Nat} →
      MALLPNatProof n →
      MALLPNatProof (suc m) →
      MALLPNatProof (n + m)

    -- Derived primitive composition: consume a closed/live result once,
    -- then the remaining linear argument once, with the result at stack top.
    natPrimitiveComposeProof :
      {n : Nat} →
      MALLPNatProof n →
      NatOp →
      MALLPNatProof (suc n)

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

  natPlusOne : (n : Nat) → n + suc zero ≡ suc n
  natPlusOne zero = refl
  natPlusOne (suc n) = cong suc (natPlusOne n)

  natContextPlusOne :
    (n : Nat) →
    natContext (n + suc zero) ≡ natAssumption ∷ natContext n
  natContextPlusOne n rewrite natPlusOne n = refl

  natContextAppendLast :
    (n : Nat) →
    natContext n ++ᴸ (natAssumption ∷ []) ≡
    natAssumption ∷ natContext n
  natContextAppendLast zero = refl
  natContextAppendLast (suc n) =
    cong (natAssumption ∷_) (natContextAppendLast n)

  natLastToHeadPermutation :
    (n : Nat) →
    ContextPermutation
      (natContext n ++ᴸ (natAssumption ∷ []))
      (natAssumption ∷ natContext n)
  natLastToHeadPermutation n =
    subst
      (λ context → ContextPermutation context (natAssumption ∷ natContext n))
      (sym (natContextAppendLast n))
      (contextPermutation-refl (natAssumption ∷ natContext n))

  natRotateHeadToLastPermutationPlus :
    (n : Nat) →
    ContextPermutation
      (natContext (n + suc zero))
      (natContext (n + suc zero))
  natRotateHeadToLastPermutationPlus n =
    subst
      (λ context → ContextPermutation context context)
      (sym (natContextPlusOne n))
      (natRotateHeadToLastPermutation n)

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
      (natRotateHeadToLastPermutationPlus n)
      (embedNatProof proof)
  embedNatProof (natPrimitiveComposeProof {n = n} proof operation) =
    mallp-nat-exchange
      (natLastToHeadPermutation n)
      (mallp-nat-cut (embedNatProof proof) (mallp-nat-primitive operation))
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

  rotateHeadToLastEnvironmentPlus :
    {n : Nat} →
    NatEnvironment (n + suc zero) →
    NatEnvironment (n + suc zero)
  rotateHeadToLastEnvironmentPlus {n = n} environment =
    subst NatEnvironment (sym (natPlusOne n))
      (rotateHeadToLastEnvironment
        (subst NatEnvironment (natPlusOne n) environment))

  appendNatEnvironmentPlus :
    {n : Nat} →
    NatEnvironment n →
    Nat →
    NatEnvironment (n + suc zero)
  appendNatEnvironmentPlus {n = zero} natEnvironmentNil value =
    natEnvironmentCons value natEnvironmentNil
  appendNatEnvironmentPlus
    {n = suc n} (natEnvironmentCons head rest) value =
      natEnvironmentCons head (appendNatEnvironmentPlus rest value)

  splitNatEnvironment-append :
    (n : Nat) →
    (environment : NatEnvironment n) →
    (value : Nat) →
    splitNatEnvironment n (suc zero)
      (appendNatEnvironmentPlus environment value) ≡
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
    (natRotateHeadToLastProof {n = n} proof) environment =
      interpretMALLPNatProof proof
        (rotateHeadToLastEnvironmentPlus {n = n} environment)
  interpretMALLPNatProof (natPrimitiveComposeProof proof operation)
    (natEnvironmentCons leftValue rightEnvironment) =
      applyNatOp operation leftValue
        (interpretMALLPNatProof proof rightEnvironment)
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
    (resourceBinary operation left right) =
      natCutProof
        (natResourceProof left)
        (natPrimitiveComposeProof (natResourceProof right) operation)

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
          | natResourceProof-adequate right rightEnvironment = refl

  ----------------------------------------------------------------------
  -- General count-indexed resource-tree target compiler.
  --
  -- This closes the formal gap between arbitrary finite NatResourceExpr
  -- trees and the indexed postfix-token machine. The index n records the
  -- exact number of live assumptions. The active environment records
  -- already-computed sibling results; each resource leaf selects the next
  -- owned input using SWAP/ROLL, and each binary node consumes two results.
  ----------------------------------------------------------------------

  natEnvironmentValues : {n : Nat} → NatEnvironment n → List Nat
  natEnvironmentValues natEnvironmentNil = []
  natEnvironmentValues (natEnvironmentCons value rest) =
    value ∷ natEnvironmentValues rest

  natEnvironmentValues-split :
    (n m : Nat) →
    (environment : NatEnvironment (n + m)) →
    (residual : List Nat) →
    natEnvironmentValues environment ++ᴳ residual ≡
    natEnvironmentValues
      (fst (splitNatEnvironment n m environment)) ++ᴳ
    (natEnvironmentValues
      (snd (splitNatEnvironment n m environment)) ++ᴳ residual)
  natEnvironmentValues-split zero m environment residual = refl
  natEnvironmentValues-split (suc n) m
    (natEnvironmentCons value rest) residual
    with splitNatEnvironment n m rest in splitResult
  ... | pair prefix suffix
    rewrite splitResult
          | natEnvironmentValues-split n m rest residual = refl

  resourceSelectTokens : Nat → List ForthToken
  resourceSelectTokens zero = []
  resourceSelectTokens (suc zero) = swapWord ∷ []
  resourceSelectTokens (suc (suc depth)) =
    rollWord (suc (suc depth)) ∷ []

  rollList-activePrefix :
    (n : Nat) →
    (active : NatEnvironment n) →
    (value : Nat) →
    (residual : List Nat) →
    rollList n
      (natEnvironmentValues active ++ᴳ (value ∷ residual)) ≡
    just (value ∷ (natEnvironmentValues active ++ᴳ residual))
  rollList-activePrefix zero natEnvironmentNil value residual = refl
  rollList-activePrefix (suc n)
    (natEnvironmentCons head rest) value residual
    rewrite rollList-activePrefix n rest value residual = refl

  resourceSelectTokens-correct :
    (n : Nat) →
    (active : NatEnvironment n) →
    (value : Nat) →
    (residual : List Nat) →
    execTokens (resourceSelectTokens n)
      (natEnvironmentValues active ++ᴳ (value ∷ residual)) ≡
    just (value ∷ (natEnvironmentValues active ++ᴳ residual))
  resourceSelectTokens-correct zero
    natEnvironmentNil value residual = refl
  resourceSelectTokens-correct (suc zero)
    (natEnvironmentCons head natEnvironmentNil) value residual = refl
  resourceSelectTokens-correct (suc (suc n))
    active value residual =
      rollList-activePrefix (suc (suc n)) active value residual

  natResourceForthTokens :
    {n : Nat} →
    NatResourceExpr n →
    (active : Nat) →
    List ForthToken
  natResourceForthTokens (resourceLiteral value) active =
    pushLiteral value ∷ []
  natResourceForthTokens resourceArgument active =
    resourceSelectTokens active
  natResourceForthTokens
    (resourceBinary operation left right) active =
      natResourceForthTokens left active ++ᴳ
        (natResourceForthTokens right (suc active) ++ᴳ
          (renderNatOp operation ∷ []))

  natResourceForthTokens-correct :
    {n : Nat} →
    (expression : NatResourceExpr n) →
    (active : Nat) →
    (activeValues : NatEnvironment active) →
    (environment : NatEnvironment n) →
    (residual : List Nat) →
    execTokens (natResourceForthTokens expression active)
      (natEnvironmentValues activeValues ++ᴳ
        (natEnvironmentValues environment ++ᴳ residual)) ≡
    just
      (evalNatResourceExpr expression environment ∷
        (natEnvironmentValues activeValues ++ᴳ residual))
  natResourceForthTokens-correct
    (resourceLiteral value) active activeValues environment residual = refl
  natResourceForthTokens-correct
    resourceArgument active activeValues
    (natEnvironmentCons value natEnvironmentNil) residual =
      resourceSelectTokens-correct active activeValues value residual
  natResourceForthTokens-correct
    (resourceBinary {n = n} {m = m} operation left right)
    active activeValues environment residual
    with splitNatEnvironment n m environment
  ... | pair leftEnvironment rightEnvironment
    rewrite natEnvironmentValues-split n m environment residual
      | execTokens-append
          (natResourceForthTokens left active)
          (natResourceForthTokens right (suc active) ++ᴳ
            (renderNatOp operation ∷ []))
          (natEnvironmentValues activeValues ++ᴳ
            (natEnvironmentValues leftEnvironment ++ᴳ
              (natEnvironmentValues rightEnvironment ++ᴳ residual)))
      | natResourceForthTokens-correct
          left active activeValues leftEnvironment
          (natEnvironmentValues rightEnvironment ++ᴳ residual)
      | execTokens-append
          (natResourceForthTokens right (suc active))
          (renderNatOp operation ∷ [])
          (evalNatResourceExpr left leftEnvironment ∷
            (natEnvironmentValues activeValues ++ᴳ
              (natEnvironmentValues rightEnvironment ++ᴳ residual)))
      | natResourceForthTokens-correct
          right (suc active)
          (natEnvironmentCons
            (evalNatResourceExpr left leftEnvironment) activeValues)
          rightEnvironment residual = refl

  -- End-to-end theorem for every count-indexed Nat resource tree:
  -- MALLP proof interpretation = formal target execution, with arbitrary
  -- active sibling results and residual stack preserved.
  natResourceMALLP-forth-sound :
    {n : Nat} →
    (expression : NatResourceExpr n) →
    (environment : NatEnvironment n) →
    (residual : List Nat) →
    execTokens (natResourceForthTokens expression zero)
      (natEnvironmentValues environment ++ᴳ residual) ≡
    just
      (interpretMALLPNatProof (natResourceProof expression) environment
        ∷ residual)
  natResourceMALLP-forth-sound expression environment residual =
    trans
      (natResourceForthTokens-correct
        expression zero natEnvironmentNil environment residual)
      (cong
        (λ value → just (value ∷ residual))
        (sym (natResourceProof-adequate expression environment)))

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

  -- Pair is a multiplicative tensor of two Bool values. Its negative
  -- occurrence in the input context is the dual par; tensor introduction,
  -- exchange, and par introduction give the field-swapping linear map.
  boolPairFormula : PolType posPolarity
  boolPairFormula = boolFormula ⊗⁺ boolFormula

  boolPairAssumption : PolType negPolarity
  boolPairAssumption = dualPos boolPairFormula

  boolPairSwapMALLP :
    MALLP (boolPairAssumption ∷ []) (just boolPairFormula)
  boolPairSwapMALLP =
    linearTensorSwapMALLP
      {A = linearBoolType}
      {B = linearBoolType}

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
    boolIdentity :
      {Γ : List BoolStackType} →
      BoolForthCode Γ Γ

    -- Tensor-field permutation: both Boolean cells remain live.
    boolSwapCode :
      {Γ : List BoolStackType} →
      BoolForthCode (boolCell ∷ boolCell ∷ Γ)
        (boolCell ∷ boolCell ∷ Γ)

    pushBoolean :
      {Γ : List BoolStackType} →
      Bool →
      BoolForthCode Γ (boolCell ∷ Γ)

    -- A conditional consumes its condition. Both branches begin with the
    -- same residual stack and may return an arbitrary stack of the same type.
    boolIfCode :
      {Γ Δ : List BoolStackType} →
      BoolForthCode Γ Δ →
      BoolForthCode Γ Δ →
      BoolForthCode (boolCell ∷ Γ) Δ

    -- A source function may case-analyse the lower of two live Boolean
    -- arguments, then return the remaining argument in either branch.
    -- The concrete lowering is SWAP IF ... ELSE ... THEN.
    boolIfPreserving :
      {Γ : List BoolStackType} →
      BoolForthCode (boolCell ∷ Γ) (boolCell ∷ Γ) →
      BoolForthCode (boolCell ∷ Γ) (boolCell ∷ Γ) →
      BoolForthCode (boolCell ∷ boolCell ∷ Γ) (boolCell ∷ Γ)

  execBoolCode :
    {Γ Δ : List BoolStackType} →
    BoolForthCode Γ Δ →
    BoolStack Γ →
    BoolStack Δ
  execBoolCode boolIdentity stack = stack
  execBoolCode boolSwapCode
    (pushBooleanValue top (pushBooleanValue next stack)) =
      pushBooleanValue next (pushBooleanValue top stack)
  execBoolCode (pushBoolean value) stack =
    pushBooleanValue value stack
  execBoolCode (boolIfCode whenTrue whenFalse)
    (pushBooleanValue true stack) =
      execBoolCode whenTrue stack
  execBoolCode (boolIfCode whenTrue whenFalse)
    (pushBooleanValue false stack) =
      execBoolCode whenFalse stack
  execBoolCode (boolIfPreserving whenTrue whenFalse)
    (pushBooleanValue value (pushBooleanValue true stack)) =
      execBoolCode whenTrue (pushBooleanValue value stack)
  execBoolCode (boolIfPreserving whenTrue whenFalse)
    (pushBooleanValue value (pushBooleanValue false stack)) =
      execBoolCode whenFalse (pushBooleanValue value stack)

  data BoolForthToken : Set where
    pushTrueToken pushFalseToken boolSwapToken : BoolForthToken
    boolIfToken : List BoolForthToken → List BoolForthToken → BoolForthToken

  renderBoolCode :
    {Γ Δ : List BoolStackType} →
    BoolForthCode Γ Δ →
    List BoolForthToken
  renderBoolCode boolIdentity = []
  renderBoolCode boolSwapCode = boolSwapToken ∷ []
  renderBoolCode (pushBoolean true) = pushTrueToken ∷ []
  renderBoolCode (pushBoolean false) = pushFalseToken ∷ []
  renderBoolCode (boolIfCode whenTrue whenFalse) =
    boolIfToken (renderBoolCode whenTrue) (renderBoolCode whenFalse) ∷ []
  renderBoolCode (boolIfPreserving whenTrue whenFalse) =
    boolSwapToken ∷
      boolIfToken (renderBoolCode whenTrue) (renderBoolCode whenFalse) ∷ []

  bindBoolTokens :
    Maybe (List Bool) →
    (List Bool → Maybe (List Bool)) →
    Maybe (List Bool)
  bindBoolTokens nothing continuation = nothing
  bindBoolTokens (just stack) continuation = continuation stack

  bindBoolTokens-identity :
    (result : Maybe (List Bool)) →
    bindBoolTokens result (λ stack → just stack) ≡ result
  bindBoolTokens-identity nothing = refl
  bindBoolTokens-identity (just stack) = refl

  execBoolTokens :
    List BoolForthToken →
    List Bool →
    Maybe (List Bool)
  execBoolTokens [] stack = just stack
  execBoolTokens (pushTrueToken ∷ tokens) stack =
    execBoolTokens tokens (true ∷ stack)
  execBoolTokens (pushFalseToken ∷ tokens) stack =
    execBoolTokens tokens (false ∷ stack)
  execBoolTokens (boolSwapToken ∷ tokens) (top ∷ next ∷ stack) =
    execBoolTokens tokens (next ∷ top ∷ stack)
  execBoolTokens (boolSwapToken ∷ tokens) _ = nothing
  execBoolTokens (boolIfToken whenTrue whenFalse ∷ tokens)
    (true ∷ stack) =
      bindBoolTokens (execBoolTokens whenTrue stack)
        (λ branchStack → execBoolTokens tokens branchStack)
  execBoolTokens (boolIfToken whenTrue whenFalse ∷ tokens)
    (false ∷ stack) =
      bindBoolTokens (execBoolTokens whenFalse stack)
        (λ branchStack → execBoolTokens tokens branchStack)
  execBoolTokens (boolIfToken whenTrue whenFalse ∷ tokens) [] = nothing

  compileBoolPairSwap :
    BoolForthCode (boolCell ∷ boolCell ∷ [])
      (boolCell ∷ boolCell ∷ [])
  compileBoolPairSwap = boolSwapCode

  boolPairSwapMALLP-forth-sound :
    (first second : Bool) →
    execBoolTokens (renderBoolCode compileBoolPairSwap)
      (second ∷ first ∷ []) ≡ just (first ∷ second ∷ [])
  boolPairSwapMALLP-forth-sound first second = refl

  renderBoolCode-sound :
    {Γ Δ : List BoolStackType} →
    (code : BoolForthCode Γ Δ) →
    (stack : BoolStack Γ) →
    execBoolTokens (renderBoolCode code) (forgetBoolStack stack) ≡
    just (forgetBoolStack (execBoolCode code stack))
  renderBoolCode-sound boolIdentity stack = refl
  renderBoolCode-sound boolSwapCode
    (pushBooleanValue top (pushBooleanValue next stack)) = refl
  renderBoolCode-sound (pushBoolean true) stack = refl
  renderBoolCode-sound (pushBoolean false) stack = refl
  renderBoolCode-sound (boolIfCode whenTrue whenFalse)
    (pushBooleanValue true stack)
    rewrite bindBoolTokens-identity
      (execBoolTokens (renderBoolCode whenTrue) (forgetBoolStack stack))
          | renderBoolCode-sound whenTrue stack = refl
  renderBoolCode-sound (boolIfCode whenTrue whenFalse)
    (pushBooleanValue false stack)
    rewrite bindBoolTokens-identity
      (execBoolTokens (renderBoolCode whenFalse) (forgetBoolStack stack))
          | renderBoolCode-sound whenFalse stack = refl
  renderBoolCode-sound (boolIfPreserving whenTrue whenFalse)
    (pushBooleanValue value (pushBooleanValue true stack))
    rewrite bindBoolTokens-identity
      (execBoolTokens (renderBoolCode whenTrue)
        (forgetBoolStack (pushBooleanValue value stack)))
          | renderBoolCode-sound whenTrue (pushBooleanValue value stack) = refl
  renderBoolCode-sound (boolIfPreserving whenTrue whenFalse)
    (pushBooleanValue value (pushBooleanValue false stack))
    rewrite bindBoolTokens-identity
      (execBoolTokens (renderBoolCode whenFalse)
        (forgetBoolStack (pushBooleanValue value stack)))
          | renderBoolCode-sound whenFalse (pushBooleanValue value stack) = refl

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

  -- Convert the proof-level Boolean program into the independent text-token
  -- renderer's nested IF representation. The renderer's Agda certificate
  -- checks the actual text emitted by Haskell against this token algebra.
  mutual
    boolForthTokenAsText : BoolForthToken → ForthTextToken
    boolForthTokenAsText pushTrueToken = textTrueWord
    boolForthTokenAsText pushFalseToken = textFalseWord
    boolForthTokenAsText boolSwapToken = textSwapWord
    boolForthTokenAsText (boolIfToken whenTrue whenFalse) =
      textIf (mapBoolForthTokensAsText whenTrue)
        (mapBoolForthTokensAsText whenFalse)

    mapBoolForthTokensAsText :
      List BoolForthToken → List ForthTextToken
    mapBoolForthTokensAsText [] = []
    mapBoolForthTokensAsText (token ∷ tokens) =
      boolForthTokenAsText token ∷ mapBoolForthTokensAsText tokens

  boolPairSwap-token-correspondence :
    mapBoolForthTokensAsText (renderBoolCode compileBoolPairSwap) ≡
    (textSwapWord ∷ [])
  boolPairSwap-token-correspondence = refl

  -- A Boolean case split is the additive MALLP elimination rule:
  -- the same residual context is available in each mutually exclusive branch.
  data BoolCaseProof : Set where
    boolCaseProof : BoolProof → BoolProof → BoolCaseProof

  selectBoolCaseProof : BoolCaseProof → Bool → BoolProof
  selectBoolCaseProof (boolCaseProof whenTrue whenFalse) true = whenTrue
  selectBoolCaseProof (boolCaseProof whenTrue whenFalse) false = whenFalse

  interpretBoolCaseProof : BoolCaseProof → Bool → Bool
  interpretBoolCaseProof proof scrutinee =
    interpretBoolProof (selectBoolCaseProof proof scrutinee)

  boolCaseMALLP-derivation :
    (proof : BoolCaseProof) →
    MALLP (dualPos boolFormula ∷ []) (just boolFormula)
  boolCaseMALLP-derivation (boolCaseProof whenTrue whenFalse) =
    mallp-with
      (mallp-bottom (boolProofDerivation whenTrue))
      (mallp-bottom (boolProofDerivation whenFalse))

  -- Closed branch selection is compiled to the corresponding Boolean literal.
  -- The MALLP derivation above proves the eliminator consumes one Bool resource;
  -- this theorem connects compile-time branch selection to target execution.
  compileBoolCaseProof :
    (scrutinee : Bool) →
    BoolCaseProof →
    BoolForthCode [] (boolCell ∷ [])
  compileBoolCaseProof scrutinee proof =
    compileBoolProof (selectBoolCaseProof proof scrutinee)

  boolCaseMALLP-forth-sound :
    (scrutinee : Bool) →
    (proof : BoolCaseProof) →
    execBoolTokens
      (renderBoolCode (compileBoolCaseProof scrutinee proof))
      [] ≡ just (interpretBoolCaseProof proof scrutinee ∷ [])
  boolCaseMALLP-forth-sound true (boolCaseProof whenTrue whenFalse) =
    boolMALLP-forth-sound whenTrue
  boolCaseMALLP-forth-sound false (boolCaseProof whenTrue whenFalse) =
    boolMALLP-forth-sound whenFalse

  compileBoolRuntimeCase :
    BoolCaseProof →
    BoolForthCode (boolCell ∷ []) (boolCell ∷ [])
  compileBoolRuntimeCase (boolCaseProof whenTrue whenFalse) =
    boolIfCode (compileBoolProof whenTrue) (compileBoolProof whenFalse)

  -- The runtime case instruction consumes one condition and selects exactly
  -- one additive branch. Both branches own the same empty residual context.
  boolCaseRuntimeMALLP-forth-sound :
    (scrutinee : Bool) →
    (proof : BoolCaseProof) →
    execBoolTokens
      (renderBoolCode (compileBoolRuntimeCase proof))
      (scrutinee ∷ []) ≡
    just (interpretBoolCaseProof proof scrutinee ∷ [])
  boolCaseRuntimeMALLP-forth-sound true (boolCaseProof whenTrue whenFalse)
    rewrite bindBoolTokens-identity
      (execBoolTokens (renderBoolCode (compileBoolProof whenTrue)) []) =
        boolMALLP-forth-sound whenTrue
  boolCaseRuntimeMALLP-forth-sound false (boolCaseProof whenTrue whenFalse)
    rewrite bindBoolTokens-identity
      (execBoolTokens (renderBoolCode (compileBoolProof whenFalse)) []) =
        boolMALLP-forth-sound whenFalse

  -- The additive left rule consumes the condition while both branches
  -- consume the same residual Bool assumption. This is the MALLP judgment
  -- for chooseBool : Bool ⊗ Bool ⊸ Bool, with no weakening or contraction.
  boolCaseWithResidualMALLP :
    MALLP
      (dualPos boolFormula ∷ dualPos boolFormula ∷ [])
      (just boolFormula)
  boolCaseWithResidualMALLP =
    mallp-with (mallp-bottom mallp-ax) (mallp-bottom mallp-ax)

  compileBoolCaseWithResidual :
    BoolForthCode (boolCell ∷ boolCell ∷ []) (boolCell ∷ [])
  compileBoolCaseWithResidual =
    boolIfPreserving boolIdentity boolIdentity

  -- The compiler's concrete instruction stream for chooseBool is SWAP
  -- followed by an additive IF whose branches each preserve the same
  -- remaining Bool. This equality links the proof-level control-flow code
  -- with the ForthTextToken algebra used by the emitted-source certificate.
  boolCaseWithResidual-token-correspondence :
    mapBoolForthTokensAsText (renderBoolCode compileBoolCaseWithResidual) ≡
    (textSwapWord ∷ textIf [] [] ∷ [])
  boolCaseWithResidual-token-correspondence = refl

  boolCaseWithResidualMALLP-forth-sound :
    (condition value : Bool) →
    execBoolTokens
      (renderBoolCode compileBoolCaseWithResidual)
      (value ∷ condition ∷ []) ≡
    just (value ∷ [])
  boolCaseWithResidualMALLP-forth-sound true value
    rewrite bindBoolTokens-identity
      (execBoolTokens [] (value ∷ [])) = refl
  boolCaseWithResidualMALLP-forth-sound false value
    rewrite bindBoolTokens-identity
      (execBoolTokens [] (value ∷ [])) = refl

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



------------------------------------------------------------------------
-- Linear call-by-need state and explicit effect protocols
--
-- These are primitive *signatures over unchanged MALLP*, not additions to
-- Laurent's logical rules.  A store/effect token is an ordinary linear
-- resource: every operation consumes one token and returns exactly one.
------------------------------------------------------------------------

module StrictStatefulProtocol where

  strictForceObservation :
    {value : Nat} →
    (continuation : Nat → Nat) →
    primForce value continuation ≡ continuation value
  strictForceObservation continuation =
    primForceLemma _ continuation


  thunkStoreFormula : PolType posPolarity
  thunkStoreFormula = atom⁺ 18

  effectTokenFormula : PolType posPolarity
  effectTokenFormula = atom⁺ 19

  listNatFormula : PolType posPolarity
  listNatFormula = atom⁺ 20

  -- A linear function owns each captured resource in its surrounding
  -- context. Domain and codomain are represented with MALLP polarity shifts.
  linearClosureFormula :
    PolType posPolarity →
    PolType posPolarity →
    PolType posPolarity
  linearClosureFormula domain codomain =
    down⁺ (dualPos domain ⅋⁻ up⁻ codomain)

  -- Computation signatures are layered over MALLP.  The only extra axioms
  -- below are declared operations with explicit resource/stack contracts.
  data MALLPProtocolTheory : Context → Stoup → Set where
    protocol-logical :
      {Γ : Context} {S : Stoup} →
      MALLP Γ S →
      MALLPProtocolTheory Γ S

    protocol-cut :
      {Γ Δ : Context} {P : PolType posPolarity} {S : Stoup} →
      MALLPProtocolTheory Γ (just P) →
      MALLPProtocolTheory (dualPos P ∷ Δ) S →
      MALLPProtocolTheory (Γ ++ᴸ Δ) S

    protocol-exchange :
      {Γ Δ : Context} {S : Stoup} →
      ContextPermutation Γ Δ →
      MALLPProtocolTheory Γ S →
      MALLPProtocolTheory Δ S

    -- Structural rules below are the corresponding existing Laurent MALLP
    -- inferences lifted over the declared primitive protocol signatures.
    protocol-par :
      {Γ : Context} {M N : PolType negPolarity} {S : Stoup} →
      MALLPProtocolTheory (M ∷ N ∷ Γ) S →
      MALLPProtocolTheory ((M ⅋⁻ N) ∷ Γ) S

    protocol-up :
      {Γ : Context} {P : PolType posPolarity} →
      MALLPProtocolTheory Γ (just P) →
      MALLPProtocolTheory (up⁻ P ∷ Γ) nothing

    protocol-down :
      {Γ : Context} {N : PolType negPolarity} →
      MALLPProtocolTheory (N ∷ Γ) nothing →
      MALLPProtocolTheory Γ (just (down⁺ N))

    -- Forcing consumes the unique store capability and returns the demanded
    -- Nat together with the updated capability.
    primitive-thunk-force :
      MALLPProtocolTheory
        (dualPos thunkStoreFormula ∷ [])
        (just (natFormula ⊗⁺ thunkStoreFormula))

    -- Emission consumes exactly one event payload and one effect capability,
    -- returning the updated capability.  No ambient unrestricted effect is
    -- available in this signature.
    primitive-effect-emit :
      MALLPProtocolTheory
        (dualPos effectTokenFormula ∷ dualPos natFormula ∷ [])
        (just effectTokenFormula)

    -- Linear closure application consumes the closure and its argument once.
    primitive-linear-apply :
      {domain codomain : PolType posPolarity} →
      MALLPProtocolTheory
        (dualPos (linearClosureFormula domain codomain) ∷
         dualPos domain ∷ [])
        (just codomain)

    primitive-list-nil :
      MALLPProtocolTheory [] (just listNatFormula)

    primitive-list-cons :
      MALLPProtocolTheory
        (dualPos natFormula ∷ dualPos listNatFormula ∷ [])
        (just listNatFormula)

    -- The fold operation is static code. The list and accumulator are the
    -- dynamic linear inputs; recursion is structurally justified by the
    -- finite Agda list semantics below.
    primitive-list-fold :
      NatOp →
      MALLPProtocolTheory
        (dualPos listNatFormula ∷ dualPos natFormula ∷ [])
        (just natFormula)

  ----------------------------------------------------------------------
  -- A total PureLang thunk fragment with explicit call-by-need update.
  ----------------------------------------------------------------------

  data ThunkExpr : Set where
    thunkLiteral : Nat → ThunkExpr
    thunkAdd : ThunkExpr → ThunkExpr → ThunkExpr
    thunkMonus : ThunkExpr → ThunkExpr → ThunkExpr
    thunkMultiply : ThunkExpr → ThunkExpr → ThunkExpr

  evalThunkExpr : ThunkExpr → Nat
  evalThunkExpr (thunkLiteral value) = value
  evalThunkExpr (thunkAdd left right) =
    evalThunkExpr left + evalThunkExpr right
  evalThunkExpr (thunkMonus left right) =
    applyNatOp monusOp (evalThunkExpr left) (evalThunkExpr right)
  evalThunkExpr (thunkMultiply left right) =
    evalThunkExpr left * evalThunkExpr right

  data ThunkState : Set where
    suspended : ThunkExpr → ThunkState
    memoized : Nat → ThunkState

  cacheThunkState : ThunkState → ThunkState
  cacheThunkState (suspended expression) =
    memoized (evalThunkExpr expression)
  cacheThunkState (memoized value) = memoized value

  data ThunkStoreToken : ThunkState → Set where
    ownThunkStore : {state : ThunkState} → ThunkStoreToken state

  -- The transition type consumes the old capability and returns one new
  -- capability indexed by the post-update heap state.
  forceThunk :
    {state : ThunkState} →
    ThunkStoreToken state →
    Nat × ThunkStoreToken (cacheThunkState state)
  forceThunk {suspended expression} ownThunkStore =
    pair (evalThunkExpr expression) ownThunkStore
  forceThunk {memoized value} ownThunkStore =
    pair value ownThunkStore

  forceThunkValue :
    {state : ThunkState} →
    ThunkStoreToken state →
    Nat
  forceThunkValue token = fst (forceThunk token)

  forceThunkNext :
    {state : ThunkState} →
    (token : ThunkStoreToken state) →
    ThunkStoreToken (cacheThunkState state)
  forceThunkNext token = snd (forceThunk token)

  cacheThunkState-idempotent :
    (state : ThunkState) →
    cacheThunkState (cacheThunkState state) ≡ cacheThunkState state
  cacheThunkState-idempotent (suspended expression) = refl
  cacheThunkState-idempotent (memoized value) = refl

  forceThunk-stable :
    {state : ThunkState} →
    (token : ThunkStoreToken state) →
    forceThunkValue (forceThunkNext token) ≡ forceThunkValue token
  forceThunk-stable {suspended expression} ownThunkStore = refl
  forceThunk-stable {memoized value} ownThunkStore = refl

  forceThunk-caches :
    {state : ThunkState} →
    (token : ThunkStoreToken state) →
    cacheThunkState state ≡
    cacheThunkState (cacheThunkState state)
  forceThunk-caches stateToken =
    sym (cacheThunkState-idempotent _)

  ----------------------------------------------------------------------
  -- An explicit linear event protocol.
  ----------------------------------------------------------------------

  appendEvent : List Nat → Nat → List Nat
  appendEvent [] event = event ∷ []
  appendEvent (head ∷ rest) event = head ∷ appendEvent rest event

  data EffectToken : List Nat → Set where
    ownEffectToken : {trace : List Nat} → EffectToken trace

  traceLength : List Nat → Nat
  traceLength [] = zero
  traceLength (_ ∷ events) = suc (traceLength events)

  appendEvent-length :
    (trace : List Nat) →
    (event : Nat) →
    traceLength (appendEvent trace event) ≡ suc (traceLength trace)
  appendEvent-length [] event = refl
  appendEvent-length (head ∷ rest) event =
    cong suc (appendEvent-length rest event)

  emitEffect :
    {trace : List Nat} →
    EffectToken trace →
    (event : Nat) →
    EffectToken (appendEvent trace event)
  emitEffect ownEffectToken event = ownEffectToken

  -- Public witnesses for the computation signatures.
  thunkForceSignature :
    MALLPProtocolTheory
      (dualPos thunkStoreFormula ∷ [])
      (just (natFormula ⊗⁺ thunkStoreFormula))
  thunkForceSignature = primitive-thunk-force

  effectEmitSignature :
    MALLPProtocolTheory
      (dualPos effectTokenFormula ∷ dualPos natFormula ∷ [])
      (just effectTokenFormula)
  effectEmitSignature = primitive-effect-emit

open StrictStatefulProtocol public


------------------------------------------------------------------------
-- Linear closures, tensor/sum data, and finite list recursors
--
-- The proof terms below use existing MALLP introduction/elimination rules.
-- Primitive application and list runtime operations are isolated in explicit
-- MALLPProtocolTheory signatures.  This does not add a recursive connective
-- to MALLP: list recursion is structural over finite Agda values.
------------------------------------------------------------------------

module StrictLinearDataCompiler where

  linearProductIntro :
    {Γ Δ : Context} {A B : PolType posPolarity} →
    MALLP Γ (just A) →
    MALLP Δ (just B) →
    MALLP (Γ ++ᴸ Δ) (just (A ⊗⁺ B))
  linearProductIntro = mallp-tensor

  linearProductElim :
    {Γ : Context} {A B : PolType posPolarity} {S : Stoup} →
    MALLP (dualPos A ∷ dualPos B ∷ Γ) S →
    MALLP (dualPos (A ⊗⁺ B) ∷ Γ) S
  linearProductElim = mallp-par

  linearSumIntroLeft :
    {Γ : Context} {A B : PolType posPolarity} →
    MALLP Γ (just A) →
    MALLP Γ (just (A ⊕⁺ B))
  linearSumIntroLeft = mallp-plus-left

  linearSumIntroRight :
    {Γ : Context} {A B : PolType posPolarity} →
    MALLP Γ (just B) →
    MALLP Γ (just (A ⊕⁺ B))
  linearSumIntroRight = mallp-plus-right

  linearSumElim :
    {Γ : Context} {A B : PolType posPolarity} {S : Stoup} →
    MALLP (dualPos A ∷ Γ) S →
    MALLP (dualPos B ∷ Γ) S →
    MALLP (dualPos (A ⊕⁺ B) ∷ Γ) S
  linearSumElim = mallp-with

  -- Γ remains present while the domain resource is abstracted.  The closure
  -- introduction consumes the argument resource once and preserves captures.
  linearClosureIntro :
    {Γ : Context} {A B : PolType posPolarity} →
    MALLP (dualPos A ∷ Γ) (just B) →
    MALLP Γ (just (linearClosureFormula A B))
  linearClosureIntro body =
    mallp-down
      (mallp-par
        (mallp-exchange permutation-swap
          (mallp-up body)))

  linearClosureApplicationSignature :
    {A B : PolType posPolarity} →
    MALLPProtocolTheory
      (dualPos (linearClosureFormula A B) ∷ dualPos A ∷ [])
      (just B)
  linearClosureApplicationSignature = primitive-linear-apply

  -- Application is a declared typed operation over unchanged MALLP.
  -- Source arguments are ordered before the function's captured context.
  data LinearApplicationTerm :
    List LinearSourceType → LinearSourceType → Set where

    application-source :
      {Γ : List LinearSourceType} {A : LinearSourceType} →
      LinearTerm Γ A →
      LinearApplicationTerm Γ A

    application-exchange :
      {Γ Δ : List LinearSourceType} {A : LinearSourceType} →
      ContextPermutation Γ Δ →
      LinearApplicationTerm Γ A →
      LinearApplicationTerm Δ A

    application-lambda :
      {Γ : List LinearSourceType} {A B : LinearSourceType} →
      LinearApplicationTerm (A ∷ Γ) B →
      LinearApplicationTerm Γ (linearArrowType A B)

    linearApplication :
      {Γ Δ : List LinearSourceType} {A B : LinearSourceType} →
      LinearApplicationTerm Δ A →
      LinearApplicationTerm Γ (linearArrowType A B) →
      LinearApplicationTerm (appendLinearContext Δ Γ) B

  rotateLastContext :
    (prefix : List (PolType negPolarity)) →
    (last : PolType negPolarity) →
    ContextPermutation
      (prefix ++ᴸ (last ∷ []))
      (last ∷ prefix)
  rotateLastContext [] last =
    permutation-cons {A = PolType negPolarity} permutation-nil
  rotateLastContext (head ∷ prefix) last =
    permutation-trans
      (permutation-cons
        {A = PolType negPolarity}
        (rotateLastContext prefix last))
      (permutation-swap {A = PolType negPolarity})

  deriveLinearApplication :
    {Γ : List LinearSourceType} {A : LinearSourceType} →
    LinearApplicationTerm Γ A →
    MALLPProtocolTheory
      (linearSourceContext Γ)
      (just (linearSourceFormula A))
  deriveLinearApplication (application-source term) =
    protocol-logical (deriveMALLP term)
  deriveLinearApplication (application-exchange permutation term) =
    protocol-exchange
      (linearContextPermutation permutation)
      (deriveLinearApplication term)
  deriveLinearApplication (application-lambda body) =
    protocol-down
      (protocol-par
        (protocol-exchange permutation-swap
          (protocol-up (deriveLinearApplication body))))
  deriveLinearApplication
    (linearApplication {Γ = Γ} {Δ = Δ} {A = A} {B = B} argument function) =
    subst
      (λ context → MALLPProtocolTheory context
        (just (linearSourceFormula B)))
      (sym (linearSourceContext-append Δ Γ))
      (protocol-cut
        (deriveLinearApplication argument)
        (protocol-exchange
          (rotateLastContext
            (linearSourceContext Γ)
            (dualPos (linearSourceFormula A)))
          (protocol-cut
            (deriveLinearApplication function)
            primitive-linear-apply)))

  -- BCI: I is identity, B is composition, and C exchanges the first
  -- two arguments. Every input variable occurs exactly once.
  bciIdentity :
    {A : LinearSourceType} →
    LinearApplicationTerm [] (linearArrowType A A)
  bciIdentity =
    application-lambda (application-source linearVariable)

  bciComposition :
    {A B C : LinearSourceType} →
    LinearApplicationTerm []
      (linearArrowType
        (linearArrowType B C)
        (linearArrowType
          (linearArrowType A B)
          (linearArrowType A C)))
  bciComposition {A} {B} {C} =
    application-lambda
      (application-lambda
        (application-lambda
          (linearApplication
            {A = B} {B = C}
            (linearApplication
              {A = A} {B = B}
              (application-source {Γ = A ∷ []} {A = A} linearVariable)
              (application-source
                {Γ = linearArrowType A B ∷ []}
                {A = linearArrowType A B}
                linearVariable))
            (application-source
              {Γ = linearArrowType B C ∷ []}
              {A = linearArrowType B C}
              linearVariable))))

  bciExchange :
    {A B C : LinearSourceType} →
    LinearApplicationTerm []
      (linearArrowType
        (linearArrowType A (linearArrowType B C))
        (linearArrowType B (linearArrowType A C)))
  bciExchange {A} {B} {C} =
    application-lambda
      (application-lambda
        (application-lambda
          (application-exchange
            permutation-swap
            (linearApplication
              {A = B} {B = C}
              (application-source {Γ = B ∷ []} {A = B} linearVariable)
              (linearApplication
                {A = A} {B = linearArrowType B C}
                (application-source {Γ = A ∷ []} {A = A} linearVariable)
                (application-source
                  {Γ = linearArrowType A (linearArrowType B C) ∷ []}
                  {A = linearArrowType A (linearArrowType B C)}
                  linearVariable))))))

  bciIdentityMALLP :
    {A : LinearSourceType} →
    MALLPProtocolTheory []
      (just (linearSourceFormula (linearArrowType A A)))
  bciIdentityMALLP = deriveLinearApplication bciIdentity

  bciCompositionMALLP :
    {A B C : LinearSourceType} →
    MALLPProtocolTheory []
      (just (linearSourceFormula
        (linearArrowType
          (linearArrowType B C)
          (linearArrowType
            (linearArrowType A B)
            (linearArrowType A C)))))
  bciCompositionMALLP = deriveLinearApplication bciComposition

  bciExchangeMALLP :
    {A B C : LinearSourceType} →
    MALLPProtocolTheory []
      (just (linearSourceFormula
        (linearArrowType
          (linearArrowType A (linearArrowType B C))
          (linearArrowType B (linearArrowType A C)))))
  bciExchangeMALLP = deriveLinearApplication bciExchange

  word64Radix : Nat
  word64Radix = 4294967296

  -- Representation relation for a Word64 value carried by two Gforth cells.
  -- A complete literal converter must construct this witness for every word;
  -- identity preserves any such witness exactly.
  record Word64Representation (word : Word64) : Set where
    constructor word64Representation
    field
      highLimb lowLimb : Nat
      highLimbBound : highLimb < word64Radix
      lowLimbBound : lowLimb < word64Radix
      word64Denotation :
        primWord64ToNat word ≡ highLimb * word64Radix + lowLimb
  open Word64Representation public

  word64IdentityPreservesRepresentation :
    {word : Word64} →
    (representation : Word64Representation word) →
    Word64Representation word
  word64IdentityPreservesRepresentation representation = representation

  data NatListValue : Set where
    natListNil : NatListValue
    natListCons : Nat → NatListValue → NatListValue

  foldNatList : NatOp → Nat → NatListValue → Nat
  foldNatList operation initial natListNil = initial
  foldNatList operation initial (natListCons head tail) =
    applyNatOp operation head (foldNatList operation initial tail)

  foldNatList-step :
    (operation : NatOp) →
    (initial head : Nat) →
    (tail : NatListValue) →
    foldNatList operation initial (natListCons head tail) ≡
    applyNatOp operation head (foldNatList operation initial tail)
  foldNatList-step operation initial head tail = refl

  foldNatList-empty :
    (operation : NatOp) →
    (initial : Nat) →
    foldNatList operation initial natListNil ≡ initial
  foldNatList-empty operation initial = refl

  listNilSignature :
    MALLPProtocolTheory [] (just listNatFormula)
  listNilSignature = primitive-list-nil

  listConsSignature :
    MALLPProtocolTheory
      (dualPos natFormula ∷ dualPos listNatFormula ∷ [])
      (just listNatFormula)
  listConsSignature = primitive-list-cons

  listFoldSignature :
    (operation : NatOp) →
    MALLPProtocolTheory
      (dualPos listNatFormula ∷ dualPos natFormula ∷ [])
      (just natFormula)
  listFoldSignature = primitive-list-fold

open StrictLinearDataCompiler public

