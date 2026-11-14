{-# OPTIONS
--rewriting
--confluence-check
--guardedness
--lossy-unification
--no-eta-equality
--with-K
--cubical=no-glue
--erased-quotients
--erased-funext
--erased-propext
--exact-split
#-}
-- ```Agda
-- ----------------------------------------------------------------------
-- SovereignRationalSED / MALLPForth
--
-- Six Foundations packages are public: Forster PEA, symmetric bar recursion,
-- negative logical schemas, Mac Lane coherence, cohesive adjunctions, and
-- idempotent quotient reflection. Laurent MALLP is the separate resource
-- calculus used by selected compiler proofs. Finite-list computation is an
-- auxiliary constructive helper, not an axiom package.
--
-- The root rewrite pragma checks the combined registered system. A rewrite
-- equation is a conversion law, not automatically a terminating evaluator.
-- Physical specifications remain separate from logical assumptions.
-- ----------------------------------------------------------------------

module MALLPForth where

-- Primitive universe levels for the predicative category and identity
-- encodings below. The root module deliberately omits --type-in-type.
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Agda.Builtin.Nat public
open import Agda.Builtin.Int public
open import SovereignRationalSEDPhysics using (Codyadic; codyadic)
open import Agda.Builtin.Bool public
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Agda.Builtin.String public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Erased.Funext public
open import Agda.Builtin.Erased.Propext public
open import Agda.Builtin.Erased.Quotient public
open import Agda.Builtin.Word using (Word64; primWord64ToNat; primWord64FromNat) public
open import Agda.Builtin.Word.Properties using (primWord64ToNatInjective) public
-- Agda has no Agda.Builtin.Tuple module; the product record _×_ below
-- is the explicit project-owned pair, while Sigma supplies dependent pairs.
open import Agda.Builtin.Unit public
open import Agda.Builtin.Strict public
import Agda.Builtin.Reflection as Reflection
open import Agda.Builtin.Reflection.Properties
  using (primMetaToNatInjective; primQNameToWord64sInjective) public
-- Agda has no Agda.Builtin.Empty module; define the empty type locally.
data ⊥ : Set where

postulate
  S : Set
  F : Set → Set → Set
  G : (Set → Set) → Set → Set → Set
  rewF : (A : Set) → F A A ≡ S
  rewG : (A : Set → Set) (X Y : Set) → G A X Y ≡ F (A X) (A Y)
{-# REWRITE rewF rewG #-}


variable A B : Set

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

-- Injectivity witnesses for Agda's reflected names and metavariables.
-- These are useful when a metaprogram stores their primitive encodings.
reflectedNameInjective :
  {left right : Reflection.Name} →
  Reflection.primQNameToWord64s left ≡
  Reflection.primQNameToWord64s right →
  left ≡ right
reflectedNameInjective = primQNameToWord64sInjective _ _

reflectedMetaInjective :
  {left right : Reflection.Meta} →
  Reflection.primMetaToNat left ≡ Reflection.primMetaToNat right →
  left ≡ right
reflectedMetaInjective = primMetaToNatInjective _ _

-- Proof-carrying Forth instruction vocabulary and canonical renderer.
-- Kept here so generated compiler witnesses and MALLP derivations share
-- one source-level interface.
data ForthTextToken : Set where
  textPushLiteral : Nat → ForthTextToken
  textPushWord64 : Nat → Nat → ForthTextToken
  textAddWord textMonusWord textMultiplyWord textSwapWord : ForthTextToken
  textRollWord : Nat → ForthTextToken
  textTrueWord textFalseWord : ForthTextToken
  textCodyadShiftLeft textCodyadShiftRight : ForthTextToken
  textIf : List ForthTextToken → List ForthTextToken → ForthTextToken

mutual
  renderForthTokenText : ForthTextToken → String
  renderForthTokenText (textPushLiteral value) =
    primStringAppend "MALLP-NAT-LITERAL "
      (primStringAppend (primShowNat value) " ")
  renderForthTokenText (textPushWord64 high low) =
    primStringAppend
      (renderForthTokenText (textPushLiteral high))
      (renderForthTokenText (textPushLiteral low))
  renderForthTokenText textAddWord = "MALLP-NAT-ADD "
  renderForthTokenText textMonusWord = "MALLP-NAT-MONUS "
  renderForthTokenText textMultiplyWord = "MALLP-NAT-MUL "
  renderForthTokenText textSwapWord = "MALLP-SWAP "
  renderForthTokenText (textRollWord depth) =
    primStringAppend
      (renderForthTokenText (textPushLiteral depth))
      "MALLP-NAT-ROLL "
  renderForthTokenText textTrueWord = "MALLP-TRUE "
  renderForthTokenText textFalseWord = "MALLP-FALSE "
  renderForthTokenText textCodyadShiftLeft = "MALLP-CODYAD-SHIFT-LEFT "
  renderForthTokenText textCodyadShiftRight = "MALLP-CODYAD-SHIFT-RIGHT "
  renderForthTokenText (textIf whenTrue whenFalse) =
    primStringAppend "MALLP-IF "
      (primStringAppend (renderForthTokensText whenTrue)
        (primStringAppend "MALLP-ELSE "
          (primStringAppend (renderForthTokensText whenFalse) "MALLP-THEN ")))

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


-- ----------------------------------------------------------------------
-- Small utilities
-- ----------------------------------------------------------------------

infixr 3 _×_
infixr 9 _∘ᶠ_

¬_ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
¬ P = P → ⊥

⊥-elim : ∀ {ℓ : Level} {A : Set ℓ} → ⊥ → A
⊥-elim ()

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

-- ----------------------------------------------------------------------
-- FINITE LIST COMPUTATION
--
-- Auxiliary constructive witness; separate from the six foundational
-- packages and the Laurent MALLP calculus. Finite coordinates are represented
-- by ordinary Lists and Nat labels.
-- No bounded-index container is introduced. Finite prefixes
-- are enumerated by tabulateList; lookupPrefix records bounded lookup as
-- Maybe, while lookupListOr supplies an explicit default for sparse tails.
-- ----------------------------------------------------------------------

-- Agda.Builtin.Nat exports _<_ : Nat → Nat → Bool. Keep that primitive
-- comparison public; proposition-level bounds use equality with true.
-- Finite lookup and Word64 limb certificates share this representation.

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
               (i : Nat) → (i < n) ≡ true → Maybe A
lookupPrefix zero xs i ()
lookupPrefix (suc n) [] i bound = nothing
lookupPrefix (suc n) (x ∷ xs) zero refl = just x
lookupPrefix (suc n) (x ∷ xs) (suc i) bound =
  lookupPrefix n xs i bound

lookupListOr : {A : Set} → A → Nat → List A → A
lookupListOr fallback zero [] = fallback
lookupListOr fallback zero (x ∷ xs) = x
lookupListOr fallback (suc i) [] = fallback
lookupListOr fallback (suc i) (x ∷ xs) = lookupListOr fallback i xs

-- ----------------------------------------------------------------------
-- FINITE LIST COMPUTATION: AUXILIARY CONSTRUCTIVE WITNESS
--
-- This theorem remains available to finite-prefix code, separate from the
-- six foundational packages and Laurent MALLP.
-- ----------------------------------------------------------------------

module FiniteListComputation where

  lookup-tabulate :
    {A : Set} → (n : Nat) → (f : Nat → A) →
    (i : Nat) → (bound : (i < n) ≡ true) →
    lookupPrefix n (tabulateList n f) i bound ≡ just (f i)
  lookup-tabulate zero f i ()
  lookup-tabulate (suc n) f zero refl = refl
  lookup-tabulate (suc n) f (suc i) bound =
    lookup-tabulate n (λ j → f (suc j)) i bound


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

  -- Finite prefix evaluator. Fuel counts tested candidates: fuel zero
  -- tests none, while fuel (suc n) tests exactly indices zero through n.
  -- This evaluator is structurally recursive and independent of unbounded search.
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

  boundedSearch-sound zero P n ()
  boundedSearch-sound (suc fuel) P zero result with P zero
  ... | true = refl
  ... | false with boundedSearch fuel (λ i → P (suc i)) in smaller
  ...   | nothing = ⊥-elim (maybeNothingNotJust result)
  ...   | just k = ⊥-elim (sucNotZero (just-injective result))
  boundedSearch-sound (suc fuel) P (suc n) result with P zero
  ... | true = ⊥-elim (zeroNotSuc (just-injective result))
  ... | false with boundedSearch fuel (λ i → P (suc i)) in smaller
  ...   | nothing = ⊥-elim (maybeNothingNotJust result)
  ...   | just k =
    boundedSearch-sound fuel (λ i → P (suc i)) n
      (trans smaller (cong just (suc-injective (just-injective result))))

  boundedSearch-falseNotTrue : false ≡ true → ⊥
  boundedSearch-falseNotTrue ()

  boundedSearch-trueNotFalse : true ≡ false → ⊥
  boundedSearch-trueNotFalse ()

  allFalseBefore-first :
    {P : Nat → Bool} {n : Nat} →
    AllFalseBefore P (suc n) → P zero ≡ false
  allFalseBefore-first {n = zero} (before-suc before-zero first) = first
  allFalseBefore-first {n = suc n}
    (before-suc (before-suc earlier next) last) =
    allFalseBefore-first (before-suc earlier next)

  allFalseBefore-tail :
    {P : Nat → Bool} {n : Nat} →
    AllFalseBefore P (suc n) →
    AllFalseBefore (λ i → P (suc i)) n
  allFalseBefore-tail {n = zero} (before-suc before-zero first) =
    before-zero
  allFalseBefore-tail {n = suc n}
    (before-suc (before-suc earlier next) last) =
    before-suc (allFalseBefore-tail (before-suc earlier next)) last

  allFalseBefore-lift :
    {P : Nat → Bool} {n : Nat} →
    P zero ≡ false →
    AllFalseBefore (λ i → P (suc i)) n →
    AllFalseBefore P (suc n)
  allFalseBefore-lift first before-zero =
    before-suc before-zero first
  allFalseBefore-lift first (before-suc earlier next) =
    before-suc (allFalseBefore-lift first earlier) next

  leastWitness-tail :
    {P : Nat → Bool} {n : Nat} →
    LeastWitness P (suc n) →
    LeastWitness (λ i → P (suc i)) n
  leastWitness-tail witness = record
    { witness-holds = witness-holds witness
    ; all-earlier-false =
        allFalseBefore-tail (all-earlier-false witness)
    }

  boundedSearch-minimal :
    (fuel : Nat) (P : Nat → Bool) (n : Nat) →
    boundedSearch fuel P ≡ just n → AllFalseBefore P n
  boundedSearch-minimal zero P n ()
  boundedSearch-minimal (suc fuel) P zero result with P zero
  ... | true = before-zero
  ... | false with boundedSearch fuel (λ i → P (suc i)) in smaller
  ...   | nothing = ⊥-elim (maybeNothingNotJust result)
  ...   | just k = ⊥-elim (sucNotZero (just-injective result))
  boundedSearch-minimal (suc fuel) P (suc n) result with P zero in first
  ... | true = ⊥-elim (zeroNotSuc (just-injective result))
  ... | false with boundedSearch fuel (λ i → P (suc i)) in smaller
  ...   | nothing = ⊥-elim (maybeNothingNotJust result)
  ...   | just k =
    allFalseBefore-lift first
      (boundedSearch-minimal fuel (λ i → P (suc i)) n
        (trans smaller
          (cong just (suc-injective (just-injective result)))))

  boundedSearch-least :
    (fuel : Nat) (P : Nat → Bool) (n : Nat) →
    boundedSearch fuel P ≡ just n → LeastWitness P n
  boundedSearch-least fuel P n result = record
    { witness-holds = boundedSearch-sound fuel P n result
    ; all-earlier-false = boundedSearch-minimal fuel P n result
    }

  boundedSearch-complete :
    (P : Nat → Bool) (n : Nat) →
    LeastWitness P n →
    boundedSearch (suc n) P ≡ just n
  boundedSearch-complete P zero witness with P zero in first
  ... | true = refl
  ... | false =
    ⊥-elim (boundedSearch-falseNotTrue
      (trans (sym first) (witness-holds witness)))
  boundedSearch-complete P (suc n) witness with P zero in first
  ... | true =
    ⊥-elim (boundedSearch-trueNotFalse
      (trans (sym first)
        (allFalseBefore-first (all-earlier-false witness))))
  ... | false
    rewrite boundedSearch-complete
      (λ i → P (suc i)) n (leastWitness-tail witness) = refl

open FiniteListComputation public

-- ----------------------------------------------------------------------
-- CONATURALS: CONSTRUCTIVE COINDUCTIVE TIME HORIZONS
-- ----------------------------------------------------------------------

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
-- represented by the cutoff k. This always terminates by recursion on k.
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

-- ----------------------------------------------------------------------
-- PRODUCTIVE CONATURAL AND SIGNED-DIGIT STREAMS
-- ----------------------------------------------------------------------

-- A stream whose length is a conatural. Its finite prefixes are always
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

-- The bound, rather than the stream, controls recursion. This evaluator is
-- total even for an infinite stream and is the executable observation API.
foldConatPrefix : {A R : Set} → (A → R → R) → R → Nat → ConatStream A → R
foldConatPrefix step initial zero stream = initial
foldConatPrefix step initial (suc n) stream with observeStream stream
... | nothing = initial
... | just (pair value rest) =
      step value (foldConatPrefix step initial n rest)

-- Codyadic is shared with the safe physical specification:
--   2 ^ binaryShift * Σ (digit[n] * 2 ^ (-(n + 1))).
-- Its mantissa is an untruncated coinductive signed-digit stream.  The
-- compiler touches only the finite signed Int shift and leaves the producer
-- resource unchanged.

shiftCodyadicExponentLeft : Int → Int
shiftCodyadicExponentLeft (pos n) = pos (suc n)
shiftCodyadicExponentLeft (negsuc zero) = pos zero
shiftCodyadicExponentLeft (negsuc (suc n)) = negsuc n

shiftCodyadicExponentRight : Int → Int
shiftCodyadicExponentRight (pos zero) = negsuc zero
shiftCodyadicExponentRight (pos (suc n)) = pos n
shiftCodyadicExponentRight (negsuc n) = negsuc (suc n)

shiftCodyadicExponentRightAfterLeft :
  (exponent : Int) →
  shiftCodyadicExponentRight (shiftCodyadicExponentLeft exponent) ≡ exponent
shiftCodyadicExponentRightAfterLeft (pos n) = refl
shiftCodyadicExponentRightAfterLeft (negsuc zero) = refl
shiftCodyadicExponentRightAfterLeft (negsuc (suc n)) = refl

shiftCodyadicExponentLeftAfterRight :
  (exponent : Int) →
  shiftCodyadicExponentLeft (shiftCodyadicExponentRight exponent) ≡ exponent
shiftCodyadicExponentLeftAfterRight (pos zero) = refl
shiftCodyadicExponentLeftAfterRight (pos (suc n)) = refl
shiftCodyadicExponentLeftAfterRight (negsuc n) = refl

shiftCodyadicLeft shiftCodyadicRight : Codyadic → Codyadic
shiftCodyadicLeft (codyadic exponent mantissa) =
  codyadic (shiftCodyadicExponentLeft exponent) mantissa
shiftCodyadicRight (codyadic exponent mantissa) =
  codyadic (shiftCodyadicExponentRight exponent) mantissa

shiftCodyadicRightAfterLeft :
  (value : Codyadic) → shiftCodyadicRight (shiftCodyadicLeft value) ≡ value
shiftCodyadicRightAfterLeft (codyadic exponent mantissa) =
  cong (λ next → codyadic next mantissa)
    (shiftCodyadicExponentRightAfterLeft exponent)

shiftCodyadicLeftAfterRight :
  (value : Codyadic) → shiftCodyadicLeft (shiftCodyadicRight value) ≡ value
shiftCodyadicLeftAfterRight (codyadic exponent mantissa) =
  cong (λ next → codyadic next mantissa)
    (shiftCodyadicExponentLeftAfterRight exponent)

-- ----------------------------------------------------------------------
-- MODULE 1: SIX FOUNDATIONAL PACKAGES AND LAURENT MALLP
-- ----------------------------------------------------------------------

module Foundations where

  -- --------------------------------------------------------------------
  -- 1. Forster parametric enumerability.
  --
  -- ProgramCode is syntax for the concrete register machine below.
  -- Analytic families supply executable programs. ParametricEA expresses
  -- uniform family compilation as a positive global postulate. Its typed
  -- code representation is not a theorem about numeric Gödel coding or
  -- equivalence with Turing-machine computability.
  -- --------------------------------------------------------------------

  module ForsterEnumerability where

    -- ------------------------------------------------------------------
    -- Analytic enumerability: a family is enumerated by one explicit
    -- register-machine program, with the family index supplied as input.
    -- The interpreter is step-indexed: one output event may occur per
    -- machine step, and absence at a step is represented by nothing.
    -- ------------------------------------------------------------------

    data RegisterInstruction : Set where
      assignRegister : Nat → Nat → Nat → RegisterInstruction
      incrementRegister : Nat → Nat → RegisterInstruction
      decrementOrJump : Nat → Nat → Nat → RegisterInstruction
      outputRegister : Nat → Nat → RegisterInstruction
      haltRegister : RegisterInstruction

    RegisterProgram : Set
    RegisterProgram = List RegisterInstruction

    natEqual : Nat → Nat → Bool
    natEqual = _==_

    updateRegister :
      (Nat → Nat) → Nat → Nat → Nat → Nat
    updateRegister registers target value index with natEqual index target
    ... | true = value
    ... | false = registers index

    record RegisterState : Set where
      constructor registerState
      field
        machinePC : Nat
        machineRegisters : Nat → Nat
        machineHalted : Bool
    open RegisterState public

    record RegisterStep : Set where
      constructor registerStep
      field
        nextState : RegisterState
        emitted : Maybe Nat
    open RegisterStep public

    instructionAt : Nat → RegisterProgram → Maybe RegisterInstruction
    instructionAt index [] = nothing
    instructionAt zero (instruction ∷ instructions) = just instruction
    instructionAt (suc index) (instruction ∷ instructions) =
      instructionAt index instructions

    executeInstruction :
      RegisterInstruction → RegisterState → RegisterStep
    executeInstruction (assignRegister register value target) state =
      registerStep
        (registerState target
          (updateRegister (machineRegisters state) register value) false)
        nothing
    executeInstruction (incrementRegister register target) state =
      registerStep
        (registerState target
          (updateRegister (machineRegisters state) register
            (suc (machineRegisters state register))) false)
        nothing
    executeInstruction (decrementOrJump register whenZero whenPositive) state
      with machineRegisters state register
    ... | zero =
      registerStep
        (registerState whenZero (machineRegisters state) false)
        nothing
    ... | suc value =
      registerStep
        (registerState whenPositive
          (updateRegister (machineRegisters state) register value) false)
        nothing
    executeInstruction (outputRegister register target) state =
      registerStep
        (registerState target (machineRegisters state) false)
        (just (machineRegisters state register))
    executeInstruction haltRegister state =
      registerStep
        (registerState (machinePC state) (machineRegisters state) true)
        nothing

    stepRegisterMachine :
      RegisterProgram → RegisterState → RegisterStep
    stepRegisterMachine program state with machineHalted state
    ... | true = registerStep state nothing
    ... | false with instructionAt (machinePC state) program
    ...   | nothing =
        registerStep
          (registerState (machinePC state) (machineRegisters state) true)
          nothing
    ...   | just instruction = executeInstruction instruction state

    runRegisterState :
      Nat → RegisterProgram → RegisterState → RegisterState
    runRegisterState zero program state = state
    runRegisterState (suc fuel) program state =
      runRegisterState fuel program
        (nextState (stepRegisterMachine program state))

    initialRegister : Nat → Nat → Nat
    initialRegister input register with natEqual register zero
    ... | true = input
    ... | false = zero

    initialRegisterState : Nat → RegisterState
    initialRegisterState input =
      registerState zero (initialRegister input) false

    registerEnumeration :
      RegisterProgram → Nat → Nat → Maybe Nat
    registerEnumeration program input zero = nothing
    registerEnumeration program input (suc stage) =
      emitted
        (stepRegisterMachine program
          (runRegisterState stage program (initialRegisterState input)))

    -- ------------------------------------------------------------------
    -- Functional presentation used by Forster's synthetic axiom.
    -- Predicates and enumerators are Set-valued because this module is
    -- compiled with --no-prop; this is an explicit encoding boundary.
    -- ------------------------------------------------------------------

    record ParametricallyEnumerable : Set₁ where
      field
        Predicate : Nat → Nat → Set
        enumerate : Nat → Nat → Maybe Nat
        enumerate-sound :
          (i stage value : Nat) →
          enumerate i stage ≡ just value →
          Predicate i value
        enumerate-complete :
          (i value : Nat) →
          Predicate i value →
          Σ Nat (λ stage → enumerate i stage ≡ just value)
    open ParametricallyEnumerable public

    -- ------------------------------------------------------------------
    -- Analytic submodel: a family whose enumeration is realized by an
    -- explicit register program. The same program receives i in register
    -- zero, so specialization is literal input passing, not a postulated
    -- Gödel-numbering theorem.
    -- ------------------------------------------------------------------

    record AnalyticEnumerableFamily : Set₁ where
      field
        analyticPredicate : Nat → Nat → Set
        analyticProgram : RegisterProgram
        analytic-sound :
          (i stage value : Nat) →
          registerEnumeration analyticProgram i stage ≡ just value →
          analyticPredicate i value
        analytic-complete :
          (i value : Nat) →
          analyticPredicate i value →
          Σ Nat
            (λ stage →
              registerEnumeration analyticProgram i stage ≡ just value)
    open AnalyticEnumerableFamily public

    analyticFamily : AnalyticEnumerableFamily → ParametricallyEnumerable
    analyticFamily F = record
      { Predicate = analyticPredicate F
      ; enumerate = registerEnumeration (analyticProgram F)
      ; enumerate-sound = analytic-sound F
      ; enumerate-complete = analytic-complete F
      }

    record ProgramCode : Set where
      constructor programCode
      field
        codeProgram : RegisterProgram
        codeParameter : Nat
    open ProgramCode public

    -- A real universal evaluator for the stated register-machine language.
    -- Code carries program syntax and a parameter, never an arbitrary
    -- semantic function masquerading as a program.
    universalEval : ProgramCode → Nat → Maybe Nat
    universalEval (programCode program parameter) stage =
      registerEnumeration program parameter stage

    analyticCode : AnalyticEnumerableFamily → Nat → ProgramCode
    analyticCode F i = programCode (analyticProgram F) i

    analyticCode-correct :
      (F : AnalyticEnumerableFamily) →
      (i stage : Nat) →
      universalEval (analyticCode F i) stage ≡
      enumerate (analyticFamily F) i stage
    analyticCode-correct F i stage = refl

    -- ------------------------------------------------------------------
    -- Forster's parametric enumerability principle (EA). The record is
    -- the contract for a uniform code selector for every functionally
    -- given enumerable family. A global positive axiom inhabitant is
    -- supplied below; the analytic model remains the explicit-code submodel.
    -- ------------------------------------------------------------------

    record ParametricEA : Set₁ where
      field
        -- One program is compiled for the whole parameterized family;
        -- parameter i is supplied as register zero at runtime.
        compileFamily :
          ParametricallyEnumerable → RegisterProgram
        -- PEA preserves the enumerated predicate by range inclusion in
        -- both directions. It does not force stage-by-stage equality:
        -- two enumerators may emit the same witnesses in different orders
        -- or after different finite delays.
        compileFamily-sound :
          (F : ParametricallyEnumerable) →
          (i stage value : Nat) →
          registerEnumeration (compileFamily F) i stage ≡ just value →
          Predicate F i value
        compileFamily-complete :
          (F : ParametricallyEnumerable) →
          (i value : Nat) →
          Predicate F i value →
          Σ Nat
            (λ stage →
              registerEnumeration (compileFamily F) i stage ≡ just value)
    open ParametricEA public

    -- The selector γ for a family F maps each parameter i to the
    -- typed code for the one universal program specialized at i.
    parametricCode :
      (ea : ParametricEA) →
      (F : ParametricallyEnumerable) →
      Nat →
      ProgramCode
    parametricCode ea F i = programCode (compileFamily ea F) i

    parametricCode-sound :
      (ea : ParametricEA) →
      (F : ParametricallyEnumerable) →
      (i stage value : Nat) →
      universalEval (parametricCode ea F i) stage ≡ just value →
      Predicate F i value
    parametricCode-sound ea F i stage value computation =
      compileFamily-sound ea F i stage value computation

    parametricCode-complete :
      (ea : ParametricEA) →
      (F : ParametricallyEnumerable) →
      (i value : Nat) →
      Predicate F i value →
      Σ Nat
        (λ stage →
          universalEval (parametricCode ea F i) stage ≡ just value)
    parametricCode-complete ea F i value witness =
      compileFamily-complete ea F i value witness

    -- Positive synthetic PEA assumption: one selector supplies codes
    -- uniformly for every parameter of every enumerable family.
    postulate
      parametricEA : ParametricEA

    abstract
      parametricCodePEA :
        (F : ParametricallyEnumerable) →
        Nat →
        ProgramCode
      parametricCodePEA F i = parametricCode parametricEA F i

      -- The registered positive rewrite exposes the selected code.
      -- Correctness is the range-equivalence contract of parametricEA,
      -- not a stage-preserving equality with the supplied enumerator.
      parametricCodePEA-code :
        (F : ParametricallyEnumerable) →
        (i : Nat) →
        parametricCodePEA F i ≡
        programCode (compileFamily parametricEA F) i
      parametricCodePEA-code F i = refl

      parametricCodePEA-sound :
        (F : ParametricallyEnumerable) →
        (i stage value : Nat) →
        universalEval (parametricCodePEA F i) stage ≡ just value →
        Predicate F i value
      parametricCodePEA-sound F i stage value computation =
        parametricCode-sound parametricEA F i stage value computation

      parametricCodePEA-complete :
        (F : ParametricallyEnumerable) →
        (i value : Nat) →
        Predicate F i value →
        Σ Nat
          (λ stage →
            universalEval (parametricCodePEA F i) stage ≡ just value)
      parametricCodePEA-complete F i value witness =
        parametricCode-complete parametricEA F i value witness

    parametricEA-analytic-sound :
      (ea : ParametricEA) →
      (F : ParametricallyEnumerable) →
      (i stage value : Nat) →
      registerEnumeration (compileFamily ea F) i stage ≡ just value →
      Predicate F i value
    parametricEA-analytic-sound ea F i stage value computation =
      compileFamily-sound ea F i stage value computation

    parametricEA-analytic-complete :
      (ea : ParametricEA) →
      (F : ParametricallyEnumerable) →
      (i value : Nat) →
      Predicate F i value →
      Σ Nat
        (λ stage →
          registerEnumeration (compileFamily ea F) i stage ≡ just value)
    parametricEA-analytic-complete ea F i value witness =
      compileFamily-complete ea F i value witness

    -- A witness of synthetic EA uniformly realizes every family in the
    -- analytic register-machine model, with correctness transported from
    -- the functional enumerator through the interpreter equation.
    parametricEA-analytic :
      (ea : ParametricEA) →
      ParametricallyEnumerable →
      AnalyticEnumerableFamily
    parametricEA-analytic ea F = record
      { analyticPredicate = Predicate F
      ; analyticProgram = compileFamily ea F
      ; analytic-sound = parametricEA-analytic-sound ea F
      ; analytic-complete = parametricEA-analytic-complete ea F
      }
  -- --------------------------------------------------------------------
  -- 2. Spector-style symmetric bar recursion over finite partial maps.
  --
  -- The control functional chooses the next key. A present key stops at
  -- the base case; an absent key extends the finite partial map using the
  -- step functional. SymmetricBarCondition is an explicit bar-coverage
  -- premise. The operator and stop/step equations are positive assumptions,
  -- not a derived terminating evaluator.
  -- --------------------------------------------------------------------

  module SymmetricBarRecursion where

    FiniteEntries : Set → Set
    FiniteEntries X = List (Nat × X)

    natEq : Nat → Nat → Bool
    natEq = _==_

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
    -- duplicates. This prevents the association-list representation from
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

    threadEntries :
      {X : Set} →
      (entries : PartialMap X) →
      (key : Nat) →
      DomainDecision entries key →
      X →
      PartialMap X
    threadEntries entries key (inDomain present) value = entries
    threadEntries entries key (outDomain absent) value =
      extendFresh entries key absent value

    threadEntries-contains-zero :
      {X : Set} →
      (entries : PartialMap X) →
      (decision : DomainDecision entries zero) →
      (value : X) →
      memberKey zero
        (mapEntries (threadEntries entries zero decision value)) ≡ true
    threadEntries-contains-zero entries (inDomain present) value = present
    threadEntries-contains-zero entries (outDomain absent) value = refl

    omegaThread :
      {X : Set} →
      (omega : (Nat → X) → Nat) →
      (default : X) →
      (alpha : Nat → X) →
      (initial : PartialMap X) →
      Nat → PartialMap X
    omegaThread omega default alpha initial zero = initial
    omegaThread omega default alpha initial (suc n) =
      let entries = omegaThread omega default alpha initial n
          key = omega (streamOf (mapEntries entries) default)
      in threadEntries entries key (decideDomain entries key) (alpha key)

    omegaThread-step-zero :
      {X : Set} →
      (default : X) →
      (alpha : Nat → X) →
      (initial : PartialMap X) →
      (fuel : Nat) →
      memberKey zero
        (mapEntries
          (omegaThread (λ stream → zero) default alpha initial (suc fuel)))
        ≡ true
    omegaThread-step-zero default alpha initial fuel =
      threadEntries-contains-zero
        (omegaThread (λ stream → zero) default alpha initial fuel)
        (decideDomain
          (omegaThread (λ stream → zero) default alpha initial fuel)
          zero)
        (alpha zero)

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



    -- ------------------------------------------------------------------
    -- Selection products and finite backward induction.
    --
    -- A selection function responds to a payoff with a chosen move.
    -- Product selection composes these responses by Bellman's continuation
    -- equation. Optimality is extra data: arbitrary payoffs need not attain
    -- maxima, and this layer never manufactures an optimizer.
    -- ------------------------------------------------------------------

    Selection : (X R : Set) → Set
    Selection X R = (X → R) → X

    selectedOutcome :
      {X R : Set} → Selection X R → (X → R) → R
    selectedOutcome choose payoff = payoff (choose payoff)

    productSelection :
      {X Y R : Set} →
      Selection X R →
      (X → Selection Y R) →
      Selection (X × Y) R
    productSelection {X = X} {Y = Y} chooseX chooseY payoff =
      let
        response : X → Y
        response x = chooseY x (λ y → payoff (pair x y))

        first : X
        first = chooseX (λ x → payoff (pair x (response x)))
      in pair first (response first)

    productSelection-bellman :
      {X Y R : Set} →
      (chooseX : Selection X R) →
      (chooseY : X → Selection Y R) →
      (payoff : X × Y → R) →
      selectedOutcome (productSelection chooseX chooseY) payoff ≡
      selectedOutcome chooseX
        (λ x → selectedOutcome (chooseY x) (λ y → payoff (pair x y)))
    productSelection-bellman chooseX chooseY payoff = refl

    record Preorder (R : Set) : Set₁ where
      field
        below : R → R → Set
        below-refl : (value : R) → below value value
        below-trans :
          {left middle right : R} →
          below left middle →
          below middle right →
          below left right
    open Preorder public

    OptimalSelection :
      {X R : Set} →
      (order : Preorder R) →
      Selection X R →
      Set
    OptimalSelection {X} {R} order choose =
      (payoff : X → R) →
      (candidate : X) →
      below order (payoff candidate) (payoff (choose payoff))

    productSelection-optimal :
      {X Y R : Set} →
      (order : Preorder R) →
      (chooseX : Selection X R) →
      (chooseY : X → Selection Y R) →
      OptimalSelection order chooseX →
      ((x : X) → OptimalSelection order (chooseY x)) →
      (payoff : X × Y → R) →
      (candidate : X × Y) →
      below order
        (payoff candidate)
        (selectedOutcome (productSelection chooseX chooseY) payoff)
    productSelection-optimal order chooseX chooseY optimalX optimalY
      payoff (pair x y) =
      below-trans order
        (optimalY x (λ y′ → payoff (pair x y′)) y)
        (optimalX
          (λ x′ →
            payoff (pair x′ (chooseY x′ (λ y′ → payoff (pair x′ y′)))))
          x)

    data Play (X : Set) : Nat → Set where
      noMoves : Play X zero
      prependMove : {n : Nat} → X → Play X n → Play X (suc n)

    playHeadOr : {X : Set} {horizon : Nat} → X → Play X horizon → X
    playHeadOr fallback noMoves = fallback
    playHeadOr fallback (prependMove move rest) = move

    backwardInduction :
      {X R : Set} →
      (horizon : Nat) →
      Selection X R →
      Selection (Play X horizon) R
    backwardInduction zero choose payoff = noMoves
    backwardInduction {X = X} {R = R} (suc horizon) choose payoff =
      let
        suffix : X → Play X horizon
        suffix x =
          backwardInduction horizon choose
            (λ rest → payoff (prependMove x rest))

        first : X
        first = choose (λ x → payoff (prependMove x (suffix x)))
      in prependMove first (suffix first)

    backwardInduction-bellman :
      {X R : Set} →
      (horizon : Nat) →
      (choose : Selection X R) →
      (payoff : Play X (suc horizon) → R) →
      selectedOutcome (backwardInduction (suc horizon) choose) payoff ≡
      selectedOutcome choose
        (λ x →
          selectedOutcome
            (backwardInduction horizon choose)
            (λ rest → payoff (prependMove x rest)))
    backwardInduction-bellman horizon choose payoff = refl

    backwardInduction-optimal :
      {X R : Set} →
      (order : Preorder R) →
      (choose : Selection X R) →
      OptimalSelection order choose →
      (horizon : Nat) →
      OptimalSelection order (backwardInduction horizon choose)
    backwardInduction-optimal order choose optimal zero payoff noMoves =
      below-refl order (payoff noMoves)
    backwardInduction-optimal order choose optimal (suc horizon)
      payoff (prependMove firstMove rest) =
      below-trans order
        (backwardInduction-optimal order choose optimal horizon
          (λ suffix → payoff (prependMove firstMove suffix))
          rest)
        (optimal
          (λ move →
            payoff
              (prependMove move
                (backwardInduction horizon choose
                  (λ suffix → payoff (prependMove move suffix)))))
          firstMove)

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

  -- --------------------------------------------------------------------
  -- 3. Negative logical and choice schemas.
  --
  -- Excluded middle and function extensionality are postulated only under
  -- double negation. DNS is represented directly by its negative
  -- counterexample principle. No dependent/countable-choice schema occurs.
  -- Double-negated DNE and Peirce remain derived from double-negated EM.
  --
  -- Set : Set is a universe-formation judgement, not a proposition or an
  -- Agda term. It has no well-typed double negation. Predicative,
  -- universe-polymorphic Set levels are retained instead.
  -- --------------------------------------------------------------------

  module DoubleNegation where

    infixr 4 _⊎ᴺ_

    data _⊎ᴺ_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
      leftᴺ : A → A ⊎ᴺ B
      rightᴺ : B → A ⊎ᴺ B

    ExcludedMiddleAt : (ℓ : Level) → Set (lsuc ℓ)
    ExcludedMiddleAt ℓ = (P : Set ℓ) → P ⊎ᴺ (¬ P)

    DoubleNegationEliminationAt : (ℓ : Level) → Set (lsuc ℓ)
    DoubleNegationEliminationAt ℓ =
      (P : Set ℓ) → ¬ (¬ P) → P

    PeirceAt : (ℓ : Level) → Set (lsuc ℓ)
    PeirceAt ℓ =
      (P Q : Set ℓ) → ((P → Q) → P) → P

    FunctionExtensionalityAt :
      (a b : Level) → Set (lsuc (a ⊔ b))
    FunctionExtensionalityAt a b =
      {A : Set a} {B : Set b} →
      (f g : A → B) →
      ((x : A) → f x ≡ g x) →
      f ≡ g

    -- DNS is already a negative principle: it says that no family can
    -- have pointwise double-negated witnesses together with a refutation of
    -- every global witness. Postulating it with another outer ¬¬ would
    -- weaken the principle unnecessarily.
    DNSCounterexampleAt : (ℓ : Level) → Set (lsuc ℓ)
    DNSCounterexampleAt ℓ =
      Σ (Nat → Set ℓ)
        (λ P →
          Σ ((n : Nat) → ¬ (¬ (P n)))
            (λ pointwise → ¬ ((n : Nat) → P n)))

    DoubleNegationShiftAt : (ℓ : Level) → Set (lsuc ℓ)
    DoubleNegationShiftAt ℓ =
      {P : Nat → Set ℓ} →
      ((n : Nat) → ¬ (¬ P n)) →
      ¬ (¬ ((n : Nat) → P n))

    dns-to-negative-counterexample :
      (ℓ : Level) →
      DoubleNegationShiftAt ℓ →
      ¬ (DNSCounterexampleAt ℓ)
    dns-to-negative-counterexample ℓ dns
      (P , (pointwise , noGlobalWitness)) =
      dns pointwise noGlobalWitness

    dns-from-negative-counterexample :
      (ℓ : Level) →
      ¬ (DNSCounterexampleAt ℓ) →
      DoubleNegationShiftAt ℓ
    dns-from-negative-counterexample ℓ noCounterexample
      {P} pointwise noGlobalWitness =
      noCounterexample (P , (pointwise , noGlobalWitness))


    mapDoubleNegation :
      {a b : Level} {P : Set a} {Q : Set b} →
      (P → Q) → ¬ (¬ P) → ¬ (¬ Q)
    mapDoubleNegation f notNotP notQ =
      notNotP (λ p → notQ (f p))

    excludedMiddle-implies-dne :
      (ℓ : Level) →
      ExcludedMiddleAt ℓ →
      DoubleNegationEliminationAt ℓ
    excludedMiddle-implies-dne ℓ excluded P notNotP
      with excluded P
    ... | leftᴺ witness = witness
    ... | rightᴺ refute = ⊥-elim (notNotP refute)

    excludedMiddle-implies-peirce :
      (ℓ : Level) →
      ExcludedMiddleAt ℓ →
      PeirceAt ℓ
    excludedMiddle-implies-peirce ℓ excluded P Q continuation
      with excluded P
    ... | leftᴺ witness = witness
    ... | rightᴺ refute =
      continuation (λ witness → ⊥-elim (refute witness))

    -- These are negative counterparts only. They supply no classical
    -- decision, extensionality proof, enumerator, or choice sequence.
    postulate
      doubleNegatedExcludedMiddle :
        (ℓ : Level) → ¬ (¬ (ExcludedMiddleAt ℓ))

      doubleNegatedFunctionExtensionality :
        (a b : Level) →
        ¬ (¬ (FunctionExtensionalityAt a b))

      -- This is literally a negation, as required by the negative-
      -- postulate canonicity theorem. It is equivalent to ordinary DNS.
      negativeDNS :
        (ℓ : Level) → ¬ (DNSCounterexampleAt ℓ)

    doubleNegationShift :
      (ℓ : Level) → DoubleNegationShiftAt ℓ
    doubleNegationShift ℓ =
      dns-from-negative-counterexample ℓ (negativeDNS ℓ)

    -- Compatibility theorem, now derived from the stronger negative form.
    doubleNegatedDNS :
      (ℓ : Level) → ¬ (¬ (DoubleNegationShiftAt ℓ))
    doubleNegatedDNS ℓ notDNS = notDNS (doubleNegationShift ℓ)

    doubleNegatedDNE :
      (ℓ : Level) →
      ¬ (¬ (DoubleNegationEliminationAt ℓ))
    doubleNegatedDNE ℓ =
      mapDoubleNegation
        (excludedMiddle-implies-dne ℓ)
        (doubleNegatedExcludedMiddle ℓ)

    doubleNegatedPeirce :
      (ℓ : Level) → ¬ (¬ (PeirceAt ℓ))
    doubleNegatedPeirce ℓ =
      mapDoubleNegation
        (excludedMiddle-implies-peirce ℓ)
        (doubleNegatedExcludedMiddle ℓ)

    -- One explicit package for the negative boundary. Its fields remain
    -- negative assumptions; bundling them creates no classical witness.
    record NegativeLogicalBoundary (ℓ : Level) : Set (lsuc ℓ) where
      field
        excludedMiddleNegative :
          ¬ (¬ (ExcludedMiddleAt ℓ))
        functionExtensionalityNegative :
          ¬ (¬ (FunctionExtensionalityAt ℓ ℓ))
        dnsNegative :
          ¬ (DNSCounterexampleAt ℓ)
    open NegativeLogicalBoundary public

    negativeLogicalBoundary : (ℓ : Level) → NegativeLogicalBoundary ℓ
    negativeLogicalBoundary ℓ = record
      { excludedMiddleNegative = doubleNegatedExcludedMiddle ℓ
      ; functionExtensionalityNegative = doubleNegatedFunctionExtensionality ℓ ℓ
      ; dnsNegative = negativeDNS ℓ
      }

  -- --------------------------------------------------------------------
  -- 4. Mac Lane coherence via the thin free monoidal category on
  -- Nat-labelled generators and a computational normal form.
  -- --------------------------------------------------------------------

  module MacLaneCoherence where

    -- ------------------------------------------------------------------
    -- Thin free monoidal category on Nat-labelled generators.
    --
    -- Objects are parenthesized tensor expressions. A morphism is an
    -- equality between their ordered atom normal forms. Normalization is
    -- executable, hom existence is decidable, and UIP makes every hom-set
    -- a proposition. Associators/unitors and all their coherence diagrams
    -- are represented by these canonical normal-form paths.
    -- ------------------------------------------------------------------

    data TensorExpr : Set where
      atom : Nat → TensorExpr
      unitₑ : TensorExpr
      tensor : TensorExpr → TensorExpr → TensorExpr

    _++_ : List Nat → List Nat → List Nat
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

    tensorNF : TensorExpr → List Nat
    tensorNF (atom n) = n ∷ []
    tensorNF unitₑ = []
    tensorNF (tensor A B) = tensorNF A ++ tensorNF B

    tensorLabelEq : Nat → Nat → Bool
    tensorLabelEq = _==_

    andBool : Bool → Bool → Bool
    andBool true x = x
    andBool false x = false

    listEq : List Nat → List Nat → Bool
    listEq [] [] = true
    listEq [] (y ∷ ys) = false
    listEq (x ∷ xs) [] = false
    listEq (x ∷ xs) (y ∷ ys) =
      andBool (tensorLabelEq x y) (listEq xs ys)

    falseNotTrue : false ≡ true → ⊥
    falseNotTrue ()

    tensorLabelEq-refl : (n : Nat) → tensorLabelEq n n ≡ true
    tensorLabelEq-refl zero = refl
    tensorLabelEq-refl (suc n) = tensorLabelEq-refl n

    listEq-refl : (xs : List Nat) → listEq xs xs ≡ true
    listEq-refl [] = refl
    listEq-refl (x ∷ xs)
      rewrite tensorLabelEq-refl x | listEq-refl xs = refl

    tensorLabelEq-sound :
      {m n : Nat} → tensorLabelEq m n ≡ true → m ≡ n
    tensorLabelEq-sound {zero} {zero} proof = refl
    tensorLabelEq-sound {zero} {suc n} ()
    tensorLabelEq-sound {suc m} {zero} ()
    tensorLabelEq-sound {suc m} {suc n} proof =
      cong suc (tensorLabelEq-sound proof)

    listEq-sound :
      {xs ys : List Nat} →
      listEq xs ys ≡ true →
      xs ≡ ys
    listEq-sound {[]} {[]} proof = refl
    listEq-sound {[]} {y ∷ ys} ()
    listEq-sound {x ∷ xs} {[]} ()
    listEq-sound {x ∷ xs} {y ∷ ys} proof
      with tensorLabelEq x y in headEquality
         | listEq xs ys in tailEquality
    ... | true | true =
      cong₂ _∷_
        (tensorLabelEq-sound headEquality)
        (listEq-sound tailEquality)
    ... | true | false = ⊥-elim (falseNotTrue proof)
    ... | false | tail = ⊥-elim (falseNotTrue proof)

    listEq-complete :
      {xs ys : List Nat} →
      xs ≡ ys →
      listEq xs ys ≡ true
    listEq-complete {xs} refl = listEq-refl xs

    TensorHom : TensorExpr → TensorExpr → Set
    TensorHom A B = tensorNF A ≡ tensorNF B

    -- A terminating decision procedure for the hom relation. The
    -- negative branch contains a proof that distinct normal forms cannot
    -- be joined by a structural morphism.
    data TensorHomDecision (A B : TensorExpr) : Set where
      homExists : TensorHom A B → TensorHomDecision A B
      homAbsent : (TensorHom A B → ⊥) → TensorHomDecision A B

    decideTensorHom : (A B : TensorExpr) → TensorHomDecision A B
    decideTensorHom A B
      with listEq (tensorNF A) (tensorNF B) in equality
    ... | true = homExists (listEq-sound equality)
    ... | false =
      homAbsent
        (λ path → falseNotTrue
          (trans (sym equality) (listEq-complete path)))

    homToEquality :
      {A B : TensorExpr} →
      TensorHom A B →
      tensorNF A ≡ tensorNF B
    homToEquality equality = equality

    homFromEquality :
      {A B : TensorExpr} →
      tensorNF A ≡ tensorNF B →
      TensorHom A B
    homFromEquality equality = equality

    tensorId : (A : TensorExpr) → TensorHom A A
    tensorId A = refl

    tensorCompose :
      {A B C : TensorExpr} →
      TensorHom B C →
      TensorHom A B →
      TensorHom A C
    tensorCompose second first = trans first second

    tensorMap :
      {A A′ B B′ : TensorExpr} →
      TensorHom A A′ →
      TensorHom B B′ →
      TensorHom (tensor A B) (tensor A′ B′)
    tensorMap first second = cong₂ _++_ first second

    trans-assoc :
      {A : Set} {a b c d : A}
      (first : a ≡ b) (second : b ≡ c) (third : c ≡ d) →
      trans (trans first second) third ≡
      trans first (trans second third)
    trans-assoc refl refl refl = refl

    trans-right-unit :
      {X : Set} {x y : X} (path : x ≡ y) →
      trans path refl ≡ path
    trans-right-unit refl = refl

    tensorPathUIP :
      {X : Set} (x y : X) (p q : x ≡ y) →
      p ≡ q
    tensorPathUIP x .x refl refl = refl

    tensorHom-proposition :
      {A B : TensorExpr} →
      (f g : TensorHom A B) →
      f ≡ g
    tensorHom-proposition {A} {B} f g =
      tensorPathUIP (tensorNF A) (tensorNF B) f g

    tensorIdentity-left :
      {A B : TensorExpr} (f : TensorHom A B) →
      tensorCompose {A = A} {B = A} {C = B} f (tensorId A) ≡ f
    tensorIdentity-left f = refl

    tensorIdentity-right :
      {A B : TensorExpr} (f : TensorHom A B) →
      tensorCompose {A = A} {B = B} {C = B} (tensorId B) f ≡ f
    tensorIdentity-right f = trans-right-unit {X = List Nat} f

    tensorAssociativity :
      {A B C D : TensorExpr}
      (f : TensorHom C D)
      (g : TensorHom B C)
      (h : TensorHom A B) →
      tensorCompose {A = A} {B = C} {C = D} f
        (tensorCompose {A = A} {B = B} {C = C} g h) ≡
      tensorCompose {A = A} {B = B} {C = D}
        (tensorCompose {A = B} {B = C} {C = D} f g) h
    tensorAssociativity {A} {B} {C} {D} f g h =
      trans-assoc
        {A = List Nat}
        {a = tensorNF A}
        {b = tensorNF B}
        {c = tensorNF C}
        {d = tensorNF D}
        h g f

    tensorMap-identity :
      (A B : TensorExpr) →
      tensorMap
        {A = A} {A′ = A} {B = B} {B′ = B}
        (tensorId A) (tensorId B) ≡
      tensorId (tensor A B)
    tensorMap-identity A B = refl

    tensorMap-composition :
      {A A′ A″ B B′ B″ : TensorExpr}
      (f₂ : TensorHom A′ A″) (f₁ : TensorHom A A′)
      (g₂ : TensorHom B′ B″) (g₁ : TensorHom B B′) →
      tensorMap
        {A = A} {A′ = A″} {B = B} {B′ = B″}
        (tensorCompose {A = A} {B = A′} {C = A″} f₂ f₁)
        (tensorCompose {A = B} {B = B′} {C = B″} g₂ g₁) ≡
      tensorCompose
        {A = tensor A B}
        {B = tensor A′ B′}
        {C = tensor A″ B″}
        (tensorMap
          {A = A′} {A′ = A″} {B = B′} {B′ = B″}
          f₂ g₂)
        (tensorMap
          {A = A} {A′ = A′} {B = B} {B′ = B′}
          f₁ g₁)
    tensorMap-composition
      {A} {A′} {A″} {B} {B′} {B″} f₂ f₁ g₂ g₁ =
      tensorHom-proposition
        {A = tensor A B}
        {B = tensor A″ B″}
        (tensorMap
          {A = A} {A′ = A″} {B = B} {B′ = B″}
          (tensorCompose {A = A} {B = A′} {C = A″} f₂ f₁)
          (tensorCompose {A = B} {B = B′} {C = B″} g₂ g₁))
        (tensorCompose
          {A = tensor A B}
          {B = tensor A′ B′}
          {C = tensor A″ B″}
          (tensorMap
            {A = A′} {A′ = A″} {B = B′} {B′ = B″}
            f₂ g₂)
          (tensorMap
            {A = A} {A′ = A′} {B = B} {B′ = B′}
            f₁ g₁))

    append-assoc :
      (xs ys zs : List Nat) →
      (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    append-assoc [] ys zs = refl
    append-assoc (x ∷ xs) ys zs =
      cong (x ∷_) (append-assoc xs ys zs)

    append-left-unit : (xs : List Nat) → [] ++ xs ≡ xs
    append-left-unit xs = refl

    append-right-unit : (xs : List Nat) → xs ++ [] ≡ xs
    append-right-unit [] = refl
    append-right-unit (x ∷ xs) =
      cong (x ∷_) (append-right-unit xs)

    associator :
      (A B C : TensorExpr) →
      TensorHom (tensor (tensor A B) C) (tensor A (tensor B C))
    associator A B C =
      append-assoc (tensorNF A) (tensorNF B) (tensorNF C)

    associatorInverse :
      (A B C : TensorExpr) →
      TensorHom (tensor A (tensor B C)) (tensor (tensor A B) C)
    associatorInverse A B C =
      sym (append-assoc (tensorNF A) (tensorNF B) (tensorNF C))

    leftUnitor :
      (A : TensorExpr) → TensorHom (tensor unitₑ A) A
    leftUnitor A = append-left-unit (tensorNF A)

    leftUnitorInverse :
      (A : TensorExpr) → TensorHom A (tensor unitₑ A)
    leftUnitorInverse A = sym (append-left-unit (tensorNF A))

    rightUnitor :
      (A : TensorExpr) → TensorHom (tensor A unitₑ) A
    rightUnitor A = append-right-unit (tensorNF A)

    rightUnitorInverse :
      (A : TensorExpr) → TensorHom A (tensor A unitₑ)
    rightUnitorInverse A = sym (append-right-unit (tensorNF A))

    fromAtoms : List Nat → TensorExpr
    fromAtoms [] = unitₑ
    fromAtoms (x ∷ xs) = tensor (atom x) (fromAtoms xs)

    tensorNF-fromAtoms : (xs : List Nat) → tensorNF (fromAtoms xs) ≡ xs
    tensorNF-fromAtoms [] = refl
    tensorNF-fromAtoms (x ∷ xs) =
      cong (x ∷_) (tensorNF-fromAtoms xs)

    normalForm : TensorExpr → TensorExpr
    normalForm A = fromAtoms (tensorNF A)

    normalizeForward :
      (A : TensorExpr) →
      TensorHom A (normalForm A)
    normalizeForward A =
      sym (tensorNF-fromAtoms (tensorNF A))

    normalizeBackward :
      (A : TensorExpr) →
      TensorHom (normalForm A) A
    normalizeBackward A =
      tensorNF-fromAtoms (tensorNF A)

    -- Coherence: every formal composite of associators, unitors, identities
    -- and tensor maps with common endpoints is equal.
    macLaneCoherence :
      {A B : TensorExpr} →
      (f g : TensorHom A B) →
      f ≡ g
    macLaneCoherence {A} {B} f g =
      tensorHom-proposition {A = A} {B = B} f g

    tensor-atom : (n : Nat) → tensorNF (atom n) ≡ n ∷ []
    tensor-atom n = refl

    tensor-unit : tensorNF unitₑ ≡ []
    tensor-unit = refl

    tensor-product : (A B : TensorExpr) →
      tensorNF (tensor A B) ≡ tensorNF A ++ tensorNF B
    tensor-product A B = refl
  module CohesiveRetractions where

    -- ------------------------------------------------------------------
    -- Lawvere–Schreiber cohesive structure is the adjoint quadruple
    --
    -- Π : H → G Disc : G → H
    -- Γ : H → G coDisc : G → H
    --
    -- satisfying Π ⊣ Disc ⊣ Γ ⊣ coDisc, full faithfulness of Disc/coDisc,
    -- and finite-product preservation by Π.
    --
    -- H and G remain distinct categories. This record states the categorical
    -- laws only; a cohesive topos also needs topos structure on H and
    -- ∞-groupoid structure on G. A concrete nonidentity three-element/
    -- two-element finite-poset model is supplied below, not a cohesive topos.
    -- ------------------------------------------------------------------

    record Category : Set₂ where
      field
        categoryObjects : Set₁
        categoryHom :
          categoryObjects → categoryObjects → Set
        categoryHomEq :
          {A B : categoryObjects} →
          categoryHom A B → categoryHom A B → Set
        categoryHomEq-refl :
          {A B : categoryObjects} →
          (f : categoryHom A B) →
          categoryHomEq f f
        categoryHomEq-sym :
          {A B : categoryObjects} {f g : categoryHom A B} →
          categoryHomEq f g → categoryHomEq g f
        categoryHomEq-trans :
          {A B : categoryObjects} {f g h : categoryHom A B} →
          categoryHomEq f g → categoryHomEq g h → categoryHomEq f h
        categoryId :
          {A : categoryObjects} → categoryHom A A
        categoryCompose :
          {A B C : categoryObjects} →
          categoryHom B C → categoryHom A B → categoryHom A C
        categoryCompose-respects :
          {A B C : categoryObjects}
          {g g′ : categoryHom B C}
          {f f′ : categoryHom A B} →
          categoryHomEq g g′ →
          categoryHomEq f f′ →
          categoryHomEq
            (categoryCompose g f)
            (categoryCompose g′ f′)
        categoryCompose-assoc :
          {A B C D : categoryObjects}
          (h : categoryHom C D)
          (g : categoryHom B C)
          (f : categoryHom A B) →
          categoryHomEq
            (categoryCompose h (categoryCompose g f))
            (categoryCompose (categoryCompose h g) f)
        categoryCompose-id-left :
          {A B : categoryObjects} →
          (f : categoryHom A B) →
          categoryHomEq (categoryCompose categoryId f) f
        categoryCompose-id-right :
          {A B : categoryObjects} →
          (f : categoryHom A B) →
          categoryHomEq (categoryCompose f categoryId) f
    open Category public

    -- ------------------------------------------------------------------
    -- A functor preserves identities and composition up to the target
    -- category's chosen hom equality. That equality is explicit in each
    -- model, so no global function-extensionality assumption is needed.
    -- ------------------------------------------------------------------

    -- Spell out object endpoints in the laws: categoryHom is a record
    -- family, so Agda cannot recover its indices by inverting categoryId
    -- or categoryCompose during elaboration.
    record Functor (C D : Category) : Set₂ where
      field
        functorObject : categoryObjects C → categoryObjects D
        functorArrow :
          {A B : categoryObjects C} →
          categoryHom C A B →
          categoryHom D (functorObject A) (functorObject B)
        functorArrow-respects :
          {A B : categoryObjects C}
          {f g : categoryHom C A B} →
          categoryHomEq C f g →
          categoryHomEq D (functorArrow f) (functorArrow g)
        functorIdentity :
          {A : categoryObjects C} →
          categoryHomEq D
            {A = functorObject A}
            {B = functorObject A}
            (functorArrow {A = A} {B = A} (categoryId C {A = A}))
            (categoryId D {A = functorObject A})
        functorComposition :
          {A B C′ : categoryObjects C}
          (g : categoryHom C B C′)
          (f : categoryHom C A B) →
          categoryHomEq D
            {A = functorObject A}
            {B = functorObject C′}
            (functorArrow {A = A} {B = C′}
              (categoryCompose C {A = A} {B = B} {C = C′} g f))
            (categoryCompose D
              {A = functorObject A}
              {B = functorObject B}
              {C = functorObject C′}
              (functorArrow {A = B} {B = C′} g)
              (functorArrow {A = A} {B = B} f))
    open Functor public

    identityFunctor : (C : Category) → Functor C C
    identityFunctor C = record
      { functorObject = λ A → A
      ; functorArrow = λ {A} {B} f → f
      ; functorArrow-respects = λ {A} {B} equality → equality
      ; functorIdentity =
          λ {A} →
            categoryHomEq-refl C
              {A = A} {B = A}
              (categoryId C {A = A})
      ; functorComposition =
          λ {A} {B} {C′} g f →
            categoryHomEq-refl C
              {A = A} {B = C′}
              (categoryCompose C
                {A = A} {B = B} {C = C′} g f)
      }

    -- ------------------------------------------------------------------
    -- An adjunction is a natural isomorphism of hom-functors, represented
    -- by transpose/untranspose and both inverse and naturality laws.
    -- ------------------------------------------------------------------

    record Adjunction
      {C D : Category}
      (F : Functor C D)
      (G : Functor D C) : Set₂ where
      field
        transpose :
          {A : categoryObjects C} {B : categoryObjects D} →
          categoryHom D (functorObject F A) B →
          categoryHom C A (functorObject G B)
        untranspose :
          {A : categoryObjects C} {B : categoryObjects D} →
          categoryHom C A (functorObject G B) →
          categoryHom D (functorObject F A) B
        transpose-respects :
          {A : categoryObjects C} {B : categoryObjects D}
          {f g : categoryHom D (functorObject F A) B} →
          categoryHomEq D f g →
          categoryHomEq C (transpose f) (transpose g)
        untranspose-respects :
          {A : categoryObjects C} {B : categoryObjects D}
          {f g : categoryHom C A (functorObject G B)} →
          categoryHomEq C f g →
          categoryHomEq D (untranspose f) (untranspose g)
        transpose-untranspose :
          {A : categoryObjects C} {B : categoryObjects D}
          (f : categoryHom C A (functorObject G B)) →
          categoryHomEq C (transpose (untranspose f)) f
        untranspose-transpose :
          {A : categoryObjects C} {B : categoryObjects D}
          (f : categoryHom D (functorObject F A) B) →
          categoryHomEq D (untranspose (transpose f)) f
        transpose-natural-source :
          {A A′ : categoryObjects C} {B : categoryObjects D}
          (f : categoryHom C A′ A)
          (g : categoryHom D (functorObject F A) B) →
          categoryHomEq C
            (transpose (categoryCompose D g (functorArrow F f)))
            (categoryCompose C (transpose g) f)
        transpose-natural-target :
          {A : categoryObjects C} {B B′ : categoryObjects D}
          (g : categoryHom D B B′)
          (f : categoryHom D (functorObject F A) B) →
          categoryHomEq C
            (transpose (categoryCompose D g f))
            (categoryCompose C (functorArrow G g) (transpose f))
    open Adjunction public

    identityAdjunction :
      (C : Category) →
      Adjunction (identityFunctor C) (identityFunctor C)
    identityAdjunction C = record
      { transpose = λ f → f
      ; untranspose = λ f → f
      ; transpose-respects = λ equality → equality
      ; untranspose-respects = λ equality → equality
      ; transpose-untranspose =
          λ f → categoryHomEq-refl C f
      ; untranspose-transpose =
          λ f → categoryHomEq-refl C f
      ; transpose-natural-source =
          λ f g → categoryHomEq-refl C (categoryCompose C g f)
      ; transpose-natural-target =
          λ g f → categoryHomEq-refl C (categoryCompose C g f)
      }

    -- ------------------------------------------------------------------
    -- Full faithfulness is the hom-set map being an isomorphism.
    -- ------------------------------------------------------------------

    record FullyFaithful
      {C D : Category}
      (F : Functor C D) : Set₂ where
      field
        reflectArrow :
          {A B : categoryObjects C} →
          categoryHom D (functorObject F A) (functorObject F B) →
          categoryHom C A B
        reflectArrow-respects :
          {A B : categoryObjects C}
          {f g : categoryHom D (functorObject F A) (functorObject F B)} →
          categoryHomEq D f g →
          categoryHomEq C (reflectArrow f) (reflectArrow g)
        reflect-map :
          {A B : categoryObjects C}
          (f : categoryHom C A B) →
          categoryHomEq C (reflectArrow (functorArrow F f)) f
        map-reflect :
          {A B : categoryObjects C}
          (f : categoryHom D (functorObject F A) (functorObject F B)) →
          categoryHomEq D (functorArrow F (reflectArrow f)) f
    open FullyFaithful public

    identityFullyFaithful :
      (C : Category) →
      FullyFaithful (identityFunctor C)
    identityFullyFaithful C = record
      { reflectArrow = λ f → f
      ; reflectArrow-respects = λ equality → equality
      ; reflect-map = λ f → categoryHomEq-refl C f
      ; map-reflect = λ f → categoryHomEq-refl C f
      }

    -- ------------------------------------------------------------------
    -- Finite products are expressed categorically by a terminal object
    -- and binary products with the universal pairing law.
    -- ------------------------------------------------------------------

    record TerminalObject (C : Category) : Set₂ where
      field
        terminalObject : categoryObjects C
        terminalArrow :
          {A : categoryObjects C} →
          categoryHom C A terminalObject
        terminalArrow-unique :
          {A : categoryObjects C}
          (f : categoryHom C A terminalObject) →
          categoryHomEq C f terminalArrow
    open TerminalObject public

    record BinaryProduct
      (C : Category)
      (A B : categoryObjects C) : Set₂ where
      field
        binaryProductObject : categoryObjects C
        binaryProductLeft : categoryHom C binaryProductObject A
        binaryProductRight : categoryHom C binaryProductObject B
        binaryProductPair :
          {X : categoryObjects C} →
          categoryHom C X A →
          categoryHom C X B →
          categoryHom C X binaryProductObject
        binaryProductPair-respects :
          {X : categoryObjects C}
          {f f′ : categoryHom C X A}
          {g g′ : categoryHom C X B} →
          categoryHomEq C f f′ →
          categoryHomEq C g g′ →
          categoryHomEq C
            (binaryProductPair f g)
            (binaryProductPair f′ g′)
        binaryProductPair-left :
          {X : categoryObjects C}
          (f : categoryHom C X A)
          (g : categoryHom C X B) →
          categoryHomEq C
            (categoryCompose C binaryProductLeft (binaryProductPair f g))
            f
        binaryProductPair-right :
          {X : categoryObjects C}
          (f : categoryHom C X A)
          (g : categoryHom C X B) →
          categoryHomEq C
            (categoryCompose C binaryProductRight (binaryProductPair f g))
            g
        binaryProduct-eta :
          {X : categoryObjects C}
          (h : categoryHom C X binaryProductObject) →
          categoryHomEq C
            (binaryProductPair
              (categoryCompose C binaryProductLeft h)
              (categoryCompose C binaryProductRight h))
            h
    open BinaryProduct public

    record FiniteProducts (C : Category) : Set₂ where
      field
        finiteTerminal : TerminalObject C
        finiteBinaryProduct :
          (A B : categoryObjects C) → BinaryProduct C A B
    open FiniteProducts public

    -- ------------------------------------------------------------------
    -- Π preserves finite products when its canonical comparison maps
    -- (and the terminal comparison) are isomorphisms.
    -- ------------------------------------------------------------------

    record PreservesFiniteProducts
      {C D : Category}
      (F : Functor C D)
      (productsC : FiniteProducts C)
      (productsD : FiniteProducts D) : Set₂ where
      field
        terminalComparison :
          categoryHom D
            (functorObject F (terminalObject (finiteTerminal productsC)))
            (terminalObject (finiteTerminal productsD))
        terminalComparisonInverse :
          categoryHom D
            (terminalObject (finiteTerminal productsD))
            (functorObject F (terminalObject (finiteTerminal productsC)))
        terminalComparison-left-inverse :
          categoryHomEq D
            (categoryCompose D terminalComparisonInverse terminalComparison)
            (categoryId D)
        terminalComparison-right-inverse :
          categoryHomEq D
            (categoryCompose D terminalComparison terminalComparisonInverse)
            (categoryId D)

        productComparison :
          {A B : categoryObjects C} →
          categoryHom D
            (functorObject F
              (binaryProductObject (finiteBinaryProduct productsC A B)))
            (binaryProductObject (finiteBinaryProduct productsD
              (functorObject F A) (functorObject F B)))
        productComparisonInverse :
          {A B : categoryObjects C} →
          categoryHom D
            (binaryProductObject (finiteBinaryProduct productsD
              (functorObject F A) (functorObject F B)))
            (functorObject F
              (binaryProductObject (finiteBinaryProduct productsC A B)))
        productComparison-left :
          {A B : categoryObjects C} →
          categoryHomEq D
            (categoryCompose D
              (binaryProductLeft (finiteBinaryProduct productsD
                (functorObject F A) (functorObject F B)))
              (productComparison {A} {B}))
            (functorArrow F (binaryProductLeft (finiteBinaryProduct productsC A B)))
        productComparison-right :
          {A B : categoryObjects C} →
          categoryHomEq D
            (categoryCompose D
              (binaryProductRight (finiteBinaryProduct productsD
                (functorObject F A) (functorObject F B)))
              (productComparison {A} {B}))
            (functorArrow F (binaryProductRight (finiteBinaryProduct productsC A B)))
        productComparison-left-inverse :
          {A B : categoryObjects C} →
          categoryHomEq D
            (categoryCompose D
              (productComparisonInverse {A} {B})
              (productComparison {A} {B}))
            (categoryId D)
        productComparison-right-inverse :
          {A B : categoryObjects C} →
          categoryHomEq D
            (categoryCompose D
              (productComparison {A} {B})
              (productComparisonInverse {A} {B}))
            (categoryId D)
    open PreservesFiniteProducts public

    -- ------------------------------------------------------------------
    -- Abstract cohesive adjunction core. H is the cohesive category and G
    -- the category of discrete homotopy types. A full cohesive topos also
    -- needs topos structure on H and ∞-groupoid structure on G. Those
    -- structures remain outside this adjoint-quadruple interface.
    -- ------------------------------------------------------------------

    record CohesiveAdjointQuadruple
      (H G : Category)
      (productsH : FiniteProducts H)
      (productsG : FiniteProducts G) : Set₃ where
      field
        cohesivePi : Functor H G
        cohesiveDisc : Functor G H
        cohesiveGamma : Functor H G
        cohesiveCodisc : Functor G H
        pi-adjoint-disc :
          Adjunction cohesivePi cohesiveDisc
        disc-adjoint-gamma :
          Adjunction cohesiveDisc cohesiveGamma
        gamma-adjoint-codisc :
          Adjunction cohesiveGamma cohesiveCodisc
        disc-fully-faithful :
          FullyFaithful cohesiveDisc
        codisc-fully-faithful :
          FullyFaithful cohesiveCodisc
        pi-preserves-finite-products :
          PreservesFiniteProducts cohesivePi productsH productsG
    open CohesiveAdjointQuadruple public

    data FiniteHObject : Set₁ where
      cohH0 cohHmid cohH1 : FiniteHObject

    data FiniteGObject : Set₁ where
      cohG0 cohG1 : FiniteGObject

    data HArrow : FiniteHObject → FiniteHObject → Set where
      h00 : HArrow cohH0 cohH0
      h0m : HArrow cohH0 cohHmid
      h01 : HArrow cohH0 cohH1
      hmm : HArrow cohHmid cohHmid
      hm1 : HArrow cohHmid cohH1
      h11 : HArrow cohH1 cohH1

    data GArrow : FiniteGObject → FiniteGObject → Set where
      g00 : GArrow cohG0 cohG0
      g01 : GArrow cohG0 cohG1
      g11 : GArrow cohG1 cohG1

    hArrowRefl : (A : FiniteHObject) → HArrow A A
    hArrowRefl cohH0 = h00
    hArrowRefl cohHmid = hmm
    hArrowRefl cohH1 = h11

    gArrowRefl : (A : FiniteGObject) → GArrow A A
    gArrowRefl cohG0 = g00
    gArrowRefl cohG1 = g11

    hArrowCompose :
      {A B C : FiniteHObject} →
      HArrow B C → HArrow A B → HArrow A C
    hArrowCompose h00 q = q
    hArrowCompose h0m h00 = h0m
    hArrowCompose h01 h00 = h01
    hArrowCompose hmm q = q
    hArrowCompose hm1 h0m = h01
    hArrowCompose hm1 hmm = hm1
    hArrowCompose h11 q = q

    gArrowCompose :
      {A B C : FiniteGObject} →
      GArrow B C → GArrow A B → GArrow A C
    gArrowCompose g00 q = q
    gArrowCompose g01 g00 = g01
    gArrowCompose g11 q = q

    finiteHCategory : Category
    finiteHCategory = record
      { categoryObjects = FiniteHObject
      ; categoryHom = HArrow
      ; categoryHomEq = λ _ _ → ⊤
      ; categoryHomEq-refl = λ _ → tt
      ; categoryHomEq-sym = λ _ → tt
      ; categoryHomEq-trans = λ _ _ → tt
      ; categoryId = hArrowRefl _
      ; categoryCompose = hArrowCompose
      ; categoryCompose-respects = λ _ _ → tt
      ; categoryCompose-assoc = λ _ _ _ → tt
      ; categoryCompose-id-left = λ _ → tt
      ; categoryCompose-id-right = λ _ → tt
      }

    finiteGCategory : Category
    finiteGCategory = record
      { categoryObjects = FiniteGObject
      ; categoryHom = GArrow
      ; categoryHomEq = λ _ _ → ⊤
      ; categoryHomEq-refl = λ _ → tt
      ; categoryHomEq-sym = λ _ → tt
      ; categoryHomEq-trans = λ _ _ → tt
      ; categoryId = gArrowRefl _
      ; categoryCompose = gArrowCompose
      ; categoryCompose-respects = λ _ _ → tt
      ; categoryCompose-assoc = λ _ _ _ → tt
      ; categoryCompose-id-left = λ _ → tt
      ; categoryCompose-id-right = λ _ → tt
      }

    finitePiObject : FiniteHObject → FiniteGObject
    finitePiObject cohH0 = cohG0
    finitePiObject cohHmid = cohG1
    finitePiObject cohH1 = cohG1

    finiteDiscObject : FiniteGObject → FiniteHObject
    finiteDiscObject cohG0 = cohH0
    finiteDiscObject cohG1 = cohH1

    finiteGammaObject : FiniteHObject → FiniteGObject
    finiteGammaObject cohH0 = cohG0
    finiteGammaObject cohHmid = cohG0
    finiteGammaObject cohH1 = cohG1

    finiteCodiscObject : FiniteGObject → FiniteHObject
    finiteCodiscObject cohG0 = cohHmid
    finiteCodiscObject cohG1 = cohH1

    finitePiArrow :
      {A B : FiniteHObject} →
      HArrow A B →
      GArrow (finitePiObject A) (finitePiObject B)
    finitePiArrow h00 = g00
    finitePiArrow h0m = g01
    finitePiArrow h01 = g01
    finitePiArrow hmm = g11
    finitePiArrow hm1 = g11
    finitePiArrow h11 = g11

    finiteDiscArrow :
      {A B : FiniteGObject} →
      GArrow A B →
      HArrow (finiteDiscObject A) (finiteDiscObject B)
    finiteDiscArrow g00 = h00
    finiteDiscArrow g01 = h01
    finiteDiscArrow g11 = h11

    finiteGammaArrow :
      {A B : FiniteHObject} →
      HArrow A B →
      GArrow (finiteGammaObject A) (finiteGammaObject B)
    finiteGammaArrow h00 = g00
    finiteGammaArrow h0m = g00
    finiteGammaArrow h01 = g01
    finiteGammaArrow hmm = g00
    finiteGammaArrow hm1 = g01
    finiteGammaArrow h11 = g11

    finiteCodiscArrow :
      {A B : FiniteGObject} →
      GArrow A B →
      HArrow (finiteCodiscObject A) (finiteCodiscObject B)
    finiteCodiscArrow g00 = hmm
    finiteCodiscArrow g01 = hm1
    finiteCodiscArrow g11 = h11

    finitePiFunctor : Functor finiteHCategory finiteGCategory
    finitePiFunctor = record
      { functorObject = finitePiObject
      ; functorArrow = finitePiArrow
      ; functorArrow-respects = λ _ → tt
      ; functorIdentity = tt
      ; functorComposition = λ _ _ → tt
      }

    finiteDiscFunctor : Functor finiteGCategory finiteHCategory
    finiteDiscFunctor = record
      { functorObject = finiteDiscObject
      ; functorArrow = finiteDiscArrow
      ; functorArrow-respects = λ _ → tt
      ; functorIdentity = tt
      ; functorComposition = λ _ _ → tt
      }

    finiteGammaFunctor : Functor finiteHCategory finiteGCategory
    finiteGammaFunctor = record
      { functorObject = finiteGammaObject
      ; functorArrow = finiteGammaArrow
      ; functorArrow-respects = λ _ → tt
      ; functorIdentity = tt
      ; functorComposition = λ _ _ → tt
      }

    finiteCodiscFunctor : Functor finiteGCategory finiteHCategory
    finiteCodiscFunctor = record
      { functorObject = finiteCodiscObject
      ; functorArrow = finiteCodiscArrow
      ; functorArrow-respects = λ _ → tt
      ; functorIdentity = tt
      ; functorComposition = λ _ _ → tt
      }

    finitePiTranspose :
      {A : FiniteHObject} {B : FiniteGObject} →
      GArrow (finitePiObject A) B →
      HArrow A (finiteDiscObject B)
    finitePiTranspose {cohH0} {cohG0} g00 = h00
    finitePiTranspose {cohH0} {cohG1} g01 = h01
    finitePiTranspose {cohHmid} {cohG0} ()
    finitePiTranspose {cohHmid} {cohG1} g11 = hm1
    finitePiTranspose {cohH1} {cohG0} ()
    finitePiTranspose {cohH1} {cohG1} g11 = h11

    finitePiUntranspose :
      {A : FiniteHObject} {B : FiniteGObject} →
      HArrow A (finiteDiscObject B) →
      GArrow (finitePiObject A) B
    finitePiUntranspose {cohH0} {cohG0} h00 = g00
    finitePiUntranspose {cohH0} {cohG1} h01 = g01
    finitePiUntranspose {cohHmid} {cohG0} ()
    finitePiUntranspose {cohHmid} {cohG1} hm1 = g11
    finitePiUntranspose {cohH1} {cohG0} ()
    finitePiUntranspose {cohH1} {cohG1} h11 = g11

    finiteDiscTranspose :
      {A : FiniteGObject} {B : FiniteHObject} →
      HArrow (finiteDiscObject A) B →
      GArrow A (finiteGammaObject B)
    finiteDiscTranspose {cohG0} {cohH0} h00 = g00
    finiteDiscTranspose {cohG0} {cohHmid} h0m = g00
    finiteDiscTranspose {cohG0} {cohH1} h01 = g01
    finiteDiscTranspose {cohG1} {cohH0} ()
    finiteDiscTranspose {cohG1} {cohHmid} ()
    finiteDiscTranspose {cohG1} {cohH1} h11 = g11

    finiteDiscUntranspose :
      {A : FiniteGObject} {B : FiniteHObject} →
      GArrow A (finiteGammaObject B) →
      HArrow (finiteDiscObject A) B
    finiteDiscUntranspose {cohG0} {cohH0} g00 = h00
    finiteDiscUntranspose {cohG0} {cohHmid} g00 = h0m
    finiteDiscUntranspose {cohG0} {cohH1} g01 = h01
    finiteDiscUntranspose {cohG1} {cohH0} ()
    finiteDiscUntranspose {cohG1} {cohHmid} ()
    finiteDiscUntranspose {cohG1} {cohH1} g11 = h11

    finiteGammaTranspose :
      {A : FiniteHObject} {B : FiniteGObject} →
      GArrow (finiteGammaObject A) B →
      HArrow A (finiteCodiscObject B)
    finiteGammaTranspose {cohH0} {cohG0} g00 = h0m
    finiteGammaTranspose {cohH0} {cohG1} g01 = h01
    finiteGammaTranspose {cohHmid} {cohG0} g00 = hmm
    finiteGammaTranspose {cohHmid} {cohG1} g01 = hm1
    finiteGammaTranspose {cohH1} {cohG0} ()
    finiteGammaTranspose {cohH1} {cohG1} g11 = h11

    finiteGammaUntranspose :
      {A : FiniteHObject} {B : FiniteGObject} →
      HArrow A (finiteCodiscObject B) →
      GArrow (finiteGammaObject A) B
    finiteGammaUntranspose {cohH0} {cohG0} h0m = g00
    finiteGammaUntranspose {cohH0} {cohG1} h01 = g01
    finiteGammaUntranspose {cohHmid} {cohG0} hmm = g00
    finiteGammaUntranspose {cohHmid} {cohG1} hm1 = g01
    finiteGammaUntranspose {cohH1} {cohG0} ()
    finiteGammaUntranspose {cohH1} {cohG1} h11 = g11

    finitePiAdjunction :
      Adjunction finitePiFunctor finiteDiscFunctor
    finitePiAdjunction = record
      { transpose = finitePiTranspose
      ; untranspose = finitePiUntranspose
      ; transpose-respects = λ _ → tt
      ; untranspose-respects = λ _ → tt
      ; transpose-untranspose = λ _ → tt
      ; untranspose-transpose = λ _ → tt
      ; transpose-natural-source = λ _ _ → tt
      ; transpose-natural-target = λ _ _ → tt
      }

    finiteDiscAdjunction :
      Adjunction finiteDiscFunctor finiteGammaFunctor
    finiteDiscAdjunction = record
      { transpose = finiteDiscTranspose
      ; untranspose = finiteDiscUntranspose
      ; transpose-respects = λ _ → tt
      ; untranspose-respects = λ _ → tt
      ; transpose-untranspose = λ _ → tt
      ; untranspose-transpose = λ _ → tt
      ; transpose-natural-source = λ _ _ → tt
      ; transpose-natural-target = λ _ _ → tt
      }

    finiteGammaAdjunction :
      Adjunction finiteGammaFunctor finiteCodiscFunctor
    finiteGammaAdjunction = record
      { transpose = finiteGammaTranspose
      ; untranspose = finiteGammaUntranspose
      ; transpose-respects = λ _ → tt
      ; untranspose-respects = λ _ → tt
      ; transpose-untranspose = λ _ → tt
      ; untranspose-transpose = λ _ → tt
      ; transpose-natural-source = λ _ _ → tt
      ; transpose-natural-target = λ _ _ → tt
      }

    finiteDiscReflect :
      {A B : FiniteGObject} →
      HArrow (finiteDiscObject A) (finiteDiscObject B) →
      GArrow A B
    finiteDiscReflect {cohG0} {cohG0} h00 = g00
    finiteDiscReflect {cohG0} {cohG1} h01 = g01
    finiteDiscReflect {cohG1} {cohG0} ()
    finiteDiscReflect {cohG1} {cohG1} h11 = g11

    finiteDiscFullyFaithful :
      FullyFaithful finiteDiscFunctor
    finiteDiscFullyFaithful = record
      { reflectArrow = finiteDiscReflect
      ; reflectArrow-respects = λ _ → tt
      ; reflect-map = λ _ → tt
      ; map-reflect = λ _ → tt
      }

    finiteCodiscReflect :
      {A B : FiniteGObject} →
      HArrow (finiteCodiscObject A) (finiteCodiscObject B) →
      GArrow A B
    finiteCodiscReflect {cohG0} {cohG0} hmm = g00
    finiteCodiscReflect {cohG0} {cohG1} hm1 = g01
    finiteCodiscReflect {cohG1} {cohG0} ()
    finiteCodiscReflect {cohG1} {cohG1} h11 = g11

    finiteCodiscFullyFaithful :
      FullyFaithful finiteCodiscFunctor
    finiteCodiscFullyFaithful = record
      { reflectArrow = finiteCodiscReflect
      ; reflectArrow-respects = λ _ → tt
      ; reflect-map = λ _ → tt
      ; map-reflect = λ _ → tt
      }

    finiteHMeet : FiniteHObject → FiniteHObject → FiniteHObject
    finiteHMeet cohH0 right = cohH0
    finiteHMeet cohHmid cohH0 = cohH0
    finiteHMeet cohHmid cohHmid = cohHmid
    finiteHMeet cohHmid cohH1 = cohHmid
    finiteHMeet cohH1 cohH0 = cohH0
    finiteHMeet cohH1 cohHmid = cohHmid
    finiteHMeet cohH1 cohH1 = cohH1

    finiteGMeet : FiniteGObject → FiniteGObject → FiniteGObject
    finiteGMeet cohG0 right = cohG0
    finiteGMeet cohG1 cohG0 = cohG0
    finiteGMeet cohG1 cohG1 = cohG1

    finiteHMeetLeft :
      (A B : FiniteHObject) → HArrow (finiteHMeet A B) A
    finiteHMeetLeft cohH0 B = h00
    finiteHMeetLeft cohHmid cohH0 = h0m
    finiteHMeetLeft cohHmid cohHmid = hmm
    finiteHMeetLeft cohHmid cohH1 = hmm
    finiteHMeetLeft cohH1 cohH0 = h01
    finiteHMeetLeft cohH1 cohHmid = hm1
    finiteHMeetLeft cohH1 cohH1 = h11

    finiteHMeetRight :
      (A B : FiniteHObject) → HArrow (finiteHMeet A B) B
    finiteHMeetRight cohH0 cohH0 = h00
    finiteHMeetRight cohH0 cohHmid = h0m
    finiteHMeetRight cohH0 cohH1 = h01
    finiteHMeetRight cohHmid cohH0 = h00
    finiteHMeetRight cohHmid cohHmid = hmm
    finiteHMeetRight cohHmid cohH1 = hm1
    finiteHMeetRight cohH1 cohH0 = h00
    finiteHMeetRight cohH1 cohHmid = hmm
    finiteHMeetRight cohH1 cohH1 = h11

    finiteHMeetGreatest :
      {X A B : FiniteHObject} →
      HArrow X A → HArrow X B → HArrow X (finiteHMeet A B)
    finiteHMeetGreatest {A = cohH0} xa xb = xa
    finiteHMeetGreatest {A = cohHmid} {B = cohH0} xa xb = xb
    finiteHMeetGreatest {A = cohHmid} {B = cohHmid} xa xb = xa
    finiteHMeetGreatest {A = cohHmid} {B = cohH1} xa xb = xa
    finiteHMeetGreatest {A = cohH1} {B = cohH0} xa xb = xb
    finiteHMeetGreatest {A = cohH1} {B = cohHmid} xa xb = xb
    finiteHMeetGreatest {A = cohH1} {B = cohH1} xa xb = xa

    finiteGMeetLeft :
      (A B : FiniteGObject) → GArrow (finiteGMeet A B) A
    finiteGMeetLeft cohG0 B = g00
    finiteGMeetLeft cohG1 cohG0 = g01
    finiteGMeetLeft cohG1 cohG1 = g11

    finiteGMeetRight :
      (A B : FiniteGObject) → GArrow (finiteGMeet A B) B
    finiteGMeetRight cohG0 cohG0 = g00
    finiteGMeetRight cohG0 cohG1 = g01
    finiteGMeetRight cohG1 cohG0 = g00
    finiteGMeetRight cohG1 cohG1 = g11

    finiteGMeetGreatest :
      {X A B : FiniteGObject} →
      GArrow X A → GArrow X B → GArrow X (finiteGMeet A B)
    finiteGMeetGreatest {A = cohG0} xa xb = xa
    finiteGMeetGreatest {A = cohG1} {B = cohG0} xa xb = xb
    finiteGMeetGreatest {A = cohG1} {B = cohG1} xa xb = xa

    finiteHTerminal : TerminalObject finiteHCategory
    finiteHTerminal = record
      { terminalObject = cohH1
      ; terminalArrow = λ { {A = cohH0} → h01
                          ; {A = cohHmid} → hm1
                          ; {A = cohH1} → h11 }
      ; terminalArrow-unique = λ _ → tt
      }

    finiteGTerminal : TerminalObject finiteGCategory
    finiteGTerminal = record
      { terminalObject = cohG1
      ; terminalArrow = λ { {A = cohG0} → g01
                          ; {A = cohG1} → g11 }
      ; terminalArrow-unique = λ _ → tt
      }

    finiteHBinaryProduct :
      (A B : FiniteHObject) → BinaryProduct finiteHCategory A B
    finiteHBinaryProduct A B = record
      { binaryProductObject = finiteHMeet A B
      ; binaryProductLeft = finiteHMeetLeft A B
      ; binaryProductRight = finiteHMeetRight A B
      ; binaryProductPair = finiteHMeetGreatest
      ; binaryProductPair-respects = λ _ _ → tt
      ; binaryProductPair-left = λ _ _ → tt
      ; binaryProductPair-right = λ _ _ → tt
      ; binaryProduct-eta = λ _ → tt
      }

    finiteGBinaryProduct :
      (A B : FiniteGObject) → BinaryProduct finiteGCategory A B
    finiteGBinaryProduct A B = record
      { binaryProductObject = finiteGMeet A B
      ; binaryProductLeft = finiteGMeetLeft A B
      ; binaryProductRight = finiteGMeetRight A B
      ; binaryProductPair = finiteGMeetGreatest
      ; binaryProductPair-respects = λ _ _ → tt
      ; binaryProductPair-left = λ _ _ → tt
      ; binaryProductPair-right = λ _ _ → tt
      ; binaryProduct-eta = λ _ → tt
      }

    finiteHProducts : FiniteProducts finiteHCategory
    finiteHProducts = record
      { finiteTerminal = finiteHTerminal
      ; finiteBinaryProduct = finiteHBinaryProduct
      }

    finiteGProducts : FiniteProducts finiteGCategory
    finiteGProducts = record
      { finiteTerminal = finiteGTerminal
      ; finiteBinaryProduct = finiteGBinaryProduct
      }

    -- Universe-polymorphic transport for arrows between Set₁ objects.
    substFiniteObject :
      {A : Set₁} {x y : A} →
      (P : A → Set) → x ≡ y → P x → P y
    substFiniteObject P refl proof = proof

    finitePiPreservesMeet :
      (A B : FiniteHObject) →
      finitePiObject (finiteHMeet A B) ≡
      finiteGMeet (finitePiObject A) (finitePiObject B)
    finitePiPreservesMeet cohH0 B = refl
    finitePiPreservesMeet cohHmid cohH0 = refl
    finitePiPreservesMeet cohHmid cohHmid = refl
    finitePiPreservesMeet cohHmid cohH1 = refl
    finitePiPreservesMeet cohH1 cohH0 = refl
    finitePiPreservesMeet cohH1 cohHmid = refl
    finitePiPreservesMeet cohH1 cohH1 = refl

    finitePiPreservesFiniteProducts :
      PreservesFiniteProducts
        finitePiFunctor finiteHProducts finiteGProducts
    finitePiPreservesFiniteProducts = record
      { terminalComparison = g11
      ; terminalComparisonInverse = g11
      ; terminalComparison-left-inverse = tt
      ; terminalComparison-right-inverse = tt
      ; productComparison = λ {A} {B} →
          substFiniteObject
            (λ target →
              GArrow
                (finitePiObject (finiteHMeet A B))
                target)
            (finitePiPreservesMeet A B)
            (gArrowRefl (finitePiObject (finiteHMeet A B)))
      ; productComparisonInverse = λ {A} {B} →
          substFiniteObject
            (λ source →
              GArrow source
                (finitePiObject (finiteHMeet A B)))
            (finitePiPreservesMeet A B)
            (gArrowRefl (finitePiObject (finiteHMeet A B)))
      ; productComparison-left = tt
      ; productComparison-right = tt
      ; productComparison-left-inverse = tt
      ; productComparison-right-inverse = tt
      }

    finitePosetalCohesion :
      CohesiveAdjointQuadruple
        finiteHCategory finiteGCategory finiteHProducts finiteGProducts
    finitePosetalCohesion = record
      { cohesivePi = finitePiFunctor
      ; cohesiveDisc = finiteDiscFunctor
      ; cohesiveGamma = finiteGammaFunctor
      ; cohesiveCodisc = finiteCodiscFunctor
      ; pi-adjoint-disc = finitePiAdjunction
      ; disc-adjoint-gamma = finiteDiscAdjunction
      ; gamma-adjoint-codisc = finiteGammaAdjunction
      ; disc-fully-faithful = finiteDiscFullyFaithful
      ; codisc-fully-faithful = finiteCodiscFullyFaithful
      ; pi-preserves-finite-products = finitePiPreservesFiniteProducts
      }

    finiteGammaDisc-object :
      (A : FiniteGObject) →
      finiteGammaObject (finiteDiscObject A) ≡ A
    finiteGammaDisc-object cohG0 = refl
    finiteGammaDisc-object cohG1 = refl

    finitePiDisc-object :
      (A : FiniteGObject) →
      finitePiObject (finiteDiscObject A) ≡ A
    finitePiDisc-object cohG0 = refl
    finitePiDisc-object cohG1 = refl

    finiteGammaCodisc-object :
      (A : FiniteGObject) →
      finiteGammaObject (finiteCodiscObject A) ≡ A
    finiteGammaCodisc-object cohG0 = refl
    finiteGammaCodisc-object cohG1 = refl

    finiteDiscCodisc-distinct :
      finiteDiscObject cohG0 ≡ finiteCodiscObject cohG0 → ⊥
    finiteDiscCodisc-distinct ()

    finitePiGamma-distinct :
      finitePiObject cohHmid ≡ finiteGammaObject cohHmid → ⊥
    finitePiGamma-distinct ()



    -- ------------------------------------------------------------------
    -- Typed syntax over the finite nonidentity model.
    --
    -- H-objects and G-objects are different sorts. Disc/coDisc move G→H;
    -- Pi/Gamma move H→G. This prevents ill-typed modality compositions.
    -- ------------------------------------------------------------------

    cohesiveSym :
      {a : Level} {A : Set a} {x y : A} →
      x ≡ y → y ≡ x
    cohesiveSym refl = refl

    cohesiveTrans :
      {a : Level} {A : Set a} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    cohesiveTrans refl second = second

    cohesiveCong :
      {a b : Level} {A : Set a} {B : Set b} →
      (f : A → B) {x y : A} →
      x ≡ y → f x ≡ f y
    cohesiveCong f refl = refl

    mutual
      data CohesiveHExpr : Set₁ where
        hAtom : FiniteHObject → CohesiveHExpr
        discExpr : CohesiveGExpr → CohesiveHExpr
        codiscExpr : CohesiveGExpr → CohesiveHExpr

      data CohesiveGExpr : Set₁ where
        gAtom : FiniteGObject → CohesiveGExpr
        piExpr : CohesiveHExpr → CohesiveGExpr
        gammaExpr : CohesiveHExpr → CohesiveGExpr

    mutual
      denoteH : CohesiveHExpr → FiniteHObject
      denoteH (hAtom object) = object
      denoteH (discExpr expression) =
        finiteDiscObject (denoteG expression)
      denoteH (codiscExpr expression) =
        finiteCodiscObject (denoteG expression)

      denoteG : CohesiveGExpr → FiniteGObject
      denoteG (gAtom object) = object
      denoteG (piExpr expression) =
        finitePiObject (denoteH expression)
      denoteG (gammaExpr expression) =
        finiteGammaObject (denoteH expression)

    gammaDiscSemantics :
      (expression : CohesiveGExpr) →
      denoteG (gammaExpr (discExpr expression)) ≡ denoteG expression
    gammaDiscSemantics expression =
      finiteGammaDisc-object (denoteG expression)

    piDiscSemantics :
      (expression : CohesiveGExpr) →
      denoteG (piExpr (discExpr expression)) ≡ denoteG expression
    piDiscSemantics expression =
      finitePiDisc-object (denoteG expression)

    gammaCodiscSemantics :
      (expression : CohesiveGExpr) →
      denoteG (gammaExpr (codiscExpr expression)) ≡ denoteG expression
    gammaCodiscSemantics expression =
      finiteGammaCodisc-object (denoteG expression)

    -- ------------------------------------------------------------------
    -- Structural normal forms. The three composite modality laws reduce
    -- in G; H syntax retains the two embedding modalities.
    -- ------------------------------------------------------------------

    mutual
      normalizeH : CohesiveHExpr → CohesiveHExpr
      normalizeH (hAtom object) = hAtom object
      normalizeH (discExpr expression) =
        discExpr (normalizeG expression)
      normalizeH (codiscExpr expression) =
        codiscExpr (normalizeG expression)

      normalizeG : CohesiveGExpr → CohesiveGExpr
      normalizeG (gAtom object) = gAtom object
      normalizeG (piExpr (discExpr expression)) =
        normalizeG expression
      normalizeG (piExpr expression) =
        piExpr (normalizeH expression)
      normalizeG (gammaExpr (discExpr expression)) =
        normalizeG expression
      normalizeG (gammaExpr (codiscExpr expression)) =
        normalizeG expression
      normalizeG (gammaExpr expression) =
        gammaExpr (normalizeH expression)

    mutual
      normalizeH-sound :
        (expression : CohesiveHExpr) →
        denoteH (normalizeH expression) ≡ denoteH expression
      normalizeH-sound (hAtom object) = refl
      normalizeH-sound (discExpr expression) =
        cohesiveCong finiteDiscObject (normalizeG-sound expression)
      normalizeH-sound (codiscExpr expression) =
        cohesiveCong finiteCodiscObject (normalizeG-sound expression)

      normalizeG-sound :
        (expression : CohesiveGExpr) →
        denoteG (normalizeG expression) ≡ denoteG expression
      normalizeG-sound (gAtom object) = refl
      normalizeG-sound (piExpr (discExpr expression)) =
        cohesiveTrans
          (normalizeG-sound expression)
          (cohesiveSym (piDiscSemantics expression))
      normalizeG-sound (piExpr (hAtom object)) = refl
      normalizeG-sound (piExpr (codiscExpr expression)) =
        cohesiveCong finitePiObject
          (normalizeH-sound (codiscExpr expression))
      normalizeG-sound (gammaExpr (discExpr expression)) =
        cohesiveTrans
          (normalizeG-sound expression)
          (cohesiveSym (gammaDiscSemantics expression))
      normalizeG-sound (gammaExpr (codiscExpr expression)) =
        cohesiveTrans
          (normalizeG-sound expression)
          (cohesiveSym (gammaCodiscSemantics expression))
      normalizeG-sound (gammaExpr (hAtom object)) =
        cohesiveCong finiteGammaObject (normalizeH-sound (hAtom object))

    mutual
      normalizeH-idempotent :
        (expression : CohesiveHExpr) →
        normalizeH (normalizeH expression) ≡ normalizeH expression
      normalizeH-idempotent (hAtom object) = refl
      normalizeH-idempotent (discExpr expression) =
        cohesiveCong discExpr (normalizeG-idempotent expression)
      normalizeH-idempotent (codiscExpr expression) =
        cohesiveCong codiscExpr (normalizeG-idempotent expression)

      normalizeG-idempotent :
        (expression : CohesiveGExpr) →
        normalizeG (normalizeG expression) ≡ normalizeG expression
      normalizeG-idempotent (gAtom object) = refl
      normalizeG-idempotent (piExpr (hAtom object)) = refl
      normalizeG-idempotent (piExpr (discExpr expression)) =
        normalizeG-idempotent expression
      normalizeG-idempotent (piExpr (codiscExpr expression)) =
        cohesiveCong piExpr
          (cohesiveCong codiscExpr (normalizeG-idempotent expression))
      normalizeG-idempotent (gammaExpr (hAtom object)) = refl
      normalizeG-idempotent (gammaExpr (discExpr expression)) =
        normalizeG-idempotent expression
      normalizeG-idempotent (gammaExpr (codiscExpr expression)) =
        normalizeG-idempotent expression

    finitePosetalCohesion-nonidentity :
      finiteDiscObject cohG0 ≡ finiteCodiscObject cohG0 → ⊥
    finitePosetalCohesion-nonidentity = finiteDiscCodisc-distinct

    finitePosetalCohesion-Pi-Gamma-distinct :
      finitePiObject cohHmid ≡ finiteGammaObject cohHmid → ⊥
    finitePosetalCohesion-Pi-Gamma-distinct = finitePiGamma-distinct

  -- --------------------------------------------------------------------
  -- 6. Quotients induced by idempotent endomaps.
  --
  -- This is an Agda, proof-relevant encoding of the Cedille-style
  -- idempotent-function construction. Nuo Li's normalizer laws are
  -- recorded separately and shown equivalent to the induced kernel
  -- relation. A non-setoid idempotent reflection monad is built below.
  -- --------------------------------------------------------------------

  module QuotientReflection where

    record IdempotentEndomap (A : Set) : Set where
      constructor idempotentEndomap
      field
        canonicalize : A → A
        canonicalize-idempotent :
          (x : A) → canonicalize (canonicalize x) ≡ canonicalize x
    open IdempotentEndomap public

    -- The quotient carrier is the fixed-point subtype of the normalizer.
    -- Sigma keeps the fixed-point witness proof-relevant in Agda.
    Quotient : (A : Set) → IdempotentEndomap A → Set
    Quotient A f = Σ A (λ x → canonicalize f x ≡ x)

    qcanon :
      {A : Set} → (f : IdempotentEndomap A) → A → Quotient A f
    qcanon f x = canonicalize f x , canonicalize-idempotent f x

    qcoerce : {A : Set} {f : IdempotentEndomap A} → Quotient A f → A
    qcoerce (x , fixed) = x

    qcoerce-qcanon :
      {A : Set} (f : IdempotentEndomap A) (x : A) →
      qcoerce {A} {f} (qcanon {A} f x) ≡ canonicalize f x
    qcoerce-qcanon f x = refl

    qcoerce-fixed :
      {A : Set} {f : IdempotentEndomap A} →
      (q : Quotient A f) →
      canonicalize f (qcoerce {A} {f} q) ≡ qcoerce {A} {f} q
    qcoerce-fixed {A} {f} (x , fixed) = fixed

    QuotientRelation :
      {A : Set} → IdempotentEndomap A → A → A → Set
    QuotientRelation f x y = canonicalize f x ≡ canonicalize f y

    -- Nuo Li's definable-quotient contract: related inputs have equal
    -- normal forms, and each input is related to its normal form.
    record NormalizerFor (A : Set) (R : A → A → Set) : Set where
      constructor normalizerFor
      field
        normalizer-refl : (x : A) → R x x
        normalizer-sym : {x y : A} → R x y → R y x
        normalizer-trans : {x y z : A} → R x y → R y z → R x z
        normalizeFor : A → A
        normalization-sound :
          {x y : A} → R x y → normalizeFor x ≡ normalizeFor y
        normalization-complete :
          (x : A) → R (normalizeFor x) x
    open NormalizerFor public

    normalization-idempotent :
      {A : Set} {R : A → A → Set} →
      (N : NormalizerFor A R) →
      (x : A) → normalizeFor N (normalizeFor N x) ≡ normalizeFor N x
    normalization-idempotent N x =
      normalization-sound N (normalization-complete N x)

    normalization-kernel-backward :
      {A : Set} {R : A → A → Set} →
      (N : NormalizerFor A R) → {x y : A} →
      normalizeFor N x ≡ normalizeFor N y → R x y
    normalization-kernel-backward {R = R} N {x} {y} equality =
      normalizer-trans N
        (normalizer-sym N (normalization-complete N x))
        (normalizer-trans N
          (subst (λ z → R (normalizeFor N x) z) equality
            (normalizer-refl N (normalizeFor N x)))
          (normalization-complete N y))

    normalization-kernel-equivalence :
      {A : Set} {R : A → A → Set} →
      (N : NormalizerFor A R) → (x y : A) →
      Equivalence (R x y)
        (normalizeFor N x ≡ normalizeFor N y)
    normalization-kernel-equivalence N x y =
      record
        { toForward = normalization-sound N
        ; toBackward = normalization-kernel-backward N
        }

    -- Nuo Li normalizers induce idempotent endomaps.
    normalizer-as-idempotent :
      {A : Set} {R : A → A → Set} →
      (N : NormalizerFor A R) → IdempotentEndomap A
    normalizer-as-idempotent N =
      idempotentEndomap
        (normalizeFor N)
        (normalization-idempotent N)

    -- Conversely, each idempotent map supplies a normalizer for its
    -- kernel relation. No second quotient carrier is introduced.
    kernelNormalizer :
      {A : Set} (f : IdempotentEndomap A) →
      NormalizerFor A (QuotientRelation f)
    kernelNormalizer f =
      normalizerFor
        (λ x → refl)
        (λ equality → sym equality)
        (λ first second → trans first second)
        (canonicalize f)
        (λ related → related)
        (canonicalize-idempotent f)

    -- ----------------------------------------------------------------
    -- A non-setoid categorical reflection on idempotent endomaps.
    --
    -- Objects are types equipped with an idempotent normalizer. No
    -- equivalence relation is stored on the carrier, and quotient values
    -- are ordinary Agda types: the fixed points of the normalizer.
    --
    -- Morphisms commute with the chosen normalizers. Equality of
    -- morphisms is pointwise equality; this avoids assuming function
    -- extensionality for the category laws.
    -- ----------------------------------------------------------------

    -- The project is compiled with --with-K. This proof uses K to identify
    -- equality witnesses when constructing paths in the fixed-point Sigma.
    -- It does not use --prop, proof erasure, or an erasure axiom.
    identityProofUnique :
      {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
    identityProofUnique refl refl = refl

    fixedPointPath :
      {A : Set} (f : IdempotentEndomap A) {x y : A} →
      (p : x ≡ y) →
      (px : canonicalize f x ≡ x) →
      (py : canonicalize f y ≡ y) →
      (x , px) ≡ (y , py)
    fixedPointPath f {x = x} refl px py =
      cong (λ proof → x , proof) (identityProofUnique px py)

    quotientEquality :
      {A : Set} (f : IdempotentEndomap A) {x y : A} →
      Equivalence
        (qcanon f x ≡ qcanon f y)
        (canonicalize f x ≡ canonicalize f y)
    quotientEquality {A} f {x} {y} =
      record
        { toForward = λ equality →
            cong (λ q → qcoerce {A = A} {f = f} q) equality
        ; toBackward = λ equality →
            fixedPointPath f equality
              (canonicalize-idempotent f x)
              (canonicalize-idempotent f y)
        }

    qcanon-canonicalize :
      {A : Set} (f : IdempotentEndomap A) (x : A) →
      qcanon f (canonicalize f x) ≡ qcanon f x
    qcanon-canonicalize f x =
      fixedPointPath f
        (canonicalize-idempotent f x)
        (canonicalize-idempotent f (canonicalize f x))
        (canonicalize-idempotent f x)

    identityEndomap : {A : Set} → IdempotentEndomap A
    identityEndomap =
      idempotentEndomap (λ x → x) (λ x → refl)

    record IdempotentObject : Set₁ where
      constructor idempotentObject
      field
        objectCarrier : Set
        objectNormalizer : IdempotentEndomap objectCarrier
    open IdempotentObject public

    record IdempotentMorphism
      (X Y : IdempotentObject) : Set where
      constructor idempotentMorphism
      field
        endomapMap : objectCarrier X → objectCarrier Y
        endomapMap-commutes :
          (x : objectCarrier X) →
          endomapMap (canonicalize (objectNormalizer X) x) ≡
          canonicalize (objectNormalizer Y) (endomapMap x)
    open IdempotentMorphism public

    IdempotentMorphismEq :
      {X Y : IdempotentObject} →
      IdempotentMorphism X Y → IdempotentMorphism X Y → Set
    IdempotentMorphismEq {X} f g =
      (x : objectCarrier X) → endomapMap f x ≡ endomapMap g x

    idempotentMorphismEq-refl :
      {X Y : IdempotentObject} (f : IdempotentMorphism X Y) →
      IdempotentMorphismEq f f
    idempotentMorphismEq-refl f x = refl

    idempotentMorphismEq-sym :
      {X Y : IdempotentObject} {f g : IdempotentMorphism X Y} →
      IdempotentMorphismEq f g → IdempotentMorphismEq g f
    idempotentMorphismEq-sym equality x = sym (equality x)

    idempotentMorphismEq-trans :
      {X Y : IdempotentObject} {f g h : IdempotentMorphism X Y} →
      IdempotentMorphismEq f g →
      IdempotentMorphismEq g h →
      IdempotentMorphismEq f h
    idempotentMorphismEq-trans first second x =
      trans (first x) (second x)

    idempotentIdentity :
      (X : IdempotentObject) → IdempotentMorphism X X
    idempotentIdentity X =
      idempotentMorphism (λ x → x) (λ x → refl)

    idempotentCompose :
      {X Y Z : IdempotentObject} →
      IdempotentMorphism Y Z →
      IdempotentMorphism X Y →
      IdempotentMorphism X Z
    idempotentCompose g f =
      idempotentMorphism
        (λ x → endomapMap g (endomapMap f x))
        (λ x →
          trans
            (cong (endomapMap g) (endomapMap-commutes f x))
            (endomapMap-commutes g (endomapMap f x)))

    idempotentCompose-respects-equality :
      {X Y Z : IdempotentObject} →
      {f f′ : IdempotentMorphism X Y} →
      {g g′ : IdempotentMorphism Y Z} →
      IdempotentMorphismEq g g′ →
      IdempotentMorphismEq f f′ →
      IdempotentMorphismEq
        (idempotentCompose g f)
        (idempotentCompose g′ f′)
    idempotentCompose-respects-equality
      {f = f} {f′ = f′} {g = g} {g′ = g′} outer inner x =
      trans
        (cong (endomapMap g) (inner x))
        (outer (endomapMap f′ x))

    idempotentCategory-id-left :
      {X Y : IdempotentObject} →
      (f : IdempotentMorphism X Y) →
      IdempotentMorphismEq (idempotentCompose (idempotentIdentity Y) f) f
    idempotentCategory-id-left f x = refl

    idempotentCategory-id-right :
      {X Y : IdempotentObject} →
      (f : IdempotentMorphism X Y) →
      IdempotentMorphismEq (idempotentCompose f (idempotentIdentity X)) f
    idempotentCategory-id-right f x = refl

    idempotentCategory-associative :
      {W X Y Z : IdempotentObject} →
      (h : IdempotentMorphism Y Z) →
      (g : IdempotentMorphism X Y) →
      (f : IdempotentMorphism W X) →
      IdempotentMorphismEq
        (idempotentCompose h (idempotentCompose g f))
        (idempotentCompose (idempotentCompose h g) f)
    idempotentCategory-associative h g f x = refl

    record IdempotentCategory : Set₂ where
      field
        Obj : Set₁
        Hom : Obj → Obj → Set
        HomEq : {X Y : Obj} → Hom X Y → Hom X Y → Set
        catId : (X : Obj) → Hom X X
        catCompose :
          {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
        homEq-refl :
          {X Y : Obj} (f : Hom X Y) → HomEq f f
        homEq-sym :
          {X Y : Obj} {f g : Hom X Y} →
          HomEq f g → HomEq g f
        homEq-trans :
          {X Y : Obj} {f g h : Hom X Y} →
          HomEq f g → HomEq g h → HomEq f h
        compose-respects :
          {X Y Z : Obj} {f f′ : Hom X Y} {g g′ : Hom Y Z} →
          HomEq g g′ → HomEq f f′ →
          HomEq (catCompose g f) (catCompose g′ f′)
        identity-left :
          {X Y : Obj} (f : Hom X Y) →
          HomEq (catCompose (catId Y) f) f
        identity-right :
          {X Y : Obj} (f : Hom X Y) →
          HomEq (catCompose f (catId X)) f
        compose-associative :
          {W X Y Z : Obj} →
          (h : Hom Y Z) → (g : Hom X Y) → (f : Hom W X) →
          HomEq (catCompose h (catCompose g f))
            (catCompose (catCompose h g) f)

    idempotentObjectCategory : IdempotentCategory
    idempotentObjectCategory =
      record
        { Obj = IdempotentObject
        ; Hom = IdempotentMorphism
        ; HomEq = IdempotentMorphismEq
        ; catId = idempotentIdentity
        ; catCompose = idempotentCompose
        ; homEq-refl = idempotentMorphismEq-refl
        ; homEq-sym =
            λ {X} {Y} {f} {g} equality →
              idempotentMorphismEq-sym
                {X = X} {Y = Y} {f = f} {g = g} equality
        ; homEq-trans =
            λ {X} {Y} {f} {g} {h} first second →
              idempotentMorphismEq-trans
                {X = X} {Y = Y} {f = f} {g = g} {h = h}
                first second
        ; compose-respects =
            λ {X} {Y} {Z} {f} {f′} {g} {g′} outer inner →
              idempotentCompose-respects-equality
                {X = X} {Y = Y} {Z = Z}
                {f = f} {f′ = f′} {g = g} {g′ = g′}
                outer inner
        ; identity-left = idempotentCategory-id-left
        ; identity-right = idempotentCategory-id-right
        ; compose-associative = idempotentCategory-associative
        }

    record IdempotentMonad (C : IdempotentCategory) : Set₂ where
      open IdempotentCategory C
      field
        T₀ : Obj → Obj
        T₁ :
          {X Y : Obj} → Hom X Y → Hom (T₀ X) (T₀ Y)
        η : (X : Obj) → Hom X (T₀ X)
        μ : (X : Obj) → Hom (T₀ (T₀ X)) (T₀ X)
        T-identity :
          (X : Obj) → HomEq (T₁ (catId X)) (catId (T₀ X))
        T-composition :
          {X Y Z : Obj} (g : Hom Y Z) (f : Hom X Y) →
          HomEq (T₁ (catCompose g f))
            (catCompose (T₁ g) (T₁ f))
        η-natural :
          {X Y : Obj} (f : Hom X Y) →
          HomEq (catCompose (T₁ f) (η X))
            (catCompose (η Y) f)
        μ-natural :
          {X Y : Obj} (f : Hom X Y) →
          HomEq (catCompose (μ Y) (T₁ (T₁ f)))
            (catCompose (T₁ f) (μ X))
        monad-left-unit :
          (X : Obj) →
          HomEq (catCompose (μ X) (T₁ (η X))) (catId (T₀ X))
        monad-right-unit :
          (X : Obj) →
          HomEq (catCompose (μ X) (η (T₀ X))) (catId (T₀ X))
        monad-associative :
          (X : Obj) →
          HomEq (catCompose (μ X) (T₁ (μ X)))
            (catCompose (μ X) (μ (T₀ X)))
        μ-inverse-left :
          (X : Obj) →
          HomEq (catCompose (η (T₀ X)) (μ X))
            (catId (T₀ (T₀ X)))
        μ-inverse-right :
          (X : Obj) →
          HomEq (catCompose (μ X) (η (T₀ X)))
            (catId (T₀ X))
    open IdempotentMonad public

    -- Reflect into the full subcategory of fixed-point objects.
    -- The reflected carrier is the genuine fixed-point type, rather than
    -- the original carrier paired with an external equivalence relation.
    reflectObject : IdempotentObject → IdempotentObject
    reflectObject X =
      idempotentObject
        (Quotient (objectCarrier X) (objectNormalizer X))
        identityEndomap

    reflectMap :
      {X Y : IdempotentObject} →
      IdempotentMorphism X Y →
      IdempotentMorphism (reflectObject X) (reflectObject Y)
    reflectMap {X} {Y} h =
      idempotentMorphism
        (λ { (x , fixed) →
          endomapMap h x ,
          trans
            (sym (endomapMap-commutes h x))
            (cong (endomapMap h) fixed) })
        (λ q → refl)

    reflectUnit :
      (X : IdempotentObject) →
      IdempotentMorphism X (reflectObject X)
    reflectUnit X =
      idempotentMorphism
        (qcanon (objectNormalizer X))
        (qcanon-canonicalize (objectNormalizer X))

    -- Local objects are precisely those whose chosen normalizer is
    -- pointwise the identity. These are the objects in the reflective
    -- subcategory selected by the quotient construction.
    FixedNormalizer : IdempotentObject → Set
    FixedNormalizer X =
      (x : objectCarrier X) →
      canonicalize (objectNormalizer X) x ≡ x

    reflectedObject-is-fixed :
      (X : IdempotentObject) →
      FixedNormalizer (reflectObject X)
    reflectedObject-is-fixed X q = refl

    -- The universal factorization into any fixed-normalizer object.
    -- A morphism h commutes with normalizers, so its value on a fixed
    -- representative is fixed in Y. The factor map evaluates h on the
    -- representative and forgets only the equality witness.
    reflectFactor :
      {X Y : IdempotentObject} →
      FixedNormalizer Y →
      IdempotentMorphism X Y →
      IdempotentMorphism (reflectObject X) Y
    reflectFactor {X} {Y} fixedY h =
      idempotentMorphism
        (λ q → endomapMap h (qcoerce
          {A = objectCarrier X}
          {f = objectNormalizer X} q))
        (λ q → sym (fixedY
          (endomapMap h (qcoerce
            {A = objectCarrier X}
            {f = objectNormalizer X} q))))

    reflectFactor-factorizes :
      {X Y : IdempotentObject} →
      (fixedY : FixedNormalizer Y) →
      (h : IdempotentMorphism X Y) →
      IdempotentMorphismEq
        (idempotentCompose (reflectFactor fixedY h) (reflectUnit X))
        h
    reflectFactor-factorizes {X} fixedY h x =
      trans
        (endomapMap-commutes h x)
        (fixedY (endomapMap h x))

    reflectFactor-unique :
      {X Y : IdempotentObject} →
      (fixedY : FixedNormalizer Y) →
      (h : IdempotentMorphism X Y) →
      (g : IdempotentMorphism (reflectObject X) Y) →
      IdempotentMorphismEq
        (idempotentCompose g (reflectUnit X))
        h →
      IdempotentMorphismEq g (reflectFactor fixedY h)
    reflectFactor-unique {X} fixedY h g factors (x , fixed) =
      trans
        (sym
          (cong (endomapMap g)
            (fixedPointPath (objectNormalizer X) fixed
              (canonicalize-idempotent (objectNormalizer X) x)
              fixed)))
        (factors x)

    -- Double reflection is the fixed-point type of the identity normalizer.
    -- Its multiplication forgets the redundant outer fixed-point witness.
    reflectMultiplication :
      (X : IdempotentObject) →
      IdempotentMorphism
        (reflectObject (reflectObject X))
        (reflectObject X)
    reflectMultiplication X =
      idempotentMorphism
        (λ q →
          qcoerce
            {A = Quotient (objectCarrier X) (objectNormalizer X)}
            {f = identityEndomap} q)
        (λ q → refl)

    reflectFunctorIdentity :
      (X : IdempotentObject) →
      IdempotentMorphismEq
        (reflectMap (idempotentIdentity X))
        (idempotentIdentity (reflectObject X))
    reflectFunctorIdentity X (x , fixed) =
      fixedPointPath (objectNormalizer X) refl
        (cong (λ z → z) fixed)
        fixed

    reflectFunctorComposition :
      {X Y Z : IdempotentObject} →
      (g : IdempotentMorphism Y Z) →
      (f : IdempotentMorphism X Y) →
      IdempotentMorphismEq
        (reflectMap (idempotentCompose g f))
        (idempotentCompose (reflectMap g) (reflectMap f))
    reflectFunctorComposition {Z = Z} g f (x , fixed) =
      fixedPointPath (objectNormalizer Z) refl
        (trans
          (sym (endomapMap-commutes (idempotentCompose g f) x))
          (cong
            (λ z → endomapMap g (endomapMap f z))
            fixed))
        (trans
          (sym (endomapMap-commutes g (endomapMap f x)))
          (cong (endomapMap g)
            (trans
              (sym (endomapMap-commutes f x))
              (cong (endomapMap f) fixed))))

    reflectUnitNatural :
      {X Y : IdempotentObject} →
      (f : IdempotentMorphism X Y) →
      IdempotentMorphismEq
        (idempotentCompose (reflectMap f) (reflectUnit X))
        (idempotentCompose (reflectUnit Y) f)
    reflectUnitNatural {X} {Y} f x =
      fixedPointPath (objectNormalizer Y)
        (endomapMap-commutes f x)
        (trans
          (sym
            (endomapMap-commutes f
              (canonicalize (objectNormalizer X) x)))
          (cong (endomapMap f)
            (canonicalize-idempotent (objectNormalizer X) x)))
        (canonicalize-idempotent
          (objectNormalizer Y) (endomapMap f x))

    reflectMultiplicationNatural :
      {X Y : IdempotentObject} →
      (f : IdempotentMorphism X Y) →
      IdempotentMorphismEq
        (idempotentCompose
          (reflectMultiplication Y)
          (reflectMap (reflectMap f)))
        (idempotentCompose
          (reflectMap f)
          (reflectMultiplication X))
    reflectMultiplicationNatural f q = refl

    reflectMonad-left-unit :
      (X : IdempotentObject) →
      IdempotentMorphismEq
        (idempotentCompose
          (reflectMultiplication X)
          (reflectMap (reflectUnit X)))
        (idempotentIdentity (reflectObject X))
    reflectMonad-left-unit X (x , fixed) =
      fixedPointPath (objectNormalizer X) fixed
        (canonicalize-idempotent (objectNormalizer X) x)
        fixed

    reflectMonad-right-unit :
      (X : IdempotentObject) →
      IdempotentMorphismEq
        (idempotentCompose
          (reflectMultiplication X)
          (reflectUnit (reflectObject X)))
        (idempotentIdentity (reflectObject X))
    reflectMonad-right-unit X q = refl

    reflectMonad-associative :
      (X : IdempotentObject) →
      IdempotentMorphismEq
        (idempotentCompose
          (reflectMultiplication X)
          (reflectMap (reflectMultiplication X)))
        (idempotentCompose
          (reflectMultiplication X)
          (reflectMultiplication (reflectObject X)))
    reflectMonad-associative X q = refl

    reflectMultiplication-inverse-left :
      (X : IdempotentObject) →
      IdempotentMorphismEq
        (idempotentCompose
          (reflectUnit (reflectObject X))
          (reflectMultiplication X))
        (idempotentIdentity
          (reflectObject (reflectObject X)))
    reflectMultiplication-inverse-left X (q , fixed) =
      sym (fixedPointPath identityEndomap refl fixed refl)

    reflectMultiplication-inverse-right :
      (X : IdempotentObject) →
      IdempotentMorphismEq
        (idempotentCompose
          (reflectMultiplication X)
          (reflectUnit (reflectObject X)))
        (idempotentIdentity (reflectObject X))
    reflectMultiplication-inverse-right X q = refl

    -- This monad is induced by the fixed-point reflection. Its unit sends
    -- each input to its canonical representative; its multiplication is an
    -- isomorphism, witnessed by the two inverse laws above.
    quotientReflectionMonad : IdempotentMonad idempotentObjectCategory
    quotientReflectionMonad =
      record
        { T₀ = reflectObject
        ; T₁ = reflectMap
        ; η = reflectUnit
        ; μ = reflectMultiplication
        ; T-identity = reflectFunctorIdentity
        ; T-composition = reflectFunctorComposition
        ; η-natural = reflectUnitNatural
        ; μ-natural = reflectMultiplicationNatural
        ; monad-left-unit = reflectMonad-left-unit
        ; monad-right-unit = reflectMonad-right-unit
        ; monad-associative = reflectMonad-associative
        ; μ-inverse-left = reflectMultiplication-inverse-left
        ; μ-inverse-right = reflectMultiplication-inverse-right
        }

    data QuotientExpr (A : Set) : Set where
      rawₑ canonicalizedₑ : A → QuotientExpr A

    normalizeQuotient : {A : Set} → QuotientExpr A → QuotientExpr A
    normalizeQuotient (rawₑ x) = canonicalizedₑ x
    normalizeQuotient (canonicalizedₑ x) = canonicalizedₑ x

    quotient-raw :
      {A : Set} (x : A) →
      normalizeQuotient (rawₑ x) ≡
      normalizeQuotient (canonicalizedₑ x)
    quotient-raw x = refl

    -- Keep the denotation opaque outside this module. Otherwise unfolding
    -- the rewrite head would expose the bare canonicalizer and turn the
    -- raw-to-normal rule into an expanding self-rewrite.
    abstract
      denoteQuotient :
        {A : Set} {f : IdempotentEndomap A} →
        QuotientExpr A → A
      denoteQuotient {f = f} (rawₑ x) = canonicalize f x
      denoteQuotient {f = f} (canonicalizedₑ x) =
        canonicalize f (canonicalize f x)

      -- The sole semantic quotient rewrite: raw representative to normal form.
      quotient-raw-sound :
        {A : Set} (f : IdempotentEndomap A) (x : A) →
        denoteQuotient {A} {f} (rawₑ x) ≡
        denoteQuotient {A} {f} (canonicalizedₑ x)
      quotient-raw-sound f x =
        sym (canonicalize-idempotent f x)

  -- --------------------------------------------------------------------
  -- 7. LAURENT'S MULTIPLICATIVE-ADDITIVE POLARIZED LINEAR LOGIC (MALLP)
  --
  -- This is Laurent's polarized linear fragment WITHOUT exponentials.
  -- Positive and negative formulas are separated by polarity; down/up
  -- are polarity shifts, not Seely modalities and not an adjoint pair
  -- asserted to be inverse. Contexts contain only negative formulas and
  -- a stoup contains at most one positive formula.
  --
  -- No weakening or contraction constructors occur here. Tensor splits
  -- resources between premises; with has the usual additive shared-context
  -- rule (one branch is selected by additive observation), not contraction.
  -- Cut is included as a derivation rule. A positive cut-elimination
  -- oracle is supplied below: it preserves the sequent and returns an
  -- idempotent cut-free normal form. This is assumed, not derived by
  -- Gentzen reductions, and its denotational preservation remains open.
  --
  -- Categorical semantics is not inferred from a Seely comonad. The
  -- Hamano–Scott model requires reflective/coreflective full subcategories
  -- inside a *-autonomous category with products. The finite cohesive
  -- preorder above does not supply that category or connect its modalities
  -- to MALLP. This module specifies formulas, duality, and proof rules.
  -- Rule reference: Laurent, "Polarized games", section 3.1 (MALLP).
  -- --------------------------------------------------------------------

  module LaurentPolarizedMALLP where

    data Polarity : Set where
      posPolarity negPolarity : Polarity

    infixr 7 _⊗⁺_ _⅋⁻_
    infixr 6 _⊕⁺_ _&⁻_

    -- Laurent's MALLP grammar:
    -- P ::= X⊥ | 1 | 0 | P ⊗ P | P ⊕ P | ↓N
    -- N ::= X | ⊥ | ⊤ | N ⅋ N | N & N | ↑P
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
    -- witnessed explicitly, without quotient equality or setoids. The
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

      -- Polarity shifts. Down moves a negative formula into the positive
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

    cutCount : {Γ : Context} {S : Stoup} → MALLP Γ S → Nat
    cutCount mallp-ax = zero
    cutCount (mallp-cut p q) = suc (cutCount p + cutCount q)
    cutCount (mallp-exchange permutation p) = cutCount p
    cutCount (mallp-tensor p q) = cutCount p + cutCount q
    cutCount mallp-one = zero
    cutCount (mallp-plus-left p) = cutCount p
    cutCount (mallp-plus-right p) = cutCount p
    cutCount (mallp-par p) = cutCount p
    cutCount (mallp-with p q) = cutCount p + cutCount q
    cutCount (mallp-bottom p) = cutCount p
    cutCount mallp-top = zero
    cutCount (mallp-down p) = cutCount p
    cutCount (mallp-up p) = cutCount p

    -- This classifies an individual derivation by whether its tree
    -- contains a cut node. It is not a cut-elimination result.
    data CutClass : Set where
      cutFree cutContaining : CutClass

    classifyMALLP : {Γ : Context} {S : Stoup} →
      MALLP Γ S → CutClass
    classifyMALLP proof with hasCut proof
    ... | false = cutFree
    ... | true = cutContaining

    -- The oracle's result has exactly the same indexed sequent as its input;
    -- cut-free and idempotent laws are part of the axiom's contract.
    record MALLPCutElimination : Set₁ where
      field
        normalizeCutProof :
          {Γ : Context} {S : Stoup} →
          MALLP Γ S →
          MALLP Γ S
        normalizeCutProof-cutFree :
          {Γ : Context} {S : Stoup} →
          (proof : MALLP Γ S) →
          hasCut (normalizeCutProof proof) ≡ false
        normalizeCutProof-idempotent :
          {Γ : Context} {S : Stoup} →
          (proof : MALLP Γ S) →
          normalizeCutProof (normalizeCutProof proof) ≡
          normalizeCutProof proof
    open MALLPCutElimination public

    postulate
      mallpCutElimination : MALLPCutElimination

    abstract
      cutEliminate :
        {Γ : Context} {S : Stoup} →
        MALLP Γ S →
        MALLP Γ S
      cutEliminate proof =
        normalizeCutProof mallpCutElimination proof

      cutEliminate-idempotent :
        {Γ : Context} {S : Stoup} →
        (proof : MALLP Γ S) →
        cutEliminate (cutEliminate proof) ≡ cutEliminate proof
      cutEliminate-idempotent proof =
        normalizeCutProof-idempotent mallpCutElimination proof

      cutEliminate-cut-free :
        {Γ : Context} {S : Stoup} →
        (proof : MALLP Γ S) →
        hasCut (cutEliminate proof) ≡ false
      cutEliminate-cut-free proof =
        normalizeCutProof-cutFree mallpCutElimination proof


  -- --------------------------------------------------------------------
  -- Publicly expose all seven Foundations.* modules: six foundational
  -- packages and Laurent's MALLP calculus. No Seely structure is included.
  -- --------------------------------------------------------------------

  open ForsterEnumerability public
  open SymmetricBarRecursion public
  open DoubleNegation public
  open MacLaneCoherence public
  open CohesiveRetractions public
  open QuotientReflection public
  open LaurentPolarizedMALLP public

open Foundations.ForsterEnumerability public
open Foundations.SymmetricBarRecursion public
open Foundations.DoubleNegation public
open Foundations.MacLaneCoherence public
open Foundations.CohesiveRetractions public
open Foundations.QuotientReflection public
open Foundations.LaurentPolarizedMALLP public

-- ----------------------------------------------------------------------
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
-- ----------------------------------------------------------------------

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


-- ----------------------------------------------------------------------
-- MALLP-CONSTRAINED SBR / BELLMAN OBJECTIVES
--
-- An SBR objective is accepted only together with MALLP derivations for its
-- base and step maps. The base consumes one encoded partial-map resource;
-- the step consumes that state and one encoded continuation exactly once.
-- Relational soundness certifies the two objective equations.
--
-- This constrains the generalized Bellman algebra independently of PEA.
-- It does not claim that the postulated SBR oracle itself is implemented by
-- MALLP, nor that the contract alone proves global SBR termination.
-- ----------------------------------------------------------------------

module SBRMALLPBellman (Atom : Nat → Set) where

  open MALLPRelationalDenotation Atom

  record MALLPSBRBellmanObjective
      (X R : Set)
      (entryAtom continuationAtom resultAtom : Nat)
      (encodeEntries : PartialMap X → Atom entryAtom)
      (encodeContinuation : (X → R) → Atom continuationAtom)
      (encodeResult : R → Atom resultAtom)
      (base : PartialMap X → R)
      (step : PartialMap X → (X → R) → R) : Set₁ where
    field
      baseDerivation :
        MALLP (atom⁻ entryAtom ∷ []) (just (atom⁺ resultAtom))
      baseRealizes :
        (entries : PartialMap X) →
        MALLPRelation baseDerivation
          (pair (encodeEntries entries) tt)
          (encodeResult (base entries))

      stepDerivation :
        MALLP
          (atom⁻ entryAtom ∷ atom⁻ continuationAtom ∷ [])
          (just (atom⁺ resultAtom))
      stepRealizes :
        (entries : PartialMap X) →
        (continuation : X → R) →
        MALLPRelation stepDerivation
          (pair (encodeEntries entries)
            (pair (encodeContinuation continuation) tt))
          (encodeResult (step entries continuation))

  open MALLPSBRBellmanObjective public

  symmetricBarRecMALLP-stop :
    {X R : Set} →
    {entryAtom continuationAtom resultAtom : Nat} →
    {encodeEntries : PartialMap X → Atom entryAtom} →
    {encodeContinuation : (X → R) → Atom continuationAtom} →
    {encodeResult : R → Atom resultAtom} →
    {base : PartialMap X → R} →
    {step : PartialMap X → (X → R) → R} →
    (objective : MALLPSBRBellmanObjective X R
      entryAtom continuationAtom resultAtom
      encodeEntries encodeContinuation encodeResult base step) →
    (omega : (Nat → X) → Nat) →
    (default : X) →
    (condition : SymmetricBarCondition omega default) →
    (entries : PartialMap X) →
    (key : Nat) →
    (present : memberKey key (mapEntries entries) ≡ true) →
    MALLPRelation (baseDerivation objective)
      (pair (encodeEntries entries) tt)
      (encodeResult
        (symmetricBarRec omega default condition base step
          entries key (inDomain present)))
  symmetricBarRecMALLP-stop
    {encodeEntries = encodeEntries}
    {encodeResult = encodeResult}
    {base = base}
    {step = step}
    objective omega default condition entries key present =
    subst
      (λ output → MALLPRelation (baseDerivation objective)
        (pair (encodeEntries entries) tt) output)
      (cong encodeResult
        (sym (sBR-stop omega default condition base step entries key present)))
      (baseRealizes objective entries)

  symmetricBarRecMALLP-step :
    {X R : Set} →
    {entryAtom continuationAtom resultAtom : Nat} →
    {encodeEntries : PartialMap X → Atom entryAtom} →
    {encodeContinuation : (X → R) → Atom continuationAtom} →
    {encodeResult : R → Atom resultAtom} →
    {base : PartialMap X → R} →
    {step : PartialMap X → (X → R) → R} →
    (objective : MALLPSBRBellmanObjective X R
      entryAtom continuationAtom resultAtom
      encodeEntries encodeContinuation encodeResult base step) →
    (omega : (Nat → X) → Nat) →
    (default : X) →
    (condition : SymmetricBarCondition omega default) →
    (entries : PartialMap X) →
    (key : Nat) →
    (absent : memberKey key (mapEntries entries) ≡ false) →
    MALLPRelation (stepDerivation objective)
      (pair (encodeEntries entries)
        (pair
          (encodeContinuation
            (λ value →
              let
                nextEntries = extendFresh entries key absent value
                nextKey = omega (streamOf (mapEntries nextEntries) default)
              in symmetricBarRec omega default condition base step
                   nextEntries nextKey (decideDomain nextEntries nextKey)))
          tt))
      (encodeResult
        (symmetricBarRec omega default condition base step
          entries key (outDomain absent)))
  symmetricBarRecMALLP-step
    {X = X}
    {R = R}
    {resultAtom = resultAtom}
    {encodeEntries = encodeEntries}
    {encodeContinuation = encodeContinuation}
    {encodeResult = encodeResult}
    {base = base}
    {step = step}
    objective omega default condition entries key absent =
    let
      continuation : X → R
      continuation value =
        let
          nextEntries = extendFresh entries key absent value
          nextKey = omega (streamOf (mapEntries nextEntries) default)
        in symmetricBarRec omega default condition base step
             nextEntries nextKey (decideDomain nextEntries nextKey)

      relationAt : Atom resultAtom → Set
      relationAt output =
        MALLPRelation (stepDerivation objective)
          (pair (encodeEntries entries)
            (pair (encodeContinuation continuation) tt))
          output
    in
    subst
      relationAt
      (cong encodeResult
        (sym (sBR-step omega default condition base step entries key absent)))
      (stepRealizes objective entries continuation)


-- ----------------------------------------------------------------------
-- ONE DEPENDENT DYNAMIC-PROGRAMMING / MALLP OPTIMIZATION CONSTRAINT
--
-- One Nat candidate family, one quotient-normalized partial-map state,
-- one payoff preorder, one finite DP, one SBR recurrence, and one pair
-- of MALLP-certified Bellman maps. Cohesion and Mac Lane coherence act on
-- those same candidate and resource types. Existing logical assumptions
-- remain explicit; this package introduces no postulates or rewrite rules.
-- ----------------------------------------------------------------------

optimizationTensor : Nat → Nat → Nat → TensorExpr
optimizationTensor entryAtom continuationAtom resultAtom =
  tensor (atom entryAtom)
    (tensor (atom continuationAtom) (atom resultAtom))

record IdentityRewriteFoundation : Set₁ where
  field
    identityReflexivityRewrite :
      (A : Set) → F A A ≡ S
    identityCompositionRewrite :
      (A : Set → Set) (X Y : Set) →
      G A X Y ≡ F (A X) (A Y)
open IdentityRewriteFoundation public

identityRewriteFoundation : IdentityRewriteFoundation
identityRewriteFoundation = record
  { identityReflexivityRewrite = rewF
  ; identityCompositionRewrite = rewG
  }

module UnifiedFoundationsOptimization (Atom : Nat → Set) where

  module Bellman = SBRMALLPBellman Atom
  open Bellman public

  -- Family coverage, quotient state, finite selection, SBR and MALLP
  -- all share exactly one Nat candidate and one payoff type.
  record DynamicProgrammingMALLPOptimization
      (candidateFamily : ParametricallyEnumerable)
      (H G : Category)
      (productsH : FiniteProducts H)
      (productsG : FiniteProducts G)
      (ℓ : Level)
      (R : Set)
      : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      negativeBoundary : NegativeLogicalBoundary ℓ
      identityRewriting : IdentityRewriteFoundation

      positiveEnumerability : ParametricEA
      candidateParameter : Nat
      candidate : Nat
      candidateStage : Nat
      candidateEnumeration :
        universalEval
          (parametricCode positiveEnumerability candidateFamily candidateParameter)
          candidateStage ≡ just candidate

      entryAtom continuationAtom resultAtom : Nat
      encodeEntries : PartialMap Nat → Atom entryAtom
      encodeContinuation : (Nat → R) → Atom continuationAtom
      encodeResult : R → Atom resultAtom
      objectiveBase : PartialMap Nat → R
      objectiveStep : PartialMap Nat → (Nat → R) → R
      bellmanResourceProof :
        MALLPSBRBellmanObjective Nat R
          entryAtom continuationAtom resultAtom
          encodeEntries encodeContinuation encodeResult
          objectiveBase objectiveStep
      cutEliminationFoundation : MALLPCutElimination

      barControl : (Nat → Nat) → Nat
      barDefault : Nat
      barCoverage :
        SymmetricBarCondition barControl barDefault
      barStopEquation :
        (entries : PartialMap Nat) (key : Nat) →
        (present : memberKey key (mapEntries entries) ≡ true) →
        symmetricBarRec barControl barDefault barCoverage
          objectiveBase objectiveStep entries key (inDomain present) ≡
        objectiveBase entries
      barStepEquation :
        (entries : PartialMap Nat) (key : Nat) →
        (absent : memberKey key (mapEntries entries) ≡ false) →
        symmetricBarRec barControl barDefault barCoverage
          objectiveBase objectiveStep entries key (outDomain absent) ≡
        objectiveStep entries
          (λ value →
            let
              nextEntries = extendFresh entries key absent value
              nextKey =
                barControl (streamOf (mapEntries nextEntries) barDefault)
            in symmetricBarRec barControl barDefault barCoverage
                 objectiveBase objectiveStep nextEntries nextKey
                 (decideDomain nextEntries nextKey))

      -- Quotient reflection: the normalized state is the single DP/SBR
      -- input, and both Bellman maps respect that same normalization.
      initialState : PartialMap Nat
      stateNormalizer : IdempotentEndomap (PartialMap Nat)
      quotientInitialState : Quotient (PartialMap Nat) stateNormalizer
      quotientInitialStateIsCanonical :
        quotientInitialState ≡ qcanon stateNormalizer initialState
      objectiveBase-invariant :
        (entries : PartialMap Nat) →
        objectiveBase (canonicalize stateNormalizer entries) ≡
          objectiveBase entries
      objectiveStep-invariant :
        (entries : PartialMap Nat) (continuation : Nat → R) →
        objectiveStep (canonicalize stateNormalizer entries) continuation ≡
          objectiveStep entries continuation
      candidateInObjectiveState :
        memberKey candidate
          (mapEntries (qcoerce {A = PartialMap Nat} {f = stateNormalizer} quotientInitialState)) ≡ true

      barKey : Nat
      barKeyIsSelected :
        barKey ≡
          barControl
            (streamOf
              (mapEntries (qcoerce {A = PartialMap Nat} {f = stateNormalizer} quotientInitialState)) barDefault)
      barKeyDecision :
        DomainDecision (qcoerce {A = PartialMap Nat} {f = stateNormalizer} quotientInitialState) barKey
      barValue : R
      barValueIsRecursor :
        symmetricBarRec barControl barDefault barCoverage
          objectiveBase objectiveStep
          (qcoerce {A = PartialMap Nat} {f = stateNormalizer} quotientInitialState) barKey barKeyDecision ≡ barValue

      -- Finite backward induction uses the same Nat move space and payoff
      -- order. Its payoff is indexed by this exact normalized initial state.
      valueOrder : Preorder R
      finiteSelection : Selection Nat R
      finiteSelection-optimal : OptimalSelection valueOrder finiteSelection
      finiteHorizon : Nat
      finitePayoff : PartialMap Nat → Play Nat finiteHorizon → R
      -- The PEA candidate is precisely the initial move of the optimal
      -- finite policy evaluated by this same payoff on the same quotient state.
      candidateIsChosen :
        playHeadOr barDefault
          (backwardInduction finiteHorizon finiteSelection
            (finitePayoff (qcoerce {A = PartialMap Nat} {f = stateNormalizer} quotientInitialState))) ≡ candidate
      finiteDynamicProgrammingValue : R
      finiteDynamicProgrammingValueIsBackwardInduction :
        finiteDynamicProgrammingValue ≡
          selectedOutcome
            (backwardInduction finiteHorizon finiteSelection)
            (finitePayoff (qcoerce {A = PartialMap Nat} {f = stateNormalizer} quotientInitialState))
      finiteDynamicProgrammingAgreesWithSBR :
        finiteDynamicProgrammingValue ≡ barValue

      -- Cohesive Π presents the same H-state in G and relates each Nat
      -- candidate to it; the adjunction itself is supplied once.
      cohesion : CohesiveAdjointQuadruple H G productsH productsG
      optimizationState : categoryObjects H
      candidateObject : Nat → categoryObjects G
      candidateReachability :
        (n : Nat) →
        categoryHom G
          (functorObject (cohesivePi cohesion) optimizationState)
          (candidateObject n)

      -- Mac Lane normalizes the exact entry/continuation/result resource
      -- tensor used by the Bellman MALLP derivations.
      resourceAssociation :
        TensorHom
          (tensor (tensor (atom entryAtom) (atom continuationAtom))
            (atom resultAtom))
          (tensor (atom entryAtom)
            (tensor (atom continuationAtom) (atom resultAtom)))

  open DynamicProgrammingMALLPOptimization public

  optimizationCandidateFeasible :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    Predicate candidateFamily
      (candidateParameter optimization) (candidate optimization)
  optimizationCandidateFeasible {candidateFamily = family} optimization =
    parametricCode-sound
      (positiveEnumerability optimization)
      family
      (candidateParameter optimization)
      (candidateStage optimization)
      (candidate optimization)
      (candidateEnumeration optimization)

  finiteOptimizationOptimal :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    OptimalSelection
      (valueOrder optimization)
      (backwardInduction
        (finiteHorizon optimization)
        (finiteSelection optimization))
  finiteOptimizationOptimal optimization =
    backwardInduction-optimal
      (valueOrder optimization)
      (finiteSelection optimization)
      (finiteSelection-optimal optimization)
      (finiteHorizon optimization)

  normalizedBellmanBase :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    MALLP
      (atom⁻ (entryAtom optimization) ∷ [])
      (just (atom⁺ (resultAtom optimization)))
  normalizedBellmanBase optimization =
    normalizeCutProof
      (cutEliminationFoundation optimization)
      (baseDerivation (bellmanResourceProof optimization))

  normalizedBellmanBase-cutFree :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    hasCut (normalizedBellmanBase optimization) ≡ false
  normalizedBellmanBase-cutFree optimization =
    normalizeCutProof-cutFree
      (cutEliminationFoundation optimization)
      (baseDerivation (bellmanResourceProof optimization))

  normalizedBellmanStep :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    MALLP
      (atom⁻ (entryAtom optimization) ∷
        atom⁻ (continuationAtom optimization) ∷ [])
      (just (atom⁺ (resultAtom optimization)))
  normalizedBellmanStep optimization =
    normalizeCutProof
      (cutEliminationFoundation optimization)
      (stepDerivation (bellmanResourceProof optimization))

  normalizedBellmanStep-cutFree :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    hasCut (normalizedBellmanStep optimization) ≡ false
  normalizedBellmanStep-cutFree optimization =
    normalizeCutProof-cutFree
      (cutEliminationFoundation optimization)
      (stepDerivation (bellmanResourceProof optimization))

  optimizationResourceCoherence :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    {A B : TensorExpr} →
    (first second : TensorHom A B) →
    first ≡ second
  optimizationResourceCoherence optimization {A} {B} first second =
    Foundations.MacLaneCoherence.tensorHom-proposition
      {A = A} {B = B} first second


-- ----------------------------------------------------------------------
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
-- ----------------------------------------------------------------------

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

-- ----------------------------------------------------------------------
-- REFLECTION-GENERATED ADT SHAPES
--
-- Reflection inspects the kernel-resolved datatype declaration and its
-- constructor Pi telescopes, then emits a quoted description. This is
-- compile-time metadata only: it does not decide linearity, runtime layout,
-- or a MALLP derivation. Those are checked by the typed source core above.
-- ----------------------------------------------------------------------

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
  parametricCodePEA-code
  sBR-stop
  sBR-step
  quotient-raw-sound
  cutEliminate-idempotent
#-}
-- This reduction uses the active quotient rewrite rule.
quotientReflectionRewriteSmoke :
  (A : Set) →
  (f : IdempotentEndomap A) →
  (x : A) →
  denoteQuotient {A} {f} (rawₑ x) ≡
  denoteQuotient {A} {f} (canonicalizedₑ x)
quotientReflectionRewriteSmoke A f x = refl


-- ----------------------------------------------------------------------
-- Rewrite computation smoke witnesses
-- ----------------------------------------------------------------------

alwaysTrue : Nat → Bool
alwaysTrue n = true

falseThenTrue : Nat → Bool
falseThenTrue zero = false
falseThenTrue (suc n) = true

boundedSearch-zero-computes :
  boundedSearch (suc zero) alwaysTrue ≡ just zero
boundedSearch-zero-computes = refl

boundedSearch-successor-computes :
  boundedSearch (suc (suc zero)) falseThenTrue ≡ just (suc zero)
boundedSearch-successor-computes = refl

parametricEA-rewrite-client :
  (F : ParametricallyEnumerable) →
  (i stage value : Nat) →
  universalEval (parametricCodePEA F i) stage ≡ just value →
  Predicate F i value
parametricEA-rewrite-client F i stage value computation =
  parametricCodePEA-sound F i stage value computation

cutEliminate-cut-free-client :
  {Γ : Context} {S : Stoup} →
  (proof : MALLP Γ S) →
  hasCut (cutEliminate proof) ≡ false
cutEliminate-cut-free-client proof = cutEliminate-cut-free proof

cutEliminate-idempotent-client :
  {Γ : Context} {S : Stoup} →
  (proof : MALLP Γ S) →
  cutEliminate (cutEliminate proof) ≡ cutEliminate proof
cutEliminate-idempotent-client proof = refl

-- ----------------------------------------------------------------------
-- Strict closed-Nat Forth combinator semantics
--
-- This compiler fragment has no variables, closures, heap, implicit copy,
-- implicit drop, exponentials, or garbage collector. Each syntax child is
-- visited once; each combinator returns exactly one Nat and preserves the
-- caller's residual stack.
-- ----------------------------------------------------------------------

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
  applyNatOp monusOp x y = x - y
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

  word64IdentityCodeWithResidual :
    {Γ : List StackType} →
    ForthCode (natCell ∷ natCell ∷ Γ) (natCell ∷ natCell ∷ Γ)
  word64IdentityCodeWithResidual = identityNat


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
  execTokens (token ∷ tokens) stack with execToken token stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack

  -- --------------------------------------------------------------------
  -- Bounded Gforth Nat machine.
  --
  -- FLib.fth represents source Nats in a signed Forth cell. Its runtime
  -- checks every consumed operand and rejects results above the positive
  -- cell bound. This interpreter gives those partial-success semantics to
  -- the same emitted token algebra. The bound is a parameter because
  -- Gforth's CELL-BITS is platform-dependent.
  -- --------------------------------------------------------------------

  natWithinBound : Nat → Nat → Bool
  natWithinBound value bound = value < suc bound

  -- A concrete target stack contains only values representable by the
  -- positive signed-cell bound selected for the Gforth process.
  data NatStackBounded (bound : Nat) : List Nat → Set where
    natStackBoundedNil : NatStackBounded bound []
    natStackBoundedCons :
      {value : Nat} {stack : List Nat} →
      natWithinBound value bound ≡ true →
      NatStackBounded bound stack →
      NatStackBounded bound (value ∷ stack)

  -- Immediate Nat operands are target-cell values too: literals and ROLL
  -- depths must fit the same signed-cell bound as runtime stack values.
  BoundedTokenParameter : Nat → ForthToken → Set
  BoundedTokenParameter bound (pushLiteral value) =
    natWithinBound value bound ≡ true
  BoundedTokenParameter bound (rollWord depth) =
    natWithinBound depth bound ≡ true
  BoundedTokenParameter bound _ = ⊤

  execBoundedToken : Nat → ForthToken → List Nat → Maybe (List Nat)
  execBoundedToken bound (pushLiteral value) stack
    with natWithinBound value bound
  ... | true = execToken (pushLiteral value) stack
  ... | false = nothing
  execBoundedToken bound addWord (right ∷ left ∷ stack)
    with natWithinBound left bound
       | natWithinBound right bound
       | natWithinBound (left + right) bound
  ... | true | true | true = execToken addWord (right ∷ left ∷ stack)
  ... | _ | _ | _ = nothing
  execBoundedToken bound addWord stack = nothing
  execBoundedToken bound monusWord (right ∷ left ∷ stack)
    with natWithinBound left bound
       | natWithinBound right bound
  ... | true | true = execToken monusWord (right ∷ left ∷ stack)
  ... | _ | _ = nothing
  execBoundedToken bound monusWord stack = nothing
  execBoundedToken bound multiplyWord (right ∷ left ∷ stack)
    with natWithinBound left bound
       | natWithinBound right bound
       | natWithinBound (left * right) bound
  ... | true | true | true =
    execToken multiplyWord (right ∷ left ∷ stack)
  ... | _ | _ | _ = nothing
  execBoundedToken bound multiplyWord stack = nothing
  execBoundedToken bound swapWord stack = execToken swapWord stack
  execBoundedToken bound (rollWord depth) stack
    with natWithinBound depth bound
  ... | true = execToken (rollWord depth) stack
  ... | false = nothing

  execBoundedTokens : Nat → List ForthToken → List Nat → Maybe (List Nat)
  execBoundedTokens bound [] stack = just stack
  execBoundedTokens bound (token ∷ tokens) stack
    with execBoundedToken bound token stack
  ... | nothing = nothing
  ... | just nextStack = execBoundedTokens bound tokens nextStack

  execBoundedToken-sound :
    (bound : Nat) (token : ForthToken) (stack result : List Nat) →
    execBoundedToken bound token stack ≡ just result →
    execToken token stack ≡ just result
  execBoundedToken-sound bound (pushLiteral value) stack result proof
    with natWithinBound value bound | proof
  ... | true | refl = refl
  ... | false | ()
  execBoundedToken-sound bound addWord [] result ()
  execBoundedToken-sound bound addWord (value ∷ []) result ()
  execBoundedToken-sound bound addWord (right ∷ left ∷ stack) result proof
    with natWithinBound left bound
       | natWithinBound right bound
       | natWithinBound (left + right) bound
       | proof
  ... | true | true | true | refl = refl
  ... | false | _ | _ | ()
  ... | true | false | _ | ()
  ... | true | true | false | ()
  execBoundedToken-sound bound monusWord [] result ()
  execBoundedToken-sound bound monusWord (value ∷ []) result ()
  execBoundedToken-sound bound monusWord (right ∷ left ∷ stack) result proof
    with natWithinBound left bound
       | natWithinBound right bound
       | proof
  ... | true | true | refl = refl
  ... | false | _ | ()
  ... | true | false | ()
  execBoundedToken-sound bound multiplyWord [] result ()
  execBoundedToken-sound bound multiplyWord (value ∷ []) result ()
  execBoundedToken-sound bound multiplyWord (right ∷ left ∷ stack) result proof
    with natWithinBound left bound
       | natWithinBound right bound
       | natWithinBound (left * right) bound
       | proof
  ... | true | true | true | refl = refl
  ... | false | _ | _ | ()
  ... | true | false | _ | ()
  ... | true | true | false | ()
  execBoundedToken-sound bound swapWord stack result proof = proof
  execBoundedToken-sound bound (rollWord depth) stack result proof
    with natWithinBound depth bound | proof
  ... | true | boundedProof = boundedProof
  ... | false | ()

  execBoundedTokens-sound :
    (bound : Nat) (tokens : List ForthToken) (stack result : List Nat) →
    execBoundedTokens bound tokens stack ≡ just result →
    execTokens tokens stack ≡ just result
  execBoundedTokens-sound bound [] stack result proof = proof
  execBoundedTokens-sound bound (token ∷ tokens) stack result proof
    with execBoundedToken bound token stack in boundedStep | proof
  ... | nothing | ()
  ... | just nextStack | restProof
    rewrite execBoundedToken-sound bound token stack nextStack boundedStep =
      execBoundedTokens-sound bound tokens nextStack result restProof

  execBoundedTokens-preserves :
    (bound : Nat) (tokens : List ForthToken) (stack : List Nat) →
    (result expected : List Nat) →
    execBoundedTokens bound tokens stack ≡ just result →
    execTokens tokens stack ≡ just expected →
    result ≡ expected
  execBoundedTokens-preserves bound tokens stack result expected
    boundedSuccess sourceSuccess =
    just-injective
      (trans
        (sym (execBoundedTokens-sound bound tokens stack result boundedSuccess))
        sourceSuccess)

  natBoundFalseNotTrue : false ≡ true → ⊥
  natBoundFalseNotTrue ()

  natStackBoundedHead :
    {bound value : Nat} {stack : List Nat} →
    NatStackBounded bound (value ∷ stack) →
    natWithinBound value bound ≡ true
  natStackBoundedHead (natStackBoundedCons valueBound _) = valueBound

  natStackBoundedTail :
    {bound value : Nat} {stack : List Nat} →
    NatStackBounded bound (value ∷ stack) →
    NatStackBounded bound stack
  natStackBoundedTail (natStackBoundedCons _ stackBound) = stackBound

  data NatStackOverflow (bound : Nat) : List Nat → Set where
    natStackOverflowHead :
      {value : Nat} {stack : List Nat} →
      natWithinBound value bound ≡ false →
      NatStackOverflow bound (value ∷ stack)

  data BoundedTokenFailure
      (bound : Nat) : ForthToken → List Nat → Set where
    boundedTokenStackError :
      {token : ForthToken} {stack : List Nat} →
      execToken token stack ≡ nothing →
      BoundedTokenFailure bound token stack
    boundedTokenCellOverflow :
      {token : ForthToken} {stack : List Nat} →
      (result : List Nat) →
      execToken token stack ≡ just result →
      NatStackOverflow bound result →
      BoundedTokenFailure bound token stack
    boundedTokenRollDepthOverflow :
      {depth : Nat} {stack : List Nat} →
      natWithinBound depth bound ≡ false →
      BoundedTokenFailure bound (rollWord depth) stack

  -- With a bounded input stack, each bounded-step failure is either the
  -- same stack/roll failure as the unbounded token machine, or an unbounded
  -- successful result whose new head exceeds the cell bound.
  execBoundedToken-roll-within-bound :
    (bound depth : Nat) (stack : List Nat) →
    natWithinBound depth bound ≡ true →
    execBoundedToken bound (rollWord depth) stack ≡
      execToken (rollWord depth) stack
  execBoundedToken-roll-within-bound bound depth stack depthBound
    rewrite depthBound = refl

  classifyBoundedRollFailure :
    (bound depth : Nat) (stack : List Nat) →
    (withinBound : Bool) →
    withinBound ≡ natWithinBound depth bound →
    execBoundedToken bound (rollWord depth) stack ≡ nothing →
    BoundedTokenFailure bound (rollWord depth) stack
  classifyBoundedRollFailure bound depth stack true withinBoundProof failure =
    boundedTokenStackError
      (trans
        (sym (execBoundedToken-roll-within-bound
          bound depth stack (sym withinBoundProof)))
        failure)
  classifyBoundedRollFailure bound depth stack false withinBoundProof failure =
    boundedTokenRollDepthOverflow (sym withinBoundProof)

  execBoundedToken-failure-classification :
    (bound : Nat) (token : ForthToken) (stack : List Nat) →
    NatStackBounded bound stack →
    execBoundedToken bound token stack ≡ nothing →
    BoundedTokenFailure bound token stack
  execBoundedToken-failure-classification
    bound (pushLiteral value) stack inputBound failure
    with natWithinBound value bound in valueCheck
       | failure
  ... | true | ()
  ... | false | refl =
    boundedTokenCellOverflow (value ∷ stack) refl
      (natStackOverflowHead valueCheck)

  execBoundedToken-failure-classification
    bound addWord [] inputBound failure =
    boundedTokenStackError refl
  execBoundedToken-failure-classification
    bound addWord (value ∷ []) inputBound failure =
    boundedTokenStackError refl
  execBoundedToken-failure-classification
    bound addWord (right ∷ left ∷ stack)
    (natStackBoundedCons rightBound
      (natStackBoundedCons leftBound stackBound))
    failure
    with natWithinBound left bound in leftCheck
       | natWithinBound right bound in rightCheck
       | natWithinBound (left + right) bound in resultCheck
       | failure
  ... | false | _ | _ | _ =
    ⊥-elim (natBoundFalseNotTrue leftBound)
  ... | true | false | _ | _ =
    ⊥-elim (natBoundFalseNotTrue rightBound)
  ... | true | true | true | ()
  ... | true | true | false | refl =
    boundedTokenCellOverflow ((left + right) ∷ stack) refl
      (natStackOverflowHead resultCheck)

  execBoundedToken-failure-classification
    bound monusWord [] inputBound failure =
    boundedTokenStackError refl
  execBoundedToken-failure-classification
    bound monusWord (value ∷ []) inputBound failure =
    boundedTokenStackError refl
  execBoundedToken-failure-classification
    bound monusWord (right ∷ left ∷ stack)
    (natStackBoundedCons rightBound
      (natStackBoundedCons leftBound stackBound))
    failure
    with natWithinBound left bound in leftCheck
       | natWithinBound right bound in rightCheck
       | failure
  ... | false | _ | _ =
    ⊥-elim (natBoundFalseNotTrue leftBound)
  ... | true | false | _ =
    ⊥-elim (natBoundFalseNotTrue rightBound)
  ... | true | true | ()

  execBoundedToken-failure-classification
    bound multiplyWord [] inputBound failure =
    boundedTokenStackError refl
  execBoundedToken-failure-classification
    bound multiplyWord (value ∷ []) inputBound failure =
    boundedTokenStackError refl
  execBoundedToken-failure-classification
    bound multiplyWord (right ∷ left ∷ stack)
    (natStackBoundedCons rightBound
      (natStackBoundedCons leftBound stackBound))
    failure
    with natWithinBound left bound in leftCheck
       | natWithinBound right bound in rightCheck
       | natWithinBound (left * right) bound in resultCheck
       | failure
  ... | false | _ | _ | _ =
    ⊥-elim (natBoundFalseNotTrue leftBound)
  ... | true | false | _ | _ =
    ⊥-elim (natBoundFalseNotTrue rightBound)
  ... | true | true | true | ()
  ... | true | true | false | refl =
    boundedTokenCellOverflow ((left * right) ∷ stack) refl
      (natStackOverflowHead resultCheck)

  execBoundedToken-failure-classification
    bound swapWord stack inputBound failure =
    boundedTokenStackError failure
  execBoundedToken-failure-classification
    bound (rollWord depth) stack inputBound failure =
    classifyBoundedRollFailure bound depth stack
      (natWithinBound depth bound) refl failure

  boundedLiteralOverflowExample :
    BoundedTokenFailure 3 (pushLiteral 4) []
  boundedLiteralOverflowExample =
    execBoundedToken-failure-classification
      3 (pushLiteral 4) [] natStackBoundedNil refl

  boundedAddOverflowExample :
    BoundedTokenFailure 3 addWord (2 ∷ 2 ∷ [])
  boundedAddOverflowExample =
    execBoundedToken-failure-classification
      3 addWord (2 ∷ 2 ∷ [])
      (natStackBoundedCons refl
        (natStackBoundedCons refl natStackBoundedNil))
      refl

  boundedRollDepthOverflowAtThreeExample :
    BoundedTokenFailure 3 (rollWord 4) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  boundedRollDepthOverflowAtThreeExample =
    execBoundedToken-failure-classification
      3 (rollWord 4) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
      (natStackBoundedCons refl
        (natStackBoundedCons refl
          (natStackBoundedCons refl
            (natStackBoundedCons refl
              (natStackBoundedCons refl natStackBoundedNil)))))
      refl

  boundedRollDepthOverflowAtThree :
    execBoundedTokens 3 (rollWord 4 ∷ []) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []) ≡ nothing
  boundedRollDepthOverflowAtThree = refl

  boundedAddUnderflowExample :
    BoundedTokenFailure 3 addWord []
  boundedAddUnderflowExample =
    execBoundedToken-failure-classification
      3 addWord [] natStackBoundedNil refl

  -- Completeness for one bounded step needs both bounded input and bounded
  -- output stacks. These carry the operand and intermediate-result side
  -- conditions omitted by a final-result-only bound.
  execBoundedToken-complete :
    (bound : Nat) (token : ForthToken) (stack result : List Nat) →
    NatStackBounded bound stack →
    BoundedTokenParameter bound token →
    execToken token stack ≡ just result →
    NatStackBounded bound result →
    execBoundedToken bound token stack ≡ just result
  execBoundedToken-complete bound (pushLiteral value) stack .(value ∷ stack)
    inputBound parameterBound refl (natStackBoundedCons valueBound restBound)
    with natWithinBound value bound in valueCheck
  ... | true = refl
  ... | false =
    ⊥-elim (natBoundFalseNotTrue valueBound)
  execBoundedToken-complete bound addWord [] result natStackBoundedNil _ () resultBound
  execBoundedToken-complete bound addWord (value ∷ []) result
    (natStackBoundedCons _ natStackBoundedNil) _ () resultBound
  execBoundedToken-complete bound addWord (right ∷ left ∷ stack)
    .((left + right) ∷ stack)
    (natStackBoundedCons rightBound (natStackBoundedCons leftBound stackBound))
    _ refl (natStackBoundedCons resultBound resultStackBound)
    with natWithinBound left bound in leftCheck
       | natWithinBound right bound in rightCheck
       | natWithinBound (left + right) bound in resultCheck
  ... | true | true | true = refl
  ... | false | _ | _ =
    ⊥-elim (natBoundFalseNotTrue leftBound)
  ... | true | false | _ =
    ⊥-elim (natBoundFalseNotTrue rightBound)
  ... | true | true | false =
    ⊥-elim (natBoundFalseNotTrue resultBound)
  execBoundedToken-complete bound monusWord [] result natStackBoundedNil _ () resultBound
  execBoundedToken-complete bound monusWord (value ∷ []) result
    (natStackBoundedCons _ natStackBoundedNil) _ () resultBound
  execBoundedToken-complete bound monusWord (right ∷ left ∷ stack)
    .(applyNatOp monusOp left right ∷ stack)
    (natStackBoundedCons rightBound (natStackBoundedCons leftBound stackBound))
    _ refl resultBound
    with natWithinBound left bound in leftCheck
       | natWithinBound right bound in rightCheck
  ... | true | true = refl
  ... | false | _ =
    ⊥-elim (natBoundFalseNotTrue leftBound)
  ... | true | false =
    ⊥-elim (natBoundFalseNotTrue rightBound)
  execBoundedToken-complete bound multiplyWord [] result natStackBoundedNil _ () resultBound
  execBoundedToken-complete bound multiplyWord (value ∷ []) result
    (natStackBoundedCons _ natStackBoundedNil) _ () resultBound
  execBoundedToken-complete bound multiplyWord (right ∷ left ∷ stack)
    .((left * right) ∷ stack)
    (natStackBoundedCons rightBound (natStackBoundedCons leftBound stackBound))
    _ refl (natStackBoundedCons resultBound resultStackBound)
    with natWithinBound left bound in leftCheck
       | natWithinBound right bound in rightCheck
       | natWithinBound (left * right) bound in resultCheck
  ... | true | true | true = refl
  ... | false | _ | _ =
    ⊥-elim (natBoundFalseNotTrue leftBound)
  ... | true | false | _ =
    ⊥-elim (natBoundFalseNotTrue rightBound)
  ... | true | true | false =
    ⊥-elim (natBoundFalseNotTrue resultBound)
  execBoundedToken-complete bound swapWord stack result inputBound _ stepBound resultBound =
    stepBound
  execBoundedToken-complete bound (rollWord depth) stack result inputBound depthBound stepBound resultBound
    with natWithinBound depth bound
  ... | true = stepBound
  ... | false = ⊥-elim (natBoundFalseNotTrue depthBound)

  -- A bounded execution trace records every intermediate abstract stack.
  -- It is exactly the side condition needed for the converse bounded-machine
  -- theorem: final boundedness alone cannot rule out an intermediate overflow.
  data BoundedExecutionTrace (bound : Nat) :
      List ForthToken → List Nat → List Nat → Set where
    boundedTraceDone :
      {stack : List Nat} →
      NatStackBounded bound stack →
      BoundedExecutionTrace bound [] stack stack

    boundedTraceStep :
      {token : ForthToken} {tokens : List ForthToken}
      {before after final : List Nat} →
      NatStackBounded bound before →
      BoundedTokenParameter bound token →
      execToken token before ≡ just after →
      NatStackBounded bound after →
      BoundedExecutionTrace bound tokens after final →
      BoundedExecutionTrace bound (token ∷ tokens) before final

  boundedExecutionTrace-unbounded :
    {bound : Nat} {tokens : List ForthToken} {before final : List Nat} →
    BoundedExecutionTrace bound tokens before final →
    execTokens tokens before ≡ just final
  boundedExecutionTrace-unbounded (boundedTraceDone stackBound) = refl
  boundedExecutionTrace-unbounded
    (boundedTraceStep beforeBound _ step afterBound rest)
    rewrite step = boundedExecutionTrace-unbounded rest

  boundedExecutionTrace-bounded :
    {bound : Nat} {tokens : List ForthToken} {before final : List Nat} →
    BoundedExecutionTrace bound tokens before final →
    execBoundedTokens bound tokens before ≡ just final
  boundedExecutionTrace-bounded (boundedTraceDone stackBound) = refl
  boundedExecutionTrace-bounded {bound = bound}
    (boundedTraceStep {token = token} {tokens = tokens}
      {before = before} {after = after}
      beforeBound parameterBound step afterBound rest)
    rewrite execBoundedToken-complete bound token before after
      beforeBound parameterBound step afterBound =
      boundedExecutionTrace-bounded rest

  -- Converse to successful bounded preservation, under an explicit proof
  -- that every intermediate abstract stack and operation result fits.
  execBoundedTokens-complete :
    {bound : Nat} {tokens : List ForthToken} {before final : List Nat} →
    BoundedExecutionTrace bound tokens before final →
    execBoundedTokens bound tokens before ≡ just final
  execBoundedTokens-complete = boundedExecutionTrace-bounded

  execBoundedTokens-complete-unbounded :
    {bound : Nat} {tokens : List ForthToken} {before final : List Nat} →
    BoundedExecutionTrace bound tokens before final →
    execTokens tokens before ≡ just final
  execBoundedTokens-complete-unbounded = boundedExecutionTrace-unbounded

  boundedAddAtLimit :
    execBoundedTokens 9
      (pushLiteral 4 ∷ pushLiteral 5 ∷ addWord ∷ []) [] ≡
    just (9 ∷ [])
  boundedAddAtLimit = refl

  boundedAddOverflow :
    execBoundedTokens 9
      (pushLiteral 5 ∷ pushLiteral 5 ∷ addWord ∷ []) [] ≡
    nothing
  boundedAddOverflow = refl

  boundedMonusUnderflow :
    execBoundedTokens 9
      (pushLiteral 0 ∷ pushLiteral 1 ∷ monusWord ∷ []) [] ≡
    just (0 ∷ [])
  boundedMonusUnderflow = refl

  boundedMultiplyOverflow :
    execBoundedTokens 9
      (pushLiteral 5 ∷ pushLiteral 2 ∷ multiplyWord ∷ []) [] ≡
    nothing
  boundedMultiplyOverflow = refl

  boundedRollDepthAtLimit :
    execBoundedTokens 1
      (rollWord 1 ∷ []) (0 ∷ 1 ∷ []) ≡ just (1 ∷ 0 ∷ [])
  boundedRollDepthAtLimit = refl

  boundedRollDepthOverflow :
    execBoundedTokens 1
      (rollWord 2 ∷ []) (1 ∷ 0 ∷ 1 ∷ []) ≡ nothing
  boundedRollDepthOverflow = refl

  boundedRollDepthOverflowExample :
    BoundedTokenFailure 1 (rollWord 2) (1 ∷ 0 ∷ 1 ∷ [])
  boundedRollDepthOverflowExample =
    execBoundedToken-failure-classification
      1 (rollWord 2) (1 ∷ 0 ∷ 1 ∷ [])
      (natStackBoundedCons refl
        (natStackBoundedCons refl
          (natStackBoundedCons refl natStackBoundedNil)))
      refl

  boundedLiteralOverflow :
    execBoundedTokens 9 (pushLiteral 10 ∷ []) [] ≡ nothing
  boundedLiteralOverflow = refl

  execTokens-roll-single :
    (depth : Nat) →
    (stack : List Nat) →
    execTokens (rollWord depth ∷ []) stack ≡ rollList depth stack
  execTokens-roll-single depth stack with rollList depth stack
  ... | nothing = refl
  ... | just nextStack = refl

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

  -- --------------------------------------------------------------------
  -- A closed, proof-carrying MALLP theory for the implemented Nat slice.
  --
  -- Numerals are nullary constants. Each arithmetic primitive is a linear
  -- axiom Nat- ⊗ Nat- ⊢ Nat+, and composition is MALLP cut. Thus every
  -- source subterm is consumed once; this is a theory over MALLP, with an
  -- explicit primitive signature, rather than bare proof-tree syntax.
  -- --------------------------------------------------------------------

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

  natTheoryCutCount :
    {Γ : Context} {S : Stoup} →
    MALLPNatTheory Γ S → Nat
  natTheoryCutCount (mallp-nat-literal value) = zero
  natTheoryCutCount (mallp-nat-primitive operation) = zero
  natTheoryCutCount (mallp-nat-cut first second) =
    suc (natTheoryCutCount first + natTheoryCutCount second)
  natTheoryCutCount (mallp-nat-exchange permutation proof) =
    natTheoryCutCount proof
  natTheoryCutCount (mallp-nat-transport equality proof) =
    natTheoryCutCount proof
  natTheoryCutCount (mallp-nat-logical proof) = cutCount proof

  classifyNatTheory :
    {Γ : Context} →
    MALLPNatTheory Γ (just natFormula) → CutClass
  classifyNatTheory (mallp-nat-literal value) = cutFree
  classifyNatTheory (mallp-nat-primitive operation) = cutFree
  classifyNatTheory (mallp-nat-cut first second) = cutContaining
  classifyNatTheory (mallp-nat-exchange permutation proof) =
    classifyNatTheory proof
  classifyNatTheory (mallp-nat-transport equality proof) =
    classifyNatTheory proof
  classifyNatTheory (mallp-nat-logical proof) = classifyMALLP proof

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

  natPlusZeroRight : (n : Nat) → n + zero ≡ n
  natPlusZeroRight zero = refl
  natPlusZeroRight (suc n) = cong suc (natPlusZeroRight n)

  natProofCutCount : {n : Nat} → MALLPNatProof n → Nat
  natProofCutCount (natLiteralProof value) = zero
  natProofCutCount (natPrimitiveProof operation) = zero
  natProofCutCount natArgumentProof = zero
  natProofCutCount (natExchangeProof proof) = natProofCutCount proof
  natProofCutCount (natRotateHeadToLastProof proof) = natProofCutCount proof
  natProofCutCount (natCutProof first second) =
    suc (natProofCutCount first + natProofCutCount second)
  natProofCutCount (natPrimitiveComposeProof proof operation) =
    suc (natProofCutCount proof)

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

  embedNatProof-cut-count :
    {n : Nat} (proof : MALLPNatProof n) →
    natTheoryCutCount (embedNatProof proof) ≡ natProofCutCount proof
  embedNatProof-cut-count (natLiteralProof value) = refl
  embedNatProof-cut-count (natPrimitiveProof operation) = refl
  embedNatProof-cut-count natArgumentProof = refl
  embedNatProof-cut-count (natExchangeProof proof) =
    embedNatProof-cut-count proof
  embedNatProof-cut-count (natRotateHeadToLastProof proof) =
    embedNatProof-cut-count proof
  embedNatProof-cut-count (natPrimitiveComposeProof proof operation)
    rewrite embedNatProof-cut-count proof =
      cong suc (natPlusZeroRight (natProofCutCount proof))
  embedNatProof-cut-count (natCutProof first second)
    rewrite embedNatProof-cut-count first
          | embedNatProof-cut-count second = refl

  data NatEnvironment : Nat → Set where
    natEnvironmentNil : NatEnvironment zero
    natEnvironmentCons :
      {n : Nat} →
      Nat →
      NatEnvironment n →
      NatEnvironment (suc n)

  takeNatEnvironment :
    (n m : Nat) →
    NatEnvironment (n + m) →
    NatEnvironment n
  takeNatEnvironment zero m environment = natEnvironmentNil
  takeNatEnvironment (suc n) m (natEnvironmentCons value rest) =
    natEnvironmentCons value (takeNatEnvironment n m rest)

  dropNatEnvironment :
    (n m : Nat) →
    NatEnvironment (n + m) →
    NatEnvironment m
  dropNatEnvironment zero m environment = environment
  dropNatEnvironment (suc n) m (natEnvironmentCons value rest) =
    dropNatEnvironment n m rest

  splitNatEnvironment :
    (n m : Nat) →
    NatEnvironment (n + m) →
    NatEnvironment n × NatEnvironment m
  splitNatEnvironment n m environment =
    pair
      (takeNatEnvironment n m environment)
      (dropNatEnvironment n m environment)

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
    (natEnvironmentCons head rest) value =
      cong
        (λ parts →
          pair
            (natEnvironmentCons head (fst parts))
            (snd parts))
        (splitNatEnvironment-append n rest value)

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
    (natCutProof {n = n} {m = m} first second) environment =
    interpretMALLPNatProof second
      (natEnvironmentCons
        (interpretMALLPNatProof first (takeNatEnvironment n m environment))
        (dropNatEnvironment n m environment))

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

  -- --------------------------------------------------------------------
  -- General finite linear Nat trees.
  --
  -- The index n counts live Nat assumptions. Literal leaves consume zero
  -- resources; an argument leaf consumes exactly one; binary composition
  -- partitions n+m assumptions between its two premises. This makes
  -- duplication and discard unrepresentable in this source core.
  -- --------------------------------------------------------------------

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
    (resourceBinary {n = n} {m = m} operation left right) environment =
    applyNatOp operation
      (evalNatResourceExpr left (takeNatEnvironment n m environment))
      (evalNatResourceExpr right (dropNatEnvironment n m environment))

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

  -- The focused proof syntax is cut-admitting. A literal or owned
  -- argument is cut-free; each binary operation contributes one outer
  -- cut and one cut composing its right operand with the primitive axiom.
  natResourceExprCutCount :
    {n : Nat} → NatResourceExpr n → Nat
  natResourceExprCutCount (resourceLiteral value) = zero
  natResourceExprCutCount resourceArgument = zero
  natResourceExprCutCount (resourceBinary operation left right) =
    suc (natResourceExprCutCount left + suc (natResourceExprCutCount right))

  natResourceProof-cut-count :
    {n : Nat} (expression : NatResourceExpr n) →
    natProofCutCount (natResourceProof expression) ≡
    natResourceExprCutCount expression
  natResourceProof-cut-count (resourceLiteral value) = refl
  natResourceProof-cut-count resourceArgument = refl
  natResourceProof-cut-count
    (resourceBinary operation left right)
    rewrite natResourceProof-cut-count left
          | natResourceProof-cut-count right = refl

  natResource-proof-derivation :
    {n : Nat} →
    (expression : NatResourceExpr n) →
    MALLPNatTheory (natContext n) (just natFormula)
  natResource-proof-derivation expression =
    embedNatProof (natResourceProof expression)

  -- The embedded MALLP theory derivation has exactly the same cut count
  -- as the focused proof and the source resource tree.
  natResource-derivation-cut-count :
    {n : Nat} (expression : NatResourceExpr n) →
    natTheoryCutCount (natResource-proof-derivation expression) ≡
    natResourceExprCutCount expression
  natResource-derivation-cut-count expression =
    trans
      (embedNatProof-cut-count (natResourceProof expression))
      (natResourceProof-cut-count expression)


  natResourceClass : {n : Nat} → NatResourceExpr n → CutClass
  natResourceClass (resourceLiteral value) = cutFree
  natResourceClass resourceArgument = cutFree
  natResourceClass (resourceBinary operation left right) = cutContaining

  natResource-derivation-class :
    {n : Nat} (expression : NatResourceExpr n) →
    classifyNatTheory (natResource-proof-derivation expression) ≡
    natResourceClass expression
  natResource-derivation-class (resourceLiteral value) = refl
  natResource-derivation-class resourceArgument = refl
  natResource-derivation-class (resourceBinary operation left right) = refl
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
    rewrite natResourceProof-adequate left (takeNatEnvironment n m environment)
          | natResourceProof-adequate right (dropNatEnvironment n m environment) = refl

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

  -- --------------------------------------------------------------------
  -- Binary linear Nat primitives.
  --
  -- The two source arguments are each consumed once. The incoming stack
  -- has the second argument at its head, matching the environment order
  -- used by the MALLP primitive signature. Exchange is explicit.
  -- --------------------------------------------------------------------

  data NatBinaryLinearExpr : Set where
    natBinaryArguments : NatOp → NatBinaryLinearExpr
    natBinaryArgumentsExchanged : NatOp → NatBinaryLinearExpr

  evalNatBinaryLinearExpr : NatBinaryLinearExpr → Nat → Nat → Nat
  evalNatBinaryLinearExpr (natBinaryArguments operation) first second =
    applyNatOp operation first second
  evalNatBinaryLinearExpr
    (natBinaryArgumentsExchanged operation) first second =
      applyNatOp operation second first

  -- Addition is commutative propositionally, not by definitional reduction.
  -- The resource compiler may select the two live arguments in the opposite
  -- order; this theorem bridges that source expression to its evaluator.
  natAdd-zero-right : (value : Nat) → value + zero ≡ value
  natAdd-zero-right zero = refl
  natAdd-zero-right (suc value) =
    cong suc (natAdd-zero-right value)

  natAdd-suc-right :
    (left right : Nat) →
    left + suc right ≡ suc (left + right)
  natAdd-suc-right zero right = refl
  natAdd-suc-right (suc left) right =
    cong suc (natAdd-suc-right left right)

  natAdd-comm : (left right : Nat) → left + right ≡ right + left
  natAdd-comm zero right = sym (natAdd-zero-right right)
  natAdd-comm (suc left) right =
    trans
      (cong suc (natAdd-comm left right))
      (sym (natAdd-suc-right right left))

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

  -- The Haskell resource decoder emits SWAP SWAP for the direct source
  -- argument order: it selects each input from the labelled environment
  -- before the primitive consumes both. The two exchanges are an involution.
  execTokens-swap-involution :
    (tokens : List ForthToken) →
    (first second : Nat) →
    (stack : List Nat) →
    execTokens (swapWord ∷ swapWord ∷ tokens)
      (first ∷ second ∷ stack) ≡
    execTokens tokens (first ∷ second ∷ stack)
  execTokens-swap-involution tokens first second stack = refl

  renderNatBinaryResource : NatBinaryLinearExpr → List ForthToken
  renderNatBinaryResource (natBinaryArguments operation) =
    swapWord ∷ swapWord ∷ renderNatOp operation ∷ []
  renderNatBinaryResource (natBinaryArgumentsExchanged operation) =
    swapWord ∷ renderNatOp operation ∷ []

  natBinaryResourceMALLP-forth-sound :
    (expression : NatBinaryLinearExpr) →
    (first second : Nat) →
    {Γ : List StackType} →
    (stack : Stack Γ) →
    execTokens (renderNatBinaryResource expression)
      (forgetStack (pushCell second (pushCell first stack))) ≡
    just
      (interpretMALLPNatProof (natBinaryProof expression)
        (natEnvironmentCons second
          (natEnvironmentCons first natEnvironmentNil)) ∷
        forgetStack stack)
  natBinaryResourceMALLP-forth-sound
    (natBinaryArguments operation) first second stack =
    trans
      (execTokens-swap-involution
        (renderNatOp operation ∷ []) second first (forgetStack stack))
      (natBinaryMALLP-forth-sound
        (natBinaryArguments operation) first second stack)
  natBinaryResourceMALLP-forth-sound
    (natBinaryArgumentsExchanged operation) first second stack =
    natBinaryMALLP-forth-sound
      (natBinaryArgumentsExchanged operation) first second stack

  -- --------------------------------------------------------------------
  -- Closed PureLang lets: substitution without weakening or contraction.
  --
  -- A closed binding owns no MALLP assumptions. A zero-use binding may be
  -- skipped, and a multi-use binding may be inlined into independent copies
  -- of its closed proof. This is distinct from copying or discarding a live
  -- linear resource. The theorem is intentionally restricted to a closed
  -- Nat term; open environments need the resource-indexed judgement below
  -- this compiler layer before analogous transformations are admitted.
  -- --------------------------------------------------------------------

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

-- ----------------------------------------------------------------------
-- Pure Boolean values as additive MALLP proofs
--
-- Bool = 1 ⊕ 1. True and False are the two additive introductions; their
-- proofs consume no linear assumptions. The target uses Forth's canonical
-- TRUE/FALSE values and preserves any caller-owned residual stack.
-- ----------------------------------------------------------------------

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

  mutual
    decodeBoolForthTextToken : ForthTextToken → Maybe BoolForthToken
    decodeBoolForthTextToken textTrueWord = just pushTrueToken
    decodeBoolForthTextToken textFalseWord = just pushFalseToken
    decodeBoolForthTextToken textSwapWord = just boolSwapToken
    decodeBoolForthTextToken (textIf whenTrue whenFalse)
      with decodeBoolForthTextTokens whenTrue
         | decodeBoolForthTextTokens whenFalse
    ... | just trueTokens | just falseTokens =
      just (boolIfToken trueTokens falseTokens)
    ... | nothing | _ = nothing
    ... | just _ | nothing = nothing
    decodeBoolForthTextToken _ = nothing

    decodeBoolForthTextTokens :
      List ForthTextToken → Maybe (List BoolForthToken)
    decodeBoolForthTextTokens [] = just []
    decodeBoolForthTextTokens (token ∷ tokens)
      with decodeBoolForthTextToken token
         | decodeBoolForthTextTokens tokens
    ... | just decoded | just rest = just (decoded ∷ rest)
    ... | nothing | _ = nothing
    ... | just _ | nothing = nothing

    decodeBoolForthTextToken-roundtrip :
      (token : BoolForthToken) →
      decodeBoolForthTextToken (boolForthTokenAsText token) ≡ just token
    decodeBoolForthTextToken-roundtrip pushTrueToken = refl
    decodeBoolForthTextToken-roundtrip pushFalseToken = refl
    decodeBoolForthTextToken-roundtrip boolSwapToken = refl
    decodeBoolForthTextToken-roundtrip (boolIfToken whenTrue whenFalse)
      rewrite decodeBoolForthTextTokens-roundtrip whenTrue
            | decodeBoolForthTextTokens-roundtrip whenFalse = refl

    decodeBoolForthTextTokens-roundtrip :
      (tokens : List BoolForthToken) →
      decodeBoolForthTextTokens (mapBoolForthTokensAsText tokens) ≡ just tokens
    decodeBoolForthTextTokens-roundtrip [] = refl
    decodeBoolForthTextTokens-roundtrip (token ∷ tokens)
      rewrite decodeBoolForthTextToken-roundtrip token
            | decodeBoolForthTextTokens-roundtrip tokens = refl

  -- Interpret the exact Boolean subset of the renderer's shared text-token
  -- vocabulary. Unsupported Nat/Word64 instructions fail closed.
  execBoolTextTokens :
    List ForthTextToken → List Bool → Maybe (List Bool)
  execBoolTextTokens tokens stack
    with decodeBoolForthTextTokens tokens
  ... | nothing = nothing
  ... | just decoded = execBoolTokens decoded stack

  execBoolTextTokens-map :
    (tokens : List BoolForthToken) →
    (stack : List Bool) →
    execBoolTextTokens (mapBoolForthTokensAsText tokens) stack ≡
    execBoolTokens tokens stack
  execBoolTextTokens-map tokens stack
    rewrite decodeBoolForthTextTokens-roundtrip tokens = refl

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

  -- Residual-stack forms make the exact compiler ABI explicit: a Bool
  -- program returns one Bool at the top and leaves every caller cell intact.
  boolCaseWithResidualMALLP-forth-sound-residual :
    (condition value : Bool) →
    (residual : List Bool) →
    execBoolTokens
      (renderBoolCode compileBoolCaseWithResidual)
      (value ∷ condition ∷ residual) ≡
    just (value ∷ residual)
  boolCaseWithResidualMALLP-forth-sound-residual true value residual = refl
  boolCaseWithResidualMALLP-forth-sound-residual false value residual = refl

  boolPairSwapMALLP-forth-sound-residual :
    (first second : Bool) →
    (residual : List Bool) →
    execBoolTokens (renderBoolCode compileBoolPairSwap)
      (second ∷ first ∷ residual) ≡
    just (first ∷ second ∷ residual)
  boolPairSwapMALLP-forth-sound-residual first second residual = refl

  boolNot : Bool → Bool
  boolNot true = false
  boolNot false = true

  -- This is the exact typed Bool program generated for the admitted unary
  -- complement function. Its branches consume the condition and produce one
  -- result, leaving the residual stack untouched.
  boolInvertCaseProof : BoolCaseProof
  boolInvertCaseProof = boolCaseProof boolFalseProof boolTrueProof

  boolInvertMALLP-derivation :
    MALLP (dualPos boolFormula ∷ []) (just boolFormula)
  boolInvertMALLP-derivation =
    boolCaseMALLP-derivation boolInvertCaseProof

  boolInvertCode :
    BoolForthCode (boolCell ∷ []) (boolCell ∷ [])
  boolInvertCode = compileBoolRuntimeCase boolInvertCaseProof

  boolInvertMALLP-forth-sound-residual :
    (argument : Bool) →
    (residual : List Bool) →
    execBoolTokens (renderBoolCode boolInvertCode)
      (argument ∷ residual) ≡
    just (boolNot argument ∷ residual)
  boolInvertMALLP-forth-sound-residual true residual = refl
  boolInvertMALLP-forth-sound-residual false residual = refl

  boolProof-forth-sound-residual :
    (proof : BoolProof) →
    (residual : List Bool) →
    execBoolTokens
      (renderBoolCode (compileBoolProof proof))
      residual ≡
    just (interpretBoolProof proof ∷ residual)
  boolProof-forth-sound-residual boolTrueProof residual = refl
  boolProof-forth-sound-residual boolFalseProof residual = refl

open StrictBoolCompiler public

open StrictNatCompiler public

-- ----------------------------------------------------------------------
-- Pure Unit as the MALLP multiplicative unit
--
-- Unit is the formula 1. Its unique source value carries no target cell;
-- compiling its proof is the identity stack transition, with no emitted
-- Forth tokens and no consumption of the caller's residual stack.
-- ----------------------------------------------------------------------

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



-- ----------------------------------------------------------------------
-- Linear call-by-need state and explicit effect protocols
--
-- These are primitive *signatures over unchanged MALLP*, not additions to
-- Laurent's logical rules. A store/effect token is an ordinary linear
-- resource: every operation consumes one token and returns exactly one.
-- ----------------------------------------------------------------------

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

  -- Computation signatures are layered over MALLP. The only extra axioms
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
    -- returning the updated capability. No ambient unrestricted effect is
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

  -- --------------------------------------------------------------------
  -- A total PureLang thunk fragment with explicit call-by-need update.
  -- --------------------------------------------------------------------

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

  -- --------------------------------------------------------------------
  -- An explicit linear event protocol.
  -- --------------------------------------------------------------------

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


-- ----------------------------------------------------------------------
-- Linear closures, tensor/sum data, and finite list recursors
--
-- The proof terms below use existing MALLP introduction/elimination rules.
-- Primitive application and list runtime operations are isolated in explicit
-- MALLPProtocolTheory signatures. This does not add a recursive connective
-- to MALLP: list recursion is structural over finite Agda values.
-- ----------------------------------------------------------------------

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

  -- Γ remains present while the domain resource is abstracted. The closure
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
      highLimbBound : (highLimb < word64Radix) ≡ true
      lowLimbBound : (lowLimb < word64Radix) ≡ true
      word64Denotation :
        primWord64ToNat word ≡ highLimb * word64Radix + lowLimb
  open Word64Representation public

  word64IdentityPreservesRepresentation :
    {word : Word64} →
    (representation : Word64Representation word) →
    Word64Representation word
  word64IdentityPreservesRepresentation representation = representation

  word64Encoding :
    {word : Word64} →
    Word64Representation word →
    List Nat
  word64Encoding representation =
    highLimb representation ∷ lowLimb representation ∷ []

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


-- ----------------------------------------------------------------------
-- PRODUCTIVE CODYAD EXPONENT MACHINE
--
-- The coinductive mantissa is an opaque residual resource.  These first
-- GForth words transform only its canonical signed exponent and preserve
-- every residual cell.  Arbitrary corecursive producers need an explicit
-- finite-state producer ABI before they can be compiled as Forth code.
-- ----------------------------------------------------------------------

data CodyadForthToken : Set where
  codyadShiftLeftToken codyadShiftRightToken : CodyadForthToken

decodeCodyadicExponent : Nat → Nat → Maybe Int
decodeCodyadicExponent zero zero = just (pos zero)
decodeCodyadicExponent (suc zero) (suc n) = just (pos (suc n))
decodeCodyadicExponent (suc (suc zero)) (suc n) = just (negsuc n)
decodeCodyadicExponent _ _ = nothing

-- Top-first stack layout: magnitude :: sign :: residual.
codyadicExponentSign : Int → Nat
codyadicExponentSign (pos zero) = zero
codyadicExponentSign (pos (suc n)) = suc zero
codyadicExponentSign (negsuc n) = suc (suc zero)

codyadicExponentMagnitude : Int → Nat
codyadicExponentMagnitude (pos zero) = zero
codyadicExponentMagnitude (pos (suc n)) = suc n
codyadicExponentMagnitude (negsuc n) = suc n

codyadicExponentStack : Int → List Nat
codyadicExponentStack exponent =
  codyadicExponentMagnitude exponent ∷ codyadicExponentSign exponent ∷ []

-- A GForth cell is a positive signed Nat, so both input and result must fit
-- the target's platform-dependent maximum. The bound is explicit in the
-- machine semantics, avoiding a false unbounded-Int / bounded-cell equality.
codyadicExponentFits : Nat → Int → Bool
codyadicExponentFits bound exponent
  with natWithinBound (codyadicExponentSign exponent) bound
... | false = false
... | true = natWithinBound (codyadicExponentMagnitude exponent) bound

applyCodyadShift : CodyadForthToken → Int → Int
applyCodyadShift codyadShiftLeftToken = shiftCodyadicExponentLeft
applyCodyadShift codyadShiftRightToken = shiftCodyadicExponentRight

execCodyadToken :
  Nat → CodyadForthToken → List Nat → Maybe (List Nat)
execCodyadToken bound token (magnitude ∷ sign ∷ residual)
  with decodeInt sign magnitude
... | nothing = nothing
... | just exponent
  with codyadicExponentFits bound exponent
     | codyadicExponentFits bound (applyCodyadShift token exponent)
...   | true | true =
        just
          (codyadicExponentStack (applyCodyadShift token exponent) ++ᴳ residual)
...   | _ | _ = nothing
execCodyadToken bound token _ = nothing

execCodyadTokens :
  Nat → List CodyadForthToken → List Nat → Maybe (List Nat)
execCodyadTokens bound [] stack = just stack
execCodyadTokens bound (token ∷ tokens) stack
  with execCodyadToken bound token stack
... | nothing = nothing
... | just nextStack = execCodyadTokens bound tokens nextStack

codyadShiftLeft-forth-sound :
  (bound : Nat) (exponent : Int) (residual : List Nat) →
  codyadicExponentFits bound exponent ≡ true →
  codyadicExponentFits bound (shiftCodyadicExponentLeft exponent) ≡ true →
  execCodyadTokens bound (codyadShiftLeftToken ∷ [])
    (codyadicExponentStack exponent ++ᴳ residual) ≡
  just (codyadicExponentStack (shiftCodyadicExponentLeft exponent) ++ᴳ residual)
codyadShiftLeft-forth-sound bound exponent residual inputFits outputFits
  with codyadicExponentFits bound exponent in inputResult
     | codyadicExponentFits bound (shiftCodyadicExponentLeft exponent) in outputResult
... | true | true = refl
... | false | _ =
  ⊥-elim (natBoundFalseNotTrue (trans (sym inputResult) inputFits))
... | true | false =
  ⊥-elim (natBoundFalseNotTrue (trans (sym outputResult) outputFits))

codyadShiftRight-forth-sound :
  (bound : Nat) (exponent : Int) (residual : List Nat) →
  codyadicExponentFits bound exponent ≡ true →
  codyadicExponentFits bound (shiftCodyadicExponentRight exponent) ≡ true →
  execCodyadTokens bound (codyadShiftRightToken ∷ [])
    (codyadicExponentStack exponent ++ᴳ residual) ≡
  just (codyadicExponentStack (shiftCodyadicExponentRight exponent) ++ᴳ residual)
codyadShiftRight-forth-sound bound exponent residual inputFits outputFits
  with codyadicExponentFits bound exponent in inputResult
     | codyadicExponentFits bound (shiftCodyadicExponentRight exponent) in outputResult
... | true | true = refl
... | false | _ =
  ⊥-elim (natBoundFalseNotTrue (trans (sym inputResult) inputFits))
... | true | false =
  ⊥-elim (natBoundFalseNotTrue (trans (sym outputResult) outputFits))

codyadMalformedExponent-rejected :
  (bound : Nat) →
  execCodyadTokens bound (codyadShiftLeftToken ∷ [])
    (zero ∷ suc zero ∷ []) ≡ nothing
codyadMalformedExponent-rejected bound = refl

codyadFormula : PolType posPolarity
codyadFormula = atom⁺ 21

-- Each exponent shift consumes and returns one Codyad capability.
-- The residual mantissa producer is preserved, never copied or discarded.
codyadShiftLeftMALLP :
  MALLPProtocolTheory (dualPos codyadFormula ∷ []) (just codyadFormula)
codyadShiftLeftMALLP = protocol-logical mallp-ax

codyadShiftRightMALLP :
  MALLPProtocolTheory (dualPos codyadFormula ∷ []) (just codyadFormula)
codyadShiftRightMALLP = protocol-logical mallp-ax


-- ----------------------------------------------------------------------
-- CONDITIONAL CANONICAL FOUNDATIONS EXTRACTION
--
-- Every inhabited optimization record yields a finite canonical MALLP Nat
-- program for its already-certified candidate.  The associated PEA
-- RegisterProgram is preserved as code with soundness/completeness evidence;
-- this module does not claim a universal register-machine-to-Forth compiler.
-- ----------------------------------------------------------------------

module CanonicalFoundationsExtraction (Atom : Nat → Set) where

  module Optimization = UnifiedFoundationsOptimization Atom

  record CanonicalMALLPProgram (value : Nat) : Set where
    field
      canonicalCode : ForthCode [] (natCell ∷ [])
      canonicalDerivation : MALLPNatTheory [] (just natFormula)
      canonicalCodeTokens :
        renderForth canonicalCode ≡ pushLiteral value ∷ []
      canonicalExecution :
        execTokens (renderForth canonicalCode) [] ≡ just (value ∷ [])
  open CanonicalMALLPProgram public

  canonicalMALLPProgram : (value : Nat) → CanonicalMALLPProgram value
  canonicalMALLPProgram value = record
    { canonicalCode = compileNat (literal value)
    ; canonicalDerivation =
        natResource-proof-derivation (resourceLiteral value)
    ; canonicalCodeTokens = refl
    ; canonicalExecution =
        renderForth-sound (compileNat (literal value)) emptyStack
    }

  record ExtractedOptimizationProgram
      {candidateFamily : ParametricallyEnumerable}
      {H G : Category}
      {productsH : FiniteProducts H}
      {productsG : FiniteProducts G}
      {ℓ : Level} {R : Set}
      (optimization :
        Optimization.DynamicProgrammingMALLPOptimization
          candidateFamily H G productsH productsG ℓ R)
      : Set₁ where
    field
      canonicalEnumeratorCode : ProgramCode
      canonicalEnumeratorCodeIsPEA :
        canonicalEnumeratorCode ≡
          parametricCode
            (Optimization.positiveEnumerability optimization)
            candidateFamily
            (Optimization.candidateParameter optimization)
      selectedCandidateFeasible :
        Predicate candidateFamily
          (Optimization.candidateParameter optimization)
          (Optimization.candidate optimization)
      selectedCandidateProgram :
        CanonicalMALLPProgram (Optimization.candidate optimization)
      selectedCandidateOptimal :
        OptimalSelection
          (Optimization.valueOrder optimization)
          (backwardInduction
            (Optimization.finiteHorizon optimization)
            (Optimization.finiteSelection optimization))
      normalizedBellmanBaseIsCutFree :
        hasCut (Optimization.normalizedBellmanBase optimization) ≡ false
      normalizedBellmanStepIsCutFree :
        hasCut (Optimization.normalizedBellmanStep optimization) ≡ false
      finiteDPAgreesWithSBR :
        Optimization.finiteDynamicProgrammingValue optimization ≡
          Optimization.barValue optimization
  open ExtractedOptimizationProgram public

  extractOptimization :
    {candidateFamily : ParametricallyEnumerable}
    {H G : Category}
    {productsH : FiniteProducts H}
    {productsG : FiniteProducts G}
    {ℓ : Level} {R : Set} →
    (optimization :
      Optimization.DynamicProgrammingMALLPOptimization
        candidateFamily H G productsH productsG ℓ R) →
    ExtractedOptimizationProgram optimization
  extractOptimization optimization = record
    { canonicalEnumeratorCode =
        parametricCode
          (Optimization.positiveEnumerability optimization)
          candidateFamily (Optimization.candidateParameter optimization)
    ; canonicalEnumeratorCodeIsPEA = refl
    ; selectedCandidateFeasible =
        Optimization.optimizationCandidateFeasible optimization
    ; selectedCandidateProgram =
        canonicalMALLPProgram (Optimization.candidate optimization)
    ; selectedCandidateOptimal =
        Optimization.finiteOptimizationOptimal optimization
    ; normalizedBellmanBaseIsCutFree =
        Optimization.normalizedBellmanBase-cutFree optimization
    ; normalizedBellmanStepIsCutFree =
        Optimization.normalizedBellmanStep-cutFree optimization
    ; finiteDPAgreesWithSBR =
        Optimization.finiteDynamicProgrammingAgreesWithSBR optimization
    }

  -- Uniform bounded extraction for the full PEA family interface, not
  -- merely the analytic submodel.  Every finite stage is evaluated by the
  -- same PEA-selected register program.  A hit carries a feasibility proof
  -- and a canonical finite MALLP literal program.
  extractPEACandidateAtStage :
    (family : ParametricallyEnumerable) (parameter stage : Nat) →
    Maybe
      (Σ Nat
        (λ candidate →
          Predicate family parameter candidate × CanonicalMALLPProgram candidate))
  extractPEACandidateAtStage family parameter stage
    with universalEval
      (parametricCode parametricEA family parameter) stage in evaluation
  ... | nothing = nothing
  ... | just candidate =
    just
      ( candidate
      , pair
          (parametricCode-sound
            parametricEA family parameter stage candidate evaluation)
          (canonicalMALLPProgram candidate)
      )

  -- A finite fuel bound gives a structurally terminating search.  The
  -- search reports a miss when the witness has not appeared yet; it never
  -- turns nontermination or non-inhabitation into a fabricated result.
  searchPEACandidateWithin :
    (fuel : Nat) (family : ParametricallyEnumerable) (parameter : Nat) →
    Maybe
      (Σ Nat
        (λ candidate →
          Predicate family parameter candidate × CanonicalMALLPProgram candidate))
  searchPEACandidateWithin zero family parameter = nothing
  searchPEACandidateWithin (suc fuel) family parameter
    with searchPEACandidateWithin fuel family parameter
  ... | just found = just found
  ... | nothing = extractPEACandidateAtStage family parameter fuel

  extractAnalyticCandidateAtStage :
    (family : AnalyticEnumerableFamily) (parameter stage : Nat) →
    Maybe
      (Σ Nat
        (λ candidate →
          (analyticPredicate family parameter candidate) ×
          CanonicalMALLPProgram candidate))
  extractAnalyticCandidateAtStage family parameter stage
    with universalEval (analyticCode family parameter) stage in evaluation
  ... | nothing = nothing
  ... | just candidate =
    just
      ( candidate
      , pair
          (analytic-sound family parameter stage candidate
            (trans
              (sym (analyticCode-correct family parameter stage))
              evaluation))
          (canonicalMALLPProgram candidate)
      )

  emptyParametricallyEnumerable : ParametricallyEnumerable
  emptyParametricallyEnumerable = record
    { Predicate = λ _ _ → ⊥
    ; enumerate = λ _ _ → nothing
    ; enumerate-sound = λ i stage value ()
    ; enumerate-complete = λ i value ()
    }

  noUniformFeasibleCandidate :
    ((family : ParametricallyEnumerable) →
      (parameter : Nat) →
      Σ Nat (λ candidate → Predicate family parameter candidate)) →
    ⊥
  noUniformFeasibleCandidate choose
    with choose emptyParametricallyEnumerable zero
  ... | candidate , impossible = impossible


-- ----------------------------------------------------------------------
-- Executable witnesses for the assumed symmetric bar-recursion equations.
--
-- A constant-zero control functional reaches its bar after at most one
-- extension: an initial map either contains key zero already, or the first
-- extension inserts it. These examples force both registered rewrite rules
-- to participate in Agda conversion, including step followed by stop.
-- ----------------------------------------------------------------------

constantZeroOmega : {X : Set} → (Nat → X) → Nat
constantZeroOmega stream = zero

constantZeroBarCondition :
  {X : Set} →
  (default : X) →
  SymmetricBarCondition constantZeroOmega default
constantZeroBarCondition default initial alpha
  with memberKey zero (mapEntries initial) in zeroPresent
... | true = zero , zeroPresent
... | false =
  suc zero ,
  omegaThread-step-zero default alpha initial zero

zeroKeyMap : {X : Set} → X → PartialMap X
zeroKeyMap value =
  partialMap
    (pair zero value ∷ [])
    (unique-cons refl unique-empty)

symmetricBarRec-stop-computes :
  {X R : Set} →
  (default : X) →
  (base : PartialMap X → R) →
  (step : PartialMap X → (X → R) → R) →
  (value : X) →
  symmetricBarRec constantZeroOmega default
    (constantZeroBarCondition default)
    base step
    (zeroKeyMap value) zero
    (inDomain refl)
  ≡ base (zeroKeyMap value)
symmetricBarRec-stop-computes default base step value = refl

symmetricBarRec-step-then-stop-computes :
  {X R : Set} →
  (default : X) →
  (base : PartialMap X → R) →
  (step : PartialMap X → (X → R) → R) →
  symmetricBarRec constantZeroOmega default
    (constantZeroBarCondition default)
    base step
    emptyMap zero
    (outDomain refl)
  ≡
  step emptyMap
    (λ value → base (zeroKeyMap value))
symmetricBarRec-step-then-stop-computes default base step = refl


-- A one-step selection is an instance of the SBR step/stop equations.
-- The continuation records the payoff of each newly threaded value, and
-- the step algebra selects exactly the value chosen by the selection map.
symmetricBarRec-selection-one-step :
  {X R : Set} →
  (default : X) →
  (choose : Selection X R) →
  (payoff : X → R) →
  symmetricBarRec constantZeroOmega default
    (constantZeroBarCondition default)
    (λ entries → payoff (streamOf (mapEntries entries) default zero))
    (λ entries continuation → selectedOutcome choose continuation)
    emptyMap zero (outDomain refl)
  ≡ selectedOutcome choose payoff
symmetricBarRec-selection-one-step default choose payoff = refl



-- ```
