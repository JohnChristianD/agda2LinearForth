{-# OPTIONS --lossy-unification --rewriting --confluence-check --no-prop --exact-split --guardedness --no-projection-like --experimental-lazy-instances --no-fast-reduce --no-postfix-projections #-}

-- Single-source-of-truth constructive specification for agda2LinearForth.
--
-- This module combines descriptor/ownership invariants, weakest-precondition
-- semantics, checked stack effects, allocation/exception contracts, denotational
-- models, and a semantic mirror of the compiler/runtime boundary.
-- The proof terms
-- below establish properties of this Agda model. They do not, by themselves,
-- establish that arbitrary Haskell or Forth implementations refine it.
module LinearModalSafety where
  
  open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
  open import Agda.Builtin.Bool using (Bool; true; false)
  open import Agda.Builtin.Equality using (_≡_; refl)
  open import Agda.Builtin.Equality.Rewrite

  -- Runtime/source ownership tags used by the compiler denotation.
  -- These are not Laurent polarity shifts or Seely exponentials.
  data SourceMode : Set where
    linear modal : SourceMode
  
  -- Single-file constructive cores. These nested modules replace three separately
  -- checked source files while retaining their original module boundaries.
  module VerifiedCoreExecutable where
    
    open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)
    open import Agda.Builtin.Bool using (Bool; true; false)
    
    -- Number of successors available versus observation depth.
    -- The conatural model proves this agrees with observing finiteCoNat.
    finiteObservation : Nat → Nat → Bool
    finiteObservation available depth = depth < available
    
    infiniteObservation : Nat → Bool
    infiniteObservation depth = true
    
    pow2 : Nat → Nat
    pow2 zero = suc zero
    pow2 (suc n) = pow2 n * suc (suc zero)
    
  
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
    open VerifiedCoreExecutable using (finiteObservation; infiniteObservation; pow2)
    
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
  
  module SovereignRationalSED where
    
    open import Agda.Builtin.Nat using (Nat; zero; suc)
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
              (λ i n → P n) (λ i → double-negated) zero)
    
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
          [_] : {A : Set} {R : A → A → Set}
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
            (x : A) → [ canonize {A} {R} {rflR} {symR} {transR} x ] ≡
                       [ x ]
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
        denoteQuotient (rawₑ x) = [ x ]
        denoteQuotient (canonicalizedₑ x) = [ canonize x ]
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
        quotient-raw-sound x = sym (quotient-canon x)
    
        quotient-class-canon-sound :
          {A : Set} {R : A → A → Set}
          {rflR : (x : A) → R x x}
          {symR : {x y : A} → R x y → R y x}
          {transR : {x y z : A} → R x y → R y z → R x z} →
          (x : A) →
          denoteQuotient (classₑ (canonicalizedₑ x)) ≡
          denoteQuotient (classₑ (rawₑ x))
        quotient-class-canon-sound x = quotient-canon x
    
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
        decideDomain entries key with memberKey key (mapEntries entries) in keyMembership
        ... | true = inDomain keyMembership
        ... | false = outDomain keyMembership
    
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
          (mapEntries entries) in keyMembership
        ...   | true = entries
        ...   | false =
          extendFresh entries
            (omega (streamOf (mapEntries entries) default))
            keyMembership
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
    -- MODULE 2: RATIONAL SED GEOMETRY AND MOMENTUM INTERFACES
    --
    -- This module deliberately does not open/import Foundations.  The seven
    -- foundational packages above therefore do not become hidden dependencies of the
    -- physical model.
    ------------------------------------------------------------------------
    
    -- Equality on the carrier is Agda's builtin intensional equality.  A concrete
    -- rational instance must therefore use canonical representatives; there is
    -- no additional rational-equality relation or setoid parameter here.
  module CoreDenotation where
    data DList (A : Set) : Set where
      dnil : DList A
      dcons : A → DList A → DList A
    
    appendD : {A : Set} → DList A → DList A → DList A
    appendD dnil ys = ys
    appendD (dcons x xs) ys = dcons x (appendD xs ys)
    
    lengthD : {A : Set} → DList A → Nat
    lengthD dnil = zero
    lengthD (dcons x xs) = suc (lengthD xs)
    
    natEq : Nat → Nat → Bool
    natEq zero zero = true
    natEq zero (suc y) = false
    natEq (suc x) zero = false
    natEq (suc x) (suc y) = natEq x y
    
    mutual
      data Term : Set where
        tNat : Nat → Term
        tBool : Bool → SourceMode → Term
        tUnit : Term
        tVar : Nat → Term
        tLambda : Term → Term
        tApply : Term → Term → Term
        tAdd : Term → Term → Term
        tSub : Term → Term → Term
        tMul : Term → Term → Term
        tQuot : Term → Term → Term
        tRem : Term → Term → Term
        tMonus : Term → Term → Term
        tEqual : Term → Term → Term
        tGeq : Term → Term → Term
        tLt : Term → Term → Term
        tIf : Term → Term → Term → Term
        tConstruct : Nat → DList Term → Term
        tMatch : Term → Nat → Nat → Term → Term → Term
        tRaise : RuntimeError → Term
        tCatch : Term → Term → Term
        tPackResult : Term → Term
        tUnpackResult : Term → Term
        tPrint : Term → Term
    
      data Value : Set where
        vNat : Nat → SourceMode → Value
        vBool : Bool → SourceMode → Value
        vUnit : Value
        vClosure : DList Value → Term → Value
        vConstructed : Nat → DList Value → Value
        vResult : Value → Value
        vError : RuntimeError → Value
    
    Env : Set
    Env = DList Value
    
    data Event : Set where
      observed : Value → Event
    
    -- The denotation preserves observable output and distinguishes normal return,
    -- a language-level exception, and exhaustion of the evaluator's finite fuel.
    data Outcome : Set where
      returned : Value → DList Event → Outcome
      raised : RuntimeError → DList Event → Outcome
      outOfFuel : DList Event → Outcome
    
    data ValuesOutcome : Set where
      valuesReturned : DList Value → DList Event → ValuesOutcome
      valuesRaised : RuntimeError → DList Event → ValuesOutcome
      valuesOutOfFuel : DList Event → ValuesOutcome
    
    prefixOutcome : DList Event → Outcome → Outcome
    prefixOutcome trace (returned value later) =
      returned value (appendD trace later)
    prefixOutcome trace (raised err later) =
      raised err (appendD trace later)
    prefixOutcome trace (outOfFuel later) = outOfFuel (appendD trace later)
    
    prefixValues : DList Event → ValuesOutcome → ValuesOutcome
    prefixValues trace (valuesReturned values later) =
      valuesReturned values (appendD trace later)
    prefixValues trace (valuesRaised err later) =
      valuesRaised err (appendD trace later)
    prefixValues trace (valuesOutOfFuel later) =
      valuesOutOfFuel (appendD trace later)
    
    bindOutcome : Outcome → (Value → Outcome) → Outcome
    bindOutcome (returned value trace) next =
      prefixOutcome trace (next value)
    bindOutcome (raised err trace) next = raised err trace
    bindOutcome (outOfFuel trace) next = outOfFuel trace
    
    combineOutcome :
      Outcome → Outcome → (Value → Value → Outcome) → Outcome
    combineOutcome (returned left leftTrace) second operation with second
    ... | returned right rightTrace =
      prefixOutcome (appendD leftTrace rightTrace) (operation left right)
    ... | raised err rightTrace = raised err (appendD leftTrace rightTrace)
    ... | outOfFuel rightTrace = outOfFuel (appendD leftTrace rightTrace)
    combineOutcome (raised err trace) second operation = raised err trace
    combineOutcome (outOfFuel trace) second operation = outOfFuel trace
    
    data MaybeValue : Set where
      missing : MaybeValue
      found : Value → MaybeValue
    
    lookupEnv : Nat → Env → MaybeValue
    lookupEnv zero dnil = missing
    lookupEnv zero (dcons value rest) = found value
    lookupEnv (suc index) dnil = missing
    lookupEnv (suc index) (dcons value rest) = lookupEnv index rest
    
    addValues : Value → Value → Outcome
    addValues (vNat x leftMode) (vNat y rightMode) =
      returned (vNat (x + y) (joinSourceMode leftMode rightMode)) dnil
    addValues _ _ = raised wrongKind dnil
    
    subValues : Value → Value → Outcome
    subValues (vNat x leftMode) (vNat y rightMode) =
      returned (vNat (bridgeNatSub x y) (joinSourceMode leftMode rightMode)) dnil
    subValues _ _ = raised wrongKind dnil
    
    mulValues : Value → Value → Outcome
    mulValues (vNat x leftMode) (vNat y rightMode) =
      returned (vNat (bridgeNatMul x y) (joinSourceMode leftMode rightMode)) dnil
    mulValues _ _ = raised wrongKind dnil
    
    quotValues : Value → Value → Outcome
    quotValues (vNat x leftMode) (vNat y rightMode)
      with bridgeNatDivMod x y
    ... | bridgeDivisionByZero = raised arithmeticDomainError dnil
    ... | bridgeDivisionResult quotient remainder =
      returned (vNat quotient (joinSourceMode leftMode rightMode)) dnil
    quotValues _ _ = raised wrongKind dnil
    
    remValues : Value → Value → Outcome
    remValues (vNat x leftMode) (vNat y rightMode)
      with bridgeNatDivMod x y
    ... | bridgeDivisionByZero = raised arithmeticDomainError dnil
    ... | bridgeDivisionResult quotient remainder =
      returned (vNat remainder (joinSourceMode leftMode rightMode)) dnil
    remValues _ _ = raised wrongKind dnil
    
    equalValues : Value → Value → Outcome
    equalValues (vNat x leftMode) (vNat y rightMode) =
      returned (vBool (natEq x y) (joinSourceMode leftMode rightMode)) dnil
    equalValues _ _ = raised wrongKind dnil
    
    geqValues : Value → Value → Outcome
    geqValues (vNat x leftMode) (vNat y rightMode) =
      returned (vBool (bridgeNatGeq x y) (joinSourceMode leftMode rightMode)) dnil
    geqValues _ _ = raised wrongKind dnil
    
    ltValues : Value → Value → Outcome
    ltValues (vNat x leftMode) (vNat y rightMode) =
      returned (vBool (bridgeNatLt x y) (joinSourceMode leftMode rightMode)) dnil
    ltValues _ _ = raised wrongKind dnil
    
    monusValues : Value → Value → Outcome
    monusValues = subValues
    
    unwrapValue : Value → Outcome
    unwrapValue (vResult value) = returned value dnil
    unwrapValue _ = raised wrongKind dnil
    
    mutual
      -- Fuel bounds recursive evaluation depth. It makes the denotation total
      -- without assuming normalization for arbitrary recursive or user Forth code.
      eval : Nat → Env → Term → Outcome
      evalList : Nat → Env → DList Term → ValuesOutcome
      matchOutcome : Nat → Env → Nat → Nat → Term → Term → Outcome → Outcome
      catchOutcome : Nat → Env → Term → Outcome → Outcome
    
      eval zero env term = outOfFuel dnil
      eval (suc fuel) env (tNat n) = returned (vNat n modal) dnil
      eval (suc fuel) env (tBool b mode) = returned (vBool b mode) dnil
      eval (suc fuel) env tUnit = returned vUnit dnil
      eval (suc fuel) env (tVar index) with lookupEnv index env
      ... | missing = raised unknownPrimitive dnil
      ... | found value = returned value dnil
      eval (suc fuel) env (tLambda body) = returned (vClosure env body) dnil
    
      eval (suc fuel) env (tApply function argument)
        with eval fuel env function | eval fuel env argument
      ... | returned (vClosure captured body) functionTrace
          | returned value argumentTrace =
        prefixOutcome (appendD functionTrace argumentTrace)
          (eval fuel (dcons value captured) body)
      ... | raised err trace | _ = raised err trace
      ... | outOfFuel trace | _ = outOfFuel trace
      ... | returned _ functionTrace | raised err argumentTrace =
        raised err (appendD functionTrace argumentTrace)
      ... | returned _ functionTrace | outOfFuel argumentTrace =
        outOfFuel (appendD functionTrace argumentTrace)
      ... | returned _ functionTrace | returned _ argumentTrace =
        raised wrongKind (appendD functionTrace argumentTrace)
    
      eval (suc fuel) env (tAdd left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) addValues
      eval (suc fuel) env (tSub left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) subValues
      eval (suc fuel) env (tMul left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) mulValues
      eval (suc fuel) env (tQuot left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) quotValues
      eval (suc fuel) env (tRem left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) remValues
      eval (suc fuel) env (tMonus left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) monusValues
      eval (suc fuel) env (tEqual left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) equalValues
      eval (suc fuel) env (tGeq left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) geqValues
      eval (suc fuel) env (tLt left right) =
        combineOutcome (eval fuel env left) (eval fuel env right) ltValues
    
      eval (suc fuel) env (tIf condition yes no) with eval fuel env condition
      ... | returned (vBool true mode) trace = prefixOutcome trace (eval fuel env yes)
      ... | returned (vBool false mode) trace = prefixOutcome trace (eval fuel env no)
      ... | returned value trace = raised wrongKind trace
      ... | raised err trace = raised err trace
      ... | outOfFuel trace = outOfFuel trace
    
      eval (suc fuel) env (tConstruct tag fields) with evalList fuel env fields
      ... | valuesReturned values trace = returned (vConstructed tag values) trace
      ... | valuesRaised err trace = raised err trace
      ... | valuesOutOfFuel trace = outOfFuel trace
    
      eval (suc fuel) env (tMatch scrutinee expectedTag expectedArity matched fallback) =
        matchOutcome fuel env expectedTag expectedArity matched fallback
          (eval fuel env scrutinee)
    
      eval (suc fuel) env (tRaise err) = raised err dnil
      eval (suc fuel) env (tCatch body handler) =
        catchOutcome fuel env handler (eval fuel env body)
    
      eval (suc fuel) env (tPackResult term) =
        bindOutcome (eval fuel env term) (λ value → returned (vResult value) dnil)
      eval (suc fuel) env (tUnpackResult term) =
        bindOutcome (eval fuel env term) unwrapValue
    
      eval (suc fuel) env (tPrint term) with eval fuel env term
      ... | returned value trace =
        returned value (appendD trace (dcons (observed value) dnil))
      ... | raised err trace = raised err trace
      ... | outOfFuel trace = outOfFuel trace
    
      evalList zero env terms = valuesOutOfFuel dnil
      evalList (suc fuel) env dnil = valuesReturned dnil dnil
      evalList (suc fuel) env (dcons term terms) with eval fuel env term
      ... | raised err trace = valuesRaised err trace
      ... | outOfFuel trace = valuesOutOfFuel trace
      ... | returned value trace with evalList fuel env terms
      ...   | valuesReturned values later =
        valuesReturned (dcons value values) (appendD trace later)
      ...   | valuesRaised err later = valuesRaised err (appendD trace later)
      ...   | valuesOutOfFuel later = valuesOutOfFuel (appendD trace later)
    
      matchOutcome fuel env expectedTag expectedArity matched fallback
        (returned (vConstructed actualTag fields) trace)
        with natEq actualTag expectedTag | natEq (lengthD fields) expectedArity
      ... | true | true =
        prefixOutcome trace (eval fuel (appendD fields env) matched)
      ... | _ | _ = prefixOutcome trace (eval fuel env fallback)
      matchOutcome fuel env expectedTag expectedArity matched fallback
        (returned value trace) = prefixOutcome trace (eval fuel env fallback)
      matchOutcome fuel env expectedTag expectedArity matched fallback
        (raised err trace) = raised err trace
      matchOutcome fuel env expectedTag expectedArity matched fallback
        (outOfFuel trace) = outOfFuel trace
    
      catchOutcome fuel env handler (returned value trace) = returned value trace
      catchOutcome fuel env handler (outOfFuel trace) = outOfFuel trace
      catchOutcome fuel env handler (raised err trace) =
        prefixOutcome trace (eval fuel (dcons (vError err) env) handler)
    
    -- Constructive equations for representative backend forms. These prove the
    -- denotation's equations; concrete compiler/runtime refinement is a separate
    -- simulation obligation and is not implied by these equations.
    
    naturalLiteralDenotesItsValue :
      (n fuel : Nat) (env : Env) →
      eval (suc fuel) env (tNat n) ≡ returned (vNat n modal) dnil
    naturalLiteralDenotesItsValue n fuel env = refl
    
    additionIsCompositional :
      (left right : Nat) →
      eval (suc (suc zero)) dnil (tAdd (tNat left) (tNat right)) ≡
      returned (vNat (left + right) modal) dnil
    additionIsCompositional left right = refl
    
    -- The evaluator prefixes the selected branch's trace. Prove the neutral-trace
    -- law explicitly rather than assuming it is definitional for an unknown outcome.
    prefixOutcomeIdentity : (outcome : Outcome) → prefixOutcome dnil outcome ≡ outcome
    prefixOutcomeIdentity (returned value trace) = refl
    prefixOutcomeIdentity (raised err trace) = refl
    prefixOutcomeIdentity (outOfFuel trace) = refl
    
    conditionalSelectsItsTrueBranch :
      (yes no : Term) →
      eval (suc (suc zero)) dnil (tIf (tBool true modal) yes no) ≡ eval (suc zero) dnil yes
    conditionalSelectsItsTrueBranch yes no =
      prefixOutcomeIdentity (eval (suc zero) dnil yes)
    
    quotientByZeroRaises :
      (numerator : Nat) →
      eval (suc (suc zero)) dnil (tQuot (tNat numerator) (tNat zero)) ≡
      raised arithmeticDomainError dnil
    quotientByZeroRaises numerator = refl
    
    betaReductionForIdentity :
      (n : Nat) →
      eval (suc (suc (suc zero))) dnil
        (tApply (tLambda (tVar zero)) (tNat n)) ≡ returned (vNat n modal) dnil
    betaReductionForIdentity n = refl
    
    constructorMatcherSelectsAndBindsFields :
      eval (suc (suc (suc (suc zero)))) dnil
        (tMatch (tConstruct 3 (dcons (tNat 42) dnil)) 3 1 (tVar zero) (tNat zero)) ≡
      returned (vNat 42 modal) dnil
    constructorMatcherSelectsAndBindsFields = refl
    
    resultPackUnpackRoundTrips :
      (n : Nat) →
      eval (suc (suc (suc zero))) dnil (tUnpackResult (tPackResult (tNat n))) ≡
      returned (vNat n modal) dnil
    resultPackUnpackRoundTrips n = refl
    
    printPreservesTheValueAndRecordsAnEvent :
      (n : Nat) →
      eval (suc (suc zero)) dnil (tPrint (tNat n)) ≡
      returned (vNat n modal) (dcons (observed (vNat n modal)) dnil)
    printPreservesTheValueAndRecordsAnEvent n = refl
    
    catchRunsItsHandlerWithTheErrorValue :
      eval (suc (suc zero)) dnil
        (tCatch (tRaise arithmeticDomainError) (tVar zero)) ≡
      returned (vError arithmeticDomainError) dnil
    catchRunsItsHandlerWithTheErrorValue = refl
    
  
  
  -- Recovered from PR #7: scalar denotation with explicit bottom and errors.
  -- Kept separate from CoreDenotation because finite fuel exhaustion and
  -- denotational divergence are different observations. The flat preorder is a
  -- Scott-style partial-order ingredient; this module does not claim to build
  -- a complete domain for unrestricted Forth.
  module ScottScalarDenotation where
  
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
  
    -- Three observable outcomes: divergence, successful return, and THROW.
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
  
    natMinus : Nat → Nat → Nat
    natMinus x zero = x
    natMinus zero (suc y) = zero
    natMinus (suc x) (suc y) = natMinus x y
  
    -- Fuel bounds repeated subtraction, avoiding axioms about division.
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
  
    -- The target cell bound is a parameter, not a hard-coded machine width.
    denoteBinary :
      Nat → NumericOp → Value → Value → Computation Value
    denoteBinary bound op (natValue x mx) (natValue y my)
      with natLe x bound | natLe y bound
    ... | yes | yes =
      mapComputation (meaningValue (joinSourceMode mx my))
        (numericMeaning bound op x y)
    ... | _ | _ = throws arithmeticOverflowError
    denoteBinary bound op _ _ = throws wrongKind
  
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
  
    everyPrimitiveHasProfile : (p : Primitive) → PrimitiveSpec p
    everyPrimitiveHasProfile = specifiesEveryPrimitive
  
    -- The fixed emitter erases the source mode. Both modalities map to the same
    -- cell, so a decoder cannot reconstruct both original modes correctly.
    erasedModeCell : SourceMode → Nat
    erasedModeCell _ = zero
  
    symDenotation : {A : Set} {x y : A} → x ≡ y → y ≡ x
    symDenotation refl = refl
  
    transDenotation : {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transDenotation refl q = q
  
    linearIsNotModal : linear ≡ modal → ⊥
    linearIsNotModal ()
  
    noRuntimeModeDecoder :
      (decode : Nat → SourceMode) →
      decode (erasedModeCell linear) ≡ linear →
      decode (erasedModeCell modal) ≡ modal →
      ⊥
    noRuntimeModeDecoder decode linearCorrect modalCorrect =
      linearIsNotModal
        (transDenotation (symDenotation linearCorrect) modalCorrect)
  
   
  -- Abstract account of the checked allocator's identity-exhaustion boundary.
  -- arenaCursor and metadataCount abstract HERE and the metadata-list mutation.
  module ABIAllocationWP where
  
    natLessBool : Nat → Nat → Bool
    natLessBool zero zero = false
    natLessBool zero (suc y) = true
    natLessBool (suc x) zero = false
    natLessBool (suc x) (suc y) = natLessBool x y
  
    natAtMost : Nat → Nat → Bool
    natAtMost n bound = natLessBool n (suc bound)
  
    natLessThanZero : (n : Nat) → natLessBool n zero ≡ false
    natLessThanZero zero = refl
    natLessThanZero (suc n) = refl
  
    natLessThanAfterPositiveAddition :
      (n k : Nat) → natLessBool (n + suc k) (suc n) ≡ false
    natLessThanAfterPositiveAddition zero k = natLessThanZero k
    natLessThanAfterPositiveAddition (suc n) k =
      natLessThanAfterPositiveAddition n k
  
    natAtMostAfterPositiveAddition :
      (n k : Nat) → natAtMost (n + suc k) n ≡ false
    natAtMostAfterPositiveAddition n k =
      natLessThanAfterPositiveAddition n k
  
    record AllocationState : Set where
      constructor allocationState
      field
        arenaCursor : Nat
        nextIdentity : Nat
        metadataCount : Nat
    open AllocationState public
  
    data AllocationOutcome : Set where
      allocationFailed : RuntimeError → AllocationState → AllocationOutcome
      allocationSucceeded : AllocationState → AllocationOutcome
  
    -- identityBound is ABI-MAX-NAT. identityCount/cellCount describe the
    -- complete preflighted allocation group. Failure leaves state untouched.
    allocationAfterCapacityCheck :
      Bool → Nat → Nat → Nat → AllocationState → AllocationOutcome
    allocationAfterCapacityCheck false identityBound identityCount cellCount state =
      allocationFailed identityOverflowError state
    allocationAfterCapacityCheck true identityBound identityCount cellCount state =
      allocationSucceeded
        (allocationState
          (arenaCursor state + cellCount)
          (nextIdentity state + identityCount)
          (metadataCount state + identityCount))
  
    allocateBlock :
      Nat → Nat → Nat → AllocationState → AllocationOutcome
    allocateBlock identityBound identityCount cellCount state =
      allocationAfterCapacityCheck
        (natAtMost (nextIdentity state + identityCount) identityBound)
        identityBound identityCount cellCount state
  
    AllocationPost :
      (normal : AllocationState → Set) →
      (exceptional : RuntimeError → AllocationState → Set) →
      AllocationOutcome → Set
    AllocationPost normal exceptional (allocationFailed err state) =
      exceptional err state
    AllocationPost normal exceptional (allocationSucceeded state) =
      normal state
  
    wpAllocateBlock :
      (identityBound identityCount cellCount : Nat) →
      (state : AllocationState) →
      (normal : AllocationState → Set) →
      (exceptional : RuntimeError → AllocationState → Set) → Set
    wpAllocateBlock identityBound identityCount cellCount state normal exceptional =
      AllocationPost normal exceptional
        (allocateBlock identityBound identityCount cellCount state)
  
    identityExhaustionIsAtomic :
      (identityBound remainingIds cellCount : Nat) →
      {state : AllocationState} →
      nextIdentity state ≡ identityBound →
      allocateBlock identityBound (suc remainingIds) cellCount state ≡
        allocationFailed identityOverflowError state
    identityExhaustionIsAtomic identityBound remainingIds cellCount {state}
      identityAtLimit
      rewrite identityAtLimit
            | natAtMostAfterPositiveAddition identityBound remainingIds = refl
  
    identityExhaustionSatisfiesWP :
      (identityBound remainingIds cellCount : Nat) →
      (state : AllocationState) →
      nextIdentity state ≡ identityBound →
      (normal : AllocationState → Set) →
      (exceptional : RuntimeError → AllocationState → Set) →
      exceptional identityOverflowError state →
      wpAllocateBlock identityBound (suc remainingIds) cellCount state
        normal exceptional
    identityExhaustionSatisfiesWP identityBound remainingIds cellCount state
      identityAtLimit normal exceptional exceptionalProof
      rewrite identityAtLimit
            | natAtMostAfterPositiveAddition identityBound remainingIds = exceptionalProof
  
    -- The runtime's makeTHUNK rejects a null execution token before allocating
    -- the handle or metadata cells. This is the Agda counterpart of the zero-page
    -- trap guard, separate from identity exhaustion.
    data ExecutionToken : Set where
      nullExecutionToken : ExecutionToken
      nonNullExecutionToken : Nat → ExecutionToken
  
    allocateThunk :
      ExecutionToken → Nat → Nat → Nat → AllocationState → AllocationOutcome
    allocateThunk nullExecutionToken identityBound identityCount cellCount state =
      allocationFailed nullExecutionTokenError state
    allocateThunk (nonNullExecutionToken token) identityBound identityCount cellCount state =
      allocateBlock identityBound identityCount cellCount state
  
    wpAllocateThunk :
      ExecutionToken → Nat → Nat → Nat → AllocationState →
      (normal : AllocationState → Set) →
      (exceptional : RuntimeError → AllocationState → Set) → Set
    wpAllocateThunk token identityBound identityCount cellCount state normal exceptional =
      AllocationPost normal exceptional
        (allocateThunk token identityBound identityCount cellCount state)
  
    nullExecutionTokenRejectedAtomically :
      (identityBound identityCount cellCount : Nat) →
      (state : AllocationState) →
      allocateThunk nullExecutionToken identityBound identityCount cellCount state ≡
        allocationFailed nullExecutionTokenError state
    nullExecutionTokenRejectedAtomically identityBound identityCount cellCount state = refl
  
    nullExecutionTokenSatisfiesWP :
      (identityBound identityCount cellCount : Nat) →
      (state : AllocationState) →
      (normal : AllocationState → Set) →
      (exceptional : RuntimeError → AllocationState → Set) →
      exceptional nullExecutionTokenError state →
      wpAllocateThunk nullExecutionToken identityBound identityCount cellCount
        state normal exceptional
    nullExecutionTokenSatisfiesWP identityBound identityCount cellCount state
      normal exceptional exceptionalProof = exceptionalProof
  
