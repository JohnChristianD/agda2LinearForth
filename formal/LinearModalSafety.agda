{-# OPTIONS --lossy-unification --rewriting --confluence-check --no-prop --exact-split --guardedness --no-projection-like --experimental-laxy-instances --no-fast-reduce --no-postfix-projections #-}

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
    
        data BoundedSearchEvidence (P : Nat → Bool) : Maybe Nat → Set where
          boundedSearch-none : BoundedSearchEvidence P nothing
          boundedSearch-found :
            (n : Nat) → P n ≡ true → BoundedSearchEvidence P (just n)

        boundedSearch-evidence :
          (fuel : Nat) (P : Nat → Bool) →
          BoundedSearchEvidence P (boundedSearch fuel P)
        boundedSearch-evidence zero P = boundedSearch-none
        boundedSearch-evidence (suc fuel) P with P zero in pzero
        ... | true = boundedSearch-found zero pzero
        ... | false with boundedSearch-evidence fuel (λ i → P (suc i))
        ...   | boundedSearch-none = boundedSearch-none
        ...   | boundedSearch-found n proof =
          boundedSearch-found (suc n) proof

        boundedSearch-sound :
          (fuel : Nat) (P : Nat → Bool) (n : Nat) →
          boundedSearch fuel P ≡ just n → P n ≡ true
        boundedSearch-sound zero P n ()

        boundedSearch-sound (suc fuel) P zero result
          with P zero in pzero | boundedSearch fuel (λ i → P (suc i))
        ... | true | _ = pzero
        ... | false | nothing with result
        ...   | ()
        ... | false | just m with result
        ...   | ()

        boundedSearch-sound (suc fuel) P (suc n) result
          with P zero | boundedSearch fuel (λ i → P (suc i))
        ... | true | _ with result
        ...   | ()
        ... | false | nothing with result
        ...   | ()
        ... | false | just m with result
        ...   | refl = boundedSearch-sound fuel (λ i → P (suc i)) n refl
    
        MarkovPrinciple : Set₁
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
        decideDomain entries key with memberKey key (mapEntries entries)
        ... | true = inDomain refl
        ... | false = outDomain refl
    
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
          (mapEntries entries)
        ...   | true = entries
        ...   | false =
          extendFresh entries
            (omega (streamOf (mapEntries entries) default))
            refl
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
      lookup-tabulate
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
    record RationalRingInterface : Set₂ where
      field
        Rational : Set
        0ℚ 1ℚ : Rational
        _+ℚ_ _-ℚ_ _*ℚ_ : Rational → Rational → Rational
    
        +ℚ-assoc : (a b c : Rational) →
                   ((a +ℚ b) +ℚ c) ≡ (a +ℚ (b +ℚ c))
        +ℚ-comm : (a b : Rational) → (a +ℚ b) ≡ (b +ℚ a)
        +ℚ-zeroˡ : (a : Rational) → (0ℚ +ℚ a) ≡ a
        +ℚ-zeroʳ : (a : Rational) → (a +ℚ 0ℚ) ≡ a
        +ℚ-inverseʳ : (a : Rational) → (a +ℚ (0ℚ -ℚ a)) ≡ 0ℚ
        -ℚ-definition : (a b : Rational) →
                        (a -ℚ b) ≡ (a +ℚ (0ℚ -ℚ b))
    
        *ℚ-assoc : (a b c : Rational) →
                   ((a *ℚ b) *ℚ c) ≡ (a *ℚ (b *ℚ c))
        *ℚ-comm : (a b : Rational) → (a *ℚ b) ≡ (b *ℚ a)
        *ℚ-oneˡ : (a : Rational) → (1ℚ *ℚ a) ≡ a
        *ℚ-oneʳ : (a : Rational) → (a *ℚ 1ℚ) ≡ a
        *ℚ-zeroˡ : (a : Rational) → (0ℚ *ℚ a) ≡ 0ℚ
        *ℚ-distribˡ : (a b c : Rational) →
                      (a *ℚ (b +ℚ c)) ≡ ((a *ℚ b) +ℚ (a *ℚ c))
    
    module RationalSED (Q : RationalRingInterface) where
    
      open RationalRingInterface Q
    
      ----------------------------------------------------------------------
      -- Four-vectors and Minkowski quadrance, signature (+---).
      ----------------------------------------------------------------------
    
      record Rational4Vector : Set where
        constructor r4
        field
          ct x y z : Rational
      open Rational4Vector public
    
      minkowskiQuadrance : Rational4Vector → Rational
      minkowskiQuadrance u =
        (((ct u *ℚ ct u) -ℚ (x u *ℚ x u)) -ℚ (y u *ℚ y u)) -ℚ (z u *ℚ z u)
    
      _+₄_ : Rational4Vector → Rational4Vector → Rational4Vector
      r4 t₁ x₁ y₁ z₁ +₄ r4 t₂ x₂ y₂ z₂ =
        r4 (t₁ +ℚ t₂) (x₁ +ℚ x₂) (y₁ +ℚ y₂) (z₁ +ℚ z₂)
    
      _-₄_ : Rational4Vector → Rational4Vector → Rational4Vector
      r4 t₁ x₁ y₁ z₁ -₄ r4 t₂ x₂ y₂ z₂ =
        r4 (t₁ -ℚ t₂) (x₁ -ℚ x₂) (y₁ -ℚ y₂) (z₁ -ℚ z₂)
    
      r4-cong : {t t′ x x′ y y′ z z′ : Rational} →
                t ≡ t′ → x ≡ x′ → y ≡ y′ → z ≡ z′ →
                r4 t x y z ≡ r4 t′ x′ y′ z′
      r4-cong refl refl refl refl = refl
    
      ----------------------------------------------------------------------
      -- Rational (ct,x)-plane Cayley boost.
      --
      -- For rational parameter a, the Cayley coefficients are
      --
      --   d = 4 - a²,  c = (4 + a²)/d,  s = 4a/d.
      --
      -- Cross-multiplied equations avoid introducing a partial division
      -- operation into the interface.  The Lorentz identity is retained as
      -- an explicit certificate to be derived from the ring laws.
      ----------------------------------------------------------------------
    
      fourℚ : Rational
      fourℚ = (1ℚ +ℚ 1ℚ) +ℚ (1ℚ +ℚ 1ℚ)
    
      record CertifiedCayleyPlaneBoost : Set₁ where
        field
          parameter denominator c s : Rational
    
          denominator-formula :
            denominator ≡ (fourℚ -ℚ (parameter *ℚ parameter))
    
          denominator-nonzero : ¬ (denominator ≡ 0ℚ)
    
          c-formula :
            (c *ℚ denominator) ≡ (fourℚ +ℚ (parameter *ℚ parameter))
    
          s-formula :
            (s *ℚ denominator) ≡ (fourℚ *ℚ parameter)
    
          lorentz-condition :
            ((c *ℚ c) -ℚ (s *ℚ s)) ≡ 1ℚ
    
          preservesQuadrance :
            (u : Rational4Vector) →
            minkowskiQuadrance
              (r4 ((c *ℚ ct u) +ℚ (s *ℚ x u))
                  ((s *ℚ ct u) +ℚ (c *ℚ x u))
                  (y u) (z u))
            ≡ minkowskiQuadrance u
    
      applyCayleyPlaneBoost :
        CertifiedCayleyPlaneBoost → Rational4Vector → Rational4Vector
      applyCayleyPlaneBoost B u =
        r4 ((CertifiedCayleyPlaneBoost.c B *ℚ ct u) +ℚ
            (CertifiedCayleyPlaneBoost.s B *ℚ x u))
           ((CertifiedCayleyPlaneBoost.s B *ℚ ct u) +ℚ
            (CertifiedCayleyPlaneBoost.c B *ℚ x u))
           (y u) (z u)
    
      ----------------------------------------------------------------------
      -- Momentum accounting without a free compensating harmonic term.
      --
      -- A transition records particle and field momentum before/after.  The
      -- conservation proposition is an obligation to prove from dynamics.
      ----------------------------------------------------------------------
    
      record MomentumSnapshot : Set where
        constructor snapshot
        field
          particleMomentum : Rational4Vector
          fieldMomentum    : Rational4Vector
      open MomentumSnapshot public
    
      totalMomentum : MomentumSnapshot → Rational4Vector
      totalMomentum s = particleMomentum s +₄ fieldMomentum s
    
      record MomentumTransition : Set where
        constructor transition
        field
          before after : MomentumSnapshot
      open MomentumTransition public
    
      MomentumConserved : MomentumTransition → Set
      MomentumConserved tr = totalMomentum (before tr) ≡ totalMomentum (after tr)
    
      -- The dynamics must construct this certificate.  No arbitrary harmonic
      -- vector is permitted to cancel a residual by definition.
      record ConservationCertificate (tr : MomentumTransition) : Set where
        field
          totalMomentumConservation : MomentumConserved tr
    
    ------------------------------------------------------------------------
    -- End of file
    ------------------------------------------------------------------------
    
    ------------------------------------------------------------------------
    -- MODULE 3: CLOSED PARTICLE / FIELD / SOURCE EXCHANGE
    -- Inlined from RSEDClosedExchange.agda; no local module imports.
    ------------------------------------------------------------------------
    module RSEDClosedExchange where
    
    
      module WithRationalRing (Q : RationalRingInterface) where
        open RationalRingInterface Q
        module P = RationalSED Q
        open P
  
        -- Exchange notation aliases the exact rational four-vector addition and
        -- subtraction already defined by RationalSED.
        _⊕_ : Rational4Vector → Rational4Vector → Rational4Vector
        _⊕_ = _+₄_
  
        _⊖_ : Rational4Vector → Rational4Vector → Rational4Vector
        _⊖_ = _-₄_
    
        ------------------------------------------------------------------------
        -- Exact additive structure inherited from RationalRingInterface.
        ------------------------------------------------------------------------
    
        refl₄ : (u : Rational4Vector) → u ≡ u
        refl₄ u = refl
    
        sym₄ : {u v : Rational4Vector} → u ≡ v → v ≡ u
        sym₄ = sym
    
        trans₄ : {u v w : Rational4Vector} → u ≡ v → v ≡ w → u ≡ w
        trans₄ = trans
    
        add₄-cong : {u v w z : Rational4Vector} →
                    u ≡ v → w ≡ z → (u ⊕ w) ≡ (v ⊕ z)
        add₄-cong refl refl = refl
    
        zero₄ : Rational4Vector
        zero₄ = r4 0ℚ 0ℚ 0ℚ 0ℚ
    
        neg₄ : Rational4Vector → Rational4Vector
        neg₄ u =
          r4 (0ℚ -ℚ ct u)
             (0ℚ -ℚ x u)
             (0ℚ -ℚ y u)
             (0ℚ -ℚ z u)
    
        add₄-assoc : (u v w : Rational4Vector) →
                     ((u ⊕ v) ⊕ w) ≡ (u ⊕ (v ⊕ w))
        add₄-assoc u v w =
          r4-cong
            (+ℚ-assoc (ct u) (ct v) (ct w))
            (+ℚ-assoc (x u) (x v) (x w))
            (+ℚ-assoc (y u) (y v) (y w))
            (+ℚ-assoc (z u) (z v) (z w))
    
        add₄-comm : (u v : Rational4Vector) → (u ⊕ v) ≡ (v ⊕ u)
        add₄-comm u v =
          r4-cong
            (+ℚ-comm (ct u) (ct v))
            (+ℚ-comm (x u) (x v))
            (+ℚ-comm (y u) (y v))
            (+ℚ-comm (z u) (z v))
    
        add₄-zeroˡ : (u : Rational4Vector) → (zero₄ ⊕ u) ≡ u
        add₄-zeroˡ u =
          r4-cong
            (+ℚ-zeroˡ (ct u))
            (+ℚ-zeroˡ (x u))
            (+ℚ-zeroˡ (y u))
            (+ℚ-zeroˡ (z u))
    
        add₄-inverseʳ : (u : Rational4Vector) → (u ⊕ neg₄ u) ≡ zero₄
        add₄-inverseʳ u =
          r4-cong
            (+ℚ-inverseʳ (ct u))
            (+ℚ-inverseʳ (x u))
            (+ℚ-inverseʳ (y u))
            (+ℚ-inverseʳ (z u))
    
        minus-as-add-neg : (u v : Rational4Vector) →
                           (u ⊖ v) ≡ (u ⊕ neg₄ v)
        minus-as-add-neg u v =
          r4-cong
            (-ℚ-definition (ct u) (ct v))
            (-ℚ-definition (x u) (x v))
            (-ℚ-definition (y u) (y v))
            (-ℚ-definition (z u) (z v))
    
        -- Middle exchange: u + (v + w) = (u + w) + v.
        add₄-middle : (u v w : Rational4Vector) →
                      (u ⊕ (v ⊕ w)) ≡ ((u ⊕ w) ⊕ v)
        add₄-middle u v w =
          trans₄
            (add₄-cong (refl₄ u) (add₄-comm v w))
            (sym₄ (add₄-assoc u w v))
    
        -- The transfer and its opposite cancel, without assuming definitional
        -- equality between rational subtraction and addition of an inverse.
        add₄-with-sub-cancel : (d f : Rational4Vector) →
                                (d ⊕ (f ⊖ d)) ≡ f
        add₄-with-sub-cancel d f =
          trans₄
            (add₄-cong (refl₄ d) (minus-as-add-neg f d))
            (trans₄
              (add₄-middle d f (neg₄ d))
              (trans₄
                (add₄-cong (add₄-inverseʳ d) (refl₄ f))
                (add₄-zeroˡ f)))
    
        pair-exchange-preserves :
          (left right transfer : Rational4Vector) →
          ((left ⊕ transfer) ⊕ (right ⊖ transfer)) ≡ (left ⊕ right)
        pair-exchange-preserves left right transfer =
          trans₄
            (sym₄ (add₄-assoc left transfer (right ⊖ transfer)))
            (add₄-cong (refl₄ left)
              (add₄-with-sub-cancel transfer right))
    
        ------------------------------------------------------------------------
        -- Closed particle / Maxwell-field / source momentum state.
        -- Every elementary update transfers one exact four-vector between two
        -- compartments. No free residual or caller-supplied conservation proof.
        ------------------------------------------------------------------------
    
        record ClosedMomentumSnapshot : Set where
          constructor closedSnapshot
          field
            particle4Momentum : Rational4Vector
            field4Momentum    : Rational4Vector
            source4Momentum   : Rational4Vector
        open ClosedMomentumSnapshot public
    
        totalClosedMomentum : ClosedMomentumSnapshot → Rational4Vector
        totalClosedMomentum s =
          particle4Momentum s ⊕ (field4Momentum s ⊕ source4Momentum s)
    
        data MomentumExchange : Set where
          particleField : Rational4Vector → MomentumExchange
          fieldSource   : Rational4Vector → MomentumExchange
    
        applyMomentumExchange :
          MomentumExchange → ClosedMomentumSnapshot → ClosedMomentumSnapshot
        applyMomentumExchange (particleField δ) s =
          closedSnapshot
            (particle4Momentum s ⊕ δ)
            (field4Momentum s ⊖ δ)
            (source4Momentum s)
        applyMomentumExchange (fieldSource δ) s =
          closedSnapshot
            (particle4Momentum s)
            (field4Momentum s ⊕ δ)
            (source4Momentum s ⊖ δ)
    
        particleField-exchange-conserves :
          (δ : Rational4Vector) (s : ClosedMomentumSnapshot) →
          totalClosedMomentum (applyMomentumExchange (particleField δ) s)
            ≡ totalClosedMomentum s
        particleField-exchange-conserves δ s =
          trans₄
            (sym₄
              (add₄-assoc
                (particle4Momentum s ⊕ δ)
                (field4Momentum s ⊖ δ)
                (source4Momentum s)))
            (trans₄
              (add₄-cong
                (pair-exchange-preserves
                  (particle4Momentum s) (field4Momentum s) δ)
                (refl₄ (source4Momentum s)))
              (add₄-assoc
                (particle4Momentum s)
                (field4Momentum s)
                (source4Momentum s)))
    
        fieldSource-exchange-conserves :
          (δ : Rational4Vector) (s : ClosedMomentumSnapshot) →
          totalClosedMomentum (applyMomentumExchange (fieldSource δ) s)
            ≡ totalClosedMomentum s
        fieldSource-exchange-conserves δ s =
          add₄-cong
            (refl₄ (particle4Momentum s))
            (pair-exchange-preserves
              (field4Momentum s) (source4Momentum s) δ)
    
        exchange-conserves :
          (e : MomentumExchange) (s : ClosedMomentumSnapshot) →
          totalClosedMomentum (applyMomentumExchange e s) ≡ totalClosedMomentum s
        exchange-conserves (particleField δ) s = particleField-exchange-conserves δ s
        exchange-conserves (fieldSource δ) s = fieldSource-exchange-conserves δ s
    
        runExchanges :
          List MomentumExchange → ClosedMomentumSnapshot → ClosedMomentumSnapshot
        runExchanges [] s = s
        runExchanges (e ∷ es) s = runExchanges es (applyMomentumExchange e s)
    
        runExchanges-conserves :
          (es : List MomentumExchange) (s : ClosedMomentumSnapshot) →
          totalClosedMomentum (runExchanges es s) ≡ totalClosedMomentum s
        runExchanges-conserves [] s = refl₄ (totalClosedMomentum s)
        runExchanges-conserves (e ∷ es) s =
          trans₄
            (runExchanges-conserves es (applyMomentumExchange e s))
            (exchange-conserves e s)
    
    ------------------------------------------------------------------------
    -- MODULE 4: Q5-A DEPENDENT RSED MOTIVE
    -- Inlined from SovereignRSEDMotive.agda; no local module imports.
    ------------------------------------------------------------------------
    module SovereignRSEDMotive where
    
    
      module WithRationalRing (Q : RationalRingInterface) where
        open RationalRingInterface Q
        module P = RationalSED Q
        open P
        module Closed = RSEDClosedExchange.WithRationalRing Q
        open Closed
    
        -- A positive cone is explicit semantic data, rather than an unproved
        -- assumption that every rational weight happens to be nonnegative.
        record RationalPositiveCone : Set₂ where
          field
            Nonnegative : Rational → Set
            zeroNonnegative : Nonnegative 0ℚ
            oneNonnegative : Nonnegative 1ℚ
            addNonnegative :
              {a b : Rational} → Nonnegative a → Nonnegative b →
              Nonnegative (a +ℚ b)
            mulNonnegative :
              {a b : Rational} → Nonnegative a → Nonnegative b →
              Nonnegative (a *ℚ b)
        open RationalPositiveCone public
    
        ------------------------------------------------------------------------
        -- Finite cell labels and list-valued cochains.
        ------------------------------------------------------------------------
    
    
        -- A cochain is a plain finite coefficient list. Its Nat parameter names
        -- the ambient cell count; this low-level interface leaves list length
        -- unrestricted and does not introduce a bounded-index datatype.
        Cochain : Nat → Set
        Cochain n = List Rational
    
        zeroCochain : {n : Nat} → Cochain n
        zeroCochain {n} = replicateList n 0ℚ
    
        ------------------------------------------------------------------------
        -- A finite oriented cochain complex C⁰ → C¹ → C² → C³.
        -- Incidence maps satisfy d² = 0 by intensional equality on list encodings.
        ------------------------------------------------------------------------
    
        record FiniteOrientedCochainComplex : Set₁ where
          field
            n₀ n₁ n₂ n₃ : Nat
            d₀ : Cochain n₀ → Cochain n₁
            d₁ : Cochain n₁ → Cochain n₂
            d₂ : Cochain n₂ → Cochain n₃
            d₁d₀-zero : (a : Cochain n₀) → _≡_ (d₁ (d₀ a)) zeroCochain
            d₂d₁-zero : (a : Cochain n₁) → _≡_ (d₂ (d₁ a)) zeroCochain
            star₂ : Cochain n₂ → Cochain n₂
        open FiniteOrientedCochainComplex public
    
        faradayFromPotential :
          (K : FiniteOrientedCochainComplex) →
          (A : Cochain (n₁ K)) →
          _≡_ (d₂ K (d₁ K A)) zeroCochain
        faradayFromPotential K A = d₂d₁-zero K A
    
        ------------------------------------------------------------------------
        -- Finite rational ensemble over complete time trajectories.
        -- A single sample index selects one value at every time/mode, so temporal
        -- correlations are retained rather than resampling independently per time.
        ------------------------------------------------------------------------
    
        sumFinite : (n : Nat) → (Nat → Rational) → Rational
        sumFinite zero f = 0ℚ
        sumFinite (suc n) f =
          f zero +ℚ sumFinite n (λ i → f (suc i))
    
        sumFinite-cong :
          (n : Nat) (f g : Nat → Rational) →
          ((i : Nat) → f i ≡ g i) →
          sumFinite n f ≡ sumFinite n g
        sumFinite-cong zero f g pointwise = refl
        sumFinite-cong (suc n) f g pointwise =
          cong₂ _+ℚ_
            (pointwise zero)
            (sumFinite-cong n
              (λ i → f (suc i))
              (λ i → g (suc i))
              (λ i → pointwise (suc i)))
    
        record FiniteRationalTemporalNoise
          (Nonnegative : Rational → Set)
          (samples times modes : Nat) : Set₁ where
          constructor temporalNoise
          field
            probabilityWeight : Nat → Rational
            weightNonnegative :
              (i : Nat) → Nonnegative (probabilityWeight i)
            normalizedWeights :
              sumFinite samples probabilityWeight ≡ 1ℚ
            sampleAmplitude :
              Nat → Nat → Nat → Rational
        open FiniteRationalTemporalNoise public
    
        noiseMean :
          {Nonnegative : Rational → Set} {samples times modes : Nat} →
          (N : FiniteRationalTemporalNoise Nonnegative samples times modes) →
          Nat → Nat → Rational
        noiseMean {samples = samples} N t m =
          sumFinite samples
            (λ ω → probabilityWeight N ω *ℚ sampleAmplitude N ω t m)
    
        noiseCovariance :
          {Nonnegative : Rational → Set} {samples times modes : Nat} →
          (N : FiniteRationalTemporalNoise Nonnegative samples times modes) →
          Nat → Nat → Nat → Nat → Rational
        noiseCovariance {samples = samples} N t u m n =
          sumFinite samples
            (λ ω →
              probabilityWeight N ω *ℚ
                ((sampleAmplitude N ω t m -ℚ noiseMean N t m) *ℚ
                 (sampleAmplitude N ω u n -ℚ noiseMean N u n)))
    
        noiseCovariance-symmetric :
          {Nonnegative : Rational → Set} {samples times modes : Nat} →
          (N : FiniteRationalTemporalNoise Nonnegative samples times modes) →
          (t u : Nat) (m n : Nat) →
          noiseCovariance N t u m n ≡ noiseCovariance N u t n m
        noiseCovariance-symmetric {samples = samples} N t u m n =
          sumFinite-cong samples
            (λ ω →
              probabilityWeight N ω *ℚ
                ((sampleAmplitude N ω t m -ℚ noiseMean N t m) *ℚ
                 (sampleAmplitude N ω u n -ℚ noiseMean N u n)))
            (λ ω →
              probabilityWeight N ω *ℚ
                ((sampleAmplitude N ω u n -ℚ noiseMean N u n) *ℚ
                 (sampleAmplitude N ω t m -ℚ noiseMean N t m)))
            (λ ω →
              cong₂ _*ℚ_
                (refl)
                (*ℚ-comm
                  (sampleAmplitude N ω t m -ℚ noiseMean N t m)
                  (sampleAmplitude N ω u n -ℚ noiseMean N u n)))
    
        ------------------------------------------------------------------------
        -- Context and world.  Q5-A: one dependent family over complete worlds.
        ------------------------------------------------------------------------
    
        record RSEDContext : Set₃ where
          field
            geometry : FiniteOrientedCochainComplex
            positiveCone : RationalPositiveCone
            sampleCount timeCount modeCount : Nat
        open RSEDContext public
    
        record RSEDWorld (V : RSEDContext) : Set₂ where
          field
            potential : Cochain (n₁ (geometry V))
            sourceCurrent : Cochain (n₃ (geometry V))
            noise : FiniteRationalTemporalNoise
                      (Nonnegative (positiveCone V))
                      (sampleCount V) (timeCount V) (modeCount V)
            initialMomentum : ClosedMomentumSnapshot
            momentumExchanges : List MomentumExchange
            cohesivePresentation : CohesiveExpr
        open RSEDWorld public
    
        fieldStrength :
          {V : RSEDContext} → RSEDWorld V → Cochain (n₂ (geometry V))
        fieldStrength {V} W = d₁ (geometry V) (potential W)
    
        worldMomentum :
          {V : RSEDContext} → RSEDWorld V → ClosedMomentumSnapshot
        worldMomentum W = runExchanges (momentumExchanges W) (initialMomentum W)
    
        ------------------------------------------------------------------------
        -- Dependent motive. Q5-A indexes one invariant package over context and
        -- complete semantic world. Only the sourced Maxwell equation is a model
        -- obligation; Faraday, normalized noise, covariance symmetry, and total
        -- momentum conservation are derived from the world structure.
        ------------------------------------------------------------------------
    
        motiveNoiseNormalization :
          (V : RSEDContext) (W : RSEDWorld V) →
          sumFinite (sampleCount V) (probabilityWeight (noise W)) ≡ 1ℚ
        motiveNoiseNormalization V W = normalizedWeights (noise W)
    
        motiveNoiseCovarianceSymmetric :
          (V : RSEDContext) (W : RSEDWorld V) →
          (t u : Nat) (m n : Nat) →
          noiseCovariance (noise W) t u m n ≡ noiseCovariance (noise W) u t n m
        motiveNoiseCovarianceSymmetric V W = noiseCovariance-symmetric (noise W)
    
        motiveFaradayLaw :
          (V : RSEDContext) (W : RSEDWorld V) →
          _≡_
            (d₂ (geometry V) (fieldStrength W))
            zeroCochain
        motiveFaradayLaw V W =
          faradayFromPotential (geometry V) (potential W)
    
        motiveMomentumConservation :
          (V : RSEDContext) (W : RSEDWorld V) →
          totalClosedMomentum (worldMomentum W)
            ≡ totalClosedMomentum (initialMomentum W)
        motiveMomentumConservation V W =
          runExchanges-conserves (momentumExchanges W) (initialMomentum W)
    
        record RSEDMotive (V : RSEDContext) (W : RSEDWorld V) : Set₁ where
          field
            maxwellSourceLaw :
              _≡_
                (d₂ (geometry V) (star₂ (geometry V) (fieldStrength W)))
                (sourceCurrent W)
            faradayLaw :
              _≡_
                (d₂ (geometry V) (fieldStrength W))
                zeroCochain
            normalizedNoise :
              sumFinite (sampleCount V) (probabilityWeight (noise W)) ≡ 1ℚ
            covarianceSymmetry :
              (t u : Nat) (m n : Nat) →
              noiseCovariance (noise W) t u m n ≡ noiseCovariance (noise W) u t n m
            totalMomentumConservation :
              totalClosedMomentum (worldMomentum W)
                ≡ totalClosedMomentum (initialMomentum W)
        open RSEDMotive public
    
        assembleRSEDMotive :
          (V : RSEDContext) (W : RSEDWorld V) →
          _≡_
            (d₂ (geometry V) (star₂ (geometry V) (fieldStrength W)))
            (sourceCurrent W) →
          RSEDMotive V W
        assembleRSEDMotive V W sourced = record
          { maxwellSourceLaw = sourced
          ; faradayLaw = motiveFaradayLaw V W
          ; normalizedNoise = motiveNoiseNormalization V W
          ; covarianceSymmetry = motiveNoiseCovarianceSymmetric V W
          ; totalMomentumConservation = motiveMomentumConservation V W
          }
    
        -- Any semantic transformation must transport the complete dependent
        -- motive witness along with its world map; transporting only world data is
        -- insufficient because the proof fields depend on that exact world.
        record RSEDWorldMap (V W : RSEDContext) : Set₃ where
          field
            mapWorld : RSEDWorld V → RSEDWorld W
            mapMotive :
              (world : RSEDWorld V) →
              RSEDMotive V world → RSEDMotive W (mapWorld world)
        open RSEDWorldMap public
    
    ------------------------------------------------------------------------
    -- PHYSICAL FOUNDATIONS: NJ WILDBERGER / FINITE HODGE-MAXWELL / SED
    --
    -- This module is additive: the foundational packages and their single outer
    -- REWRITE registration in SovereignRationalSED remain separate.  It gives
    -- the physical layer actual types, equations, and proof
    -- obligations rather than treating an arbitrary star map or arbitrary
    -- exchange list as a physical realization.
    ------------------------------------------------------------------------
    
    module RSEDPhysicalFoundations (Q : RationalRingInterface) where
    
      open RationalRingInterface Q
      module Relativity = RationalSED Q
      module Exchange = RSEDClosedExchange.WithRationalRing Q
    
      ----------------------------------------------------------------------
      -- 1. NJ WILDBERGER RATIONAL EUCLIDEAN GEOMETRY
      --
      -- Coordinates, quadrance, dot product, cross product, and spread are
      -- algebraic.  A quotient is represented by an exact numerator,
      -- denominator, and a proof that the denominator is nonzero; no square
      -- roots, angles, or floating-point operations occur.
      ----------------------------------------------------------------------
    
      record PlaneVector₂ : Set where
        constructor planeVector₂
        field
          vx vy : Rational
      open PlaneVector₂ public
    
      record Point₂ : Set where
        constructor point₂
        field
          px py : Rational
      open Point₂ public
    
      difference₂ : Point₂ → Point₂ → PlaneVector₂
      difference₂ p q =
        planeVector₂ (px p -ℚ px q) (py p -ℚ py q)
    
      dot₂ : PlaneVector₂ → PlaneVector₂ → Rational
      dot₂ u v = (vx u *ℚ vx v) +ℚ (vy u *ℚ vy v)
    
      cross₂ : PlaneVector₂ → PlaneVector₂ → Rational
      cross₂ u v = (vx u *ℚ vy v) -ℚ (vy u *ℚ vx v)
    
      quadrance₂ : PlaneVector₂ → Rational
      quadrance₂ u = dot₂ u u
    
      pointQuadrance₂ : Point₂ → Point₂ → Rational
      pointQuadrance₂ p q = quadrance₂ (difference₂ p q)
    
      record SpaceVector₃ : Set where
        constructor spaceVector₃
        field
          vx₃ vy₃ vz₃ : Rational
      open SpaceVector₃ public
    
      record Point₃ : Set where
        constructor point₃
        field
          px₃ py₃ pz₃ : Rational
      open Point₃ public
    
      difference₃ : Point₃ → Point₃ → SpaceVector₃
      difference₃ p q =
        spaceVector₃ (px₃ p -ℚ px₃ q)
              (py₃ p -ℚ py₃ q)
              (pz₃ p -ℚ pz₃ q)
    
      dot₃ : SpaceVector₃ → SpaceVector₃ → Rational
      dot₃ u v =
        ((vx₃ u *ℚ vx₃ v) +ℚ (vy₃ u *ℚ vy₃ v)) +ℚ
        (vz₃ u *ℚ vz₃ v)
    
      quadrance₃ : SpaceVector₃ → Rational
      quadrance₃ u = dot₃ u u
    
      cross₃ : SpaceVector₃ → SpaceVector₃ → SpaceVector₃
      cross₃ u v =
        spaceVector₃
          ((vy₃ u *ℚ vz₃ v) -ℚ (vz₃ u *ℚ vy₃ v))
          ((vz₃ u *ℚ vx₃ v) -ℚ (vx₃ u *ℚ vz₃ v))
          ((vx₃ u *ℚ vy₃ v) -ℚ (vy₃ u *ℚ vx₃ v))
    
      pointQuadrance₃ : Point₃ → Point₃ → Rational
      pointQuadrance₃ p q = quadrance₃ (difference₃ p q)
    
      Nonzero : Rational → Set
      Nonzero r = ¬ (r ≡ 0ℚ)
    
      record RationalFraction : Set where
        constructor fraction
        field
          numerator denominator : Rational
          denominatorNonzero : Nonzero denominator
      open RationalFraction public
    
      -- Wildberger's spread, represented exactly as
      -- cross(u,v)^2 / (Q(u) Q(v)).
      rationalSpread₂ : (u v : PlaneVector₂) →
        Nonzero (quadrance₂ u *ℚ quadrance₂ v) → RationalFraction
      rationalSpread₂ u v denominator-proof =
        fraction
          (cross₂ u v *ℚ cross₂ u v)
          (quadrance₂ u *ℚ quadrance₂ v)
          denominator-proof
    
      -- Three-dimensional spread is the quadrance of the cross product
      -- divided by the product of the two direction quadrances.
      rationalSpread₃ : (u v : SpaceVector₃) →
        Nonzero (quadrance₃ u *ℚ quadrance₃ v) → RationalFraction
      rationalSpread₃ u v denominator-proof =
        fraction
          (quadrance₃ (cross₃ u v))
          (quadrance₃ u *ℚ quadrance₃ v)
          denominator-proof
    
      record Line₂ : Set where
        constructor line₂
        field
          lineA lineB lineC : Rational
      open Line₂ public
    
      lineNormalQuadrance₂ : Line₂ → Rational
      lineNormalQuadrance₂ l =
        (lineA l *ℚ lineA l) +ℚ (lineB l *ℚ lineB l)
    
      lineSpread₂ : (l m : Line₂) →
        Nonzero (lineNormalQuadrance₂ l *ℚ lineNormalQuadrance₂ m) →
        RationalFraction
      lineSpread₂ l m denominator-proof =
        fraction
          (((lineA l *ℚ lineB m) -ℚ (lineA m *ℚ lineB l)) *ℚ
           ((lineA l *ℚ lineB m) -ℚ (lineA m *ℚ lineB l)))
          (lineNormalQuadrance₂ l *ℚ lineNormalQuadrance₂ m)
          denominator-proof
    
      -- Cramer's rule as exact rational fractions.  This is deliberately a
      -- construction of the coordinates, not a floating-point intersection.
      record RationalLineIntersection₂ (l m : Line₂) : Set where
        constructor lineIntersection₂
        field
          intersectionX intersectionY : RationalFraction
      open RationalLineIntersection₂ public
    
      lineDeterminant₂ : Line₂ → Line₂ → Rational
      lineDeterminant₂ l m =
        (lineA l *ℚ lineB m) -ℚ (lineA m *ℚ lineB l)
    
      intersectionFormula₂ : (l m : Line₂) →
        Nonzero (lineDeterminant₂ l m) → RationalLineIntersection₂ l m
      intersectionFormula₂ l m det-nonzero =
        lineIntersection₂
          (fraction
            ((lineB l *ℚ lineC m) -ℚ (lineB m *ℚ lineC l))
            (lineDeterminant₂ l m)
            det-nonzero)
          (fraction
            ((lineC l *ℚ lineA m) -ℚ (lineC m *ℚ lineA l))
            (lineDeterminant₂ l m)
            det-nonzero)
    
      lineMeetResidual₂ : {l m : Line₂} →
        (line : Line₂) → RationalLineIntersection₂ l m → Rational
      -- Clear both coordinate denominators independently.  For
      -- x = nx/dx and y = ny/dy, the numerator of A*x + B*y + C
      -- over dx*dy is A*nx*dy + B*ny*dx + C*dx*dy.
      -- Keeping dx and dy distinct matters for arbitrary intersections;
      -- the Cramer's-rule constructor happens to choose equal denominators.
      lineMeetResidual₂ line I =
        (((lineA line *ℚ numerator (intersectionX I)) *ℚ
           denominator (intersectionY I)) +ℚ
         ((lineB line *ℚ numerator (intersectionY I)) *ℚ
           denominator (intersectionX I))) +ℚ
        ((lineC line *ℚ denominator (intersectionX I)) *ℚ
          denominator (intersectionY I))
    
      -- The dot/cross identity and Cramer's-rule incidence are explicit laws
      -- required of each concrete rational plane instance.
      record RationalTrigonometryLawWitness : Set₁ where
        field
          dotCrossQuadrance : (u v : PlaneVector₂) →
            ((dot₂ u v *ℚ dot₂ u v) +ℚ
             (cross₂ u v *ℚ cross₂ u v)) ≡
            (quadrance₂ u *ℚ quadrance₂ v)
          dotCrossQuadrance₃ : (u v : SpaceVector₃) →
            ((dot₃ u v *ℚ dot₃ u v) +ℚ
             quadrance₃ (cross₃ u v)) ≡
            (quadrance₃ u *ℚ quadrance₃ v)
          intersectionOnFirst : (l m : Line₂) →
            (det-nonzero : Nonzero (lineDeterminant₂ l m)) →
            lineMeetResidual₂ l (intersectionFormula₂ l m det-nonzero) ≡ 0ℚ
          intersectionOnSecond : (l m : Line₂) →
            (det-nonzero : Nonzero (lineDeterminant₂ l m)) →
            lineMeetResidual₂ m (intersectionFormula₂ l m det-nonzero) ≡ 0ℚ
      open RationalTrigonometryLawWitness public
    
      ----------------------------------------------------------------------
      -- 2. FINITE SPATIAL COCHAIN COMPLEX AND METRIC HODGE STRUCTURE
      --
      -- Spatial primal cochains have degrees 0,1,2,3.  Incidence maps are
      -- metric-free and satisfy d²=0.  Positive inner products and their
      -- adjoints are separate metric data.  This distinction is essential:
      -- the spatial Hodge metric is positive definite, while the spacetime
      -- Minkowski metric is Lorentzian.
      ----------------------------------------------------------------------
    
    
      -- Cochains use ordinary finite lists. The Nat
      -- parameter names the ambient cell count; operators below return lists
      -- with exactly that many entries, while lookup zero-extends short inputs.
      Cochain : Nat → Set
      Cochain n = List Rational
    
      zeroCochain : {n : Nat} → Cochain n
      zeroCochain {n} = replicateList n 0ℚ
    
      addCochain : {n : Nat} → Cochain n → Cochain n → Cochain n
      addCochain {n} xs ys =
        tabulateList n (λ i →
          lookupListOr 0ℚ i xs +ℚ lookupListOr 0ℚ i ys)
    
      negCochain : {n : Nat} → Cochain n → Cochain n
      negCochain {n} xs =
        tabulateList n (λ i → 0ℚ -ℚ lookupListOr 0ℚ i xs)
    
      subCochain : {n : Nat} → Cochain n → Cochain n → Cochain n
      subCochain f g = addCochain f (negCochain g)
    
      scaleCochain : {n : Nat} → Rational → Cochain n → Cochain n
      scaleCochain {n} r xs =
        tabulateList n (λ i → r *ℚ lookupListOr 0ℚ i xs)
    
      sumFinite : (n : Nat) → (Nat → Rational) → Rational
      sumFinite zero f = 0ℚ
      sumFinite (suc n) f =
        f zero +ℚ sumFinite n (λ i → f (suc i))
    
      sumFinite-cong :
        (n : Nat) (f g : Nat → Rational) →
        ((i : Nat) → f i ≡ g i) →
        sumFinite n f ≡ sumFinite n g
      sumFinite-cong zero f g pointwise = refl
      sumFinite-cong (suc n) f g pointwise =
        cong₂ _+ℚ_
          (pointwise zero)
          (sumFinite-cong n
            (λ i → f (suc i))
            (λ i → g (suc i))
            (λ i → pointwise (suc i)))
    
      ----------------------------------------------------------------------
      -- A finite embedded rational 3D cell complex.  Incidence coefficients
      -- are typed signs (−1,0,+1), not arbitrary floating weights.  Edge
      -- lengths/quadrances come from the embedded rational vertex positions.
      ----------------------------------------------------------------------
    
      record OrientedEdge (vertices : Nat) : Set where
        constructor orientedEdge
        field
          edgeSource edgeTarget : Nat
          edgeSourceBound : edgeSource < vertices
          edgeTargetBound : edgeTarget < vertices
      open OrientedEdge public
    
      data IncidenceSign : Set where
        minusSign zeroSign plusSign : IncidenceSign
    
      incidenceValue : IncidenceSign → Rational
      incidenceValue minusSign = 0ℚ -ℚ 1ℚ
      incidenceValue zeroSign = 0ℚ
      incidenceValue plusSign = 1ℚ
    
      record FiniteRationalMesh3D : Set₂ where
        field
          vertexCount edgeCount faceCount cellCount : Nat
          vertexPosition : Nat → Point₃
          orientedEdgeAt : Nat → OrientedEdge vertexCount
          faceBoundary : Nat → Nat → IncidenceSign
          cellBoundary : Nat → Nat → IncidenceSign
      open FiniteRationalMesh3D public
    
      meshEdgeQuadrance :
        (M : FiniteRationalMesh3D) → Nat → Rational
      meshEdgeQuadrance M e =
        pointQuadrance₃
          (vertexPosition M (edgeSource (orientedEdgeAt M e)))
          (vertexPosition M (edgeTarget (orientedEdgeAt M e)))
    
      meshGradient :
        (M : FiniteRationalMesh3D) →
        Cochain (vertexCount M) → Cochain (edgeCount M)
      meshGradient M potential =
        tabulateList (edgeCount M) (λ e →
          lookupListOr 0ℚ (edgeTarget (orientedEdgeAt M e)) potential -ℚ
          lookupListOr 0ℚ (edgeSource (orientedEdgeAt M e)) potential)
    
      meshCurl :
        (M : FiniteRationalMesh3D) →
        Cochain (edgeCount M) → Cochain (faceCount M)
      meshCurl M edgeField =
        tabulateList (faceCount M) (λ f →
          sumFinite (edgeCount M)
            (λ e → incidenceValue (faceBoundary M f e) *ℚ
              lookupListOr 0ℚ e edgeField))
    
      meshDivergence :
        (M : FiniteRationalMesh3D) →
        Cochain (faceCount M) → Cochain (cellCount M)
      meshDivergence M faceField =
        tabulateList (cellCount M) (λ c →
          sumFinite (faceCount M)
            (λ f → incidenceValue (cellBoundary M c f) *ℚ
              lookupListOr 0ℚ f faceField))
    
      record MeshBoundaryProof (M : FiniteRationalMesh3D) : Set₁ where
        field
          faceBoundaryOfBoundary :
            (potential : Cochain (vertexCount M)) →
            _≡_ (meshCurl M (meshGradient M potential)) zeroCochain
          cellBoundaryOfBoundary :
            (edgeField : Cochain (edgeCount M)) →
            _≡_ (meshDivergence M (meshCurl M edgeField)) zeroCochain
      open MeshBoundaryProof public
    
      record FiniteSpatialCochainComplex : Set₁ where
        field
          n₀ n₁ n₂ n₃ : Nat
          d₀ : Cochain n₀ → Cochain n₁
          d₁ : Cochain n₁ → Cochain n₂
          d₂ : Cochain n₂ → Cochain n₃
          d₁d₀-zero : (a : Cochain n₀) →
            _≡_ (d₁ (d₀ a)) zeroCochain
          d₂d₁-zero : (a : Cochain n₁) →
            _≡_ (d₂ (d₁ a)) zeroCochain
      open FiniteSpatialCochainComplex public
    
      meshCochainComplex :
        (M : FiniteRationalMesh3D) → MeshBoundaryProof M →
        FiniteSpatialCochainComplex
      meshCochainComplex M boundary = record
        { n₀ = vertexCount M
        ; n₁ = edgeCount M
        ; n₂ = faceCount M
        ; n₃ = cellCount M
        ; d₀ = meshGradient M
        ; d₁ = meshCurl M
        ; d₂ = meshDivergence M
        ; d₁d₀-zero = faceBoundaryOfBoundary boundary
        ; d₂d₁-zero = cellBoundaryOfBoundary boundary
        }
    
      record RationalPositivity : Set₂ where
        field
          Nonnegative : Rational → Set
          Positive : Rational → Set
          zeroNonnegative : Nonnegative 0ℚ
          onePositive : Positive 1ℚ
          positiveNonnegative : {x : Rational} →
            Positive x → Nonnegative x
          positiveNonzero : {x : Rational} →
            Positive x → Nonzero x
          squareNonnegative : (x : Rational) → Nonnegative (x *ℚ x)
          addNonnegative : {x y : Rational} →
            Nonnegative x → Nonnegative y → Nonnegative (x +ℚ y)
          multiplyNonnegative : {x y : Rational} →
            Nonnegative x → Nonnegative y → Nonnegative (x *ℚ y)
          multiplyPositive : {x y : Rational} →
            Positive x → Positive y → Positive (x *ℚ y)
      open RationalPositivity public
    
      -- Future-directed timelike vectors use the chosen exact positive cone.
      -- The algebraic Cayley certificate in the core preserves quadrance; this
      -- stricter wrapper also rejects the denominator-negative, time-reversing
      -- branch (for example parameter=3 in ordinary rational arithmetic).
      FutureTimelike : (P : RationalPositivity) →
        Relativity.Rational4Vector → Set
      FutureTimelike P u =
        Positive P (Relativity.ct u) ×
        Positive P (Relativity.minkowskiQuadrance u)
    
      record OrthoChronousCayleyPlaneBoost
        (P : RationalPositivity) : Set₁ where
        field
          algebraicBoost : Relativity.CertifiedCayleyPlaneBoost
          positiveBoostDenominator :
            Positive P (Relativity.CertifiedCayleyPlaneBoost.denominator algebraicBoost)
          preservesFutureCone : (u : Relativity.Rational4Vector) →
            FutureTimelike P u →
            FutureTimelike P (Relativity.applyCayleyPlaneBoost algebraicBoost u)
      open OrthoChronousCayleyPlaneBoost public
    
      applyOrthoChronousCayleyPlaneBoost :
        {P : RationalPositivity} →
        OrthoChronousCayleyPlaneBoost P →
        Relativity.Rational4Vector → Relativity.Rational4Vector
      applyOrthoChronousCayleyPlaneBoost B =
        Relativity.applyCayleyPlaneBoost (algebraicBoost B)
    
      record RationalInnerProduct (P : RationalPositivity) (n : Nat) : Set₁ where
        field
          inner : Cochain n → Cochain n → Rational
          inner-cong : {x y u v : Cochain n} →
            _≡_ x y → _≡_ u v →
            inner x u ≡ inner y v
          inner-symmetric : (x y : Cochain n) →
            inner x y ≡ inner y x
          inner-zero-left : (x : Cochain n) →
            inner zeroCochain x ≡ 0ℚ
          inner-add-left : (x y z : Cochain n) →
            inner (addCochain x y) z ≡
            (inner x z +ℚ inner y z)
          inner-scale-left : (a : Rational) (x y : Cochain n) →
            inner (scaleCochain a x) y ≡ (a *ℚ inner x y)
          inner-norm-nonnegative : (x : Cochain n) →
            Nonnegative P (inner x x)
          inner-norm-positive : (x : Cochain n) →
            ¬ _≡_ x zeroCochain → Positive P (inner x x)
          positive-definite : (x : Cochain n) →
            inner x x ≡ 0ℚ → _≡_ x zeroCochain
      open RationalInnerProduct public
    
      -- Dual cochains are distinct Agda types.  Dual k-cells correspond to
      -- primal (3-k)-cells, so their counts reverse: dual C⁰ has one value per
      -- primal 3-cell, dual C¹ per primal 2-cell, etc.
      record DualCochain₀ (M : FiniteRationalMesh3D) : Set where
        constructor dualCochain₀
        field dual₀Values : Cochain (cellCount M)
      open DualCochain₀ public
    
      record DualCochain₁ (M : FiniteRationalMesh3D) : Set where
        constructor dualCochain₁
        field dual₁Values : Cochain (faceCount M)
      open DualCochain₁ public
    
      record DualCochain₂ (M : FiniteRationalMesh3D) : Set where
        constructor dualCochain₂
        field dual₂Values : Cochain (edgeCount M)
      open DualCochain₂ public
    
      record DualCochain₃ (M : FiniteRationalMesh3D) : Set where
        constructor dualCochain₃
        field dual₃Values : Cochain (vertexCount M)
      open DualCochain₃ public
    
      record DualSpatialCochainComplex (M : FiniteRationalMesh3D) : Set₁ where
        field
          dualD₀ : DualCochain₀ M → DualCochain₁ M
          dualD₁ : DualCochain₁ M → DualCochain₂ M
          dualD₂ : DualCochain₂ M → DualCochain₃ M
          dualD₁D₀-zero : (a : DualCochain₀ M) →
            _≡_ (dual₁Values (dualD₁ (dualD₀ a))) zeroCochain
          dualD₂D₁-zero : (a : DualCochain₁ M) →
            _≡_ (dual₃Values (dualD₂ (dualD₁ a))) zeroCochain
      open DualSpatialCochainComplex public
    
      record MetricHodgeComplex (P : RationalPositivity) : Set₂ where
        field
          mesh : FiniteRationalMesh3D
          meshBoundaryProof : MeshBoundaryProof mesh
          dualComplex : DualSpatialCochainComplex mesh
          metric₀ : RationalInnerProduct P (vertexCount mesh)
          metric₁ : RationalInnerProduct P (edgeCount mesh)
          metric₂ : RationalInnerProduct P (faceCount mesh)
          metric₃ : RationalInnerProduct P (cellCount mesh)
          dualMetric₀ : RationalInnerProduct P (cellCount mesh)
          dualMetric₁ : RationalInnerProduct P (faceCount mesh)
          dualMetric₂ : RationalInnerProduct P (edgeCount mesh)
          dualMetric₃ : RationalInnerProduct P (vertexCount mesh)
          -- Hodge stars map primal k-cochains to dual (3-k)-cochains.
          -- Inverses have the genuinely dual types; primal C¹ and C² need not
          -- have equal dimensions.
          star₀ : Cochain (vertexCount mesh) → DualCochain₃ mesh
          star₁ : Cochain (edgeCount mesh) → DualCochain₂ mesh
          star₂ : Cochain (faceCount mesh) → DualCochain₁ mesh
          star₃ : Cochain (cellCount mesh) → DualCochain₀ mesh
          invStar₀ : DualCochain₃ mesh → Cochain (vertexCount mesh)
          invStar₁ : DualCochain₂ mesh → Cochain (edgeCount mesh)
          invStar₂ : DualCochain₁ mesh → Cochain (faceCount mesh)
          invStar₃ : DualCochain₀ mesh → Cochain (cellCount mesh)
          invStar₀-star₀-id : (a : Cochain (vertexCount mesh)) →
            _≡_ (invStar₀ (star₀ a)) a
          star₀-invStar₀-id : (a : DualCochain₃ mesh) →
            _≡_ (dual₃Values (star₀ (invStar₀ a))) (dual₃Values a)
          invStar₁-star₁-id : (a : Cochain (edgeCount mesh)) →
            _≡_ (invStar₁ (star₁ a)) a
          star₁-invStar₁-id : (a : DualCochain₂ mesh) →
            _≡_ (dual₂Values (star₁ (invStar₁ a))) (dual₂Values a)
          invStar₂-star₂-id : (a : Cochain (faceCount mesh)) →
            _≡_ (invStar₂ (star₂ a)) a
          star₂-invStar₂-id : (a : DualCochain₁ mesh) →
            _≡_ (dual₁Values (star₂ (invStar₂ a))) (dual₁Values a)
          invStar₃-star₃-id : (a : Cochain (cellCount mesh)) →
            _≡_ (invStar₃ (star₃ a)) a
          star₃-invStar₃-id : (a : DualCochain₀ mesh) →
            _≡_ (dual₀Values (star₃ (invStar₃ a))) (dual₀Values a)
          star₀-isometry : (a b : Cochain (vertexCount mesh)) →
            inner dualMetric₃ (dual₃Values (star₀ a)) (dual₃Values (star₀ b))
              ≡ inner metric₀ a b
          star₁-isometry : (a b : Cochain (edgeCount mesh)) →
            inner dualMetric₂ (dual₂Values (star₁ a)) (dual₂Values (star₁ b))
              ≡ inner metric₁ a b
          star₂-isometry : (a b : Cochain (faceCount mesh)) →
            inner dualMetric₁ (dual₁Values (star₂ a)) (dual₁Values (star₂ b))
              ≡ inner metric₂ a b
          star₃-isometry : (a b : Cochain (cellCount mesh)) →
            inner dualMetric₀ (dual₀Values (star₃ a)) (dual₀Values (star₃ b))
              ≡ inner metric₃ a b
          δ₁ : Cochain (edgeCount mesh) → Cochain (vertexCount mesh)
          δ₂ : Cochain (faceCount mesh) → Cochain (edgeCount mesh)
          δ₃ : Cochain (cellCount mesh) → Cochain (faceCount mesh)
          -- In dimension three: δ₁ = -*⁻¹₀ d*₂ *, δ₂ = *⁻¹₁ d*₁ *,
          -- δ₃ = -*⁻¹₂ d*₀ *.  Dual coboundaries act on dual cells.
          δ₁-hodge-star : (a : Cochain (edgeCount mesh)) →
            _≡_ (δ₁ a)
              (negCochain (invStar₀ (dualD₂ dualComplex (star₁ a))))
          δ₂-hodge-star : (a : Cochain (faceCount mesh)) →
            _≡_ (δ₂ a)
              (invStar₁ (dualD₁ dualComplex (star₂ a)))
          δ₃-hodge-star : (a : Cochain (cellCount mesh)) →
            _≡_ (δ₃ a)
              (negCochain (invStar₂ (dualD₀ dualComplex (star₃ a))))
          adjoint-d₀ : (a : Cochain (vertexCount mesh)) →
            (b : Cochain (edgeCount mesh)) →
            inner metric₁ (meshGradient mesh a) b ≡
            inner metric₀ a (δ₁ b)
          adjoint-d₁ : (a : Cochain (edgeCount mesh)) →
            (b : Cochain (faceCount mesh)) →
            inner metric₂ (meshCurl mesh a) b ≡
            inner metric₁ a (δ₂ b)
          adjoint-d₂ : (a : Cochain (faceCount mesh)) →
            (b : Cochain (cellCount mesh)) →
            inner metric₃ (meshDivergence mesh a) b ≡
            inner metric₂ a (δ₃ b)
          δ₁δ₂-zero : (b : Cochain (faceCount mesh)) →
            _≡_ (δ₁ (δ₂ b)) zeroCochain
          δ₂δ₃-zero : (c : Cochain (cellCount mesh)) →
            _≡_ (δ₂ (δ₃ c)) zeroCochain
          edgeQuadrancePositive : (e : Nat) →
            Positive P (meshEdgeQuadrance mesh e)
      open MetricHodgeComplex public
    
      complex : {P : RationalPositivity} →
        MetricHodgeComplex P → FiniteSpatialCochainComplex
      complex H = meshCochainComplex (mesh H) (meshBoundaryProof H)
    
    
      hodgeLaplacian₁ : {P : RationalPositivity} → (H : MetricHodgeComplex P) →
        Cochain (n₁ (complex H)) → Cochain (n₁ (complex H))
      hodgeLaplacian₁ H x =
        addCochain
          (d₀ (complex H) (δ₁ H x))
          (δ₂ H (d₁ (complex H) x))
    
      hodgeLaplacian₂ : {P : RationalPositivity} → (H : MetricHodgeComplex P) →
        Cochain (n₂ (complex H)) → Cochain (n₂ (complex H))
      hodgeLaplacian₂ H x =
        addCochain
          (d₁ (complex H) (δ₂ H x))
          (δ₃ H (d₂ (complex H) x))
    
      Harmonic₂ : {P : RationalPositivity} → (H : MetricHodgeComplex P) → Cochain (n₂ (complex H)) → Set
      Harmonic₂ H x =
        (_≡_ (d₂ (complex H) x) zeroCochain) ×
        (_≡_ (δ₂ H x) zeroCochain)
    
      -- Degree-one Hodge split: exact gradients, co-exact curls, and harmonic
      -- 1-cochains. Each component carries its actual preimage.
      record HodgeDecomposition₁
        {P : RationalPositivity}
        (H : MetricHodgeComplex P)
        (field₁ : Cochain (n₁ (complex H))) : Set₁ where
        field
          exactPotential₁ : Cochain (n₀ (complex H))
          coexactPotential₁ : Cochain (n₂ (complex H))
          harmonicPart₁ : Cochain (n₁ (complex H))
          reconstructs₁ : _≡_ field₁
            (addCochain
              (addCochain
                (d₀ (complex H) exactPotential₁)
                (δ₂ H coexactPotential₁))
              harmonicPart₁)
          harmonicClosed₁ : _≡_
            (d₁ (complex H) harmonicPart₁) zeroCochain
          harmonicCoclosed₁ : _≡_
            (δ₁ H harmonicPart₁) zeroCochain
          exactCoexactOrthogonal₁ :
            inner (metric₁ H)
              (d₀ (complex H) exactPotential₁)
              (δ₂ H coexactPotential₁) ≡ 0ℚ
          exactHarmonicOrthogonal₁ :
            inner (metric₁ H)
              (d₀ (complex H) exactPotential₁) harmonicPart₁ ≡ 0ℚ
          coexactHarmonicOrthogonal₁ :
            inner (metric₁ H)
              (δ₂ H coexactPotential₁) harmonicPart₁ ≡ 0ℚ
      open HodgeDecomposition₁ public
    
      -- Degree-two Hodge split: exact, co-exact, and harmonic 2-cochains.
      -- Each component carries its actual preimage and proof obligations.
      record HodgeDecomposition₂
        {P : RationalPositivity}
        (H : MetricHodgeComplex P)
        (field₂ : Cochain (n₂ (complex H))) : Set₁ where
        field
          exactPotential : Cochain (n₁ (complex H))
          coexactPotential : Cochain (n₃ (complex H))
          harmonicPart : Cochain (n₂ (complex H))
          reconstructs : _≡_ field₂
            (addCochain
              (addCochain
                (d₁ (complex H) exactPotential)
                (δ₃ H coexactPotential))
              harmonicPart)
          harmonicClosed : _≡_
            (d₂ (complex H) harmonicPart) zeroCochain
          harmonicCoclosed : _≡_
            (δ₂ H harmonicPart) zeroCochain
          exactCoexactOrthogonal :
            inner (metric₂ H)
              (d₁ (complex H) exactPotential)
              (δ₃ H coexactPotential) ≡ 0ℚ
          exactHarmonicOrthogonal :
            inner (metric₂ H)
              (d₁ (complex H) exactPotential) harmonicPart ≡ 0ℚ
          coexactHarmonicOrthogonal :
            inner (metric₂ H)
              (δ₃ H coexactPotential) harmonicPart ≡ 0ℚ
      open HodgeDecomposition₂ public
    
      ----------------------------------------------------------------------
      -- 3. HODGE-MAXWELL: SPATIAL FINITE-DIMENSIONAL EQUATIONS
      --
      -- E is a primal 1-cochain and B is a primal 2-cochain.  The equations
      -- use the metric adjoints δ, not an arbitrary untyped star₂.  A midpoint
      -- step is a proof-carrying exact rational update.  Its work identity is
      -- part of the step contract and can be checked from a concrete solver.
      ----------------------------------------------------------------------
    
      record MaxwellState {P : RationalPositivity} (H : MetricHodgeComplex P) : Set₁ where
        field
          electricField : Cochain (n₁ (complex H))
          magneticField : Cochain (n₂ (complex H))
          chargeDensity : Cochain (n₀ (complex H))
          gaussElectric : _≡_ (δ₁ H electricField) chargeDensity
          gaussMagnetic : _≡_
            (d₂ (complex H) magneticField) zeroCochain
      open MaxwellState public
    
      twice : Rational
      twice = 1ℚ +ℚ 1ℚ
    
      record MaxwellMidpointStep
        {P : RationalPositivity}
        (H : MetricHodgeComplex P)
        (dt : Rational)
        (current : Cochain (n₁ (complex H)))
        (before after : MaxwellState H) : Set₁ where
        field
          faradayMidpoint : _≡_
            (scaleCochain twice
              (subCochain (magneticField after) (magneticField before)))
            (scaleCochain (0ℚ -ℚ dt)
              (d₁ (complex H)
                (addCochain (electricField before) (electricField after))))
          ampereMidpoint : _≡_
            (scaleCochain twice
              (subCochain (electricField after) (electricField before)))
            (scaleCochain dt
              (subCochain
                (δ₂ H (addCochain (magneticField before) (magneticField after)))
                (scaleCochain twice current)))
          chargeContinuity : _≡_
            (scaleCochain twice
              (subCochain (chargeDensity after) (chargeDensity before)))
            (scaleCochain (0ℚ -ℚ dt)
              (δ₁ H (scaleCochain twice current)))
          -- Twice the field energy is <E,E> + <B,B>.  Thus this exact identity
          -- is Δ(2U) = -dt <E_before+E_after,J>, i.e. midpoint current work.
          exactDiscreteWorkBalance :
            ((inner (metric₁ H) (electricField after) (electricField after) +ℚ
              inner (metric₂ H) (magneticField after) (magneticField after)) -ℚ
             (inner (metric₁ H) (electricField before) (electricField before) +ℚ
              inner (metric₂ H) (magneticField before) (magneticField before)))
            ≡
            ((0ℚ -ℚ dt) *ℚ
              inner (metric₁ H)
                (addCochain (electricField before) (electricField after))
                current)
      open MaxwellMidpointStep public
    
      ----------------------------------------------------------------------
      -- 4. FINITE RATIONAL STOCHASTIC ELECTRODYNAMICS
      --
      -- The ensemble consists of complete histories, not independent samples
      -- drawn afresh at each time.  Mean, covariance, stationarity, positive
      -- mode frequencies, and the finite-band ω^3 density target are explicit.
      -- A separate Maxwell history is associated with each sample.
      ----------------------------------------------------------------------
    
      record FiniteTimeAction (times : Nat) : Set₁ where
        field
          -- An explicit origin makes the finite time index nonempty by construction.
          timeOrigin : Nat
          timeStep : Nat
          translateTime : Nat → Nat → Nat
          nextTime : Nat → Nat
          translate-origin : (t : Nat) →
            translateTime t timeOrigin ≡ t
          translate-compose : (t s r : Nat) →
            translateTime (translateTime t s) r ≡
            translateTime t (translateTime s r)
          next-is-translation : (t : Nat) →
            nextTime t ≡ translateTime t timeStep
      open FiniteTimeAction public
    
      record FiniteSEDEnsemble
        (P : RationalPositivity)
        (samples times modes : Nat) : Set₁ where
        field
          probabilityWeight : Nat → Rational
          weightNonnegative : (w : Nat) →
            Nonnegative P (probabilityWeight w)
          normalizedWeights :
            sumFinite samples probabilityWeight ≡ 1ℚ
          electricAmplitude : Nat → Nat → Nat → Rational
          magneticAmplitude : Nat → Nat → Nat → Rational
      open FiniteSEDEnsemble public
    
      componentAmplitude :
        {P : RationalPositivity} {samples times modes : Nat} →
        FiniteSEDEnsemble P samples times modes →
        Nat → Nat → Nat → Bool → Rational
      componentAmplitude N w t m true = electricAmplitude N w t m
      componentAmplitude N w t m false = magneticAmplitude N w t m
    
      stochasticMean :
        {P : RationalPositivity} {samples times modes : Nat} →
        (N : FiniteSEDEnsemble P samples times modes) →
        Nat → Nat → Bool → Rational
      stochasticMean {samples = samples} N t m electric? =
        sumFinite samples
          (λ w → probabilityWeight N w *ℚ
            componentAmplitude N w t m electric?)
    
      stochasticCovariance :
        {P : RationalPositivity} {samples times modes : Nat} →
        (N : FiniteSEDEnsemble P samples times modes) →
        Nat → Nat → Nat → Nat → Bool → Bool → Rational
      stochasticCovariance {samples = samples} N t u m n electric? magnetic? =
        sumFinite samples
          (λ w → probabilityWeight N w *ℚ
            ((componentAmplitude N w t m electric? -ℚ
              stochasticMean N t m electric?) *ℚ
             (componentAmplitude N w u n magnetic? -ℚ
              stochasticMean N u n magnetic?)))
    
      stochasticCovariance-symmetric :
        {P : RationalPositivity} {samples times modes : Nat} →
        (N : FiniteSEDEnsemble P samples times modes) →
        (t u : Nat) (m n : Nat) (e b : Bool) →
        stochasticCovariance N t u m n e b ≡
        stochasticCovariance N u t n m b e
      stochasticCovariance-symmetric {samples = samples} N t u m n e b =
        sumFinite-cong samples
          (λ w → probabilityWeight N w *ℚ
            ((componentAmplitude N w t m e -ℚ stochasticMean N t m e) *ℚ
             (componentAmplitude N w u n b -ℚ stochasticMean N u n b)))
          (λ w → probabilityWeight N w *ℚ
            ((componentAmplitude N w u n b -ℚ stochasticMean N u n b) *ℚ
             (componentAmplitude N w t m e -ℚ stochasticMean N t m e)))
          (λ w →
            cong₂ _*ℚ_
              (refl)
              (*ℚ-comm
                (componentAmplitude N w t m e -ℚ stochasticMean N t m e)
                (componentAmplitude N w u n b -ℚ stochasticMean N u n b)))
    
      sumNonnegative :
        (P : RationalPositivity) →
        (n : Nat) → (f : Nat → Rational) →
        ((i : Nat) → Nonnegative P (f i)) →
        Nonnegative P (sumFinite n f)
      sumNonnegative P zero f nonnegative = zeroNonnegative P
      sumNonnegative P (suc n) f nonnegative =
        addNonnegative P
          (nonnegative zero)
          (sumNonnegative P n (λ i → f (suc i))
            (λ i → nonnegative (suc i)))
    
      stochasticVarianceNonnegative :
        {P : RationalPositivity} {samples times modes : Nat} →
        (N : FiniteSEDEnsemble P samples times modes) →
        (t : Nat) (m : Nat) (electric? : Bool) →
        Nonnegative P (stochasticCovariance N t t m m electric? electric?)
      stochasticVarianceNonnegative {P} {samples} N t m electric? =
        sumNonnegative P samples
          (λ w → probabilityWeight N w *ℚ
            ((componentAmplitude N w t m electric? -ℚ
              stochasticMean N t m electric?) *ℚ
             (componentAmplitude N w t m electric? -ℚ
              stochasticMean N t m electric?)))
          (λ w →
            multiplyNonnegative P
              (weightNonnegative N w)
              (squareNonnegative P
                (componentAmplitude N w t m electric? -ℚ
                 stochasticMean N t m electric?)))
    
      -- A finite time-translation action makes stationarity a checkable
      -- condition on the full temporal covariance kernel.
      record FiniteSEDVacuum
        (P : RationalPositivity)
        (samples times modes : Nat) : Set₂ where
        field
          ensemble : FiniteSEDEnsemble P samples times modes
          timeAction : FiniteTimeAction times
          meanZeroElectric : (t : Nat) (m : Nat) →
            stochasticMean ensemble t m true ≡ 0ℚ
          meanZeroMagnetic : (t : Nat) (m : Nat) →
            stochasticMean ensemble t m false ≡ 0ℚ
          covarianceStationary :
            (t u s : Nat) (m n : Nat) (e b : Bool) →
            stochasticCovariance ensemble
              (translateTime timeAction t s)
              (translateTime timeAction u s) m n e b ≡
            stochasticCovariance ensemble t u m n e b
          modeFrequency : Nat → Rational
          frequencyPositive : (m : Nat) →
            Positive P (modeFrequency m)
          hbarScale : Rational
          hbarScalePositive : Positive P hbarScale
          modeEnergyCovariance : (t : Nat) (m : Nat) →
            (stochasticCovariance ensemble t t m m true true +ℚ
             stochasticCovariance ensemble t t m m false false)
            ≡ (hbarScale *ℚ modeFrequency m)
          densityNormalization : Rational
          densityNormalizationPositive : Positive P densityNormalization
          densityScale : Rational
          densityScalePositive : Positive P densityScale
          densityScaleLaw :
            densityScale ≡ (hbarScale *ℚ densityNormalization)
          spectralDensity : Nat → Rational
          spectralDensityPositive : (m : Nat) →
            Positive P (spectralDensity m)
          -- Three-dimensional zero-point energy density target, on a finite
          -- rational frequency grid.  The exact irrational constants and
          -- continuum limit are deliberately not smuggled into Rational.
          omegaCubedLaw : (m : Nat) →
            spectralDensity m ≡
            (densityScale *ℚ
              (modeFrequency m *ℚ
               (modeFrequency m *ℚ modeFrequency m)))
      open FiniteSEDVacuum public
    
      ----------------------------------------------------------------------
      -- CONATURAL INFINITE-HORIZON STATIONARY COVARIANCE ORBIT
      --
      -- The finite solver remains indexed by finite time labels.  The finite
      -- time-translation action induces a productive, potentially infinite
      -- orbit of covariance observations.  This is an infinite translation
      -- history over the finite model, not a claim of a continuum-time limit.
      ----------------------------------------------------------------------
    
      advanceCovarianceShift : {times : Nat} →
        (A : FiniteTimeAction times) → Nat → Nat
      advanceCovarianceShift A shift = translateTime A shift (timeStep A)
    
      covarianceAtShift :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        Nat → Nat → Nat → Nat → Bool → Bool →
        Nat → Rational
      covarianceAtShift V t u m n e b shift =
        stochasticCovariance (ensemble V)
          (translateTime (timeAction V) t shift)
          (translateTime (timeAction V) u shift) m n e b
    
      covarianceAtShift-stationary :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        (t u : Nat) (m n : Nat) (e b : Bool) →
        (shift : Nat) →
        covarianceAtShift V t u m n e b shift ≡
        stochasticCovariance (ensemble V) t u m n e b
      covarianceAtShift-stationary V t u m n e b shift =
        covarianceStationary V t u shift m n e b
    
      covarianceOrbitFromShift :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        (t u : Nat) (m n : Nat) (e b : Bool) →
        Nat → ConatStream Rational
      covarianceOrbitFromShift V t u m n e b initialShift =
        mapConatStream
          (covarianceAtShift V t u m n e b)
          (iterateConat (advanceCovarianceShift (timeAction V))
            infinity initialShift)
    
      covarianceOrbitFromShift-head :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        (t u : Nat) (m n : Nat) (e b : Bool) →
        (shift : Nat) →
        observeStream (covarianceOrbitFromShift V t u m n e b shift) ≡
        just (pair (covarianceAtShift V t u m n e b shift)
          (covarianceOrbitFromShift V t u m n e b
            (advanceCovarianceShift (timeAction V) shift)))
      covarianceOrbitFromShift-head V t u m n e b shift = refl
    
      covarianceOrbitPrefix :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        Nat → (t u : Nat) → (m n : Nat) → Bool → Bool →
        Nat → Rational
      covarianceOrbitPrefix V depth t u m n e b shift =
        foldConatPrefix _+ℚ_ 0ℚ depth
          (covarianceOrbitFromShift V t u m n e b shift)
    
      repeatRationalSum : Nat → Rational → Rational
      repeatRationalSum zero value = 0ℚ
      repeatRationalSum (suc depth) value =
        value +ℚ repeatRationalSum depth value
    
      -- Every finite prefix of the infinite covariance orbit sums the same
      -- stationary covariance value once per observation.  This is a theorem,
      -- not an assumed convergence result or an infinite arithmetic oracle.
      covarianceOrbitPrefix-stationary :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        (depth : Nat) → (t u : Nat) →
        (m n : Nat) → (e b : Bool) →
        (shift : Nat) →
        covarianceOrbitPrefix V depth t u m n e b shift ≡
        repeatRationalSum depth
          (stochasticCovariance (ensemble V) t u m n e b)
      covarianceOrbitPrefix-stationary V zero t u m n e b shift =
        refl
      covarianceOrbitPrefix-stationary V (suc depth) t u m n e b shift
        rewrite covarianceOrbitFromShift-head V t u m n e b shift =
          cong₂ _+ℚ_
            (covarianceAtShift-stationary V t u m n e b shift)
            (covarianceOrbitPrefix-stationary V depth t u m n e b
              (advanceCovarianceShift (timeAction V) shift))
    
      infiniteCovarianceHistory :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        (t u : Nat) → (m n : Nat) → Bool → Bool →
        ConatStream Rational
      infiniteCovarianceHistory V t u m n e b =
        covarianceOrbitFromShift V t u m n e b (timeOrigin (timeAction V))
    
      infiniteCovariancePrefix :
        {P : RationalPositivity} {samples times modes : Nat} →
        (V : FiniteSEDVacuum P samples times modes) →
        Nat → (t u : Nat) → (m n : Nat) → Bool → Bool →
        Rational
      infiniteCovariancePrefix V depth t u m n e b =
        covarianceOrbitPrefix V depth t u m n e b
          (timeOrigin (timeAction V))
    
      ----------------------------------------------------------------------
      -- Exact rational Cayley evolution of each stochastic normal mode.
      -- For h = omega*dt, the oscillator rotation has
      -- c=(4-h²)/(4+h²), s=4h/(4+h²).  Cross multiplication keeps all
      -- equations inside the rational ring and the positive denominator proof
      -- makes the update domain explicit.  The energy law is part of the
      -- certificate and can be checked against any concrete finite trajectory.
      ----------------------------------------------------------------------
    
      fourRational : Rational
      fourRational = twice +ℚ twice
    
      record RationalCayleyModeStep
        (P : RationalPositivity)
        (omega dt electricBefore magneticBefore electricAfter magneticAfter : Rational)
        : Set₁ where
        field
          scaledFrequency : Rational
          scaledFrequencyLaw : scaledFrequency ≡ (omega *ℚ dt)
          denominator : Rational
          denominatorLaw : denominator ≡
            (fourRational +ℚ (scaledFrequency *ℚ scaledFrequency))
          denominatorPositive : Positive P denominator
          electricNumeratorEquation :
            (denominator *ℚ electricAfter) ≡
            (((fourRational -ℚ (scaledFrequency *ℚ scaledFrequency)) *ℚ
              electricBefore) +ℚ
             ((fourRational *ℚ scaledFrequency) *ℚ magneticBefore))
          magneticNumeratorEquation :
            (denominator *ℚ magneticAfter) ≡
            (((0ℚ -ℚ (fourRational *ℚ scaledFrequency)) *ℚ
              electricBefore) +ℚ
             ((fourRational -ℚ (scaledFrequency *ℚ scaledFrequency)) *ℚ
              magneticBefore))
          oscillatorEnergyPreserved :
            ((electricAfter *ℚ electricAfter) +ℚ
             (magneticAfter *ℚ magneticAfter)) ≡
            ((electricBefore *ℚ electricBefore) +ℚ
             (magneticBefore *ℚ magneticBefore))
      open RationalCayleyModeStep public
    
      ----------------------------------------------------------------------
      -- CONSTRUCTIVE FINITE MODE EVALUATOR
      --
      -- Exact Cayley update as numerator/denominator pairs.  This evaluator
      -- computes the finite rational step without floating-point trigonometry
      -- or a partial division operation.  The caller supplies the proof that
      -- the common denominator is nonzero.
      ----------------------------------------------------------------------
    
      cayleyModeDenominator : Rational → Rational
      cayleyModeDenominator h =
        fourRational +ℚ (h *ℚ h)
    
      cayleyModeElectricNumerator :
        Rational → Rational → Rational → Rational
      cayleyModeElectricNumerator h electric magnetic =
        ((fourRational -ℚ (h *ℚ h)) *ℚ electric) +ℚ
        ((fourRational *ℚ h) *ℚ magnetic)
    
      cayleyModeMagneticNumerator :
        Rational → Rational → Rational → Rational
      cayleyModeMagneticNumerator h electric magnetic =
        ((0ℚ -ℚ (fourRational *ℚ h)) *ℚ electric) +ℚ
        ((fourRational -ℚ (h *ℚ h)) *ℚ magnetic)
    
      record RationalCayleyModeFractions : Set where
        constructor rationalCayleyModeFractions
        field
          electricResultFraction : RationalFraction
          magneticResultFraction : RationalFraction
      open RationalCayleyModeFractions public
    
      evaluateRationalCayleyMode :
        (omega dt electric magnetic : Rational) →
        Nonzero (cayleyModeDenominator (omega *ℚ dt)) →
        RationalCayleyModeFractions
      evaluateRationalCayleyMode omega dt electric magnetic denominatorProof =
        let h = omega *ℚ dt
            denominator = cayleyModeDenominator h
        in rationalCayleyModeFractions
          (fraction
            (cayleyModeElectricNumerator h electric magnetic)
            denominator denominatorProof)
          (fraction
            (cayleyModeMagneticNumerator h electric magnetic)
            denominator denominatorProof)
    
      -- Exact polynomial residual of the oscillator energy identity.  It is
      -- computed, never silently cancelled.  Its vanishing is an explicit
      -- proof obligation for a concrete lawful rational instance.
      cayleyModeNumeratorEnergy :
        (h electric magnetic : Rational) → Rational
      cayleyModeNumeratorEnergy h electric magnetic =
        (cayleyModeElectricNumerator h electric magnetic *ℚ
         cayleyModeElectricNumerator h electric magnetic) +ℚ
        (cayleyModeMagneticNumerator h electric magnetic *ℚ
         cayleyModeMagneticNumerator h electric magnetic)
    
      cayleyModeDenominatorEnergy :
        (h electric magnetic : Rational) → Rational
      cayleyModeDenominatorEnergy h electric magnetic =
        (cayleyModeDenominator h *ℚ cayleyModeDenominator h) *ℚ
        ((electric *ℚ electric) +ℚ (magnetic *ℚ magnetic))
    
      cayleyModeEnergyResidual :
        (h electric magnetic : Rational) → Rational
      cayleyModeEnergyResidual h electric magnetic =
        cayleyModeNumeratorEnergy h electric magnetic -ℚ
        cayleyModeDenominatorEnergy h electric magnetic
    
      record VerifiedRationalCayleyModeFractions
        (omega dt electric magnetic : Rational)
        (denominatorProof :
          Nonzero (cayleyModeDenominator (omega *ℚ dt))) : Set₁ where
        field
          fractions : RationalCayleyModeFractions
          fractionsAreComputed :
            fractions ≡ evaluateRationalCayleyMode
              omega dt electric magnetic denominatorProof
          exactEnergyResidualZero :
            cayleyModeEnergyResidual (omega *ℚ dt) electric magnetic ≡ 0ℚ
      open VerifiedRationalCayleyModeFractions public
    
      ----------------------------------------------------------------------
      -- 5. RECONSTRUCTION OF STOCHASTIC ELECTROMAGNETIC FIELDS
      --
      -- A finite mode basis maps stochastic mode amplitudes into actual spatial
      -- electric 1-cochains and magnetic 2-cochains.  The basis obeys Maxwell's
      -- discrete curl eigen-relations.  No continuum Lorentz-invariance claim
      -- is made by this finite-band representation.
      ----------------------------------------------------------------------
    
      record MaxwellModeBasis
        {P : RationalPositivity}
        (H : MetricHodgeComplex P) (modes : Nat)
        (frequency : Nat → Rational) : Set₁ where
        field
          electricMode : Nat → Cochain (n₁ (complex H))
          magneticMode : Nat → Cochain (n₂ (complex H))
          modeFaraday : (m : Nat) →
            _≡_
              (d₁ (complex H) (electricMode m))
              (scaleCochain (frequency m) (magneticMode m))
          modeAmpere : (m : Nat) →
            _≡_
              (δ₂ H (magneticMode m))
              (scaleCochain (frequency m) (electricMode m))
      open MaxwellModeBasis public
    
      sumCochain :
        {n : Nat} → (k : Nat) → (Nat → Cochain n) → Cochain n
      sumCochain zero f = zeroCochain
      sumCochain (suc k) f =
        addCochain (f zero) (sumCochain k (λ i → f (suc i)))
    
      sampleElectricField :
        {P : RationalPositivity} {samples times modes : Nat} →
        {frequency : Nat → Rational} →
        (H : MetricHodgeComplex P) →
        (B : MaxwellModeBasis H modes frequency) →
        (N : FiniteSEDEnsemble P samples times modes) →
        Nat → Nat → Cochain (n₁ (complex H))
      sampleElectricField H B N w t =
        sumCochain _ (λ m →
          scaleCochain (electricAmplitude N w t m) (electricMode B m))
    
      sampleMagneticField :
        {P : RationalPositivity} {samples times modes : Nat} →
        {frequency : Nat → Rational} →
        (H : MetricHodgeComplex P) →
        (B : MaxwellModeBasis H modes frequency) →
        (N : FiniteSEDEnsemble P samples times modes) →
        Nat → Nat → Cochain (n₂ (complex H))
      sampleMagneticField H B N w t =
        sumCochain _ (λ m →
          scaleCochain (magneticAmplitude N w t m) (magneticMode B m))
    
      ----------------------------------------------------------------------
      -- 6. FINITE SED VACUUM-MAXWELL WORLD
      --
      -- This is the source-free zero-point background sector. Charged particle
      -- deposition, self-consistent source current, and recoil are a separate
      -- coupled-matter layer and are not claimed by this record.
      ----------------------------------------------------------------------
    
      record FiniteSEDVacuumMaxwellWorld
        (P : RationalPositivity)
        (samples times modes : Nat) : Set₃ where
        field
          hodgeMaxwell : MetricHodgeComplex P
          zpfVacuum : FiniteSEDVacuum P samples times modes
          modeBasis : MaxwellModeBasis hodgeMaxwell modes
            (modeFrequency zpfVacuum)
          timeStepSize : Rational
          timeStepPositive : Positive P timeStepSize
          sampleState : Nat → Nat → MaxwellState hodgeMaxwell
          sampleModeCayleyTransition :
            (w : Nat) (t : Nat) (m : Nat) →
            RationalCayleyModeStep P
              (modeFrequency zpfVacuum m) timeStepSize
              (electricAmplitude (ensemble zpfVacuum) w t m)
              (magneticAmplitude (ensemble zpfVacuum) w t m)
              (electricAmplitude (ensemble zpfVacuum) w
                (nextTime (timeAction zpfVacuum) t) m)
              (magneticAmplitude (ensemble zpfVacuum) w
                (nextTime (timeAction zpfVacuum) t) m)
          sampleFieldMatchesElectricModes :
            (w : Nat) (t : Nat) →
            _≡_
              (electricField (sampleState w t))
              (sumCochain modes
                (λ m → scaleCochain
                  (electricAmplitude (ensemble zpfVacuum) w t m)
                  (electricMode modeBasis m)))
          sampleFieldMatchesMagneticModes :
            (w : Nat) (t : Nat) →
            _≡_
              (magneticField (sampleState w t))
              (sumCochain modes
                (λ m → scaleCochain
                  (magneticAmplitude (ensemble zpfVacuum) w t m)
                  (magneticMode modeBasis m)))
          sampleVacuumChargeFree : (w : Nat) (t : Nat) →
            _≡_ (chargeDensity (sampleState w t)) zeroCochain
          sampleElectricHodgeSplit : (w : Nat) (t : Nat) →
            HodgeDecomposition₁ hodgeMaxwell (electricField (sampleState w t))
          sampleMagneticHodgeSplit : (w : Nat) (t : Nat) →
            HodgeDecomposition₂ hodgeMaxwell (magneticField (sampleState w t))
          sampleMaxwellTransition :
            (w : Nat) (t : Nat) →
            MaxwellMidpointStep hodgeMaxwell timeStepSize zeroCochain
              (sampleState w t)
              (sampleState w (nextTime (timeAction zpfVacuum) t))
          initialMomentum : Exchange.ClosedMomentumSnapshot
          momentumExchanges : List Exchange.MomentumExchange
          euclideanLaws : RationalTrigonometryLawWitness
          cohesiveSyntax : CohesiveExpr
      open FiniteSEDVacuumMaxwellWorld public
    
      ----------------------------------------------------------------------
      -- 7. Q5-A PHYSICAL MOTIVE OVER THE COMPLETE FINITE WORLD
      --
      -- This bundles the actual certified properties of a world, including
      -- the finite Maxwell steps, Hodge splits, SED spectrum and closed-system
      -- momentum theorem.  It is indexed by the complete world value.
      ----------------------------------------------------------------------
    
      record FiniteSEDVacuumMotive
        (P : RationalPositivity)
        (samples times modes : Nat)
        (W : FiniteSEDVacuumMaxwellWorld P samples times modes) : Set₁ where
        field
          probabilityNormalization :
            sumFinite samples (probabilityWeight (ensemble (zpfVacuum W))) ≡ 1ℚ
          electricMeanZero : (t : Nat) (m : Nat) →
            stochasticMean (ensemble (zpfVacuum W)) t m true ≡ 0ℚ
          magneticMeanZero : (t : Nat) (m : Nat) →
            stochasticMean (ensemble (zpfVacuum W)) t m false ≡ 0ℚ
          electricVarianceNonnegative : (t : Nat) (m : Nat) →
            Nonnegative P (stochasticCovariance (ensemble (zpfVacuum W))
              t t m m true true)
          magneticVarianceNonnegative : (t : Nat) (m : Nat) →
            Nonnegative P (stochasticCovariance (ensemble (zpfVacuum W))
              t t m m false false)
          covarianceStationarity :
            (t u s : Nat) (m n : Nat) (e b : Bool) →
            stochasticCovariance (ensemble (zpfVacuum W))
              (translateTime (timeAction (zpfVacuum W)) t s)
              (translateTime (timeAction (zpfVacuum W)) u s) m n e b ≡
            stochasticCovariance (ensemble (zpfVacuum W)) t u m n e b
          covarianceSymmetry : (t u : Nat) (m n : Nat) (e b : Bool) →
            stochasticCovariance (ensemble (zpfVacuum W)) t u m n e b ≡
            stochasticCovariance (ensemble (zpfVacuum W)) u t n m b e
          -- Executable access to finite prefixes of the conatural infinite
          -- stationary-translation covariance history.  No limit-existence axiom
          -- is implied: every requested prefix is computed by finite folding.
          conaturalCovariancePrefix :
            (depth : Nat) (t u : Nat) (m n : Nat) (e b : Bool) →
            Rational
          conaturalCovariancePrefixStationary :
            (depth : Nat) (t u : Nat) (m n : Nat) (e b : Bool) →
            (shift : Nat) →
            covarianceOrbitPrefix (zpfVacuum W) depth t u m n e b shift ≡
            repeatRationalSum depth
              (stochasticCovariance (ensemble (zpfVacuum W)) t u m n e b)
          zeroPointModeEnergy : (t : Nat) (m : Nat) →
            (stochasticCovariance (ensemble (zpfVacuum W)) t t m m true true +ℚ
             stochasticCovariance (ensemble (zpfVacuum W)) t t m m false false)
            ≡ (hbarScale (zpfVacuum W) *ℚ modeFrequency (zpfVacuum W) m)
          densityScaleCalibration :
            densityScale (zpfVacuum W) ≡
            (hbarScale (zpfVacuum W) *ℚ densityNormalization (zpfVacuum W))
          finiteBandSpectrum : (m : Nat) →
            spectralDensity (zpfVacuum W) m ≡
            (densityScale (zpfVacuum W) *ℚ
              (modeFrequency (zpfVacuum W) m *ℚ
               (modeFrequency (zpfVacuum W) m *ℚ modeFrequency (zpfVacuum W) m)))
          modeCayleyEvolution : (w : Nat) (t : Nat) (m : Nat) →
            RationalCayleyModeStep P
              (modeFrequency (zpfVacuum W) m) (timeStepSize W)
              (electricAmplitude (ensemble (zpfVacuum W)) w t m)
              (magneticAmplitude (ensemble (zpfVacuum W)) w t m)
              (electricAmplitude (ensemble (zpfVacuum W)) w
                (nextTime (timeAction (zpfVacuum W)) t) m)
              (magneticAmplitude (ensemble (zpfVacuum W)) w
                (nextTime (timeAction (zpfVacuum W)) t) m)
          electricHodge : (w : Nat) (t : Nat) →
            HodgeDecomposition₁ hodgeMaxwell (electricField (sampleState W w t))
          magneticHodge : (w : Nat) (t : Nat) →
            HodgeDecomposition₂ hodgeMaxwell (magneticField (sampleState W w t))
          vacuumMaxwellStep : (w : Nat) (t : Nat) →
            MaxwellMidpointStep hodgeMaxwell timeStepSize zeroCochain
              (sampleState W w t)
              (sampleState W w (nextTime (timeAction (zpfVacuum W)) t))
          totalMomentumConservation :
            Exchange.runExchanges-conserves (momentumExchanges W) (initialMomentum W)
      open FiniteSEDVacuumMotive public
    
      assembleFiniteSEDVacuumMotive :
        {P : RationalPositivity} {samples times modes : Nat} →
        (W : FiniteSEDVacuumMaxwellWorld P samples times modes) →
        FiniteSEDVacuumMotive P samples times modes W
      assembleFiniteSEDVacuumMotive W = record
        { probabilityNormalization = normalizedWeights (ensemble (zpfVacuum W))
        ; electricMeanZero = meanZeroElectric (zpfVacuum W)
        ; magneticMeanZero = meanZeroMagnetic (zpfVacuum W)
        ; electricVarianceNonnegative = λ t m → stochasticVarianceNonnegative (ensemble (zpfVacuum W)) t m true
        ; magneticVarianceNonnegative = λ t m → stochasticVarianceNonnegative (ensemble (zpfVacuum W)) t m false
        ; covarianceStationarity = covarianceStationary (zpfVacuum W)
        ; covarianceSymmetry = stochasticCovariance-symmetric (ensemble (zpfVacuum W))
        ; conaturalCovariancePrefix = λ depth t u m n e b →
            infiniteCovariancePrefix (zpfVacuum W) depth t u m n e b
        ; conaturalCovariancePrefixStationary =
            covarianceOrbitPrefix-stationary (zpfVacuum W)
        ; zeroPointModeEnergy = modeEnergyCovariance (zpfVacuum W)
        ; densityScaleCalibration = densityScaleLaw (zpfVacuum W)
        ; finiteBandSpectrum = omegaCubedLaw (zpfVacuum W)
        ; modeCayleyEvolution = sampleModeCayleyTransition W
        ; electricHodge = sampleElectricHodgeSplit W
        ; magneticHodge = sampleMagneticHodgeSplit W
        ; vacuumMaxwellStep = sampleMaxwellTransition W
        ; totalMomentumConservation =
            Exchange.runExchanges-conserves (momentumExchanges W) (initialMomentum W)
        }
    
    
    ------------------------------------------------------------------------
    -- End RSEDPhysicalFoundations
    ------------------------------------------------------------------------
    
    ------------------------------------------------------------------------
    -- End of self-contained single-file Agda monolith.
    ------------------------------------------------------------------------
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
  
  -- Checked ABI values must carry one of the two source-language modalities.
  data AnnotatedMode : RuntimeMode → Set where
    checkedLinearMode : AnnotatedMode linearMode
    checkedModalMode : AnnotatedMode modalMode
  
  sourceMode : SourceMode → RuntimeMode
  sourceMode linear = linearMode
  sourceMode modal = modalMode
  
  data Life : Set where
    live consumed : Life
  
  data Kind : Set where
    thunk result scalar boolean : Kind
  
  data RuntimeError : Set where
    unknownHandle consumedHandle invalidMode wrongKind : RuntimeError
    aliasedLinearOperands : RuntimeError
    expectedScalar expectedBoolean invalidBoolean : RuntimeError
    linearCaptureNotAccounted modalPromotionRejected : RuntimeError
    unknownPrimitive badStackEffect : RuntimeError
    badResultPayload abiEscapeHatch : RuntimeError
    arithmeticDomainError arithmeticOverflowError identityOverflowError : RuntimeError
    nullExecutionTokenError : RuntimeError
  
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
    notSelfLess (subst {P = λ k → n < k} nextEqN nBelow)
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
  
  -- Checked descriptors point only to older identities. Since allocation identities
  -- strictly increase, this rules out direct cycles and supports finite recursive
  -- retirement of captured linear subtrees on exceptional exit.
  ReferencesOlder : Heap → Set
  ReferencesOlder [] = ⊤
  ReferencesOlder (d :: ds) =
    AllBelow (key d) (references d) × ReferencesOlder ds
  
  noDirectSelfReference :
    (d : Descriptor) →
    AllBelow (key d) (references d) →
    (key d ∈ₙ references d) → ⊥
  noDirectSelfReference d = freshNotPresent
  
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
  
  liveLinearAtKey :
    {d : Descriptor} {h : Heap} →
    HasDescriptor d h →
    mode d ≡ linearMode →
    life d ≡ live →
    HasLiveLinear (key d) h
  liveLinearAtKey descriptorHere modeIsLinear lifeIsLive =
    linearLiveHere refl modeIsLinear lifeIsLive
  liveLinearAtKey (descriptorThere registered) modeIsLinear lifeIsLive =
    linearLiveThere (liveLinearAtKey registered modeIsLinear lifeIsLive)
  
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
  
  -- A live result wrapper is an active owner/reference to its contained payload.
  -- This matters when the payload is a live linear thunk with captures.
  activePayloads : Heap → List Nat
  activePayloads [] = []
  activePayloads (d :: ds) with kind d | life d | payloadRef d
  ... | result | live | hasPayload n = n :: activePayloads ds
  ... | _ | _ | _ = activePayloads ds
  
  LivePayloads : Heap → Heap → Set
  LivePayloads full [] = ⊤
  LivePayloads full (d :: ds) with kind d | life d | payloadRef d
  ... | result | live | hasPayload n = HasLive n full × LivePayloads full ds
  ... | result | live | noPayload = ⊥ × LivePayloads full ds
  ... | _ | _ | _ = LivePayloads full ds
  
  LiveResultPayloadModes : Heap → Heap → Set
  LiveResultPayloadModes full [] = ⊤
  LiveResultPayloadModes full (d :: ds) with kind d | life d | mode d | payloadRef d
  ... | result | live | linearMode | hasPayload n =
    HasLiveLinear n full × LiveResultPayloadModes full ds
  ... | result | live | modalMode | hasPayload n =
    HasLiveModal n full × LiveResultPayloadModes full ds
  ... | result | live | _ | noPayload =
    ⊥ × LiveResultPayloadModes full ds
  ... | _ | _ | _ | _ = LiveResultPayloadModes full ds
  
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
  activeReferences s = roots s ++ activeCaptures (heap s) ++ activePayloads (heap s)
  
  record WellFormed (s : Machine) : Set where
    constructor wellFormed
    field
      identityUnique : NoDup (keys (heap s))
      rootsRegistered : AllIn (roots s) (keys (heap s))
      rootsLive : AllLive (roots s) (heap s)
      allReferencesRegistered : RegisteredRefs (heap s) (heap s)
      referencesDescendByIdentity : ReferencesOlder (heap s)
      activeCapturesLive : LiveCaptures (heap s) (heap s)
      liveResultPayloads : LivePayloads (heap s) (heap s)
      resultPayloadModes : LiveResultPayloadModes (heap s) (heap s)
      everyLinearResourceOwned : LiveLinearOwned (heap s) (activeReferences s)
      noLinearAliasing : NoDupOn (λ n → HasLiveLinear n (heap s)) (activeReferences s)
      noLiveUnannotated : AllAnnotated (heap s)
      nextIdentityFresh : AllBelow (nextIdentity s) (keys (heap s))
  open WellFormed public
  
  -- The operand-root list records the two inputs as separate positions.
  record OperandRoots (left right : Nat) (xs : List Nat) : Set where
    constructor operandRoots
    field
      rootTail : List Nat
      rootsContainBothOperands : xs ≡ left :: right :: rootTail
  open OperandRoots public
  
  record BinaryScalarPrecondition
    (s : Machine) (left right : Descriptor) : Set where
    constructor binaryScalarPrecondition
    field
      leftRegistered : HasDescriptor left (heap s)
      rightRegistered : HasDescriptor right (heap s)
      leftIsScalar : kind left ≡ scalar
      rightIsScalar : kind right ≡ scalar
      leftIsLive : life left ≡ live
      rightIsLive : life right ≡ live
      leftHasCheckedMode : AnnotatedMode (mode left)
      rightHasCheckedMode : AnnotatedMode (mode right)
      operandRootOrder : OperandRoots (key left) (key right) (roots s)
  open BinaryScalarPrecondition public
  
  -- A well-formed machine has no linear aliasing. Because the binary-call
  -- precondition records two separate operand-root positions, an aliased live
  -- linear input contradicts the machine invariant constructively.
  linearOperandsCannotAlias :
    (s : Machine) → WellFormed s →
    {left right : Descriptor} →
    BinaryScalarPrecondition s left right →
    key left ≡ key right →
    mode left ≡ linearMode → ⊥
  linearOperandsCannotAlias s wf {left} {right} pre sameIdentity leftLinear
    with subst
      {P = λ rs →
        NoDupOn (λ n → HasLiveLinear n (heap s))
          (rs ++ activeCaptures (heap s) ++ activePayloads (heap s))}
      (rootsContainBothOperands (operandRootOrder pre))
      (noLinearAliasing wf)
  ... | (noRepeatedLinearRoot , _) =
    noRepeatedLinearRoot
      (liveLinearAtKey (leftRegistered pre) leftLinear (leftIsLive pre))
      (here sameIdentity)
  
  nextIsFresh :
    (s : Machine) → WellFormed s →
    (nextIdentity s ∈ₙ keys (heap s)) → ⊥
  nextIsFresh s wf = freshNotPresent (nextIdentityFresh wf)
  
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
  
  -- Do not model ownership with a bare indexed token. A constructor of the form
  -- `token : Token identity mode life` for arbitrary indices makes each such
  -- proposition trivially inhabited and proves no real consume/move transition.
  -- Linear ownership is therefore expressed by the heap/root/capture invariant in
  -- `WellFormed`: every live linear descriptor has exactly one active reference,
  -- while `CanDuplicate` and `CanDiscard` permit those structural rules only for
  -- modal values. Runtime refinement remains a separate obligation.
  
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
  
  -- Equality utilities used to derive exclusivity from the machine invariants.
  symEq : {A : Set} {x y : A} → x ≡ y → y ≡ x
  symEq refl = refl
  
  transEq : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  transEq refl q = q
  
  modalIsNotLinear : modalMode ≡ linearMode → ⊥
  modalIsNotLinear ()
  
  modalKeyMember :
    {n : Nat} {h : Heap} → HasLiveModal n h → n ∈ₙ keys h
  modalKeyMember (modalLiveHere keyEq _ _) = here (symEq keyEq)
  modalKeyMember (modalLiveThere p) = there (modalKeyMember p)
  
  linearKeyMember :
    {n : Nat} {h : Heap} → HasLiveLinear n h → n ∈ₙ keys h
  linearKeyMember (linearLiveHere keyEq _ _) = here (symEq keyEq)
  linearKeyMember (linearLiveThere p) = there (linearKeyMember p)
  
  -- One identity cannot simultaneously denote live modal and live linear
  -- descriptors in a heap whose descriptor identities are unique.
  notBothLiveModes :
    (h : Heap) → NoDup (keys h) → {n : Nat} →
    HasLiveModal n h → HasLiveLinear n h → ⊥
  notBothLiveModes [] unique () _
  notBothLiveModes (d :: ds) (noDupHead , noDupTail)
    (modalLiveHere keyEq modalEq _) (linearLiveHere _ linearEq _) =
      modalIsNotLinear (transEq (symEq modalEq) linearEq)
  notBothLiveModes (d :: ds) (noDupHead , noDupTail)
    (modalLiveHere keyEq _ _) (linearLiveThere linearTail) =
      noDupHead
        (subst {P = λ k → k ∈ₙ keys ds}
          (symEq keyEq) (linearKeyMember linearTail))
  notBothLiveModes (d :: ds) (noDupHead , noDupTail)
    (modalLiveThere modalTail) (linearLiveHere keyEq _ _) =
      noDupHead
        (subst {P = λ k → k ∈ₙ keys ds}
          (symEq keyEq) (modalKeyMember modalTail))
  notBothLiveModes (d :: ds) (noDupHead , noDupTail)
    (modalLiveThere modalTail) (linearLiveThere linearTail) =
      notBothLiveModes ds noDupTail modalTail linearTail
  
  modalWitnessForMember :
    {h : Heap} → (ids : List Nat) → {n : Nat} →
    AllModal ids h → n ∈ₙ ids → HasLiveModal n h
  modalWitnessForMember [] allModal ()
  modalWitnessForMember {h = h} (x :: xs) (headModal , tailModal) (here eq) =
    subst {P = λ k → HasLiveModal k h} (symEq eq) headModal
  modalWitnessForMember (x :: xs) (headModal , tailModal) (there member) =
    modalWitnessForMember xs tailModal member
  
  -- A well-formed heap plus a promotion precondition proves that no captured
  -- identity is a live linear value. This is a genuine consequence of both
  -- pieces of evidence, not a trusted execution-token flag.
  promotionExcludesLinearCaptures :
    (s : Machine) → WellFormed s → {d : Descriptor} →
    PromotionPrecondition s d →
    (n : Nat) → n ∈ₙ captures d → HasLiveLinear n (heap s) → ⊥
  promotionExcludesLinearCaptures s wf {d} pre n captured linearWitness =
    notBothLiveModes (heap s) (identityUnique wf)
      (modalWitnessForMember (captures d) (capturedValuesModal pre) captured)
      linearWitness
  
  -- Opaque user Forth execution tokens can never satisfy modal promotion's
  -- closed-code evidence requirement.
  noOpaqueModalCode : ModalCode codeOpaque → ⊥
  noOpaqueModalCode ()
  
  promotionExcludesOpaqueCode :
    {s : Machine} {d : Descriptor} →
    PromotionPrecondition s d → codeClass d ≡ codeOpaque → ⊥
  promotionExcludesOpaqueCode pre codeEq =
    noOpaqueModalCode
      (subst {P = ModalCode} codeEq (modalCodeWitness pre))
  
  -- The core-language model covers these operations; escape hatches are excluded.
  data Primitive : Set where
    pNatAdd pNatSub pNatMul pNatQuot pNatRem : Primitive
    pNatEq pNatGeq pNatLt pNatMonus pIf : Primitive
    pMakeScalar pMakeBool pMakeThunk pApply pForce pMakeResult pUnwrapResult : Primitive
    pPromoteModal pAssertLinear pConstruct pMatch pPrint pThrow pCatch : Primitive
  
  
  -- Complete profile table for every primitive admitted by the proposed checked
  -- core ABI. This table is a specification; implementation correspondence is a
  -- separate theorem and is currently an open obligation.
  data Arity : Set where
    fixedArity : Nat → Arity
    constructorDefinedArity matcherDefinedArity : Arity
  
  data OperandRule : Set where
    twoCheckedScalars : OperandRule
    threeCheckedBranches : OperandRule
    modeAndScalar modeAndBoolean : OperandRule
    checkedCode : OperandRule
    checkedClosureAndValue : OperandRule
    checkedClosure : OperandRule
    checkedResult : OperandRule
    checkedThunk : OperandRule
    checkedConstructorFields : OperandRule
    checkedMatchInputs : OperandRule
    checkedObservableValue : OperandRule
    checkedErrorAndHandler : OperandRule
  
  data OwnershipEffect : Set where
    consumeLinearOperands : OwnershipEffect
    makeFreshScalar makeFreshBoolean : OwnershipEffect
    makeFreshClosure : OwnershipEffect
    moveCaptures : OwnershipEffect
    forceByMode : OwnershipEffect
    moveIntoResult : OwnershipEffect
    moveOutOfResult : OwnershipEffect
    promoteOnlyWithProof : OwnershipEffect
    markLinearOnlyWithProof : OwnershipEffect
    moveConstructorFields : OwnershipEffect
    accountPatternFields : OwnershipEffect
    selectBranchAndAccountResources : OwnershipEffect
    observeWithoutHiddenForce : OwnershipEffect
    raiseCheckedError : OwnershipEffect
    catchAndPreserveState : OwnershipEffect
  
  data ResultModeRule : Set where
    joinOperandModes : ResultModeRule
    selectedBranchMode : ResultModeRule
    inputMode : ResultModeRule
    codeResultMode : ResultModeRule
    freshAnnotatedMode : ResultModeRule
    noValue : ResultModeRule
  
  data EvidenceRequirement : Set where
    noCodeEvidence : EvidenceRequirement
    runtimeValueValidation : EvidenceRequirement
    compilerDerivedCodeProof : EvidenceRequirement
    explicitlyTrustedLegacyCode : EvidenceRequirement
  
  record PrimitiveSpec (p : Primitive) : Set where
    constructor mkPrimitiveSpec
    field
      stackArity : Arity
      operandRule : OperandRule
      ownershipRule : OwnershipEffect
      resultModeRule : ResultModeRule
      evidenceRequirement : EvidenceRequirement
      possibleErrors : List RuntimeError
  open PrimitiveSpec public
  
  numericErrors : List RuntimeError
  numericErrors = unknownHandle :: consumedHandle :: wrongKind :: expectedScalar ::
    invalidMode :: aliasedLinearOperands :: arithmeticOverflowError :: identityOverflowError :: []
  
  booleanErrors : List RuntimeError
  booleanErrors = unknownHandle :: consumedHandle :: wrongKind :: expectedBoolean :: invalidMode :: invalidBoolean :: identityOverflowError :: []
  
  divisionErrors : List RuntimeError
  divisionErrors = numericErrors ++ (arithmeticDomainError :: [])
  
  closureErrors : List RuntimeError
  closureErrors = unknownHandle :: consumedHandle :: wrongKind ::
    invalidMode :: badStackEffect :: identityOverflowError :: nullExecutionTokenError :: []
  
  modalErrors : List RuntimeError
  modalErrors = unknownHandle :: consumedHandle :: wrongKind ::
    modalPromotionRejected :: badResultPayload :: []
  
  constructErrors : List RuntimeError
  constructErrors = unknownHandle :: consumedHandle :: wrongKind ::
    badStackEffect :: abiEscapeHatch :: identityOverflowError :: []
  
  throwErrors : List RuntimeError
  throwErrors = abiEscapeHatch :: []
  
  primitiveSpecFor : (p : Primitive) → PrimitiveSpec p
  primitiveSpecFor pNatAdd = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
  primitiveSpecFor pNatSub = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
  primitiveSpecFor pNatMul = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
  primitiveSpecFor pNatQuot = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation divisionErrors
  primitiveSpecFor pNatRem = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation divisionErrors
  primitiveSpecFor pNatEq = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation (numericErrors ++ (invalidBoolean :: []))
  primitiveSpecFor pNatGeq = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation (numericErrors ++ (invalidBoolean :: []))
  primitiveSpecFor pNatLt = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation (numericErrors ++ (invalidBoolean :: []))
  primitiveSpecFor pNatMonus = mkPrimitiveSpec (fixedArity 2) twoCheckedScalars consumeLinearOperands joinOperandModes runtimeValueValidation numericErrors
  primitiveSpecFor pIf = mkPrimitiveSpec (fixedArity 3) threeCheckedBranches selectBranchAndAccountResources selectedBranchMode runtimeValueValidation closureErrors
  primitiveSpecFor pMakeScalar = mkPrimitiveSpec (fixedArity 2) modeAndScalar makeFreshScalar inputMode noCodeEvidence (invalidMode :: numericErrors)
  primitiveSpecFor pMakeBool = mkPrimitiveSpec (fixedArity 2) modeAndBoolean makeFreshBoolean inputMode runtimeValueValidation booleanErrors
  primitiveSpecFor pMakeThunk = mkPrimitiveSpec (fixedArity 2) checkedCode makeFreshClosure codeResultMode compilerDerivedCodeProof closureErrors
  primitiveSpecFor pApply = mkPrimitiveSpec (fixedArity 2) checkedClosureAndValue moveCaptures codeResultMode compilerDerivedCodeProof closureErrors
  primitiveSpecFor pForce = mkPrimitiveSpec (fixedArity 1) checkedClosure forceByMode codeResultMode compilerDerivedCodeProof closureErrors
  primitiveSpecFor pMakeResult = mkPrimitiveSpec (fixedArity 1) checkedObservableValue moveIntoResult inputMode runtimeValueValidation closureErrors
  primitiveSpecFor pUnwrapResult = mkPrimitiveSpec (fixedArity 1) checkedResult moveOutOfResult inputMode runtimeValueValidation closureErrors
  primitiveSpecFor pPromoteModal = mkPrimitiveSpec (fixedArity 1) checkedThunk promoteOnlyWithProof inputMode compilerDerivedCodeProof modalErrors
  primitiveSpecFor pAssertLinear = mkPrimitiveSpec (fixedArity 1) checkedThunk markLinearOnlyWithProof inputMode compilerDerivedCodeProof modalErrors
  primitiveSpecFor pConstruct = mkPrimitiveSpec constructorDefinedArity checkedConstructorFields moveConstructorFields codeResultMode compilerDerivedCodeProof constructErrors
  primitiveSpecFor pMatch = mkPrimitiveSpec matcherDefinedArity checkedMatchInputs accountPatternFields selectedBranchMode compilerDerivedCodeProof constructErrors
  primitiveSpecFor pPrint = mkPrimitiveSpec (fixedArity 1) checkedObservableValue observeWithoutHiddenForce noValue runtimeValueValidation numericErrors
  primitiveSpecFor pThrow = mkPrimitiveSpec (fixedArity 1) checkedErrorAndHandler raiseCheckedError noValue noCodeEvidence throwErrors
  primitiveSpecFor pCatch = mkPrimitiveSpec (fixedArity 2) checkedErrorAndHandler catchAndPreserveState inputMode noCodeEvidence (unknownHandle :: badStackEffect :: [])
  
  -- This exhaustive function is accepted by Agda only if every Primitive constructor
  -- has a profile. It does not claim that each Gforth implementation satisfies it.
  specifiesEveryPrimitive : (p : Primitive) → PrimitiveSpec p
  specifiesEveryPrimitive = primitiveSpecFor
  
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
  
  -- Weakest-precondition semantics is the authoritative contract interface.
  -- A command is modeled as a total state transformer into an explicit outcome:
  -- normal return or a THROW carrying both the post-state and error.  The WP
  -- requires the normal postcondition on return and the exceptional postcondition
  -- on every exceptional exit.  Divergence is not silently identified with
  -- success: the current Execution model is total-outcome and does not model
  -- divergence; finite-fuel denotation below records exhaustion explicitly.
  wp :
    {S : Set} →
    (command : S → Execution S) →
    (normalPostcondition : S → Set) →
    (exceptionalPostcondition : S → RuntimeError → Set) →
    S → Set
  wp command normalPostcondition exceptionalPostcondition s =
    executionPost normalPostcondition exceptionalPostcondition (command s)
  
  -- Sequential composition propagates THROW without running the next command.
  sequenceExecution :
    {S : Set} → Execution S → (S → Execution S) → Execution S
  sequenceExecution (returned s) next = next s
  sequenceExecution (thrown s e) next = thrown s e
  
  sequence :
    {S : Set} →
    (first second : S → Execution S) → S → Execution S
  sequence first second s = sequenceExecution (first s) second
  
  -- Dijkstra's sequencing law: compute the later condition first, then pull it
  -- backwards through the first command. Exceptional exits of the first command
  -- use the final exceptional postcondition directly.
  wpSequence :
    {S : Set} →
    (first second : S → Execution S) →
    (normalPostcondition : S → Set) →
    (exceptionalPostcondition : S → RuntimeError → Set) →
    (s : S) →
    wp (sequence first second) normalPostcondition exceptionalPostcondition s ≡
    wp first
      (λ s' → wp second normalPostcondition exceptionalPostcondition s')
      exceptionalPostcondition s
  wpSequence first second normalPostcondition exceptionalPostcondition s
    with first s
  ... | returned s' = refl
  ... | thrown s' e = refl
  
  -- Weakest-precondition rule for CATCH: when the protected command throws,
  -- its actual post-state and error are passed to the handler's WP.  On normal
  -- return, the handler is irrelevant.
  wpCatch :
    {S : Set} →
    (command : S → Execution S) →
    (handler : RuntimeError → S → Execution S) →
    (normalPostcondition : S → Set) →
    (exceptionalPostcondition : S → RuntimeError → Set) →
    (s : S) →
    wp (λ state → catchExecution (command state) handler)
      normalPostcondition exceptionalPostcondition s
    ≡
    wp command normalPostcondition
      (λ state err → wp (λ state' → handler err state')
        normalPostcondition exceptionalPostcondition state) s
  wpCatch command handler normalPostcondition exceptionalPostcondition s
    with command s
  ... | returned s' = refl
  ... | thrown s' e = refl
  
  -- Operational correctness is defined directly from command outcomes.
  -- There is deliberately no parallel triple API or second rule system.
  SemanticTriple :
    {S : Set} →
    (precondition : S → Set) →
    (command : S → Execution S) →
    (normalPostcondition : S → Set) →
    (exceptionalPostcondition : S → RuntimeError → Set) →
    Set
  SemanticTriple {S} precondition command normalPostcondition exceptionalPostcondition =
    (s : S) → precondition s →
    executionPost normalPostcondition exceptionalPostcondition (command s)
  
  -- The WP predicate itself is a valid precondition for the requested outcomes.
  wpSemanticallyAdmissible :
    {S : Set}
    (command : S → Execution S)
    (normalPostcondition : S → Set)
    (exceptionalPostcondition : S → RuntimeError → Set) →
    SemanticTriple
      (wp command normalPostcondition exceptionalPostcondition)
      command normalPostcondition exceptionalPostcondition
  wpSemanticallyAdmissible command normalPostcondition exceptionalPostcondition
    s preconditionProof = preconditionProof
  
  -- Leastness from the operational contract: any precondition which proves the
  -- requested outcome entails WP. This is precondition validity/leastness for
  -- the finite Execution model, not domain-theoretic admissibility over a domain.
  wpLeastnessFromOperationalSemantics :
    {S : Set}
    (precondition : S → Set)
    (command : S → Execution S)
    (normalPostcondition : S → Set)
    (exceptionalPostcondition : S → RuntimeError → Set) →
    SemanticTriple precondition command normalPostcondition exceptionalPostcondition →
    (s : S) → precondition s →
    wp command normalPostcondition exceptionalPostcondition s
  wpLeastnessFromOperationalSemantics precondition command normalPostcondition
    exceptionalPostcondition valid s proof = valid s proof
  
  skip : {S : Set} → S → Execution S
  skip s = returned s
  
  wpSkip :
    {S : Set} {P : S → Set} →
    (s : S) → P s →
    wp skip P (λ state err → P state) s
  wpSkip s proof = proof
  
  -- CATCH preservation is derived directly from the WP contract of the protected
  -- command and the handler's operational outcome.
  wpCatchPreserves :
    {S : Set} {P : S → Set}
    (command : S → Execution S)
    (handler : RuntimeError → S → Execution S) →
    ((s : S) → P s → wp command P (λ state err → P state) s) →
    ((err : RuntimeError) (state : S) → P state →
      executionPost P (λ state' err' → P state') (handler err state)) →
    (s : S) → P s →
    wp (λ state → catchExecution (command state) handler)
      P (λ state err → P state) s
  wpCatchPreserves command handler commandSafe handlerSafe s proof
    with command s | commandSafe s proof
  ... | returned s' | normalProof = normalProof
  ... | thrown s' err | exceptionalProof = handlerSafe err s' exceptionalProof
  
  
  -- ── 2. Closed checked-ABI stack effects ──
  
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
    rawBoolItem : StackItem
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
  -- LinearModalSafety; these effects say which well-typed shapes an operation accepts.
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
  
    makeBooleanEffect : {m : SourceMode} {tail : StackShape} →
      StackEffect pMakeBool
        (modeTokenItem m :: rawBoolItem :: tail)
        (valueItem (booleanTypeFor m) :: tail)
  
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
  
  -- A stack-tail frame law for the declarative stack-effect semantics.
  -- It is stronger than testing a primitive at an empty stack: any framed suffix
  -- remains unchanged by the specified effect. This is a theorem about StackEffect,
  -- not yet the implementation-correspondence theorem for the Forth word.
  stackAppendAssoc :
    {A : Set} (xs ys zs : List A) →
    ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  stackAppendAssoc [] ys zs = refl
  stackAppendAssoc (x :: xs) ys zs rewrite stackAppendAssoc xs ys zs = refl
  
  stackTailFrame :
    {p : Primitive} {input output : StackShape} →
    StackEffect p input output →
    (frame : StackShape) →
    StackEffect p (input ++ frame) (output ++ frame)
  stackTailFrame (natAddEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natAddEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natSubEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natSubEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natMulEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natMulEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natQuotEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natQuotEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natRemEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natRemEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natEqEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natEqEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natGeqEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natGeqEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natLtEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natLtEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (natMonusEffect {A = A} {B = B} {tail = tail} leftNat rightNat) frame =
    natMonusEffect {A = A} {B = B} {tail = tail ++ frame} leftNat rightNat
  stackTailFrame (makeScalarEffect {m = m} {tail = tail}) frame =
    makeScalarEffect {m = m} {tail = tail ++ frame}
  stackTailFrame (makeBooleanEffect {m = m} {tail = tail}) frame =
    makeBooleanEffect {m = m} {tail = tail ++ frame}
  stackTailFrame (makeLinearThunkEffect {c = c} {tail = tail} safeCode) frame =
    makeLinearThunkEffect {c = c} {tail = tail ++ frame} safeCode
  stackTailFrame (makeModalThunkEffect {c = c} {tail = tail} safeCode) frame =
    makeModalThunkEffect {c = c} {tail = tail ++ frame} safeCode
  stackTailFrame (applyLinearEffect {m = m} {c = c} {captures = captures}
    {A = A} {B = B} {tail = tail} safeCode) frame =
    applyLinearEffect {m = m} {c = c} {captures = captures} {A = A} {B = B}
      {tail = tail ++ frame} safeCode
  stackTailFrame (forceLinearEffect {c = c} {captures = captures}
    {A = A} {tail = tail} safeCode) frame =
    forceLinearEffect {c = c} {captures = captures} {A = A} {tail = tail ++ frame} safeCode
  stackTailFrame (forceModalEffect {c = c} {captures = captures}
    {A = A} {tail = tail} safeCode modalCaptures) frame =
    forceModalEffect {c = c} {captures = captures} {A = A} {tail = tail ++ frame}
      safeCode modalCaptures
  stackTailFrame (makeResultEffect {A = A} {tail = tail}) frame =
    makeResultEffect {A = A} {tail = tail ++ frame}
  stackTailFrame (unwrapResultEffect {A = A} {tail = tail}) frame =
    unwrapResultEffect {A = A} {tail = tail ++ frame}
  stackTailFrame (promoteModalEffect {c = c} {captures = captures}
    {A = A} {tail = tail} safeCode modalCaptures) frame =
    promoteModalEffect {c = c} {captures = captures} {A = A} {tail = tail ++ frame}
      safeCode modalCaptures
  stackTailFrame (assertLinearEffect {c = c} {captures = captures}
    {A = A} {tail = tail} {m = m} safeCode) frame =
    assertLinearEffect {c = c} {captures = captures} {A = A}
      {tail = tail ++ frame} {m = m} safeCode
  stackTailFrame (ifModalBranchesEffect {C = C} {A = A} {c1 = c1} {c2 = c2}
    {captures1 = captures1} {captures2 = captures2} {tail = tail}
    condition modalCode1 modalCode2 capturesSafe1 capturesSafe2) frame =
    ifModalBranchesEffect {C = C} {A = A} {c1 = c1} {c2 = c2}
      {captures1 = captures1} {captures2 = captures2} {tail = tail ++ frame}
      condition modalCode1 modalCode2 capturesSafe1 capturesSafe2
  stackTailFrame (constructEffect sig {tail = tail}) frame =
    subst
      {P = λ input → StackEffect pConstruct input
        (valueItem (constructorResult sig) :: (tail ++ frame))}
      (symEq (stackAppendAssoc (valuesOf (constructorFields sig))
        (constructorTokenItem (constructorTag sig) :: tail) frame))
      (constructEffect sig {tail = tail ++ frame})
  stackTailFrame (matchEffect sig {tail = tail}) frame =
    matchEffect sig {tail = tail ++ frame}
  stackTailFrame (printLinearEffect {A = A} {tail = tail} linearTy) frame =
    printLinearEffect {A = A} {tail = tail ++ frame} linearTy
  stackTailFrame (printModalEffect {A = A} {tail = tail}) frame =
    printModalEffect {A = A} {tail = tail ++ frame}
  
  -- These are error transitions, not ordinary stack-returning effects. The
  -- state/error payload is modeled by Execution and the WP contracts.
  data ErrorEffect : Primitive → StackShape → RuntimeError → Set where
    throwEffect : {e : RuntimeError} {tail : StackShape} →
      ErrorEffect pThrow (errorTokenItem e :: tail) e
  
  -- Every primitive with an ordinary return path must have a stack-effect derivation
  -- for the specific input/output shape. Dynamic constructor/matcher effects carry
  -- explicit schemas; throws use ErrorEffect instead.
  
  -- A bare emitted natural literal is not a checked ABI scalar. The only way to
  -- turn a raw natural into a checked scalar is the explicit pMakeScalar effect,
  -- which requires a source-mode token. In particular, raw/raw arithmetic does
  -- not inhabit the checked numeric primitive signature.
  rawLiteralCannotUseCheckedAddition :
    {tail output : StackShape} →
    StackEffect pNatAdd
      (rawNatItem :: rawNatItem :: tail)
      output →
    ⊥
  rawLiteralCannotUseCheckedAddition ()
  
  rawLiteralCannotUseCheckedEquality :
    {tail output : StackShape} →
    StackEffect pNatEq
      (rawNatItem :: rawNatItem :: tail)
      output →
    ⊥
  rawLiteralCannotUseCheckedEquality ()
  
  -- The checked constructor has the missing witness explicitly: it takes a
  -- runtime mode token and a raw natural, producing a mode-indexed value.
  rawLiteralNeedsModeWitness :
    {m : SourceMode} {tail : StackShape} →
    StackEffect pMakeScalar
      (modeTokenItem m :: rawNatItem :: tail)
      (valueItem (naturalTypeFor m) :: tail)
  rawLiteralNeedsModeWitness = makeScalarEffect
  
  
  -- ── 3. Concrete witnesses for selected checked-ABI compositions ──
  
  linearNatAddition :
    {tail : StackShape} →
    StackEffect pNatAdd
      (valueItem naturalTy :: valueItem naturalTy :: tail)
      (valueItem naturalTy :: tail)
  linearNatAddition = natAddEffect naturalIsNatural naturalIsNatural
  
  modalNatAddition :
    {tail : StackShape} →
    StackEffect pNatAdd
      (valueItem (!Ty naturalTy) :: valueItem (!Ty naturalTy) :: tail)
      (valueItem (!Ty naturalTy) :: tail)
  modalNatAddition = natAddEffect boxedNaturalIsNatural boxedNaturalIsNatural
  
  mixedNatAddition :
    {tail : StackShape} →
    StackEffect pNatAdd
      (valueItem (!Ty naturalTy) :: valueItem naturalTy :: tail)
      (valueItem naturalTy :: tail)
  mixedNatAddition = natAddEffect naturalIsNatural boxedNaturalIsNatural
  
  linearNatEquality :
    {tail : StackShape} →
    StackEffect pNatEq
      (valueItem naturalTy :: valueItem naturalTy :: tail)
      (valueItem booleanTy :: tail)
  linearNatEquality = natEqEffect naturalIsNatural naturalIsNatural
  
  modalNatEquality :
    {tail : StackShape} →
    StackEffect pNatEq
      (valueItem (!Ty naturalTy) :: valueItem (!Ty naturalTy) :: tail)
      (valueItem (!Ty booleanTy) :: tail)
  modalNatEquality = natEqEffect boxedNaturalIsNatural boxedNaturalIsNatural
  
  mixedNatEquality :
    {tail : StackShape} →
    StackEffect pNatEq
      (valueItem (!Ty naturalTy) :: valueItem naturalTy :: tail)
      (valueItem booleanTy :: tail)
  mixedNatEquality = natEqEffect naturalIsNatural boxedNaturalIsNatural
  
  checkedModalBooleanConstruction :
    StackEffect pMakeBool
      (modeTokenItem modal :: rawBoolItem :: [])
      (valueItem (!Ty booleanTy) :: [])
  checkedModalBooleanConstruction = makeBooleanEffect
  
  checkedModalAddClosure :
    StackEffect pMakeThunk
      (modeTokenItem modal :: codeItem codeNatAdd :: [])
      (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
  checkedModalAddClosure = makeModalThunkEffect modalNatAdd
  
  checkedLinearAddClosure :
    StackEffect pMakeThunk
      (modeTokenItem linear :: codeItem codeNatAdd :: [])
      (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
  checkedLinearAddClosure = makeLinearThunkEffect linearNatAdd
  
  modalPromotionEffect :
    StackEffect pPromoteModal
      (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
      (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
  modalPromotionEffect = promoteModalEffect modalNatAdd modalCapturesNil
  
  
  -- ── 4. Compiler emission boundary mirrored from ToForth.hs ──
  
  data NatExpr : Set where
    natLiteral : Nat → NatExpr
    natAddition : NatExpr → NatExpr → NatExpr
    natMultiplication : NatExpr → NatExpr → NatExpr
    natMonus : NatExpr → NatExpr → NatExpr
  
  -- These constructors distinguish raw literals, saturated primitive calls routed
  -- through the checked-or-legacy ABI adapters, and checked result constructors.
  -- The checked constructors are included so the predicate below can state, and prove, their absence.
  data EmittedFragment : Set where
    rawNaturalCell : Nat → EmittedFragment
    rawTrueCell rawFalseCell : EmittedFragment
    abiAddAdapterCode : EmittedFragment → EmittedFragment → EmittedFragment
    abiMulAdapterCode : EmittedFragment → EmittedFragment → EmittedFragment
    abiMonusAdapterCode : EmittedFragment → EmittedFragment → EmittedFragment
    checkedScalarCode : SourceMode → Nat → EmittedFragment
    checkedBooleanCode : SourceMode → EmittedFragment
  
  -- Mirrors the selected ToForth.hs emission paths: Nat literals are emitted
  -- as decimal text and parsed by ABI-PARSE-NAT into raw cells only when they fit
  -- the target cell bound; saturated addition, multiplication, and builtin Nat
  -- subtraction use ABI-ADD-OR-LEGACY, ABI-MUL-OR-LEGACY, and
  -- ABI-MONUS-OR-LEGACY. The result remains a raw cell without source-mode evidence.
  -- This is a manual semantic mirror, not extraction from the Haskell emitter.
  compileNatFragment : NatExpr → EmittedFragment
  compileNatFragment (natLiteral n) = rawNaturalCell n
  compileNatFragment (natAddition left right) =
    abiAddAdapterCode (compileNatFragment left) (compileNatFragment right)
  compileNatFragment (natMultiplication left right) =
    abiMulAdapterCode (compileNatFragment left) (compileNatFragment right)
  compileNatFragment (natMonus left right) =
    abiMonusAdapterCode (compileNatFragment left) (compileNatFragment right)
  
  compiledNatMultiplicationUsesAdapter :
    (left right : NatExpr) →
    compileNatFragment (natMultiplication left right) ≡
      abiMulAdapterCode (compileNatFragment left) (compileNatFragment right)
  compiledNatMultiplicationUsesAdapter left right = refl
  
  compiledNatMonusUsesAdapter :
    (left right : NatExpr) →
    compileNatFragment (natMonus left right) ≡
      abiMonusAdapterCode (compileNatFragment left) (compileNatFragment right)
  compiledNatMonusUsesAdapter left right = refl
  
  -- A small interpreter for the selected emitted Nat fragment. It deliberately
  -- treats booleans and checked handles as outside this Nat-only observation model.
  data NatFragmentObservation : Set where
    observedNat : Nat → NatFragmentObservation
    notObservedNat : NatFragmentObservation
  
  modelNatMonus : Nat → Nat → Nat
  modelNatMonus n zero = n
  modelNatMonus zero (suc m) = zero
  modelNatMonus (suc n) (suc m) = modelNatMonus n m
  
  natExprMeaning : NatExpr → Nat
  natExprMeaning (natLiteral n) = n
  natExprMeaning (natAddition left right) =
    natExprMeaning left + natExprMeaning right
  natExprMeaning (natMultiplication left right) =
    natExprMeaning left * natExprMeaning right
  natExprMeaning (natMonus left right) =
    modelNatMonus (natExprMeaning left) (natExprMeaning right)
  
  observeNatFragment : EmittedFragment → NatFragmentObservation
  observeNatFragment (rawNaturalCell n) = observedNat n
  observeNatFragment rawTrueCell = notObservedNat
  observeNatFragment rawFalseCell = notObservedNat
  observeNatFragment (abiAddAdapterCode left right)
    with observeNatFragment left | observeNatFragment right
  ... | observedNat x | observedNat y = observedNat (x + y)
  ... | _ | _ = notObservedNat
  observeNatFragment (abiMulAdapterCode left right)
    with observeNatFragment left | observeNatFragment right
  ... | observedNat x | observedNat y = observedNat (x * y)
  ... | _ | _ = notObservedNat
  observeNatFragment (abiMonusAdapterCode left right)
    with observeNatFragment left | observeNatFragment right
  ... | observedNat x | observedNat y = observedNat (modelNatMonus x y)
  ... | _ | _ = notObservedNat
  observeNatFragment (checkedScalarCode mode n) = notObservedNat
  observeNatFragment (checkedBooleanCode mode) = notObservedNat
  
  -- This is an induction theorem about the two explicit ASTs above. It does not
  -- infer anything about the Haskell emitter or the concrete Gforth interpreter.
  compiledNatFragmentPreservesMeaning :
    (expr : NatExpr) →
    observeNatFragment (compileNatFragment expr) ≡
      observedNat (natExprMeaning expr)
  compiledNatFragmentPreservesMeaning (natLiteral n) = refl
  compiledNatFragmentPreservesMeaning (natAddition left right)
    rewrite compiledNatFragmentPreservesMeaning left
          | compiledNatFragmentPreservesMeaning right = refl
  compiledNatFragmentPreservesMeaning (natMultiplication left right)
    rewrite compiledNatFragmentPreservesMeaning left
          | compiledNatFragmentPreservesMeaning right = refl
  compiledNatFragmentPreservesMeaning (natMonus left right)
    rewrite compiledNatFragmentPreservesMeaning left
          | compiledNatFragmentPreservesMeaning right = refl
  
  -- ── 4a. Forward simulation for the Nat stack-code fragment ──
  --
  -- This target program is a linear sequence of the exact operation classes used
  -- by the current raw-cell path: literal cells followed by ABI-ADD-OR-LEGACY,
  -- ABI-MUL-OR-LEGACY, or ABI-MONUS-OR-LEGACY. The execution relation below
  -- specifies their raw/raw stack behavior, with the top cell first. It is a
  -- target-language specification; it is not an interpreter for arbitrary Forth.
  
  data NatStackInstruction : Set where
    pushNatCellInstruction : Nat → NatStackInstruction
    abiAddOrLegacyInstruction : NatStackInstruction
    abiMulOrLegacyInstruction : NatStackInstruction
    abiMonusOrLegacyInstruction : NatStackInstruction
  
  NatStackProgram : Set
  NatStackProgram = List NatStackInstruction
  
  compileNatStackProgram : NatExpr → NatStackProgram
  compileNatStackProgram (natLiteral n) = pushNatCellInstruction n :: []
  compileNatStackProgram (natAddition left right) =
    compileNatStackProgram left ++
      (compileNatStackProgram right ++ (abiAddOrLegacyInstruction :: []))
  compileNatStackProgram (natMultiplication left right) =
    compileNatStackProgram left ++
      (compileNatStackProgram right ++ (abiMulOrLegacyInstruction :: []))
  compileNatStackProgram (natMonus left right) =
    compileNatStackProgram left ++
      (compileNatStackProgram right ++ (abiMonusOrLegacyInstruction :: []))
  
  -- A successful execution derivation describes the whole remaining program.
  -- Binary instructions consume right :: left :: tail and push their result.
  -- Consequently the source-to-target theorem also proves that an arbitrary
  -- suffix of the caller's stack is framed unchanged.
  data NatStackExec : NatStackProgram → List Nat → List Nat → Set where
    natStackDone :
      {stack : List Nat} →
      NatStackExec [] stack stack
    natStackPush :
      {n : Nat} {program : NatStackProgram}
      {initial final : List Nat} →
      NatStackExec program (n :: initial) final →
      NatStackExec (pushNatCellInstruction n :: program) initial final
    natStackAdd :
      {program : NatStackProgram} {left right : Nat}
      {initial final : List Nat} →
      NatStackExec program ((left + right) :: initial) final →
      NatStackExec (abiAddOrLegacyInstruction :: program)
        (right :: left :: initial) final
    natStackMultiply :
      {program : NatStackProgram} {left right : Nat}
      {initial final : List Nat} →
      NatStackExec program ((left * right) :: initial) final →
      NatStackExec (abiMulOrLegacyInstruction :: program)
        (right :: left :: initial) final
    natStackMonus :
      {program : NatStackProgram} {left right : Nat}
      {initial final : List Nat} →
      NatStackExec program (modelNatMonus left right :: initial) final →
      NatStackExec (abiMonusOrLegacyInstruction :: program)
        (right :: left :: initial) final
  
  -- Append is composition: run the first program, then the second. This lemma is
  -- the sequencing fact used by the compiler simulation, not an assumed axiom.
  natStackExecAppend :
    {first second : NatStackProgram}
    {initial middle final : List Nat} →
    NatStackExec first initial middle →
    NatStackExec second middle final →
    NatStackExec (first ++ second) initial final
  natStackExecAppend natStackDone secondRun = secondRun
  natStackExecAppend (natStackPush firstRun) secondRun =
    natStackPush (natStackExecAppend firstRun secondRun)
  natStackExecAppend (natStackAdd firstRun) secondRun =
    natStackAdd (natStackExecAppend firstRun secondRun)
  natStackExecAppend (natStackMultiply firstRun) secondRun =
    natStackMultiply (natStackExecAppend firstRun secondRun)
  natStackExecAppend (natStackMonus firstRun) secondRun =
    natStackMonus (natStackExecAppend firstRun secondRun)
  
  -- The tree-shaped emission mirror linearizes to exactly the instruction
  -- sequence used above. Unsupported/non-Nat fragments are explicitly outside
  -- this projection instead of being assigned fabricated numeric semantics.
  data NatStackProjection : Set where
    outsideNatStackProjection : NatStackProjection
    projectedNatStackProgram : NatStackProgram → NatStackProjection
  
  projectNatStackFragment : EmittedFragment → NatStackProjection
  projectNatStackFragment (rawNaturalCell n) =
    projectedNatStackProgram (pushNatCellInstruction n :: [])
  projectNatStackFragment rawTrueCell = outsideNatStackProjection
  projectNatStackFragment rawFalseCell = outsideNatStackProjection
  projectNatStackFragment (abiAddAdapterCode left right)
    with projectNatStackFragment left | projectNatStackFragment right
  ... | projectedNatStackProgram leftCode | projectedNatStackProgram rightCode =
    projectedNatStackProgram
      (leftCode ++ (rightCode ++ (abiAddOrLegacyInstruction :: [])))
  ... | _ | _ = outsideNatStackProjection
  projectNatStackFragment (abiMulAdapterCode left right)
    with projectNatStackFragment left | projectNatStackFragment right
  ... | projectedNatStackProgram leftCode | projectedNatStackProgram rightCode =
    projectedNatStackProgram
      (leftCode ++ (rightCode ++ (abiMulOrLegacyInstruction :: [])))
  ... | _ | _ = outsideNatStackProjection
  projectNatStackFragment (abiMonusAdapterCode left right)
    with projectNatStackFragment left | projectNatStackFragment right
  ... | projectedNatStackProgram leftCode | projectedNatStackProgram rightCode =
    projectedNatStackProgram
      (leftCode ++ (rightCode ++ (abiMonusOrLegacyInstruction :: [])))
  ... | _ | _ = outsideNatStackProjection
  projectNatStackFragment (checkedScalarCode mode n) = outsideNatStackProjection
  projectNatStackFragment (checkedBooleanCode mode) = outsideNatStackProjection
  
  emissionTreeAgreesWithStackProgram :
    (expr : NatExpr) →
    projectNatStackFragment (compileNatFragment expr) ≡
      projectedNatStackProgram (compileNatStackProgram expr)
  emissionTreeAgreesWithStackProgram (natLiteral n) = refl
  emissionTreeAgreesWithStackProgram (natAddition left right)
    rewrite emissionTreeAgreesWithStackProgram left
          | emissionTreeAgreesWithStackProgram right = refl
  emissionTreeAgreesWithStackProgram (natMultiplication left right)
    rewrite emissionTreeAgreesWithStackProgram left
          | emissionTreeAgreesWithStackProgram right = refl
  emissionTreeAgreesWithStackProgram (natMonus left right)
    rewrite emissionTreeAgreesWithStackProgram left
          | emissionTreeAgreesWithStackProgram right = refl
  
  -- Forward simulation theorem:
  --   executing compileNatStackProgram e on any tail yields
  --   natExprMeaning e :: tail.
  -- The tail is preserved by every derivation; this rules out modeled stack
  -- underflow for these compiled expressions. The proof covers this explicit
  -- Nat expression grammar, not all Agda terms or concrete Gforth internals.
  natExpressionForwardSimulatesStackProgram :
    (expr : NatExpr) (tail : List Nat) →
    NatStackExec (compileNatStackProgram expr) tail
      (natExprMeaning expr :: tail)
  natExpressionForwardSimulatesStackProgram (natLiteral n) tail =
    natStackPush natStackDone
  natExpressionForwardSimulatesStackProgram (natAddition left right) tail =
    natStackExecAppend
      (natExpressionForwardSimulatesStackProgram left tail)
      (natStackExecAppend
        (natExpressionForwardSimulatesStackProgram right
          (natExprMeaning left :: tail))
        (natStackAdd natStackDone))
  natExpressionForwardSimulatesStackProgram (natMultiplication left right) tail =
    natStackExecAppend
      (natExpressionForwardSimulatesStackProgram left tail)
      (natStackExecAppend
        (natExpressionForwardSimulatesStackProgram right
          (natExprMeaning left :: tail))
        (natStackMultiply natStackDone))
  natExpressionForwardSimulatesStackProgram (natMonus left right) tail =
    natStackExecAppend
      (natExpressionForwardSimulatesStackProgram left tail)
      (natStackExecAppend
        (natExpressionForwardSimulatesStackProgram right
          (natExprMeaning left :: tail))
        (natStackMonus natStackDone))
  
  -- A raw Gforth cell is finite, unlike Agda's mathematical Nat. Representability
  -- therefore belongs in the theorem's input contract, not hidden in a claim that
  -- arbitrary natural-number arithmetic is machine arithmetic. The bound is a
  -- parameter: a concrete bridge must instantiate it from the selected runtime.
  -- Every literal and every recursively computed intermediate result must fit.
  data NatCellRepresentable (bound : Nat) : NatExpr → Set where
    natLiteralCellFits : {n : Nat} →
      n < suc bound →
      NatCellRepresentable bound (natLiteral n)
    natAdditionCellFits : {left right : NatExpr} →
      NatCellRepresentable bound left →
      NatCellRepresentable bound right →
      (natExprMeaning left + natExprMeaning right) < suc bound →
      NatCellRepresentable bound (natAddition left right)
    natMultiplicationCellFits : {left right : NatExpr} →
      NatCellRepresentable bound left →
      NatCellRepresentable bound right →
      (natExprMeaning left * natExprMeaning right) < suc bound →
      NatCellRepresentable bound (natMultiplication left right)
    natMonusCellFits : {left right : NatExpr} →
      NatCellRepresentable bound left →
      NatCellRepresentable bound right →
      modelNatMonus (natExprMeaning left) (natExprMeaning right) < suc bound →
      NatCellRepresentable bound (natMonus left right)
  
  natExprValueFitsCellBound :
    (bound : Nat) (expr : NatExpr) →
    NatCellRepresentable bound expr →
    natExprMeaning expr < suc bound
  natExprValueFitsCellBound bound (natLiteral n) (natLiteralCellFits fits) = fits
  natExprValueFitsCellBound bound (natAddition left right)
    (natAdditionCellFits leftFits rightFits resultFits) = resultFits
  natExprValueFitsCellBound bound (natMultiplication left right)
    (natMultiplicationCellFits leftFits rightFits resultFits) = resultFits
  natExprValueFitsCellBound bound (natMonus left right)
    (natMonusCellFits leftFits rightFits resultFits) = resultFits
  
  -- The pair theorem makes the machine-cell side condition visible at the same
  -- call site as source-to-target simulation. The recursive witness carries the
  -- bound for every intermediate node, while the stack theorem preserves any tail.
  -- This remains a parameterized mathematical model, not an overflow check in Forth.
  natExpressionBoundedForwardSimulatesStackProgram :
    (bound : Nat) (expr : NatExpr) (tail : List Nat) →
    NatCellRepresentable bound expr →
    NatStackExec (compileNatStackProgram expr) tail
      (natExprMeaning expr :: tail) ×
    (natExprMeaning expr < suc bound)
  natExpressionBoundedForwardSimulatesStackProgram bound expr tail representable =
    natExpressionForwardSimulatesStackProgram expr tail ,
    natExprValueFitsCellBound bound expr representable
  
  
  -- ── 4b. Executable target semantics and compositional pass certificates ──
  --
  -- CakeML/PureCake make each compiler pass preserve a named semantic
  -- observation, then compose those pass theorems.  Reuse that discipline
  -- here: the instruction list has an executable semantics, and compiler
  -- correctness is stated as equality of source and target observations.
  -- This remains the deliberately small Nat stack fragment.
  
  data NatStackRunResult : Set where
    natStackReturned : List Nat → NatStackRunResult
    natStackUnderflow : NatStackRunResult
  
  natStackEqTrans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  natStackEqTrans refl second = second
  
  runNatStackProgram : NatStackProgram → List Nat → NatStackRunResult
  runNatStackProgram [] stack = natStackReturned stack
  runNatStackProgram (pushNatCellInstruction n :: program) stack =
    runNatStackProgram program (n :: stack)
  runNatStackProgram (abiAddOrLegacyInstruction :: program)
    (right :: left :: stack) =
    runNatStackProgram program ((left + right) :: stack)
  runNatStackProgram (abiAddOrLegacyInstruction :: program) [] =
    natStackUnderflow
  runNatStackProgram (abiAddOrLegacyInstruction :: program) (only :: []) =
    natStackUnderflow
  runNatStackProgram (abiMulOrLegacyInstruction :: program)
    (right :: left :: stack) =
    runNatStackProgram program ((left * right) :: stack)
  runNatStackProgram (abiMulOrLegacyInstruction :: program) [] =
    natStackUnderflow
  runNatStackProgram (abiMulOrLegacyInstruction :: program) (only :: []) =
    natStackUnderflow
  runNatStackProgram (abiMonusOrLegacyInstruction :: program)
    (right :: left :: stack) =
    runNatStackProgram program (modelNatMonus left right :: stack)
  runNatStackProgram (abiMonusOrLegacyInstruction :: program) [] =
    natStackUnderflow
  runNatStackProgram (abiMonusOrLegacyInstruction :: program) (only :: []) =
    natStackUnderflow
  
  -- Every relational execution proof is accepted by the executable
  -- interpreter.  Thus the inductive simulation is not a second, unrelated
  -- target semantics.
  natStackExecSound :
    {program : NatStackProgram} {initial final : List Nat} →
    NatStackExec program initial final →
    runNatStackProgram program initial ≡ natStackReturned final
  natStackExecSound natStackDone = refl
  natStackExecSound (natStackPush execution) = natStackExecSound execution
  natStackExecSound (natStackAdd execution) = natStackExecSound execution
  natStackExecSound (natStackMultiply execution) = natStackExecSound execution
  natStackExecSound (natStackMonus execution) = natStackExecSound execution
  
  natSourceStackSemantics : NatExpr → List Nat → NatStackRunResult
  natSourceStackSemantics expr tail =
    natStackReturned (natExprMeaning expr :: tail)
  
  -- A pass is a lowering function plus a proof that its target observation
  -- agrees with its source observation for every caller stack.
  record StackSemanticPass
    {Source Target : Set}
    (lower : Source → Target)
    (sourceSemantics : Source → List Nat → NatStackRunResult)
    (targetSemantics : Target → List Nat → NatStackRunResult) : Set where
    field
      preservesStack :
        (sourceTerm : Source) (tail : List Nat) →
        targetSemantics (lower sourceTerm) tail ≡
          sourceSemantics sourceTerm tail
  open StackSemanticPass public
  
  -- Composition is theorem composition, not an assumed compiler axiom.
  composeStackSemanticPass :
    {Source Middle Target : Set}
    {lower₁ : Source → Middle}
    {lower₂ : Middle → Target}
    {sourceSemantics : Source → List Nat → NatStackRunResult}
    {middleSemantics : Middle → List Nat → NatStackRunResult}
    {targetSemantics : Target → List Nat → NatStackRunResult} →
    StackSemanticPass lower₁ sourceSemantics middleSemantics →
    StackSemanticPass lower₂ middleSemantics targetSemantics →
    StackSemanticPass
      (λ sourceTerm → lower₂ (lower₁ sourceTerm))
      sourceSemantics targetSemantics
  composeStackSemanticPass {lower₁ = lowerOne} first second = record
    { preservesStack = λ sourceTerm tail →
        natStackEqTrans
          (preservesStack second (lowerOne sourceTerm) tail)
          (preservesStack first sourceTerm tail)
    }
  
  -- Concrete instance: NatExpr compiles into the current modeled ABI
  -- instructions, whose executable stack semantics preserves the Nat meaning
  -- and leaves every caller-owned suffix unchanged.
  natStackCompilerPass :
    StackSemanticPass
      compileNatStackProgram natSourceStackSemantics runNatStackProgram
  natStackCompilerPass = record
    { preservesStack = λ expr tail →
        natStackExecSound
          (natExpressionForwardSimulatesStackProgram expr tail)
    }
  
  -- Proof-carrying artifact for this one supported fragment.  Its four fields
  -- cover: emission-tree meaning, tree-to-instruction linearization, target
  -- execution, and finite-cell representability.  The bound must still be
  -- instantiated from the actual Forth ABI before it is a machine-cell proof.
  record NatCompilationCertificate (bound : Nat) (expr : NatExpr) : Set where
    field
      certifiedRepresentability : NatCellRepresentable bound expr
      certifiedEmissionMeaning :
        observeNatFragment (compileNatFragment expr) ≡
          observedNat (natExprMeaning expr)
      certifiedLinearization :
        projectNatStackFragment (compileNatFragment expr) ≡
          projectedNatStackProgram (compileNatStackProgram expr)
      certifiedStackExecution :
        (tail : List Nat) →
        runNatStackProgram (compileNatStackProgram expr) tail ≡
          natStackReturned (natExprMeaning expr :: tail)
      certifiedCellBound :
        natExprMeaning expr < suc bound
  open NatCompilationCertificate public
  
  certifyNatCompilation :
    (bound : Nat) (expr : NatExpr) →
    NatCellRepresentable bound expr →
    NatCompilationCertificate bound expr
  certifyNatCompilation bound expr representable = record
    { certifiedRepresentability = representable
    ; certifiedEmissionMeaning = compiledNatFragmentPreservesMeaning expr
    ; certifiedLinearization = emissionTreeAgreesWithStackProgram expr
    ; certifiedStackExecution = preservesStack natStackCompilerPass expr
    ; certifiedCellBound =
        natExprValueFitsCellBound bound expr representable
    }
  
  -- Model the runtime contract of a curried arithmetic word: the first pass
  -- captures its left operand; the next application supplies the right operand.
  -- The names correspond to the selected Forth preamble words, not extracted code.
  data CurriedNatWord : Set where
    natAddWord natMonusWord natMultiplyWord : CurriedNatWord
  
  data CurriedNatClosure : Set where
    pendingNatClosure : CurriedNatWord → Nat → CurriedNatClosure
  
  lowerPartialNatAddition : Nat → CurriedNatClosure
  lowerPartialNatAddition left = pendingNatClosure natAddWord left
  
  lowerPartialNatMonus : Nat → CurriedNatClosure
  lowerPartialNatMonus left = pendingNatClosure natMonusWord left
  
  lowerPartialNatMultiplication : Nat → CurriedNatClosure
  lowerPartialNatMultiplication left = pendingNatClosure natMultiplyWord left
  
  applyCurriedNatClosure : CurriedNatClosure → Nat → Nat
  applyCurriedNatClosure (pendingNatClosure natAddWord left) right = left + right
  applyCurriedNatClosure (pendingNatClosure natMonusWord left) right =
    modelNatMonus left right
  applyCurriedNatClosure (pendingNatClosure natMultiplyWord left) right =
    left * right
  
  curriedNatAdditionPreservesMeaning :
    (left right : Nat) →
    applyCurriedNatClosure (lowerPartialNatAddition left) right ≡ left + right
  curriedNatAdditionPreservesMeaning left right = refl
  
  curriedNatMonusPreservesMeaning :
    (left right : Nat) →
    applyCurriedNatClosure (lowerPartialNatMonus left) right ≡
      modelNatMonus left right
  curriedNatMonusPreservesMeaning left right = refl
  
  curriedNatMultiplicationPreservesMeaning :
    (left right : Nat) →
    applyCurriedNatClosure (lowerPartialNatMultiplication left) right ≡ left * right
  curriedNatMultiplicationPreservesMeaning left right = refl
  
  -- Historical counterexample for the pre-fix curried-application path. The
  -- earlier generated fixture emitted a lambda body `a c pass`; the raw/non-thunk
  -- branch of `pass { x h -- result }` returns h unchanged. This witness is kept
  -- as a regression specification, not a claim about the current output after
  -- saturated primitive/builtin lowering was routed through ABI adapters. It is
  -- a model of the observed body, not a proof extracted from the Haskell emitter.
  historicalPassRawFallback : Nat → Nat → Nat
  historicalPassRawFallback x h = h
  
  historicalGeneratedScalarAddBody : Nat → Nat → Nat
  historicalGeneratedScalarAddBody left right = historicalPassRawFallback left right
  
  historicalGeneratedBodyReturnsRightArgument :
    (left right : Nat) → historicalGeneratedScalarAddBody left right ≡ right
  historicalGeneratedBodyReturnsRightArgument left right = refl
  
  historicalGeneratedScalarBodyAt20And5 :
    historicalGeneratedScalarAddBody 20 5 ≡ 5
  historicalGeneratedScalarBodyAt20And5 = refl
  
  sourceAdditionAt20And5 : 20 + 5 ≡ 25
  sourceAdditionAt20And5 = refl
  
  fiveIsNotTwentyFive : 5 ≡ 25 → ⊥
  fiveIsNotTwentyFive ()
  
  historicalGeneratedBodyCannotRefineAddition :
    (historicalGeneratedScalarAddBody 20 5 ≡ 20 + 5) → ⊥
  historicalGeneratedBodyCannotRefineAddition bodyRefinement =
    fiveIsNotTwentyFive
      (transEq
        (transEq (symEq historicalGeneratedScalarBodyAt20And5) bodyRefinement)
        sourceAdditionAt20And5)
  
  HistoricalGeneratedScalarRefinesAddition : Set
  HistoricalGeneratedScalarRefinesAddition =
    (left right : Nat) →
    historicalGeneratedScalarAddBody left right ≡ left + right
  
  historicalGeneratedScalarDoesNotRefineAddition :
    HistoricalGeneratedScalarRefinesAddition → ⊥
  historicalGeneratedScalarDoesNotRefineAddition refinement =
    historicalGeneratedBodyCannotRefineAddition (refinement 20 5)
  
  NoCheckedRepresentation : EmittedFragment → Set
  NoCheckedRepresentation (rawNaturalCell n) = ⊤
  NoCheckedRepresentation rawTrueCell = ⊤
  NoCheckedRepresentation rawFalseCell = ⊤
  NoCheckedRepresentation (abiAddAdapterCode left right) =
    NoCheckedRepresentation left × NoCheckedRepresentation right
  NoCheckedRepresentation (abiMulAdapterCode left right) =
    NoCheckedRepresentation left × NoCheckedRepresentation right
  NoCheckedRepresentation (abiMonusAdapterCode left right) =
    NoCheckedRepresentation left × NoCheckedRepresentation right
  NoCheckedRepresentation (checkedScalarCode mode n) = ⊥
  NoCheckedRepresentation (checkedBooleanCode mode) = ⊥
  
  compilerNatFragmentHasNoCheckedRepresentation :
    (expr : NatExpr) → NoCheckedRepresentation (compileNatFragment expr)
  compilerNatFragmentHasNoCheckedRepresentation (natLiteral n) = tt
  compilerNatFragmentHasNoCheckedRepresentation (natAddition left right) =
    compilerNatFragmentHasNoCheckedRepresentation left ,
    compilerNatFragmentHasNoCheckedRepresentation right
  compilerNatFragmentHasNoCheckedRepresentation (natMultiplication left right) =
    compilerNatFragmentHasNoCheckedRepresentation left ,
    compilerNatFragmentHasNoCheckedRepresentation right
  compilerNatFragmentHasNoCheckedRepresentation (natMonus left right) =
    compilerNatFragmentHasNoCheckedRepresentation left ,
    compilerNatFragmentHasNoCheckedRepresentation right
  
  -- Literal booleans in the pinned source are output as raw -1/0 cells, not as
  -- ABI boolean handles; the separate constructors record their source meaning,
  -- not runtime type tags.
  data BoolLiteral : Set where
    trueLiteral falseLiteral : BoolLiteral
  
  compileBoolFragment : BoolLiteral → EmittedFragment
  compileBoolFragment trueLiteral = rawTrueCell
  compileBoolFragment falseLiteral = rawFalseCell
  
  compilerBoolLiteralHasNoCheckedRepresentation :
    (literal : BoolLiteral) → NoCheckedRepresentation (compileBoolFragment literal)
  compilerBoolLiteralHasNoCheckedRepresentation trueLiteral = tt
  compilerBoolLiteralHasNoCheckedRepresentation falseLiteral = tt
  
  data CheckedABIValue : StackItem → Set where
    checkedLinearNatural : CheckedABIValue (valueItem naturalTy)
    checkedModalNatural : CheckedABIValue (valueItem (!Ty naturalTy))
    checkedLinearBoolean : CheckedABIValue (valueItem booleanTy)
    checkedModalBoolean : CheckedABIValue (valueItem (!Ty booleanTy))
  
  rawNaturalCannotBeCheckedABIValue :
    CheckedABIValue rawNatItem → ⊥
  rawNaturalCannotBeCheckedABIValue ()
  
  rawBooleanCannotBeCheckedABIValue :
    CheckedABIValue rawBoolItem → ⊥
  rawBooleanCannotBeCheckedABIValue ()
  
  -- Every natural-literal/addition expression in this fragment leaves a raw
  -- natural cell as its result. It cannot carry the mode-indexed descriptor
  -- witness required by a checked ABI operand.
  compiledNatResultShape : NatExpr → StackItem
  compiledNatResultShape _ = rawNatItem
  
  compiledNatResultCannotBeChecked :
    (expr : NatExpr) →
    CheckedABIValue (compiledNatResultShape expr) → ⊥
  compiledNatResultCannotBeChecked expr = rawNaturalCannotBeCheckedABIValue
  
  compiledBooleanResultShape : BoolLiteral → StackItem
  compiledBooleanResultShape _ = rawBoolItem
  
  compiledBoolResultCannotBeChecked :
    (literal : BoolLiteral) →
    CheckedABIValue (compiledBooleanResultShape literal) → ⊥
  compiledBoolResultCannotBeChecked literal = rawBooleanCannotBeCheckedABIValue
  
  -- Import and reuse the closed stack-effect lemmas rather than assuming that
  -- raw output is accepted by checked operations.
  rawCompilerOperandsCannotUseCheckedAddition :
    {tail output : StackShape} →
    StackEffect pNatAdd (rawNatItem :: rawNatItem :: tail) output → ⊥
  rawCompilerOperandsCannotUseCheckedAddition =
    rawLiteralCannotUseCheckedAddition
  
  rawCompilerOperandsCannotUseCheckedEquality :
    {tail output : StackShape} →
    StackEffect pNatEq (rawNatItem :: rawNatItem :: tail) output → ⊥
  rawCompilerOperandsCannotUseCheckedEquality =
    rawLiteralCannotUseCheckedEquality
  
  -- For a checked scalar to be introduced from a raw literal, the compiler must
  -- emit a pMakeScalar effect with a source-mode token. The theorem's type makes
  -- the missing evidence explicit; the upstream lowering above does not supply it.
  checkedScalarRequiresModeWitness :
    {m : SourceMode} {tail : StackShape} →
    StackEffect pMakeScalar
      (modeTokenItem m :: rawNatItem :: tail)
      (valueItem (naturalTypeFor m) :: tail)
  checkedScalarRequiresModeWitness = rawLiteralNeedsModeWitness
  
  
  -- ── 5. Explicit compiler-emission table ──
  --
  -- This table mirrors the current ToForth.hs TPrim case and literal translation.
  -- The supported primitive vocabulary is narrower than Agda's full primitive
  -- vocabulary. Unsupported operations go through fthError, which emits a
  -- diagnostic followed by ABI-ERR-COMPILED-UNSUPPORTED (a catchable THROW).
  --
  -- This is a manually maintained semantic mirror, not a generated proof about
  -- Haskell. The per-file provenance check pins the source; it does not prove
  -- semantic equivalence between this table and the Haskell implementation.
  
  data SupportedBackendPrimitive : Set where
    backendAdd backendSub backendMul backendQuot backendRem : SupportedBackendPrimitive
    backendIf backendIntegerEq backendGeq backendLt : SupportedBackendPrimitive
  
  data BackendPrimitive : Set where
    backendSupported : SupportedBackendPrimitive → BackendPrimitive
    backendUnsupported : BackendPrimitive
  
  data BackendEmission : Set where
    emitBinaryAdapterAdd emitBinaryAdapterSub emitBinaryAdapterMul emitBinaryAdapterQuot emitBinaryAdapterRem : BackendEmission
    emitInlineIf emitBinaryAdapterEq emitBinaryAdapterGeq emitBinaryAdapterLt : BackendEmission
    emitDiagnosticThrow : BackendEmission
  
  emitSupportedPrimitive : SupportedBackendPrimitive → BackendEmission
  emitSupportedPrimitive backendAdd = emitBinaryAdapterAdd
  emitSupportedPrimitive backendSub = emitBinaryAdapterSub
  emitSupportedPrimitive backendMul = emitBinaryAdapterMul
  emitSupportedPrimitive backendQuot = emitBinaryAdapterQuot
  emitSupportedPrimitive backendRem = emitBinaryAdapterRem
  emitSupportedPrimitive backendIf = emitInlineIf
  emitSupportedPrimitive backendIntegerEq = emitBinaryAdapterEq
  emitSupportedPrimitive backendGeq = emitBinaryAdapterGeq
  emitSupportedPrimitive backendLt = emitBinaryAdapterLt
  
  emitBackendPrimitive : BackendPrimitive → BackendEmission
  emitBackendPrimitive (backendSupported p) = emitSupportedPrimitive p
  emitBackendPrimitive backendUnsupported = emitDiagnosticThrow
  
  data SupportedEmission : BackendEmission → Set where
    adapterAddEmission : SupportedEmission emitBinaryAdapterAdd
    adapterSubEmission : SupportedEmission emitBinaryAdapterSub
    adapterMulEmission : SupportedEmission emitBinaryAdapterMul
    adapterQuotEmission : SupportedEmission emitBinaryAdapterQuot
    adapterRemEmission : SupportedEmission emitBinaryAdapterRem
    inlineIfEmission : SupportedEmission emitInlineIf
    adapterEqEmission : SupportedEmission emitBinaryAdapterEq
    adapterGeqEmission : SupportedEmission emitBinaryAdapterGeq
    adapterLtEmission : SupportedEmission emitBinaryAdapterLt
  
  -- Every supported primitive maps to a typed ABI adapter or an inline conditional.
  supportedPrimitiveEmissionIsSpecified :
    (p : SupportedBackendPrimitive) → SupportedEmission (emitSupportedPrimitive p)
  supportedPrimitiveEmissionIsSpecified backendAdd = adapterAddEmission
  supportedPrimitiveEmissionIsSpecified backendSub = adapterSubEmission
  supportedPrimitiveEmissionIsSpecified backendMul = adapterMulEmission
  supportedPrimitiveEmissionIsSpecified backendQuot = adapterQuotEmission
  supportedPrimitiveEmissionIsSpecified backendRem = adapterRemEmission
  supportedPrimitiveEmissionIsSpecified backendIf = inlineIfEmission
  supportedPrimitiveEmissionIsSpecified backendIntegerEq = adapterEqEmission
  supportedPrimitiveEmissionIsSpecified backendGeq = adapterGeqEmission
  supportedPrimitiveEmissionIsSpecified backendLt = adapterLtEmission
  
  unsupportedPrimitiveUsesCatchableDiagnostic :
    emitBackendPrimitive backendUnsupported ≡ emitDiagnosticThrow
  unsupportedPrimitiveUsesCatchableDiagnostic = refl
  
  -- Exact-arity TPrim applications bypass generic closure application. Partial,
  -- under-applied, or over-applied calls to these same nine primitives fall back
  -- through the existing curried Forth words and fthApps/pass. Other primitives
  -- fail closed instead of being sent through generic closure application.
  data PrimitiveApplicationArity : Set where
    primitiveBinaryArity primitiveIfArity primitiveOtherArity
      : PrimitiveApplicationArity
  
  data PrimitiveApplicationEmission : Set where
    emitDirectAdd emitDirectSub emitDirectMul emitDirectQuot emitDirectRem
      emitDirectEqI emitDirectGeq emitDirectLt emitDirectIf
      emitCurriedAdd emitCurriedSub emitCurriedMul emitCurriedQuot emitCurriedRem
      emitCurriedEqI emitCurriedGeq emitCurriedLt emitCurriedIf
      emitUnsupportedPrimitiveApplication : PrimitiveApplicationEmission
  
  emitPrimitiveApplication :
    SupportedBackendPrimitive → PrimitiveApplicationArity →
    PrimitiveApplicationEmission
  emitPrimitiveApplication backendAdd primitiveBinaryArity = emitDirectAdd
  emitPrimitiveApplication backendAdd _ = emitCurriedAdd
  emitPrimitiveApplication backendSub primitiveBinaryArity = emitDirectSub
  emitPrimitiveApplication backendSub _ = emitCurriedSub
  emitPrimitiveApplication backendMul primitiveBinaryArity = emitDirectMul
  emitPrimitiveApplication backendMul _ = emitCurriedMul
  emitPrimitiveApplication backendQuot primitiveBinaryArity = emitDirectQuot
  emitPrimitiveApplication backendQuot _ = emitCurriedQuot
  emitPrimitiveApplication backendRem primitiveBinaryArity = emitDirectRem
  emitPrimitiveApplication backendRem _ = emitCurriedRem
  emitPrimitiveApplication backendIf primitiveIfArity = emitDirectIf
  emitPrimitiveApplication backendIf _ = emitCurriedIf
  emitPrimitiveApplication backendIntegerEq primitiveBinaryArity = emitDirectEqI
  emitPrimitiveApplication backendIntegerEq _ = emitCurriedEqI
  emitPrimitiveApplication backendGeq primitiveBinaryArity = emitDirectGeq
  emitPrimitiveApplication backendGeq _ = emitCurriedGeq
  emitPrimitiveApplication backendLt primitiveBinaryArity = emitDirectLt
  emitPrimitiveApplication backendLt _ = emitCurriedLt
  
  -- TDef has a second special lowering: saturated builtin Nat addition and
  -- subtraction use ABI adapters, while partial applications use curried
  -- add/monus; all other definitions use their registered Forth word.
  data BuiltinNatDefinition : Set where
    builtinNatPlusDefinition builtinNatMinusDefinition : BuiltinNatDefinition
  
  data DefinitionApplicationArity : Set where
    definitionSaturatedBinary definitionOtherArity : DefinitionApplicationArity
  
  data DefinitionApplicationEmission : Set where
    emitDirectBuiltinNatAdd emitDirectBuiltinNatMonus
      emitCurriedBuiltinNatAdd emitCurriedBuiltinNatMonus
      emitNamedDefinitionApplication : DefinitionApplicationEmission
  
  emitBuiltinNatDefinitionApplication :
    BuiltinNatDefinition → DefinitionApplicationArity →
    DefinitionApplicationEmission
  emitBuiltinNatDefinitionApplication builtinNatPlusDefinition
    definitionSaturatedBinary = emitDirectBuiltinNatAdd
  emitBuiltinNatDefinitionApplication builtinNatPlusDefinition _ =
    emitCurriedBuiltinNatAdd
  emitBuiltinNatDefinitionApplication builtinNatMinusDefinition
    definitionSaturatedBinary = emitDirectBuiltinNatMonus
  emitBuiltinNatDefinitionApplication builtinNatMinusDefinition _ =
    emitCurriedBuiltinNatMonus
  
  -- Literal support mirrors ToForth.hs's Literal case. Nat becomes decimal
  -- text consumed by ABI-PARSE-NAT; Word64/Float/String/Char/QName/Meta use
  -- fthError, which emits ABI-ERROR-COMPILED-UNSUPPORTED and throws catchably.
  -- Boolean flags are constructor cases (TCon), modeled separately below.
  data UnsupportedLiteralKind : Set where
    unsupportedWord64 unsupportedFloat unsupportedString unsupportedChar
      unsupportedQName unsupportedMeta : UnsupportedLiteralKind
  
  data BackendLiteral : Set where
    backendNatLiteral : Nat → BackendLiteral
    backendUnsupportedLiteral : UnsupportedLiteralKind → BackendLiteral
  
  data LiteralEmission : Set where
    emitNaturalCell : LiteralEmission
    emitLiteralDiagnosticThrow : UnsupportedLiteralKind → LiteralEmission
  
  emitBackendLiteral : BackendLiteral → LiteralEmission
  emitBackendLiteral (backendNatLiteral n) = emitNaturalCell
  emitBackendLiteral (backendUnsupportedLiteral kind) =
    emitLiteralDiagnosticThrow kind
  
  unsupportedLiteralUsesCatchableDiagnostic :
    (kind : UnsupportedLiteralKind) →
    emitBackendLiteral (backendUnsupportedLiteral kind) ≡
      emitLiteralDiagnosticThrow kind
  unsupportedLiteralUsesCatchableDiagnostic kind = refl
  
  unsupportedStringLiteralUsesCatchableDiagnostic :
    emitBackendLiteral (backendUnsupportedLiteral unsupportedString) ≡
      emitLiteralDiagnosticThrow unsupportedString
  unsupportedStringLiteralUsesCatchableDiagnostic = refl
  
  -- The term-level cases classify each TTerm branch in ToForth.hs. Generic
  -- variables, primitives, definitions, lambdas, constructors, lets and cases
  -- take their corresponding backend paths. Unit/sort/erased terms emit zero;
  -- Bool constructors emit -1/0; Bool cases become IF/ELSE/THEN; coercions are
  -- transparent. TError TUnreachable and TMeta use fthError; an absent pattern
  -- fallback uses ABI-ERROR-UNREACHABLE. TApp is an internal invariant failure.
  data BackendTermCase : Set where
    backendVariableTerm backendPrimitiveApplication backendDefinitionApplication
      backendLambdaTerm backendConstructorApplication backendLetTerm
      backendGeneralCase : BackendTermCase
    backendUnitTerm backendSortTerm backendErasedTerm : BackendTermCase
    backendTrueConstructor backendFalseConstructor : BackendTermCase
    backendBooleanCase backendCoerceTerm : BackendTermCase
    backendPanicTerm backendUnsolvedMetaTerm backendUnmatchedPatternFallback
      backendInternalApplicationTerm : BackendTermCase
  
  data TermEmission : Set where
    emitVariableLookup emitPrimitiveDispatch emitDefinitionDispatch
      emitClosureLambda emitConstructorApplication emitLetBinding emitPatternMatch
      emitZeroCell emitTrueFlag emitFalseFlag emitInlineConditional
      emitTransparentTerm emitTermDiagnosticThrow emitUnreachableErrorThrow
      emitInternalImpossible : TermEmission
  
  emitBackendTermCase : BackendTermCase → TermEmission
  emitBackendTermCase backendVariableTerm = emitVariableLookup
  emitBackendTermCase backendPrimitiveApplication = emitPrimitiveDispatch
  emitBackendTermCase backendDefinitionApplication = emitDefinitionDispatch
  emitBackendTermCase backendLambdaTerm = emitClosureLambda
  emitBackendTermCase backendConstructorApplication = emitConstructorApplication
  emitBackendTermCase backendLetTerm = emitLetBinding
  emitBackendTermCase backendGeneralCase = emitPatternMatch
  emitBackendTermCase backendUnitTerm = emitZeroCell
  emitBackendTermCase backendSortTerm = emitZeroCell
  emitBackendTermCase backendErasedTerm = emitZeroCell
  emitBackendTermCase backendTrueConstructor = emitTrueFlag
  emitBackendTermCase backendFalseConstructor = emitFalseFlag
  emitBackendTermCase backendBooleanCase = emitInlineConditional
  emitBackendTermCase backendCoerceTerm = emitTransparentTerm
  emitBackendTermCase backendPanicTerm = emitTermDiagnosticThrow
  emitBackendTermCase backendUnsolvedMetaTerm = emitTermDiagnosticThrow
  emitBackendTermCase backendUnmatchedPatternFallback = emitUnreachableErrorThrow
  emitBackendTermCase backendInternalApplicationTerm = emitInternalImpossible
  
  -- TAlt lowering is encoded through an intermediate RichSExpr shape.
  -- Constructor alternatives and literal alternatives both become
  -- [pattern, wildcard-list, body], so fthPatternMatch routes both through its
  -- constructor-pattern branch. A literal is therefore syntactically accepted
  -- by this branch, but the current emitter/runtime does not establish correct
  -- literal-pattern equality semantics. Guard alternatives use a separate
  -- [guard, body] branch; malformed alternative shapes emit a catchable error.
  data BackendAlternativeCase : Set where
    backendConstructorAlternative backendLiteralAlternative
      backendGuardAlternative backendMalformedAlternative : BackendAlternativeCase
  
  data AlternativeEmission : Set where
    emitConstructorPatternBranch emitGuardBranch emitLiteralPatternBranch
      emitUnsupportedAlternativeThrow : AlternativeEmission
  
  emitBackendAlternative : BackendAlternativeCase → AlternativeEmission
  emitBackendAlternative backendConstructorAlternative = emitConstructorPatternBranch
  emitBackendAlternative backendLiteralAlternative = emitLiteralPatternBranch
  emitBackendAlternative backendGuardAlternative = emitGuardBranch
  emitBackendAlternative backendMalformedAlternative = emitUnsupportedAlternativeThrow
  
  panicTermUsesCatchableDiagnostic :
    emitBackendTermCase backendPanicTerm ≡ emitTermDiagnosticThrow
  panicTermUsesCatchableDiagnostic = refl
  
  unsolvedMetaUsesCatchableDiagnostic :
    emitBackendTermCase backendUnsolvedMetaTerm ≡ emitTermDiagnosticThrow
  unsolvedMetaUsesCatchableDiagnostic = refl
  
  unmatchedPatternUsesCatchableUnreachableError :
    emitBackendTermCase backendUnmatchedPatternFallback ≡
      emitUnreachableErrorThrow
  unmatchedPatternUsesCatchableUnreachableError = refl
  
  literalAlternativeUsesPatternBranch :
    emitBackendAlternative backendLiteralAlternative ≡ emitLiteralPatternBranch
  literalAlternativeUsesPatternBranch = refl
  
  malformedAlternativeFailsClosed :
    emitBackendAlternative backendMalformedAlternative ≡
      emitUnsupportedAlternativeThrow
  malformedAlternativeFailsClosed = refl
  
  -- Definition compilation is a separate ToForth instance. Non-compiling
  -- definitions (including inline functions, generalizable variables, datatype
  -- and record declarations) contribute no word; axioms/primitives fail through
  -- fthAxiom; functions compile bodies; constructors define constructor words.
  -- AbstractDefn and DataOrRecSig are compiler-internal impossible cases.
  data BackendDefinitionCase : Set where
    backendAxiomDefinition backendPrimitiveDefinition : BackendDefinitionCase
    backendFunctionDefinition backendConstructorDefinition : BackendDefinitionCase
    backendSkippedDefinition backendImpossibleDefinition : BackendDefinitionCase
  
  data DefinitionEmission : Set where
    emitDefinitionDiagnosticThrow emitCompiledFunctionWord
      emitConstructorWord emitNoDefinition emitDefinitionInternalImpossible
      : DefinitionEmission
  
  emitBackendDefinition : BackendDefinitionCase → DefinitionEmission
  emitBackendDefinition backendAxiomDefinition = emitDefinitionDiagnosticThrow
  emitBackendDefinition backendPrimitiveDefinition = emitDefinitionDiagnosticThrow
  emitBackendDefinition backendFunctionDefinition = emitCompiledFunctionWord
  emitBackendDefinition backendConstructorDefinition = emitConstructorWord
  emitBackendDefinition backendSkippedDefinition = emitNoDefinition
  emitBackendDefinition backendImpossibleDefinition = emitDefinitionInternalImpossible
  
  axiomDefinitionFailsClosed :
    emitBackendDefinition backendAxiomDefinition ≡ emitDefinitionDiagnosticThrow
  axiomDefinitionFailsClosed = refl
  
  primitiveDefinitionFailsClosed :
    emitBackendDefinition backendPrimitiveDefinition ≡ emitDefinitionDiagnosticThrow
  primitiveDefinitionFailsClosed = refl
  
  -- ── 6. Runtime dispatch table mirrored from data/FLib.fth ──
  --
  -- ABI-DISPATCH-BINARY's branch structure is:
  --   * two unregistered cells -> legacy operation;
  --   * two registered scalar handles -> checked operation;
  --   * one registered and one unregistered value -> reject mixed representation;
  --   * two registered values where either is not a scalar -> reject wrong kind.
  --
  -- The Agda function below makes that decision table explicit and proves its
  -- equations. It is a model of inspected Forth behavior, not extraction from it.
  
  data RuntimeOperandClass : Set where
    rawUnregistered trackedScalar trackedNonScalar : RuntimeOperandClass
  
  data BinaryDispatchRoute : Set where
    dispatchCheckedABI dispatchLegacy dispatchRejectMixed dispatchRejectWrongKind : BinaryDispatchRoute
  
  runtimeBinaryRoute : RuntimeOperandClass → RuntimeOperandClass → BinaryDispatchRoute
  runtimeBinaryRoute rawUnregistered rawUnregistered = dispatchLegacy
  runtimeBinaryRoute trackedScalar trackedScalar = dispatchCheckedABI
  runtimeBinaryRoute trackedScalar rawUnregistered = dispatchRejectMixed
  runtimeBinaryRoute trackedNonScalar rawUnregistered = dispatchRejectMixed
  runtimeBinaryRoute rawUnregistered trackedScalar = dispatchRejectMixed
  runtimeBinaryRoute rawUnregistered trackedNonScalar = dispatchRejectMixed
  runtimeBinaryRoute trackedNonScalar trackedScalar = dispatchRejectWrongKind
  runtimeBinaryRoute trackedNonScalar trackedNonScalar = dispatchRejectWrongKind
  runtimeBinaryRoute trackedScalar trackedNonScalar = dispatchRejectWrongKind
  
  rawPairUsesLegacyRoute :
    runtimeBinaryRoute rawUnregistered rawUnregistered ≡ dispatchLegacy
  rawPairUsesLegacyRoute = refl
  
  checkedScalarPairUsesCheckedRoute :
    runtimeBinaryRoute trackedScalar trackedScalar ≡ dispatchCheckedABI
  checkedScalarPairUsesCheckedRoute = refl
  
  trackedScalarPlusRawFailsClosed :
    runtimeBinaryRoute trackedScalar rawUnregistered ≡ dispatchRejectMixed
  trackedScalarPlusRawFailsClosed = refl
  
  rawPlusTrackedScalarFailsClosed :
    runtimeBinaryRoute rawUnregistered trackedScalar ≡ dispatchRejectMixed
  rawPlusTrackedScalarFailsClosed = refl
  
  trackedNonScalarPlusRawFailsClosed :
    runtimeBinaryRoute trackedNonScalar rawUnregistered ≡ dispatchRejectMixed
  trackedNonScalarPlusRawFailsClosed = refl
  
  rawPlusTrackedNonScalarFailsClosed :
    runtimeBinaryRoute rawUnregistered trackedNonScalar ≡ dispatchRejectMixed
  rawPlusTrackedNonScalarFailsClosed = refl
  
  
  -- The concrete runtime's combineModes has one extra state: unannotated.
  -- Model the exact rule implemented by data/FLib.fth: unannotated is absorbing,
  -- linear is absorbing over annotated modes, and only modal/modal joins to modal.
  runtimeCombineModes : RuntimeMode → RuntimeMode → RuntimeMode
  runtimeCombineModes unannotated _ = unannotated
  runtimeCombineModes _ unannotated = unannotated
  runtimeCombineModes linearMode linearMode = linearMode
  runtimeCombineModes linearMode modalMode = linearMode
  runtimeCombineModes modalMode linearMode = linearMode
  runtimeCombineModes modalMode modalMode = modalMode
  
  unannotatedIsAbsorbingLeft :
    (m : RuntimeMode) → runtimeCombineModes unannotated m ≡ unannotated
  unannotatedIsAbsorbingLeft m = refl
  
  unannotatedIsAbsorbingRight :
    (m : RuntimeMode) → runtimeCombineModes m unannotated ≡ unannotated
  unannotatedIsAbsorbingRight unannotated = refl
  unannotatedIsAbsorbingRight linearMode = refl
  unannotatedIsAbsorbingRight modalMode = refl
  
  linearWithAnnotatedRight :
    (m : RuntimeMode) → AnnotatedMode m →
    runtimeCombineModes linearMode m ≡ linearMode
  linearWithAnnotatedRight linearMode checkedLinearMode = refl
  linearWithAnnotatedRight modalMode checkedModalMode = refl
  
  linearWithAnnotatedLeft :
    (m : RuntimeMode) → AnnotatedMode m →
    runtimeCombineModes m linearMode ≡ linearMode
  linearWithAnnotatedLeft linearMode checkedLinearMode = refl
  linearWithAnnotatedLeft modalMode checkedModalMode = refl
  
  modalOnlyJoinsToModal :
    runtimeCombineModes modalMode modalMode ≡ modalMode
  modalOnlyJoinsToModal = refl
  
  -- ── 7. Constructive transaction contract for ABI-BINARY ──
  --
  -- This models the order in data/FLib.fth's ABI-BINARY:
  --   1. validate both handles as live checked scalars (precondition here);
  --   2. reject aliased linear operands;
  --   3. evaluate the raw arithmetic/comparison operator;
  --   4. allocate the result with the joined operand mode;
  --   5. consume linear inputs only after result allocation succeeds.
  --
  -- The runtime blob checked by CI is the exact source examined for this contract.
  -- These are proofs of the following explicit transition model, not a proof
  -- extracted from the concrete Forth implementation.
  
  data BinaryAliasStatus : Set where
    noLinearAlias linearAliasDetected : BinaryAliasStatus
  
  data OperationOutcome (A : Set) : Set where
    operationReturned : A → OperationOutcome A
    operationThrew : RuntimeError → OperationOutcome A
  
  data BinaryCommitResult (leftMode rightMode : SourceMode) : Set where
    binaryFailure :
      RuntimeError → Life → Life → BinaryCommitResult leftMode rightMode
    binarySuccess :
      Nat → SourceMode → Life → Life → BinaryCommitResult leftMode rightMode
  
  lifeAfterBinarySuccess : SourceMode → Life
  lifeAfterBinarySuccess linear = consumed
  lifeAfterBinarySuccess modal = live
  
  checkedBinaryTransaction :
    {leftMode rightMode : SourceMode} →
    BinaryAliasStatus →
    OperationOutcome Nat →
    (Nat → SourceMode → OperationOutcome Nat) →
    BinaryCommitResult leftMode rightMode
  checkedBinaryTransaction {leftMode} {rightMode} linearAliasDetected operation makeResult =
    binaryFailure aliasedLinearOperands live live
  checkedBinaryTransaction {leftMode} {rightMode} noLinearAlias
      (operationThrew err) makeResult =
    binaryFailure err live live
  checkedBinaryTransaction {leftMode} {rightMode} noLinearAlias
      (operationReturned rawValue) makeResult
    with makeResult rawValue (joinSourceMode leftMode rightMode)
  ... | operationThrew err = binaryFailure err live live
  ... | operationReturned resultHandle =
    binarySuccess resultHandle (joinSourceMode leftMode rightMode)
      (lifeAfterBinarySuccess leftMode) (lifeAfterBinarySuccess rightMode)
  
  -- These equations prove that no failure before the ownership-commit writes
  -- consumes either logical operand.
  linearAliasRejectedBeforeOperation :
    {leftMode rightMode : SourceMode} →
    (operation : OperationOutcome Nat) →
    (makeResult : Nat → SourceMode → OperationOutcome Nat) →
    checkedBinaryTransaction {leftMode} {rightMode}
      linearAliasDetected operation makeResult ≡
    binaryFailure aliasedLinearOperands live live
  linearAliasRejectedBeforeOperation operation makeResult = refl
  
  operationFailurePreservesOperands :
    {leftMode rightMode : SourceMode} →
    (err : RuntimeError) →
    (makeResult : Nat → SourceMode → OperationOutcome Nat) →
    checkedBinaryTransaction {leftMode} {rightMode}
      noLinearAlias (operationThrew err) makeResult ≡
    binaryFailure err live live
  operationFailurePreservesOperands err makeResult = refl
  
  resultAllocationFailurePreservesOperands :
    {leftMode rightMode : SourceMode} →
    (rawValue : Nat) →
    (err : RuntimeError) →
    checkedBinaryTransaction {leftMode} {rightMode}
      noLinearAlias (operationReturned rawValue)
      (λ _ _ → operationThrew err) ≡
    binaryFailure err live live
  resultAllocationFailurePreservesOperands rawValue err = refl
  
  successfulBinaryCommitsJoinedModeAndOwnership :
    {leftMode rightMode : SourceMode} →
    (rawValue resultHandle : Nat) →
    checkedBinaryTransaction {leftMode} {rightMode}
      noLinearAlias (operationReturned rawValue)
      (λ _ _ → operationReturned resultHandle) ≡
    binarySuccess resultHandle (joinSourceMode leftMode rightMode)
      (lifeAfterBinarySuccess leftMode) (lifeAfterBinarySuccess rightMode)
  successfulBinaryCommitsJoinedModeAndOwnership rawValue resultHandle = refl
  
  -- WP for the checked binary transaction, with normal and exceptional postconditions.
  -- The failure postcondition observes both input ownership states.
  BinaryWPPost :
    {leftMode rightMode : SourceMode} →
    (normal : Nat → SourceMode → Life → Life → Set) →
    (exceptional : RuntimeError → Life → Life → Set) →
    BinaryCommitResult leftMode rightMode → Set
  BinaryWPPost normal exceptional (binaryFailure err leftLife rightLife) =
    exceptional err leftLife rightLife
  BinaryWPPost normal exceptional (binarySuccess value mode leftLife rightLife) =
    normal value mode leftLife rightLife
  
  checkedBinaryWP :
    {leftMode rightMode : SourceMode} →
    BinaryAliasStatus →
    OperationOutcome Nat →
    (Nat → SourceMode → OperationOutcome Nat) →
    (normal : Nat → SourceMode → Life → Life → Set) →
    (exceptional : RuntimeError → Life → Life → Set) → Set
  checkedBinaryWP {leftMode} {rightMode} alias operation makeResult normal exceptional =
    BinaryWPPost {leftMode = leftMode} {rightMode = rightMode} normal exceptional
      (checkedBinaryTransaction {leftMode = leftMode} {rightMode = rightMode}
        alias operation makeResult)
  
  -- A primitive THROW happens before the linear-ownership commit writes.
  checkedBinaryWPArithmeticFailurePreservesOperands :
    {leftMode rightMode : SourceMode} →
    (err : RuntimeError) →
    (makeResult : Nat → SourceMode → OperationOutcome Nat) →
    (normal : Nat → SourceMode → Life → Life → Set) →
    (exceptional : RuntimeError → Life → Life → Set) →
    exceptional err live live →
    checkedBinaryWP {leftMode = leftMode} {rightMode = rightMode}
      noLinearAlias (operationThrew err) makeResult normal exceptional
  checkedBinaryWPArithmeticFailurePreservesOperands err makeResult normal exceptional proof = proof
  
  -- Result-allocation failure also occurs before either operand is consumed.
  checkedBinaryWPResultAllocationFailurePreservesOperands :
    {leftMode rightMode : SourceMode} →
    (rawValue : Nat) →
    (err : RuntimeError) →
    (normal : Nat → SourceMode → Life → Life → Set) →
    (exceptional : RuntimeError → Life → Life → Set) →
    exceptional err live live →
    checkedBinaryWP {leftMode = leftMode} {rightMode = rightMode}
      noLinearAlias (operationReturned rawValue)
      (λ value mode → operationThrew err) normal exceptional
  checkedBinaryWPResultAllocationFailurePreservesOperands rawValue err normal exceptional proof = proof
  
  linearInputConsumedOnSuccessfulCommit :
    lifeAfterBinarySuccess linear ≡ consumed
  linearInputConsumedOnSuccessfulCommit = refl
  
  modalInputRemainsLiveOnSuccessfulCommit :
    lifeAfterBinarySuccess modal ≡ live
  modalInputRemainsLiveOnSuccessfulCommit = refl
  
  -- ── 8. Verification boundary ──
  --
  -- To close end-to-end refinement, future work must prove that:
  -- (1) each supported compiler translation corresponds to the stated emission;
  -- (2) every generated application/closure/constructor/conditional routes through
  --     a specified ABI path;
  -- (3) each concrete Forth word preserves WellFormed on normal and exceptional
  --     exits; and
  -- (4) unsupported cases fail through a specified, catchable error boundary.
  -- These obligations remain open while the Haskell backend emits raw literals
  -- and legacy operator forms.
  
  
  -- Full-state WP is the contract mechanism: stack, descriptor heap, roots,
  -- metadata identities and exception state belong in S. The former generic frame
  -- theorem merely threaded an unrelated F value unchanged by construction; it did
  -- not prove footprint locality for any Forth word, so it was removed. Reintroduce
  -- a frame theorem only with concrete read/write-footprint evidence for a runtime
  -- operation, not a stack-tail product that is untouched by definition.
  
  
  -- ── Scalar bridge correspondence for the opt-in runtime gate ──
  --
  -- This bridge has two deliberately distinct views:
  --   * bridgeNormalizeNat/Bool are source-semantic views; a closed literal has a
  --     modal interpretation because it has no linear dependencies.
  --   * bridgeRuntimeModeNat/Bool model the actual representation boundary:
  --     FLib.fth's raw/raw dispatch leaves raw cells unannotated, while only checked
  --     handles carry MODE-LINEAR or MODE-MODAL metadata.
  -- Thus source-level modal interpretation is NOT itself evidence of a runtime !.
  -- This mismatch is a proved limitation of the current emitter, not a hidden
  -- assumption in the Girard-preservation claim.
  data BridgeNatCell : Set where
    bridgeRawNat : Nat → BridgeNatCell
    bridgeCheckedNat : Nat → SourceMode → BridgeNatCell
  
  bridgeNatPayload : BridgeNatCell → Nat
  bridgeNatPayload (bridgeRawNat n) = n
  bridgeNatPayload (bridgeCheckedNat n m) = n
  
  bridgeNormalizeNat : BridgeNatCell → Nat × SourceMode
  bridgeNormalizeNat (bridgeRawNat n) = n , modal
  bridgeNormalizeNat (bridgeCheckedNat n m) = n , m
  
  bridgeNatPayloadPreserved :
    (v : BridgeNatCell) → fst (bridgeNormalizeNat v) ≡ bridgeNatPayload v
  bridgeNatPayloadPreserved (bridgeRawNat n) = refl
  bridgeNatPayloadPreserved (bridgeCheckedNat n m) = refl
  
  bridgeRawNatIsModal :
    (n : Nat) → snd (bridgeNormalizeNat (bridgeRawNat n)) ≡ modal
  bridgeRawNatIsModal n = refl
  
  bridgeCheckedModePreserved :
    (n : Nat) (m : SourceMode) →
    snd (bridgeNormalizeNat (bridgeCheckedNat n m)) ≡ m
  bridgeCheckedModePreserved n m = refl
  
  -- Runtime tags are distinct from the logical source interpretation above.
  -- Raw Nat cells emitted by ToForth.hs contain no descriptor/mode witness.
  bridgeRuntimeModeNat : BridgeNatCell → RuntimeMode
  bridgeRuntimeModeNat (bridgeRawNat n) = unannotated
  bridgeRuntimeModeNat (bridgeCheckedNat n m) = sourceMode m
  
  rawNatRuntimeModeIsUnannotated :
    (n : Nat) → bridgeRuntimeModeNat (bridgeRawNat n) ≡ unannotated
  rawNatRuntimeModeIsUnannotated n = refl
  
  checkedNatRuntimeModePreserved :
    (n : Nat) (m : SourceMode) →
    bridgeRuntimeModeNat (bridgeCheckedNat n m) ≡ sourceMode m
  checkedNatRuntimeModePreserved n m = refl
  
  unannotatedCannotBeModal : unannotated ≡ modalMode → ⊥
  unannotatedCannotBeModal ()
  
  unannotatedCannotBeLinear : unannotated ≡ linearMode → ⊥
  unannotatedCannotBeLinear ()
  
  rawNatCannotEstablishModalSourceMode :
    (n : Nat) →
    bridgeRuntimeModeNat (bridgeRawNat n) ≡ sourceMode modal → ⊥
  rawNatCannotEstablishModalSourceMode n ()
  
  rawNatCannotEstablishLinearSourceMode :
    (n : Nat) →
    bridgeRuntimeModeNat (bridgeRawNat n) ≡ sourceMode linear → ⊥
  rawNatCannotEstablishLinearSourceMode n ()
  
  data BridgeBoolCell : Set where
    bridgeRawBool : Bool → BridgeBoolCell
    bridgeCheckedBool : Bool → SourceMode → BridgeBoolCell
  
  bridgeBoolPayload : BridgeBoolCell → Bool
  bridgeBoolPayload (bridgeRawBool b) = b
  bridgeBoolPayload (bridgeCheckedBool b m) = b
  
  bridgeNormalizeBool : BridgeBoolCell → Bool × SourceMode
  bridgeNormalizeBool (bridgeRawBool b) = b , modal
  bridgeNormalizeBool (bridgeCheckedBool b m) = b , m
  
  bridgeBoolPayloadPreserved :
    (v : BridgeBoolCell) → fst (bridgeNormalizeBool v) ≡ bridgeBoolPayload v
  bridgeBoolPayloadPreserved (bridgeRawBool b) = refl
  bridgeBoolPayloadPreserved (bridgeCheckedBool b m) = refl
  
  bridgeRawBoolIsModal :
    (b : Bool) → snd (bridgeNormalizeBool (bridgeRawBool b)) ≡ modal
  bridgeRawBoolIsModal b = refl
  
  bridgeRuntimeModeBool : BridgeBoolCell → RuntimeMode
  bridgeRuntimeModeBool (bridgeRawBool b) = unannotated
  bridgeRuntimeModeBool (bridgeCheckedBool b m) = sourceMode m
  
  rawBoolRuntimeModeIsUnannotated :
    (b : Bool) → bridgeRuntimeModeBool (bridgeRawBool b) ≡ unannotated
  rawBoolRuntimeModeIsUnannotated b = refl
  
  checkedBoolRuntimeModePreserved :
    (b : Bool) (m : SourceMode) →
    bridgeRuntimeModeBool (bridgeCheckedBool b m) ≡ sourceMode m
  checkedBoolRuntimeModePreserved b m = refl
  
  rawBoolCannotEstablishModalSourceMode :
    (b : Bool) →
    bridgeRuntimeModeBool (bridgeRawBool b) ≡ sourceMode modal → ⊥
  rawBoolCannotEstablishModalSourceMode b ()
  
  rawBoolCannotEstablishLinearSourceMode :
    (b : Bool) →
    bridgeRuntimeModeBool (bridgeRawBool b) ≡ sourceMode linear → ⊥
  rawBoolCannotEstablishLinearSourceMode b ()
  
  bridgeNatSub : Nat → Nat → Nat
  bridgeNatSub n zero = n
  bridgeNatSub zero (suc m) = zero
  bridgeNatSub (suc n) (suc m) = bridgeNatSub n m
  
  bridgeNatEq : Nat → Nat → Bool
  bridgeNatEq zero zero = true
  bridgeNatEq zero (suc m) = false
  bridgeNatEq (suc n) zero = false
  bridgeNatEq (suc n) (suc m) = bridgeNatEq n m
  
  bridgeEvalAdd : BridgeNatCell → BridgeNatCell → Nat × SourceMode
  bridgeEvalAdd left right =
    (fst (bridgeNormalizeNat left) + fst (bridgeNormalizeNat right)) ,
    joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))
  
  bridgeEvalSub : BridgeNatCell → BridgeNatCell → Nat × SourceMode
  bridgeEvalSub left right =
    bridgeNatSub (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
    joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))
  
  bridgeEvalEq : BridgeNatCell → BridgeNatCell → Bool × SourceMode
  bridgeEvalEq left right =
    bridgeNatEq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
    joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))
  
  bridgeAddPayloadCorrespondence :
    (left right : BridgeNatCell) →
    fst (bridgeEvalAdd left right) ≡
      fst (bridgeNormalizeNat left) + fst (bridgeNormalizeNat right)
  bridgeAddPayloadCorrespondence left right = refl
  
  bridgeSubPayloadCorrespondence :
    (left right : BridgeNatCell) →
    fst (bridgeEvalSub left right) ≡
      bridgeNatSub (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
  bridgeSubPayloadCorrespondence left right = refl
  
  bridgeEqualityPayloadCorrespondence :
    (left right : BridgeNatCell) →
    fst (bridgeEvalEq left right) ≡
      bridgeNatEq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
  bridgeEqualityPayloadCorrespondence left right = refl
  
  bridgeSelect : Bool → BridgeNatCell → BridgeNatCell → BridgeNatCell
  bridgeSelect true yes no = yes
  bridgeSelect false yes no = no
  
  bridgeTrueSelectsLeft :
    (yes no : BridgeNatCell) → bridgeSelect true yes no ≡ yes
  bridgeTrueSelectsLeft yes no = refl
  
  bridgeFalseSelectsRight :
    (yes no : BridgeNatCell) → bridgeSelect false yes no ≡ no
  bridgeFalseSelectsRight yes no = refl
  
  
  -- Model the rest of the checked scalar ABI vocabulary, including the domain
  -- error for quotient/remainder by zero and the operation-specific joined mode.
  bridgeNatMul : Nat → Nat → Nat
  bridgeNatMul left right = left * right
  
  bridgeNatLt : Nat → Nat → Bool
  bridgeNatLt zero zero = false
  bridgeNatLt zero (suc right) = true
  bridgeNatLt (suc left) zero = false
  bridgeNatLt (suc left) (suc right) = bridgeNatLt left right
  
  bridgeNatGeq : Nat → Nat → Bool
  bridgeNatGeq zero zero = true
  bridgeNatGeq zero (suc right) = false
  bridgeNatGeq (suc left) zero = true
  bridgeNatGeq (suc left) (suc right) = bridgeNatGeq left right
  
  bridgeEvalMul : BridgeNatCell → BridgeNatCell → Nat × SourceMode
  bridgeEvalMul left right =
    bridgeNatMul (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
    joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))
  
  bridgeEvalGeq : BridgeNatCell → BridgeNatCell → Bool × SourceMode
  bridgeEvalGeq left right =
    bridgeNatGeq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
    joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))
  
  bridgeEvalLt : BridgeNatCell → BridgeNatCell → Bool × SourceMode
  bridgeEvalLt left right =
    bridgeNatLt (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right)) ,
    joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right))
  
  bridgeMulPayloadCorrespondence :
    (left right : BridgeNatCell) →
    fst (bridgeEvalMul left right) ≡
      fst (bridgeNormalizeNat left) * fst (bridgeNormalizeNat right)
  bridgeMulPayloadCorrespondence left right = refl
  
  bridgeGeqPayloadCorrespondence :
    (left right : BridgeNatCell) →
    fst (bridgeEvalGeq left right) ≡
      bridgeNatGeq (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
  bridgeGeqPayloadCorrespondence left right = refl
  
  bridgeLtPayloadCorrespondence :
    (left right : BridgeNatCell) →
    fst (bridgeEvalLt left right) ≡
      bridgeNatLt (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
  bridgeLtPayloadCorrespondence left right = refl
  
  bridgeNatDivModFuel : Nat → Nat → Nat → Nat → Nat × Nat
  bridgeNatDivModFuel zero dividend divisor quotient = quotient , dividend
  bridgeNatDivModFuel (suc fuel) dividend divisor quotient
    with bridgeNatLt dividend divisor
  ... | true = quotient , dividend
  ... | false =
    bridgeNatDivModFuel fuel (bridgeNatSub dividend divisor) divisor (suc quotient)
  
  data BridgeDivision : Set where
    bridgeDivisionByZero : BridgeDivision
    bridgeDivisionResult : Nat → Nat → BridgeDivision
  
  bridgeNatDivMod : Nat → Nat → BridgeDivision
  bridgeNatDivMod dividend zero = bridgeDivisionByZero
  bridgeNatDivMod dividend (suc divisor)
    with bridgeNatDivModFuel dividend dividend (suc divisor) zero
  ... | quotient , remainder = bridgeDivisionResult quotient remainder
  
  data BridgeNatEval : Set where
    bridgeNatFailure : RuntimeError → BridgeNatEval
    bridgeNatSuccess : Nat → SourceMode → BridgeNatEval
  
  bridgeEvalQuot : BridgeNatCell → BridgeNatCell → BridgeNatEval
  bridgeEvalQuot left right
    with bridgeNatDivMod (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
  ... | bridgeDivisionByZero = bridgeNatFailure arithmeticDomainError
  ... | bridgeDivisionResult quotient remainder =
    bridgeNatSuccess quotient
      (joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right)))
  
  bridgeEvalRem : BridgeNatCell → BridgeNatCell → BridgeNatEval
  bridgeEvalRem left right
    with bridgeNatDivMod (fst (bridgeNormalizeNat left)) (fst (bridgeNormalizeNat right))
  ... | bridgeDivisionByZero = bridgeNatFailure arithmeticDomainError
  ... | bridgeDivisionResult quotient remainder =
    bridgeNatSuccess remainder
      (joinSourceMode (snd (bridgeNormalizeNat left)) (snd (bridgeNormalizeNat right)))
  
  bridgeQuotZeroIsDomainError :
    (left : BridgeNatCell) →
    bridgeEvalQuot left (bridgeRawNat zero) ≡ bridgeNatFailure arithmeticDomainError
  bridgeQuotZeroIsDomainError left = refl
  
  bridgeRemainderZeroIsDomainError :
    (left : BridgeNatCell) →
    bridgeEvalRem left (bridgeRawNat zero) ≡ bridgeNatFailure arithmeticDomainError
  bridgeRemainderZeroIsDomainError left = refl
  
  -- ── 10. Compositional denotation for the closed Nat/Bool scalar fragment ──
  --
  -- This is a Scott-Strachey-style denotation for a finite, total expression
  -- fragment with explicit runtime errors. Syntax maps compositionally to values
  -- and errors. It deliberately does not claim to model arbitrary Forth, mutable
  -- dictionary operations, untrusted execution tokens, or nontermination.
  
  data ScalarTerm : CoreTy → Set where
    sNatLiteral : Nat → ScalarTerm naturalTy
    sCheckedNat : Nat → SourceMode → ScalarTerm naturalTy
    sBoolLiteral : Bool → SourceMode → ScalarTerm booleanTy
    sAdd : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
    sSub : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
    sMul : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
    sQuot : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
    sRem : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
    sMonus : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm naturalTy
    sEq : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm booleanTy
    sGeq : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm booleanTy
    sLt : ScalarTerm naturalTy → ScalarTerm naturalTy → ScalarTerm booleanTy
    sIfNat :
      ScalarTerm booleanTy →
      ScalarTerm naturalTy →
      ScalarTerm naturalTy →
      ScalarTerm naturalTy
  
  data ScalarValue : CoreTy → Set where
    scalarNat : Nat → SourceMode → ScalarValue naturalTy
    scalarBool : Bool → SourceMode → ScalarValue booleanTy
  
  data ScalarResult (A : Set) : Set where
    scalarRaised : RuntimeError → ScalarResult A
    scalarReturned : A → ScalarResult A
  
  scalarQuotDenotation :
    Nat → SourceMode → Nat → SourceMode →
    ScalarResult (ScalarValue naturalTy)
  scalarQuotDenotation left leftMode right rightMode
    with bridgeNatDivMod left right
  ... | bridgeDivisionByZero = scalarRaised arithmeticDomainError
  ... | bridgeDivisionResult quotient remainder =
    scalarReturned (scalarNat quotient (joinSourceMode leftMode rightMode))
  
  scalarRemDenotation :
    Nat → SourceMode → Nat → SourceMode →
    ScalarResult (ScalarValue naturalTy)
  scalarRemDenotation left leftMode right rightMode
    with bridgeNatDivMod left right
  ... | bridgeDivisionByZero = scalarRaised arithmeticDomainError
  ... | bridgeDivisionResult quotient remainder =
    scalarReturned (scalarNat remainder (joinSourceMode leftMode rightMode))
  
  denoteScalar :
    {A : CoreTy} → ScalarTerm A → ScalarResult (ScalarValue A)
  denoteScalar (sNatLiteral n) = scalarReturned (scalarNat n modal)
  denoteScalar (sCheckedNat n mode) = scalarReturned (scalarNat n mode)
  denoteScalar (sBoolLiteral b mode) = scalarReturned (scalarBool b mode)
  denoteScalar (sAdd left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarReturned (scalarNat (x + y) (joinSourceMode leftMode rightMode))
  denoteScalar (sSub left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarReturned (scalarNat (bridgeNatSub x y) (joinSourceMode leftMode rightMode))
  denoteScalar (sMul left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarReturned (scalarNat (bridgeNatMul x y) (joinSourceMode leftMode rightMode))
  denoteScalar (sQuot left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarQuotDenotation x leftMode y rightMode
  denoteScalar (sRem left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarRemDenotation x leftMode y rightMode
  denoteScalar (sMonus left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarReturned (scalarNat (bridgeNatSub x y) (joinSourceMode leftMode rightMode))
  denoteScalar (sEq left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarReturned (scalarBool (bridgeNatEq x y) (joinSourceMode leftMode rightMode))
  denoteScalar (sGeq left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarReturned (scalarBool (bridgeNatGeq x y) (joinSourceMode leftMode rightMode))
  denoteScalar (sLt left right) with denoteScalar left | denoteScalar right
  ... | scalarRaised err | _ = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarNat x leftMode) | scalarReturned (scalarNat y rightMode) =
    scalarReturned (scalarBool (bridgeNatLt x y) (joinSourceMode leftMode rightMode))
  denoteScalar (sIfNat condition yes no) with denoteScalar condition
  ... | scalarRaised err = scalarRaised err
  ... | scalarReturned (scalarBool true conditionMode) = denoteScalar yes
  ... | scalarReturned (scalarBool false conditionMode) = denoteScalar no
  
  scalarFromCell : BridgeNatCell → ScalarTerm naturalTy
  scalarFromCell (bridgeRawNat n) = sNatLiteral n
  scalarFromCell (bridgeCheckedNat n mode) = sCheckedNat n mode
  
  scalarCellIsModal :
    (n : Nat) →
    denoteScalar (scalarFromCell (bridgeRawNat n)) ≡
      scalarReturned (scalarNat n modal)
  scalarCellIsModal n = refl
  
  scalarCheckedCellPreservesMode :
    (n : Nat) (mode : SourceMode) →
    denoteScalar (scalarFromCell (bridgeCheckedNat n mode)) ≡
      scalarReturned (scalarNat n mode)
  scalarCheckedCellPreservesMode n mode = refl
  
  scalarAdditionCompositional :
    (left right : Nat) →
    denoteScalar (sAdd (sNatLiteral left) (sNatLiteral right)) ≡
      scalarReturned (scalarNat (left + right) modal)
  scalarAdditionCompositional left right = refl
  
  scalarMixedAdditionCompositional :
    (left right : Nat) (mode : SourceMode) →
    denoteScalar (sAdd (sCheckedNat left mode) (sNatLiteral right)) ≡
      scalarReturned (scalarNat (left + right) (joinSourceMode mode modal))
  scalarMixedAdditionCompositional left right mode = refl
  
  scalarEqualityCompositional :
    (left right : Nat) →
    denoteScalar (sEq (sNatLiteral left) (sNatLiteral right)) ≡
      scalarReturned (scalarBool (bridgeNatEq left right) modal)
  scalarEqualityCompositional left right = refl
  
  scalarTrueChoosesThenBranch :
    (yes no : ScalarTerm naturalTy) →
    denoteScalar (sIfNat (sBoolLiteral true modal) yes no) ≡ denoteScalar yes
  scalarTrueChoosesThenBranch yes no = refl
  
  scalarFalseChoosesElseBranch :
    (yes no : ScalarTerm naturalTy) →
    denoteScalar (sIfNat (sBoolLiteral false modal) yes no) ≡ denoteScalar no
  scalarFalseChoosesElseBranch yes no = refl
  
  scalarQuotientByZeroRaises :
    (numerator : Nat) →
    denoteScalar (sQuot (sNatLiteral numerator) (sNatLiteral zero)) ≡
      scalarRaised arithmeticDomainError
  scalarQuotientByZeroRaises numerator = refl
  
  scalarRemainderByZeroRaises :
    (numerator : Nat) →
    denoteScalar (sRem (sNatLiteral numerator) (sNatLiteral zero)) ≡
      scalarRaised arithmeticDomainError
  scalarRemainderByZeroRaises numerator = refl
  
  scalarNatEvalToResult : BridgeNatEval → ScalarResult (ScalarValue naturalTy)
  scalarNatEvalToResult (bridgeNatFailure err) = scalarRaised err
  scalarNatEvalToResult (bridgeNatSuccess n mode) = scalarReturned (scalarNat n mode)
  
  scalarAdditionMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sAdd (scalarFromCell left) (scalarFromCell right)) ≡
      scalarReturned (scalarNat (fst (bridgeEvalAdd left right)) (snd (bridgeEvalAdd left right)))
  scalarAdditionMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
  scalarAdditionMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
  scalarAdditionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
  scalarAdditionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl
  
  scalarSubtractionMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sSub (scalarFromCell left) (scalarFromCell right)) ≡
      scalarReturned (scalarNat (fst (bridgeEvalSub left right)) (snd (bridgeEvalSub left right)))
  scalarSubtractionMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
  scalarSubtractionMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
  scalarSubtractionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
  scalarSubtractionMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl
  
  scalarMultiplicationMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sMul (scalarFromCell left) (scalarFromCell right)) ≡
      scalarReturned (scalarNat (fst (bridgeEvalMul left right)) (snd (bridgeEvalMul left right)))
  scalarMultiplicationMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
  scalarMultiplicationMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
  scalarMultiplicationMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
  scalarMultiplicationMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl
  
  scalarEqualityMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sEq (scalarFromCell left) (scalarFromCell right)) ≡
      scalarReturned (scalarBool (fst (bridgeEvalEq left right)) (snd (bridgeEvalEq left right)))
  scalarEqualityMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
  scalarEqualityMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
  scalarEqualityMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
  scalarEqualityMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl
  
  scalarGreaterEqualMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sGeq (scalarFromCell left) (scalarFromCell right)) ≡
      scalarReturned (scalarBool (fst (bridgeEvalGeq left right)) (snd (bridgeEvalGeq left right)))
  scalarGreaterEqualMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
  scalarGreaterEqualMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
  scalarGreaterEqualMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
  scalarGreaterEqualMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl
  
  scalarLessThanMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sLt (scalarFromCell left) (scalarFromCell right)) ≡
      scalarReturned (scalarBool (fst (bridgeEvalLt left right)) (snd (bridgeEvalLt left right)))
  scalarLessThanMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y) = refl
  scalarLessThanMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode) = refl
  scalarLessThanMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y) = refl
  scalarLessThanMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode') = refl
  
  scalarQuotientMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sQuot (scalarFromCell left) (scalarFromCell right)) ≡
      scalarNatEvalToResult (bridgeEvalQuot left right)
  scalarQuotientMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  scalarQuotientMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  scalarQuotientMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  scalarQuotientMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode')
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  
  scalarRemainderMatchesRuntimeBridge :
    (left right : BridgeNatCell) →
    denoteScalar (sRem (scalarFromCell left) (scalarFromCell right)) ≡
      scalarNatEvalToResult (bridgeEvalRem left right)
  scalarRemainderMatchesRuntimeBridge (bridgeRawNat x) (bridgeRawNat y)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  scalarRemainderMatchesRuntimeBridge (bridgeRawNat x) (bridgeCheckedNat y mode)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  scalarRemainderMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeRawNat y)
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  scalarRemainderMatchesRuntimeBridge (bridgeCheckedNat x mode) (bridgeCheckedNat y mode')
    with bridgeNatDivMod x y
  ... | bridgeDivisionByZero = refl
  ... | bridgeDivisionResult quotient remainder = refl
  
  -- Recovered compositional semantics from the formerly separate denotation
  -- module. Kept nested here so there is one authoritative Agda specification.
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
  
