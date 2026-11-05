{-# OPTIONS --safe --cubical=no-glue #-}

module LinearModalSafety where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Equality using (_≡_; refl)

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C)
      → {x y : A} {u v : B} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

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

open LaurentPolarizedMALLP public

------------------------------------------------------------------------
-- Strict closed-Nat Forth combinator semantics
--
-- This compiler fragment has no variables, closures, heap, implicit copy,
-- implicit drop, exponentials, or garbage collector.  Each syntax child is
-- visited once; each combinator returns exactly one Nat and preserves the
-- caller's residual stack.
------------------------------------------------------------------------

module StrictNatCompiler where

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

  data ForthCode : Set where
    pushNat : Nat → ForthCode
    binaryWord : NatOp → ForthCode → ForthCode → ForthCode

  compileNat : NatExpr → ForthCode
  compileNat (literal n) = pushNat n
  compileNat (binary op left right) =
    binaryWord op (compileNat left) (compileNat right)

  evalForthCode : ForthCode → Nat
  evalForthCode (pushNat n) = n
  evalForthCode (binaryWord op left right) =
    applyNatOp op (evalForthCode left) (evalForthCode right)

  compileNat-correct : (e : NatExpr) →
    evalForthCode (compileNat e) ≡ evalNatExpr e
  compileNat-correct (literal n) = refl
  compileNat-correct (binary op left right) =
    cong₂ (applyNatOp op)
      (compileNat-correct left)
      (compileNat-correct right)

  -- The abstract Forth combinator machine returns one new top value and
  -- preserves the caller's residual stack.  Binary code runs its left child,
  -- then its right child, then consumes those two results with one word.
  record StackOutcome : Set where
    constructor outcome
    field
      resultCell : Nat
      residualStack : List Nat
  open StackOutcome public

  execForthCode : ForthCode → List Nat → StackOutcome
  execForthCode (pushNat n) stack = outcome n stack
  execForthCode (binaryWord op left right) stack
    with execForthCode left stack
  ... | outcome leftValue afterLeft
    with execForthCode right afterLeft
  ...   | outcome rightValue afterRight =
          outcome (applyNatOp op leftValue rightValue) afterRight

  execForthCode-preserves-residual :
    (code : ForthCode) (stack : List Nat) →
    residualStack (execForthCode code stack) ≡ stack
  execForthCode-preserves-residual (pushNat n) stack = refl
  execForthCode-preserves-residual (binaryWord op left right) stack
    with execForthCode left stack
  ... | outcome leftValue afterLeft
    rewrite execForthCode-preserves-residual left stack
    with execForthCode right stack
  ...   | outcome rightValue afterRight
    rewrite execForthCode-preserves-residual right stack = refl

  execForthCode-correct :
    (code : ForthCode) (stack : List Nat) →
    resultCell (execForthCode code stack) ≡ evalForthCode code
  execForthCode-correct (pushNat n) stack = refl
  execForthCode-correct (binaryWord op left right) stack
    with execForthCode left stack
  ... | outcome leftValue afterLeft
    rewrite execForthCode-preserves-residual left stack
    with execForthCode right stack
  ...   | outcome rightValue afterRight
    rewrite execForthCode-correct left stack
          | execForthCode-correct right stack = refl

  compiledNat-stack-correct :
    (e : NatExpr) (stack : List Nat) →
    resultCell (execForthCode (compileNat e) stack) ≡ evalNatExpr e
  compiledNat-stack-correct e stack =
    trans (execForthCode-correct (compileNat e) stack)
         (compileNat-correct e)

  data ForthToken : Set where
    pushLiteral : Nat → ForthToken
    addWord monusWord multiplyWord : ForthToken

  _++ᴳ_ : {A : Set} → List A → List A → List A
  [] ++ᴳ ys = ys
  (x ∷ xs) ++ᴳ ys = x ∷ (xs ++ᴳ ys)

  renderNatOp : NatOp → ForthToken
  renderNatOp addOp = addWord
  renderNatOp monusOp = monusWord
  renderNatOp multiplyOp = multiplyWord

  renderForth : ForthCode → List ForthToken
  renderForth (pushNat n) = pushLiteral n ∷ []
  renderForth (binaryWord op left right) =
    (renderForth left ++ᴳ renderForth right) ++ᴳ (renderNatOp op ∷ [])

  maxNat : Nat → Nat → Nat
  maxNat zero y = y
  maxNat (suc x) zero = suc x
  maxNat (suc x) (suc y) = suc (maxNat x y)

  -- Maximum number of newly-produced stack cells during postfix emission.
  -- Binary code evaluates its left child, then its right child with one cell
  -- already present, then consumes two cells and returns one.
  peakStackGrowth : ForthCode → Nat
  peakStackGrowth (pushNat n) = suc zero
  peakStackGrowth (binaryWord op left right) =
    maxNat (peakStackGrowth left) (suc (peakStackGrowth right))

  record StackContract : Set where
    constructor stackContract
    field
      requiredInputCells : Nat
      resultCells : Nat
      peakAdditionalCells : Nat
  open StackContract public

  stackContractOf : ForthCode → StackContract
  stackContractOf code =
    stackContract zero (suc zero) (peakStackGrowth code)

  compiledNat-contract : (e : NatExpr) →
    requiredInputCells (stackContractOf (compileNat e)) ≡ zero
  compiledNat-contract e = refl

  compiledNat-result : (e : NatExpr) →
    resultCells (stackContractOf (compileNat e)) ≡ suc zero
  compiledNat-result e = refl

open StrictNatCompiler public
