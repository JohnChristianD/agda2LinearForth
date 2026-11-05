{-# OPTIONS --safe --without-K --cubical=no-glue #-}

module MALLPForth where

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

  -- A single value type is enough for this initial strict fragment.
  -- Each stack transition consumes precisely its indexed input resources.
  data StackType : Set where
    natCell : StackType

  data Stack : List StackType → Set where
    emptyStack : Stack []
    pushCell : {Γ : List StackType} → Nat → Stack Γ → Stack (natCell ∷ Γ)

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

  -- Indexed postfix combinators. There is no constructor for DUP, DROP,
  -- weakening, contraction, a heap address, or a closure.
  data ForthCode : List StackType → List StackType → Set where
    pushNat : {Γ : List StackType} → Nat → ForthCode Γ (natCell ∷ Γ)
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

  execForthCode : {Γ Δ : List StackType} → ForthCode Γ Δ → Stack Γ → Stack Δ
  execForthCode (pushNat n) stack = pushCell n stack
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
  execForthCode-correct (literal n) stack = refl
  execForthCode-correct (binary op left right) stack
    rewrite execForthCode-correct left stack
          | execForthCode-correct right (pushCell (evalNatExpr left) stack) =
      refl

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

  renderForth : {Γ Δ : List StackType} → ForthCode Γ Δ → List ForthToken
  renderForth (pushNat n) = pushLiteral n ∷ []
  renderForth (binaryWord op) = renderNatOp op ∷ []
  renderForth (sequence first second) =
    renderForth first ++ᴳ renderForth second

  -- Interpret the actual postfix token list produced by renderForth.
  forgetStack : {Γ : List StackType} → Stack Γ → List Nat
  forgetStack emptyStack = []
  forgetStack (pushCell n stack) = n ∷ forgetStack stack

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

  maybeBind : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  maybeBind nothing continuation = nothing
  maybeBind (just value) continuation = continuation value

  execTokens : List ForthToken → List Nat → Maybe (List Nat)
  execTokens [] stack = just stack
  execTokens (token ∷ tokens) stack with execToken token stack
  ... | nothing = nothing
  ... | just nextStack = execTokens tokens nextStack

  execTokens-append :
    (first second : List ForthToken) (stack : List Nat) →
    execTokens (first ++ᴳ second) stack ≡
    maybeBind (execTokens first stack) (λ nextStack → execTokens second nextStack)
  execTokens-append [] second stack = refl
  execTokens-append (token ∷ first) second stack
    with execToken token stack
  ... | nothing = refl
  ... | just nextStack = execTokens-append first second nextStack

  renderForth-sound :
    {Γ Δ : List StackType} (code : ForthCode Γ Δ) (stack : Stack Γ) →
    execTokens (renderForth code) (forgetStack stack) ≡
    just (forgetStack (execForthCode code stack))
  renderForth-sound (pushNat n) stack = refl
  renderForth-sound (binaryWord addOp) (pushCell right (pushCell left stack)) = refl
  renderForth-sound (binaryWord monusOp) (pushCell right (pushCell left stack)) = refl
  renderForth-sound (binaryWord multiplyOp) (pushCell right (pushCell left stack)) = refl
  renderForth-sound (sequence first second) stack
    rewrite execTokens-append (renderForth first) (renderForth second) (forgetStack stack)
          | renderForth-sound first stack
          | renderForth-sound second (execForthCode first stack) = refl

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

open StrictNatCompiler public

