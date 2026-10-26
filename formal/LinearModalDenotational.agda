{-# OPTIONS --safe #-}

-- A postulate-free Scott-Strachey-style reference semantics for the backend's
-- major core forms. This is an abstract source/core semantics, not a claim that
-- the separate Haskell and Forth implementations have already been proved to
-- refine it. The heap/ownership contracts live in LinearModalSafety.
module LinearModalDenotational where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import LinearModalSafety using
  ( RuntimeError; unknownPrimitive; wrongKind; arithmeticDomainError
  ; SourceMode; linear; modal; joinSourceMode
  ; bridgeNatSub; bridgeNatMul; bridgeNatLt; bridgeNatGeq
  ; bridgeNatDivMod; BridgeDivision; bridgeDivisionByZero; bridgeDivisionResult
  )

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

  evalList : Nat → Env → DList Term → ValuesOutcome
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

conditionalSelectsItsTrueBranch :
  (yes no : Term) →
  eval (suc (suc zero)) dnil (tIf (tBool true modal) yes no) ≡ eval (suc zero) dnil yes
conditionalSelectsItsTrueBranch yes no = refl

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
