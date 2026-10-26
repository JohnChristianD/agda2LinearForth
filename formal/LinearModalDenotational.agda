{-# OPTIONS --safe #-}

-- Scott-Strachey style compositional semantics for the source-level core
-- represented by the fixed ToForth.hs vocabulary. Fuel exhaustion is explicit:
-- it is a semantic approximation to divergence, not a successful return.
-- This module is constructive and imports only Agda builtins plus the local ABI
-- vocabulary. Its equations define the reference semantics; they do not by
-- themselves certify the concrete Forth implementation.
module LinearModalDenotational where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import LinearModalABI using
  ( List; []; _::_; _++_
  ; RuntimeError; wrongKind; unknownHandle; badResultPayload
  ; arithmeticDomainError
  )

data Truth : Set where
  yes no : Truth

ifTruth : {A : Set} → Truth → A → A → A
ifTruth yes x y = x
ifTruth no x y = y

notTruth : Truth → Truth
notTruth yes = no
notTruth no = yes

andTruth : Truth → Truth → Truth
andTruth yes y = y
andTruth no y = no

eqNat : Nat → Nat → Truth
eqNat zero zero = yes
eqNat zero (suc y) = no
eqNat (suc x) zero = no
eqNat (suc x) (suc y) = eqNat x y

ltNat : Nat → Nat → Truth
ltNat zero zero = no
ltNat zero (suc y) = yes
ltNat (suc x) zero = no
ltNat (suc x) (suc y) = ltNat x y

addNat : Nat → Nat → Nat
addNat zero y = y
addNat (suc x) y = suc (addNat x y)

-- Natural subtraction is truncated at zero, matching Agda Nat subtraction.
subNat : Nat → Nat → Nat
subNat zero y = zero
subNat (suc x) zero = suc x
subNat (suc x) (suc y) = subNat x y

mulNat : Nat → Nat → Nat
mulNat zero y = zero
mulNat (suc x) y = addNat y (mulNat x y)

lengthNat : {A : Set} → List A → Nat
lengthNat [] = zero
lengthNat (_ :: xs) = suc (lengthNat xs)

data PartialNat : Set where
  numericResult : Nat → PartialNat
  divisionByZero : PartialNat
  fuelExhausted : PartialNat

-- Total approximants for division and remainder. Increasing fuel extends the
-- computation; exhausting it is kept distinct from a source-level domain error.
quotientFuel : Nat → Nat → Nat → PartialNat
quotientFuel zero n d = fuelExhausted
quotientFuel (suc fuel) n zero = divisionByZero
quotientFuel (suc fuel) n (suc d) with ltNat n (suc d)
... | yes = numericResult zero
... | no with quotientFuel fuel (subNat n (suc d)) (suc d)
...   | numericResult q = numericResult (suc q)
...   | divisionByZero = divisionByZero
...   | fuelExhausted = fuelExhausted

remainderFuel : Nat → Nat → Nat → PartialNat
remainderFuel zero n d = fuelExhausted
remainderFuel (suc fuel) n zero = divisionByZero
remainderFuel (suc fuel) n (suc d) with ltNat n (suc d)
... | yes = numericResult n
... | no with remainderFuel fuel (subNat n (suc d)) (suc d)
...   | numericResult r = numericResult r
...   | divisionByZero = divisionByZero
...   | fuelExhausted = fuelExhausted

data DenotationalPrimitive : Set where
  natAdd natSub natMul natQuot natRem natEq natGeq natLt natMonus : DenotationalPrimitive

mutual
  data Term : Set where
    natLit : Nat → Term
    boolLit : Truth → Term
    unitLit : Term
    var : Nat → Term
    lam : Term → Term
    app : Term → Term → Term
    primCall : DenotationalPrimitive → Term → Term → Term
    ifThenElse : Term → Term → Term → Term
    constr : Nat → List Term → Term
    caseTerm : Term → Nat → Nat → Term → Term → Term
    raiseTerm : RuntimeError → Term
    catchTerm : Term → Term → Term
    packResult : Term → Term
    unpackResult : Term → Term
    printTerm : Term → Term

  data Value : Set where
    natValue : Nat → Value
    boolValue : Truth → Value
    unitValue : Value
    closureValue : List Value → Term → Value
    constructorValue : Nat → List Value → Value
    resultValue : Value → Value
    errorValue : RuntimeError → Value
    valueList : List Value → Value

data FoundValue : Set where
  missingValue : FoundValue
  found : Value → FoundValue

lookupValue : Nat → List Value → FoundValue
lookupValue zero [] = missingValue
lookupValue zero (v :: env) = found v
lookupValue (suc n) [] = missingValue
lookupValue (suc n) (v :: env) = lookupValue n env

data Event : Set where
  printedValue : Value → Event

data Outcome : Set where
  returned : Value → List Event → Outcome
  raised : RuntimeError → List Event → Outcome
  outOfFuel : List Event → Outcome

bind : Outcome → (Value → Outcome) → Outcome
bind (returned v trace) k with k v
... | returned result trace' = returned result (trace ++ trace')
... | raised err trace' = raised err (trace ++ trace')
... | outOfFuel trace' = outOfFuel (trace ++ trace')
bind (raised err trace) k = raised err trace
bind (outOfFuel trace) k = outOfFuel trace

prefixTrace : List Event → Outcome → Outcome
prefixTrace trace (returned v later) = returned v (trace ++ later)
prefixTrace trace (raised err later) = raised err (trace ++ later)
prefixTrace trace (outOfFuel later) = outOfFuel (trace ++ later)

primitiveDenotation : Nat → DenotationalPrimitive → Value → Value → Outcome
primitiveDenotation fuel natAdd (natValue x) (natValue y) =
  returned (natValue (addNat x y)) []
primitiveDenotation fuel natSub (natValue x) (natValue y) =
  returned (natValue (subNat x y)) []
primitiveDenotation fuel natMonus (natValue x) (natValue y) =
  returned (natValue (subNat x y)) []
primitiveDenotation fuel natMul (natValue x) (natValue y) =
  returned (natValue (mulNat x y)) []
primitiveDenotation fuel natQuot (natValue x) (natValue zero) =
  raised arithmeticDomainError []
primitiveDenotation fuel natQuot (natValue x) (natValue (suc y))
  with quotientFuel fuel x (suc y)
... | numericResult q = returned (natValue q) []
... | divisionByZero = raised arithmeticDomainError []
... | fuelExhausted = outOfFuel []
primitiveDenotation fuel natRem (natValue x) (natValue zero) =
  raised arithmeticDomainError []
primitiveDenotation fuel natRem (natValue x) (natValue (suc y))
  with remainderFuel fuel x (suc y)
... | numericResult r = returned (natValue r) []
... | divisionByZero = raised arithmeticDomainError []
... | fuelExhausted = outOfFuel []
primitiveDenotation fuel natEq (natValue x) (natValue y) =
  returned (boolValue (eqNat x y)) []
primitiveDenotation fuel natGeq (natValue x) (natValue y) =
  returned (boolValue (notTruth (ltNat x y))) []
primitiveDenotation fuel natLt (natValue x) (natValue y) =
  returned (boolValue (ltNat x y)) []
primitiveDenotation fuel op left right = raised wrongKind []

mutual
  eval : Nat → List Value → Term → Outcome
  eval zero env term = outOfFuel []
  eval (suc fuel) env (natLit n) = returned (natValue n) []
  eval (suc fuel) env (boolLit b) = returned (boolValue b) []
  eval (suc fuel) env unitLit = returned unitValue []
  eval (suc fuel) env (var index) with lookupValue index env
  ... | missingValue = raised unknownHandle []
  ... | found value = returned value []
  eval (suc fuel) env (lam body) = returned (closureValue env body) []
  eval (suc fuel) env (app fn arg) =
    bind (eval fuel env fn) (λ fnValue →
      bind (eval fuel env arg) (λ argValue →
        applyValue fuel fnValue argValue))
  eval (suc fuel) env (primCall op left right) =
    bind (eval fuel env left) (λ leftValue →
      bind (eval fuel env right) (λ rightValue →
        primitiveDenotation fuel op leftValue rightValue))
  eval (suc fuel) env (ifThenElse condition yesBranch noBranch) =
    bind (eval fuel env condition) (λ conditionValue →
      chooseBranch fuel env conditionValue yesBranch noBranch)
  eval (suc fuel) env (constr tag args) =
    bind (evalTerms fuel env args) (λ values →
      finishConstructor tag values)
  eval (suc fuel) env (caseTerm scrutinee tag arity body fallback) =
    bind (eval fuel env scrutinee) (λ value →
      matchValue fuel env tag arity body fallback value)
  eval (suc fuel) env (raiseTerm err) = raised err []
  eval (suc fuel) env (catchTerm body handler) =
    catchOutcome fuel env handler (eval fuel env body)
  eval (suc fuel) env (packResult body) =
    bind (eval fuel env body) (λ value →
      returned (resultValue value) [])
  eval (suc fuel) env (unpackResult body) =
    bind (eval fuel env body) unwrapValue
  eval (suc fuel) env (printTerm body) =
    bind (eval fuel env body) (λ value →
      returned unitValue (printedValue value :: []))

  evalTerms : Nat → List Value → List Term → Outcome
  evalTerms zero env [] = returned (valueList []) []
  evalTerms zero env (term :: terms) = outOfFuel []
  evalTerms (suc fuel) env [] = returned (valueList []) []
  evalTerms (suc fuel) env (term :: terms) =
    bind (eval fuel env term) (λ value →
      bind (evalTerms fuel env terms) (λ values →
        prependValue value values))

  applyValue : Nat → Value → Value → Outcome
  applyValue zero fn arg = outOfFuel []
  applyValue (suc fuel) (closureValue captured body) arg =
    eval fuel (arg :: captured) body
  applyValue (suc fuel) fn arg = raised wrongKind []

  chooseBranch : Nat → List Value → Value → Term → Term → Outcome
  chooseBranch fuel env (boolValue yes) yesBranch noBranch =
    eval fuel env yesBranch
  chooseBranch fuel env (boolValue no) yesBranch noBranch =
    eval fuel env noBranch
  chooseBranch fuel env value yesBranch noBranch = raised wrongKind []

  prependValue : Value → Value → Outcome
  prependValue value (valueList values) = returned (valueList (value :: values)) []
  prependValue value other = raised wrongKind []

  finishConstructor : Nat → Value → Outcome
  finishConstructor tag (valueList values) = returned (constructorValue tag values) []
  finishConstructor tag other = raised wrongKind []

  matchValue : Nat → List Value → Nat → Nat → Term → Term → Value → Outcome
  matchValue fuel env tag arity body fallback (constructorValue actual fields)
    with andTruth (eqNat tag actual) (eqNat arity (lengthNat fields))
  ... | yes = eval fuel (fields ++ env) body
  ... | no = eval fuel env fallback
  matchValue fuel env tag arity body fallback other = eval fuel env fallback

  unwrapValue : Value → Outcome
  unwrapValue (resultValue value) = returned value []
  unwrapValue other = raised badResultPayload []

  catchOutcome : Nat → List Value → Term → Outcome → Outcome
  catchOutcome fuel env handler (returned value trace) = returned value trace
  catchOutcome fuel env handler (raised err trace) =
    prefixTrace trace (eval fuel (errorValue err :: env) handler)
  catchOutcome fuel env handler (outOfFuel trace) = outOfFuel trace

-- These equations are definitional reference-meaning facts. They do not claim
-- that arbitrary Forth, or every current emitted Forth path, refines this model.
denotesAddition :
  (fuel x y : Nat) →
  eval (suc (suc fuel)) [] (primCall natAdd (natLit x) (natLit y))
    ≡ returned (natValue (addNat x y)) []
denotesAddition fuel x y = refl

denotesSubtraction :
  (fuel x y : Nat) →
  eval (suc (suc fuel)) [] (primCall natSub (natLit x) (natLit y))
    ≡ returned (natValue (subNat x y)) []
denotesSubtraction fuel x y = refl

denotesMultiplication :
  (fuel x y : Nat) →
  eval (suc (suc fuel)) [] (primCall natMul (natLit x) (natLit y))
    ≡ returned (natValue (mulNat x y)) []
denotesMultiplication fuel x y = refl

denotesEquality :
  (fuel x y : Nat) →
  eval (suc (suc fuel)) [] (primCall natEq (natLit x) (natLit y))
    ≡ returned (boolValue (eqNat x y)) []
denotesEquality fuel x y = refl

denotesGreaterEqual :
  (fuel x y : Nat) →
  eval (suc (suc fuel)) [] (primCall natGeq (natLit x) (natLit y))
    ≡ returned (boolValue (notTruth (ltNat x y))) []
denotesGreaterEqual fuel x y = refl

denotesLessThan :
  (fuel x y : Nat) →
  eval (suc (suc fuel)) [] (primCall natLt (natLit x) (natLit y))
    ≡ returned (boolValue (ltNat x y)) []
denotesLessThan fuel x y = refl

denotesMonus :
  (fuel x y : Nat) →
  eval (suc (suc fuel)) [] (primCall natMonus (natLit x) (natLit y))
    ≡ returned (natValue (subNat x y)) []
denotesMonus fuel x y = refl

denotesQuotientByZero :
  (fuel x : Nat) →
  eval (suc (suc fuel)) [] (primCall natQuot (natLit x) (natLit zero))
    ≡ raised arithmeticDomainError []
denotesQuotientByZero fuel x = refl

denotesRemainderByZero :
  (fuel x : Nat) →
  eval (suc (suc fuel)) [] (primCall natRem (natLit x) (natLit zero))
    ≡ raised arithmeticDomainError []
denotesRemainderByZero fuel x = refl

denotesTrueConditional :
  (fuel : Nat) (yesBranch noBranch : Term) →
  eval (suc (suc fuel)) [] (ifThenElse (boolLit yes) yesBranch noBranch)
    ≡ eval (suc fuel) [] yesBranch
denotesTrueConditional fuel yesBranch noBranch = refl

denotesFalseConditional :
  (fuel : Nat) (yesBranch noBranch : Term) →
  eval (suc (suc fuel)) [] (ifThenElse (boolLit no) yesBranch noBranch)
    ≡ eval (suc fuel) [] noBranch
denotesFalseConditional fuel yesBranch noBranch = refl

denotesResultRoundTrip :
  (fuel : Nat) (value : Term) →
  eval (suc (suc fuel)) [] (unpackResult (packResult value))
    ≡ eval fuel [] value
denotesResultRoundTrip fuel value = refl

denotesCatchRaisedError :
  (fuel : Nat) →
  eval (suc (suc fuel)) [] (catchTerm (raiseTerm arithmeticDomainError) (var zero))
    ≡ returned (errorValue arithmeticDomainError) []
denotesCatchRaisedError fuel = refl

denotesIdentityApplication :
  (fuel n : Nat) →
  eval (suc (suc (suc (suc fuel)))) []
    (app (lam (var zero)) (natLit n))
    ≡ returned (natValue n) []
denotesIdentityApplication fuel n = refl

denotesSingleConstructorMatch :
  (fuel tag n : Nat) →
  eval (suc (suc (suc (suc fuel)))) []
    (caseTerm (constr tag (natLit n :: [])) tag (suc zero) (var zero) (natLit zero))
    ≡ returned (natValue n) []
denotesSingleConstructorMatch fuel tag n = refl
