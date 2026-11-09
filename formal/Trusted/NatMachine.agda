{-# OPTIONS --safe #-}

module Trusted.NatMachine where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)

-- A small, axiom-free target machine.  Stack head is the top of stack.
-- This module deliberately has no dependency on the exploratory,
-- rewrite-enabled foundations in MALLPForth.agda.

data Token : Set where
  pushNat : Nat → Token
  addNat : Token
  monusNat : Token
  multiplyNat : Token
  swapNat : Token

Stack : Set
Stack = List Nat

monus : Nat → Nat → Nat
monus zero y = y
monus (suc x) zero = zero
monus (suc x) (suc y) = monus x y

step : Token → Stack → Maybe Stack
step (pushNat n) stack = just (n ∷ stack)
step addNat (x ∷ y ∷ rest) = just ((y + x) ∷ rest)
step addNat _ = nothing
step monusNat (x ∷ y ∷ rest) = just (monus x y ∷ rest)
step monusNat _ = nothing
step multiplyNat (x ∷ y ∷ rest) = just ((y * x) ∷ rest)
step multiplyNat _ = nothing
step swapNat (x ∷ y ∷ rest) = just (y ∷ x ∷ rest)
step swapNat _ = nothing

exec : List Token → Stack → Maybe Stack
exec [] stack = just stack
exec (token ∷ tokens) stack with step token stack
... | nothing = nothing
... | just next = exec tokens next

-- Constructor equations are definitional and need no global rewrite axiom.
push-exec : (n : Nat) (stack : Stack) →
  exec (pushNat n ∷ []) stack ≡ just (n ∷ stack)
push-exec n stack = refl

add-exec : (x y : Nat) (rest : Stack) →
  exec (addNat ∷ []) (x ∷ y ∷ rest) ≡ just ((y + x) ∷ rest)
add-exec x y rest = refl

monus-exec : (x y : Nat) (rest : Stack) →
  exec (monusNat ∷ []) (x ∷ y ∷ rest) ≡ just (monus x y ∷ rest)
monus-exec x y rest = refl

multiply-exec : (x y : Nat) (rest : Stack) →
  exec (multiplyNat ∷ []) (x ∷ y ∷ rest) ≡ just ((y * x) ∷ rest)
multiply-exec x y rest = refl

swap-exec : (x y : Nat) (rest : Stack) →
  exec (swapNat ∷ []) (x ∷ y ∷ rest) ≡ just (y ∷ x ∷ rest)
swap-exec x y rest = refl
