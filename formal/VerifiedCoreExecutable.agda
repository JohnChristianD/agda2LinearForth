{-# OPTIONS --safe --without-K #-}

-- Finite-observation interface executable by the existing Forth backend.
-- A co-natural itself may be genuinely coinductive; only its finite observation
-- boundary is represented here, because concrete Forth cannot materialize an
-- arbitrary infinite object in a finite number of cells.
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
