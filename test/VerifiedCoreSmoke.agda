{-# OPTIONS --safe --without-K #-}

module VerifiedCoreSmoke where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool)
open import VerifiedCoreExecutable using (finiteObservation; infiniteObservation; pow2)

-- The runtime exports only bounded observations, not an infinite heap object.
coreCoNatAtZero : Bool
coreCoNatAtZero = finiteObservation (suc zero) zero

coreCoNatStopsAtOne : Bool
coreCoNatStopsAtOne = finiteObservation (suc zero) (suc zero)

coreInfinityAtDepthEight : Bool
coreInfinityAtDepthEight = infiniteObservation (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

corePow2Zero : Nat
corePow2Zero = pow2 zero

corePow2One : Nat
corePow2One = pow2 (suc zero)
