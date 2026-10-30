{ OPTIONS --without-K #-}


module VerifiedCoreSmoke where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool)
open import VerifiedCoreExecutable using (finiteObservation; infiniteObservation; pow2)

-- The runtime exports only bounded observations, not an infinite heap object.
coreCoNatAtZero : Bool
coreCoNatAtZero = finiteObservation 1 0

coreCoNatStopsAtOne : Bool
coreCoNatStopsAtOne = finiteObservation 1 1

coreInfinityAtDepthEight : Bool
coreInfinityAtDepthEight = infiniteObservation 8

corePow2Zero : Nat
corePow2Zero = pow2 0

corePow2One : Nat
corePow2One = pow2 1
