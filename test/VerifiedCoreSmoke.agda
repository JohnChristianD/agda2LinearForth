{-# OPTIONS --without-K #-}

module VerifiedCoreSmoke where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import VerifiedCoreExecutable using (finiteObservation; infiniteObservation; pow2)

-- Convert observed Bool results to Nat at the source boundary. This keeps
-- the smoke test on the backend's already-supported raw Nat result path.
boolToNat : Bool → Nat
boolToNat false = zero
boolToNat true = suc zero

-- Executable examples taken directly from the formal conatural/dyad core.
-- Their generated Forth results are checked in the Gforth integration test.
coreCoNatAtZero : Nat
coreCoNatAtZero = boolToNat (finiteObservation 1 0)

coreCoNatStopsAtOne : Nat
coreCoNatStopsAtOne = boolToNat (finiteObservation 1 1)

coreInfinityAtDepthEight : Nat
coreInfinityAtDepthEight = boolToNat (infiniteObservation 8)

corePow2Zero : Nat
corePow2Zero = pow2 zero

corePow2One : Nat
corePow2One = pow2 (suc zero)

-- Erased parameters must be absent from generated runtime code.
erasedArgument : {@0 ignored : Nat} → Nat
erasedArgument = suc zero

coreErasedArgument : Nat
coreErasedArgument = erasedArgument {ignored = suc zero}
