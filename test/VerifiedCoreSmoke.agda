module VerifiedCoreSmoke where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool)
open import VerifiedPLLCore using (observe; finiteCoNat; pow2)

-- Executable examples taken directly from the formal conatural/dyad core.
-- Their generated Forth results are checked in the Gforth integration test.
coreCoNatAtZero : Bool
coreCoNatAtZero = observe (finiteCoNat (suc zero)) zero

coreCoNatAtOne : Bool
coreCoNatAtOne = observe (finiteCoNat (suc zero)) (suc zero)

corePow2Zero : Nat
corePow2Zero = pow2 zero

corePow2One : Nat
corePow2One = pow2 (suc zero)
