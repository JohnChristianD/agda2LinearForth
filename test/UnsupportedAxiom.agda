module UnsupportedAxiom where

open import Agda.Builtin.Nat using (Nat)

-- The backend must not silently turn an axiom into an empty Forth definition.
postulate unknownNat : Nat

axiomUse : Nat
axiomUse = unknownNat
