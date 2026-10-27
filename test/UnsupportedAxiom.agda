module UnsupportedAxiom where

-- The backend must not silently turn an axiom into an empty Forth definition.
postulate unknownNat : Nat

axiomUse : Nat
axiomUse = unknownNat
