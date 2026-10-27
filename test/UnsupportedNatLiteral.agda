module UnsupportedNatLiteral where

open import Agda.Builtin.Nat using (Nat)

-- This must survive code generation as decimal text and be rejected by
-- ABI-PARSE-NAT at runtime, not become a double-cell Forth literal.
tooLarge : Nat
tooLarge = 9999999999999999999999999999999999999999
