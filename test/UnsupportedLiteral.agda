module UnsupportedLiteral where

open import Agda.Builtin.String using (String)

-- Regression fixture for an unsupported literal. With ToForth.hs unchanged,
-- the current backend emits its legacy diagnostic followed by BYE. This is
-- intentionally not claimed as a catchable checked-ABI boundary.
unsupported : String
unsupported = "not supported by the checked GForth ABI"
