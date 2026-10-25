module UnsupportedLiteral where

open import Agda.Builtin.String using (String)

-- This backend deliberately rejects unsupported runtime literals. The emitted
-- Forth must raise a catchable ABI error, never terminate the interpreter with BYE.
unsupported : String
unsupported = "not supported by the checked GForth ABI"
