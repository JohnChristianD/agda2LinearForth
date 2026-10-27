module UnsupportedLiteral where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Float using (Float; primFloatPlus)

-- Both types exist in Agda. This compiler slice explicitly rejects them at
-- runtime until their target representations and operational semantics are modeled.
unsupported : String
unsupported = "not supported by the checked GForth ABI"

unsupportedFloat : Float
unsupportedFloat = 1.5

-- Exercise unsupported primitive lowering independently of Float literals.
unsupportedFloatPlus : Float → Float → Float
unsupportedFloatPlus x y = primFloatPlus x y
