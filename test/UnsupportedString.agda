module UnsupportedString where

open import Agda.Builtin.String

unsupported : String
unsupported = "string literals are outside the checked Forth subset"
