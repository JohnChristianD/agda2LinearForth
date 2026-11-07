module ForthRenderer where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

data ForthTextToken : Set where
  textPushLiteral : Nat → ForthTextToken
  textAddWord textMonusWord textMultiplyWord textSwapWord : ForthTextToken
  textRollWord : Nat → ForthTextToken
  textTrueWord textFalseWord : ForthTextToken
  textIf : List ForthTextToken → List ForthTextToken → ForthTextToken

mutual
  renderForthTokenText : ForthTextToken → String
  renderForthTokenText (textPushLiteral value) =
    primStringAppend "s\" "
      (primStringAppend (primShowNat value) "\" MALLP-PARSE-NAT ")
  renderForthTokenText textAddWord = "MALLP-NAT-ADD "
  renderForthTokenText textMonusWord = "MALLP-NAT-MONUS "
  renderForthTokenText textMultiplyWord = "MALLP-NAT-MUL "
  renderForthTokenText textSwapWord = "SWAP "
  renderForthTokenText (textRollWord depth) =
    primStringAppend (primShowNat depth) " ROLL "
  renderForthTokenText textTrueWord = "TRUE "
  renderForthTokenText textFalseWord = "FALSE "
  renderForthTokenText (textIf whenTrue whenFalse) =
    primStringAppend "IF "
      (primStringAppend (renderForthTokensText whenTrue)
        (primStringAppend "ELSE "
          (primStringAppend (renderForthTokensText whenFalse) "THEN ")))

  renderForthTokensText : List ForthTextToken → String
  renderForthTokensText [] = ""
  renderForthTokensText (token ∷ tokens) =
    primStringAppend (renderForthTokenText token)
      (renderForthTokensText tokens)

renderForthWordText : String → List ForthTextToken → String
renderForthWordText name tokens =
  primStringAppend ": "
    (primStringAppend name
      (primStringAppend " "
        (primStringAppend (renderForthTokensText tokens) ";")))
