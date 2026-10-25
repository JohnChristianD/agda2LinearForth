{-# OPTIONS --safe #-}

-- Small witnesses exercise the stack signatures so they cannot drift into
-- uninhabited or internally inconsistent declarations unnoticed.
module LinearModalExamples where

open import Agda.Builtin.Nat using (Nat)
open import LinearModalABI
open import LinearModalStackEffects

linearNatAddition :
  {tail : StackShape} →
  StackEffect pNatAdd
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatAddition = natAddEffect naturalIsNatural naturalIsNatural

modalNatAddition :
  {tail : StackShape} →
  StackEffect pNatAdd
    (valueItem (!Ty naturalTy) :: valueItem (!Ty naturalTy) :: tail)
    (valueItem (!Ty naturalTy) :: tail)
modalNatAddition = natAddEffect boxedNaturalIsNatural boxedNaturalIsNatural

mixedNatAddition :
  {tail : StackShape} →
  StackEffect pNatAdd
    (valueItem (!Ty naturalTy) :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
mixedNatAddition = natAddEffect naturalIsNatural boxedNaturalIsNatural

checkedModalAddClosure :
  StackEffect pMakeThunk
    (modeTokenItem modal :: codeItem codeNatAdd :: [])
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
checkedModalAddClosure = makeModalThunkEffect modalNatAdd

checkedLinearAddClosure :
  StackEffect pMakeThunk
    (modeTokenItem linear :: codeItem codeNatAdd :: [])
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
checkedLinearAddClosure = makeLinearThunkEffect linearNatAdd

modalPromotionEffect :
  StackEffect pPromoteModal
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
modalPromotionEffect = promoteModalEffect modalNatAdd modalCapturesNil
