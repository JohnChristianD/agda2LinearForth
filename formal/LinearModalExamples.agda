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

linearNatEquality :
  {tail : StackShape} →
  StackEffect pNatEq
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
linearNatEquality = natEqEffect naturalIsNatural naturalIsNatural

modalNatEquality :
  {tail : StackShape} →
  StackEffect pNatEq
    (valueItem (!Ty naturalTy) :: valueItem (!Ty naturalTy) :: tail)
    (valueItem (!Ty booleanTy) :: tail)
modalNatEquality = natEqEffect boxedNaturalIsNatural boxedNaturalIsNatural

mixedNatEquality :
  {tail : StackShape} →
  StackEffect pNatEq
    (valueItem (!Ty naturalTy) :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
mixedNatEquality = natEqEffect naturalIsNatural boxedNaturalIsNatural

checkedModalBooleanConstruction :
  StackEffect pMakeBool
    (modeTokenItem modal :: rawBoolItem :: [])
    (valueItem (!Ty booleanTy) :: [])
checkedModalBooleanConstruction = makeBooleanEffect

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

\ The catalogue covers every scalar primitive, not just addition and equality.
linearNatSubtraction :
  {tail : StackShape} →
  StackEffect pNatSub
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatSubtraction = natSubEffect naturalIsNatural naturalIsNatural

linearNatMultiplication :
  {tail : StackShape} →
  StackEffect pNatMul
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatMultiplication = natMulEffect naturalIsNatural naturalIsNatural

linearNatQuotient :
  {tail : StackShape} →
  StackEffect pNatQuot
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatQuotient = natQuotEffect naturalIsNatural naturalIsNatural

linearNatRemainder :
  {tail : StackShape} →
  StackEffect pNatRem
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatRemainder = natRemEffect naturalIsNatural naturalIsNatural

linearNatGreaterEqual :
  {tail : StackShape} →
  StackEffect pNatGeq
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
linearNatGreaterEqual = natGeqEffect naturalIsNatural naturalIsNatural

linearNatLessThan :
  {tail : StackShape} →
  StackEffect pNatLt
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem booleanTy :: tail)
linearNatLessThan = natLtEffect naturalIsNatural naturalIsNatural

linearNatMonus :
  {tail : StackShape} →
  StackEffect pNatMonus
    (valueItem naturalTy :: valueItem naturalTy :: tail)
    (valueItem naturalTy :: tail)
linearNatMonus = natMonusEffect naturalIsNatural naturalIsNatural

\ Conditional, algebraic data, result movement, force, and observation effects.
modalNaturalConditional :
  StackEffect pIf
    (thunkItem modal codeNatAdd [] naturalTy ::
     thunkItem modal codeNatSub [] naturalTy ::
     valueItem booleanTy :: [])
    (valueItem naturalTy :: [])
modalNaturalConditional =
  ifModalBranchesEffect booleanIsBoolean modalNatAdd modalNatSub
    modalCapturesNil modalCapturesNil

natConstructorSignature : ConstructorSignature
natConstructorSignature = constructorSignature 0 (naturalTy :: []) naturalTy

natConstructorEffect :
  StackEffect pConstruct
    (valueItem naturalTy :: constructorTokenItem 0 :: [])
    (valueItem naturalTy :: [])
natConstructorEffect = constructEffect natConstructorSignature

natMatcherSignature : MatcherSignature
natMatcherSignature = matcherSignature naturalTy naturalTy

natMatcherEffect :
  StackEffect pMatch
    (matcherTokenItem natMatcherSignature :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natMatcherEffect = matchEffect natMatcherSignature

linearResultPacking :
  StackEffect pMakeResult
    (valueItem naturalTy :: [])
    (resultItem naturalTy :: [])
linearResultPacking = makeResultEffect

linearResultUnpacking :
  StackEffect pUnwrapResult
    (resultItem naturalTy :: [])
    (valueItem naturalTy :: [])
linearResultUnpacking = unwrapResultEffect

linearNaturalObservation :
  StackEffect pPrint (valueItem naturalTy :: []) []
linearNaturalObservation = printLinearEffect linearNatural

modalNaturalObservation :
  StackEffect pPrint (valueItem (!Ty naturalTy) :: [])
    (valueItem (!Ty naturalTy) :: [])
modalNaturalObservation = printModalEffect
