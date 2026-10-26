{-# OPTIONS --safe #-}

-- Concrete type-checking witnesses for the complete Primitive enumeration.
-- These are static ABI signatures, not claims that current generated Forth
-- emits every witness or that every Forth definition has been refined.
module LinearModalPrimitiveCoverage where

open import Agda.Builtin.Nat using (zero)
open import LinearModalABI
open import LinearModalStackEffects

natAddWitness :
  StackEffect pNatAdd
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natAddWitness = natAddEffect naturalIsNatural naturalIsNatural

natSubWitness :
  StackEffect pNatSub
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natSubWitness = natSubEffect naturalIsNatural naturalIsNatural

natMulWitness :
  StackEffect pNatMul
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natMulWitness = natMulEffect naturalIsNatural naturalIsNatural

natQuotWitness :
  StackEffect pNatQuot
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natQuotWitness = natQuotEffect naturalIsNatural naturalIsNatural

natRemWitness :
  StackEffect pNatRem
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natRemWitness = natRemEffect naturalIsNatural naturalIsNatural

natEqWitness :
  StackEffect pNatEq
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem booleanTy :: [])
natEqWitness = natEqEffect naturalIsNatural naturalIsNatural

natGeqWitness :
  StackEffect pNatGeq
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem booleanTy :: [])
natGeqWitness = natGeqEffect naturalIsNatural naturalIsNatural

natLtWitness :
  StackEffect pNatLt
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem booleanTy :: [])
natLtWitness = natLtEffect naturalIsNatural naturalIsNatural

natMonusWitness :
  StackEffect pNatMonus
    (valueItem naturalTy :: valueItem naturalTy :: [])
    (valueItem naturalTy :: [])
natMonusWitness = natMonusEffect naturalIsNatural naturalIsNatural

makeLinearScalarWitness :
  StackEffect pMakeScalar
    (modeTokenItem linear :: rawNatItem :: [])
    (valueItem naturalTy :: [])
makeLinearScalarWitness = makeScalarEffect

makeModalScalarWitness :
  StackEffect pMakeScalar
    (modeTokenItem modal :: rawNatItem :: [])
    (valueItem (!Ty naturalTy) :: [])
makeModalScalarWitness = makeScalarEffect

makeLinearBooleanWitness :
  StackEffect pMakeBool
    (modeTokenItem linear :: rawBoolItem :: [])
    (valueItem booleanTy :: [])
makeLinearBooleanWitness = makeBooleanEffect

makeModalBooleanWitness :
  StackEffect pMakeBool
    (modeTokenItem modal :: rawBoolItem :: [])
    (valueItem (!Ty booleanTy) :: [])
makeModalBooleanWitness = makeBooleanEffect

makeLinearThunkWitness :
  StackEffect pMakeThunk
    (modeTokenItem linear :: codeItem codeNatAdd :: [])
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
makeLinearThunkWitness = makeLinearThunkEffect linearNatAdd

makeModalThunkWitness :
  StackEffect pMakeThunk
    (modeTokenItem modal :: codeItem codeNatAdd :: [])
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
makeModalThunkWitness = makeModalThunkEffect modalNatAdd

applyLinearArgumentWitness :
  StackEffect pApply
    (thunkItem linear codeNatAdd [] (naturalTy ⇒ (naturalTy ⇒ naturalTy)) ::
     valueItem naturalTy :: [])
    (thunkItem linear codeNatAdd ([] ++ (naturalTy :: []))
      (naturalTy ⇒ naturalTy) :: [])
applyLinearArgumentWitness = applyLinearEffect (linearCodeSafe linearNatAdd)

forceLinearThunkWitness :
  StackEffect pForce
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
    (valueItem (codeSignature codeNatAdd) :: [])
forceLinearThunkWitness = forceLinearEffect linearNatAdd

forceModalThunkWitness :
  StackEffect pForce
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
    (valueItem (codeSignature codeNatAdd) :: [])
forceModalThunkWitness = forceModalEffect modalNatAdd modalCapturesNil

makeResultWitness :
  StackEffect pMakeResult (valueItem naturalTy :: []) (resultItem naturalTy :: [])
makeResultWitness = makeResultEffect

unwrapResultWitness :
  StackEffect pUnwrapResult (resultItem naturalTy :: []) (valueItem naturalTy :: [])
unwrapResultWitness = unwrapResultEffect

promoteModalWitness :
  StackEffect pPromoteModal
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
promoteModalWitness = promoteModalEffect modalNatAdd modalCapturesNil

assertLinearWitness :
  StackEffect pAssertLinear
    (thunkItem modal codeNatAdd [] (codeSignature codeNatAdd) :: [])
    (thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
assertLinearWitness = assertLinearEffect linearNatAdd

conditionalWitness :
  StackEffect pIf
    (thunkItem modal codeNatAdd [] naturalTy ::
     thunkItem modal codeNatAdd [] naturalTy ::
     valueItem booleanTy :: [])
    (valueItem naturalTy :: [])
conditionalWitness =
  ifModalBranchesEffect booleanIsBoolean modalNatAdd modalNatAdd
    modalCapturesNil modalCapturesNil

nullaryConstructor : ConstructorSignature
nullaryConstructor = constructorSignature zero [] unitTy

constructorWitness :
  StackEffect pConstruct
    (constructorTokenItem zero :: [])
    (valueItem unitTy :: [])
constructorWitness = constructEffect nullaryConstructor

unitMatcher : MatcherSignature
unitMatcher = matcherSignature unitTy naturalTy

matcherWitness :
  StackEffect pMatch
    (matcherTokenItem unitMatcher :: valueItem unitTy :: [])
    (valueItem naturalTy :: [])
matcherWitness = matchEffect unitMatcher

linearPrintWitness :
  StackEffect pPrint (valueItem unitTy :: []) []
linearPrintWitness = printLinearEffect linearUnit

modalPrintWitness :
  StackEffect pPrint (valueItem (!Ty naturalTy) :: [])
    (valueItem (!Ty naturalTy) :: [])
modalPrintWitness = printModalEffect

throwWitness : ErrorEffect pThrow (errorTokenItem unknownHandle :: []) unknownHandle
throwWitness = throwEffect

catchWitness :
  StackEffect pCatch
    (handlerTokenItem ::
     thunkItem linear codeNatAdd [] (codeSignature codeNatAdd) :: [])
    (valueItem (codeSignature codeNatAdd) :: [])
catchWitness = catchEffect (linearCodeSafe linearNatAdd)

-- The stronger negative proof applies to every primitive, not just addition
-- and equality: an untagged literal pair cannot directly inhabit any checked
-- operation's required input shape.
rawPairRejectedForEveryPrimitive :
  {p : Primitive} {tail output : StackShape} →
  StackEffect p (rawNatItem :: rawNatItem :: tail) output → ⊥
rawPairRejectedForEveryPrimitive = rawNatsCannotEnterCheckedABI
