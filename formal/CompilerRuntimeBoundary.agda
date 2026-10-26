{-# OPTIONS --safe #-}

-- Constructive boundary correspondence for the pinned upstream Forth backend.
-- This models the emitted value/operator footprint for natural literals and
-- integer addition; it is not a mechanically extracted proof about Haskell
-- or a simulation of the entire Forth runtime.
module CompilerRuntimeBoundary where

open import Agda.Builtin.Nat using (Nat)
open import LinearModalABI
open import LinearModalStackEffects

data NatExpr : Set where
  natLiteral : Nat → NatExpr
  natAddition : NatExpr → NatExpr → NatExpr

-- These constructors distinguish the compiler's legacy/raw representation
-- from the representation required by the checked ABI. The checked constructors
-- are included so the predicate below can state, and prove, their absence.
data EmittedFragment : Set where
  rawNaturalCell : Nat → EmittedFragment
  rawTrueCell rawFalseCell : EmittedFragment
  legacyAddCode : EmittedFragment → EmittedFragment → EmittedFragment
  checkedScalarCode : SourceMode → Nat → EmittedFragment
  checkedBooleanCode : SourceMode → EmittedFragment

-- Mirrors ToForth.hs's LitNat and PAdd cases at the value/operator-footprint
-- level: a numeric literal is a raw cell; integer addition uses legacy "add".
compileNatFragment : NatExpr → EmittedFragment
compileNatFragment (natLiteral n) = rawNaturalCell n
compileNatFragment (natAddition left right) =
  legacyAddCode (compileNatFragment left) (compileNatFragment right)

NoCheckedRepresentation : EmittedFragment → Set
NoCheckedRepresentation (rawNaturalCell n) = ⊤
NoCheckedRepresentation rawTrueCell = ⊤
NoCheckedRepresentation rawFalseCell = ⊤
NoCheckedRepresentation (legacyAddCode left right) =
  NoCheckedRepresentation left × NoCheckedRepresentation right
NoCheckedRepresentation (checkedScalarCode mode n) = ⊥
NoCheckedRepresentation (checkedBooleanCode mode) = ⊥

compilerNatFragmentHasNoCheckedRepresentation :
  (expr : NatExpr) → NoCheckedRepresentation (compileNatFragment expr)
compilerNatFragmentHasNoCheckedRepresentation (natLiteral n) = tt
compilerNatFragmentHasNoCheckedRepresentation (natAddition left right) =
  compilerNatFragmentHasNoCheckedRepresentation left ,
  compilerNatFragmentHasNoCheckedRepresentation right

-- Literal booleans in the pinned source are output as raw -1/0 cells, not as
-- ABI boolean handles; the separate constructors record their source meaning,
-- not runtime type tags.
data BoolLiteral : Set where
  trueLiteral falseLiteral : BoolLiteral

compileBoolFragment : BoolLiteral → EmittedFragment
compileBoolFragment trueLiteral = rawTrueCell
compileBoolFragment falseLiteral = rawFalseCell

compilerBoolLiteralHasNoCheckedRepresentation :
  (literal : BoolLiteral) → NoCheckedRepresentation (compileBoolFragment literal)
compilerBoolLiteralHasNoCheckedRepresentation trueLiteral = tt
compilerBoolLiteralHasNoCheckedRepresentation falseLiteral = tt

data CheckedABIValue : StackItem → Set where
  checkedLinearNatural : CheckedABIValue (valueItem naturalTy)
  checkedModalNatural : CheckedABIValue (valueItem (!Ty naturalTy))
  checkedLinearBoolean : CheckedABIValue (valueItem booleanTy)
  checkedModalBoolean : CheckedABIValue (valueItem (!Ty booleanTy))

rawNaturalCannotBeCheckedABIValue :
  CheckedABIValue rawNatItem → ⊥
rawNaturalCannotBeCheckedABIValue ()

rawBooleanCannotBeCheckedABIValue :
  CheckedABIValue rawBoolItem → ⊥
rawBooleanCannotBeCheckedABIValue ()

-- Every natural-literal/addition expression in this fragment leaves a raw
-- natural cell as its result. It cannot carry the mode-indexed descriptor
-- witness required by a checked ABI operand.
compiledNatResultShape : NatExpr → StackItem
compiledNatResultShape _ = rawNatItem

compiledNatResultCannotBeChecked :
  (expr : NatExpr) →
  CheckedABIValue (compiledNatResultShape expr) → ⊥
compiledNatResultCannotBeChecked expr = rawNaturalCannotBeCheckedABIValue

compiledBooleanResultShape : BoolLiteral → StackItem
compiledBooleanResultShape _ = rawBoolItem

compiledBoolResultCannotBeChecked :
  (literal : BoolLiteral) →
  CheckedABIValue (compiledBooleanResultShape literal) → ⊥
compiledBoolResultCannotBeChecked literal = rawBooleanCannotBeCheckedABIValue

-- Import and reuse the closed stack-effect lemmas rather than assuming that
-- raw output is accepted by checked operations.
rawCompilerOperandsCannotUseCheckedAddition :
  {tail output : StackShape} →
  StackEffect pNatAdd (rawNatItem :: rawNatItem :: tail) output → ⊥
rawCompilerOperandsCannotUseCheckedAddition =
  rawLiteralCannotUseCheckedAddition

rawCompilerOperandsCannotUseCheckedEquality :
  {tail output : StackShape} →
  StackEffect pNatEq (rawNatItem :: rawNatItem :: tail) output → ⊥
rawCompilerOperandsCannotUseCheckedEquality =
  rawLiteralCannotUseCheckedEquality

-- For a checked scalar to be introduced from a raw literal, the compiler must
-- emit a pMakeScalar effect with a source-mode token. The theorem's type makes
-- the missing evidence explicit; the upstream lowering above does not supply it.
checkedScalarRequiresModeWitness :
  {m : SourceMode} {tail : StackShape} →
  StackEffect pMakeScalar
    (modeTokenItem m :: rawNatItem :: tail)
    (valueItem (naturalTypeFor m) :: tail)
checkedScalarRequiresModeWitness = rawLiteralNeedsModeWitness
