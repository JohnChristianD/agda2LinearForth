{-# OPTIONS --safe #-}

-- Heap-specific separation/frame rules. They require disjoint descriptor
-- identities before and after the local command; a disjoint initial state alone
-- cannot prove that a concrete Forth operation preserves separation.
module LinearModalConcurrency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import LinearModalSafety using
  ( Heap; _++_; keys; Disjoint; Sep; splitHeap
  )

record FramedSeparation
  (P Q R : Heap → Set)
  (before after frame : Heap) : Set where
  constructor framedSeparation
  field
    initialSplit : Sep P R (before ++ frame)
    finalSplit : Sep Q R (after ++ frame)
open FramedSeparation public

frameRuleForDisjointHeaps :
  {P Q R : Heap → Set} {before after frame : Heap} →
  P before →
  Q after →
  R frame →
  Disjoint (keys before) (keys frame) →
  Disjoint (keys after) (keys frame) →
  FramedSeparation P Q R before after frame
frameRuleForDisjointHeaps {before = before} {after = after} {frame = frame}
  pre post frameInvariant beforeDisjoint afterDisjoint =
  framedSeparation
    (splitHeap before frame refl pre frameInvariant beforeDisjoint)
    (splitHeap after frame refl post frameInvariant afterDisjoint)

record FramedExceptional
  (E R : Heap → Set)
  (after frame : Heap) : Set where
  constructor framedExceptional
  field
    errorSplit : Sep E R (after ++ frame)
open FramedExceptional public

exceptionalFrameRuleForDisjointHeaps :
  {E R : Heap → Set} {after frame : Heap} →
  E after →
  R frame →
  Disjoint (keys after) (keys frame) →
  FramedExceptional E R after frame
exceptionalFrameRuleForDisjointHeaps {after = after} {frame = frame}
  errorInvariant frameInvariant disjoint =
  framedExceptional
    (splitHeap after frame refl errorInvariant frameInvariant disjoint)

-- The concurrent precondition and postcondition are deliberately separate
-- evidence: interference freedom is not inherited merely from the pre-state.
record ConcurrentPrecondition (left right : Heap) : Set where
  constructor concurrentPrecondition
  field
    leftRightDisjoint : Disjoint (keys left) (keys right)
open ConcurrentPrecondition public

record ConcurrentPostcondition (left right : Heap) : Set where
  constructor concurrentPostcondition
  field
    postLeftRightDisjoint : Disjoint (keys left) (keys right)
open ConcurrentPostcondition public

makeConcurrentPrecondition :
  {left right : Heap} →
  Disjoint (keys left) (keys right) →
  ConcurrentPrecondition left right
makeConcurrentPrecondition = concurrentPrecondition

makeConcurrentPostcondition :
  {left right : Heap} →
  Disjoint (keys left) (keys right) →
  ConcurrentPostcondition left right
makeConcurrentPostcondition = concurrentPostcondition
