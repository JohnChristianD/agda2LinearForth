{-# OPTIONS --safe #-}

-- Separation/frame rules for concurrent use of independent ABI regions.
-- The rule is conditional on local code preserving disjointness before and
-- after its step. This is exactly the side condition a concrete Forth-word
-- refinement proof must discharge; disjoint starting heaps alone are not enough.
module LinearModalConcurrency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import LinearModalABI using
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

-- Frame rule: a local proof over the before/after heaps lifts to the combined
-- heap if the unchanged frame satisfies R and is disjoint at both boundaries.
-- The frame itself is definitionally the same list on both sides.
frameRule :
  {P Q R : Heap → Set} {before after frame : Heap} →
  P before →
  Q after →
  R frame →
  Disjoint (keys before) (keys frame) →
  Disjoint (keys after) (keys frame) →
  FramedSeparation P Q R before after frame
frameRule {before = before} {after = after} {frame = frame}
  pre post frameInvariant beforeDisjoint afterDisjoint =
  framedSeparation
    (splitHeap before frame refl pre frameInvariant beforeDisjoint)
    (splitHeap after frame refl post frameInvariant afterDisjoint)

-- The same proof pattern applies to the exceptional side of a normal/exceptional
-- Hoare contract. Runtime code must preserve frame-disjointness on that path too.
record FramedExceptional
  (E R : Heap → Set)
  (before after frame : Heap) : Set where
  constructor framedExceptional
  field
    errorSplit : Sep E R (after ++ frame)
open FramedExceptional public

exceptionalFrameRule :
  {E R : Heap → Set} {before after frame : Heap} →
  E after →
  R frame →
  Disjoint (keys after) (keys frame) →
  FramedExceptional E R before after frame
exceptionalFrameRule {after = after} {frame = frame}
  errorInvariant frameInvariant disjoint =
  framedExceptional
    (splitHeap after frame refl errorInvariant frameInvariant disjoint)

-- A caller cannot infer concurrency safety from a pre-state alone. These
-- witnesses make the before/after separation obligations explicit.
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

-- Establish the precondition for a pair of independently owned regions.
makeConcurrentPrecondition :
  {left right : Heap} →
  Disjoint (keys left) (keys right) →
  ConcurrentPrecondition left right
makeConcurrentPrecondition = concurrentPrecondition

-- Re-establishing the same condition after an operation is a separate proof
-- input, not a corollary of makeConcurrentPrecondition.
makeConcurrentPostcondition :
  {left right : Heap} →
  Disjoint (keys left) (keys right) →
  ConcurrentPostcondition left right
makeConcurrentPostcondition = concurrentPostcondition
