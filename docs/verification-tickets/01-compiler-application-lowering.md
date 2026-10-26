# Frontier: prove compiler application lowering against Forth execution

## Question

What exact relation between a supported source/Treeless application and emitted Forth is sufficient to prove that curried application preserves the source result, closure environment and resource ownership?

## Evidence

The earlier CI integration emitted an application body similar to :noname { a c } a c pass ; and executed 5 20 scalarAdd pass pass, observing 5 instead of the source result 25. The generic pass word implements application by capturing an argument into a thunk; it is not a numeric operator. The failure must be explained at the emitter/lowering boundary, or the supported language fragment must be constrained.

## Acceptance criteria

- State a formal source/Treeless application rule and the exact Forth stack/closure-state transition.
- Prove translation preserves normal results, exceptional outcomes and linear/modal capture ownership.
- Add compiler-generated integration regressions for this witness and a second non-commutative witness.
- Only `src/Agda/Compiler/ToForth.hs` may diverge from upstream Haskell; every other `.hs` file remains pinned. Do not claim end-to-end completion while the observed witness fails.
