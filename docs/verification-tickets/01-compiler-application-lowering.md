# Frontier: prove compiler application lowering against Forth execution

## Question

What exact relation between a supported source/Treeless application and emitted Forth is sufficient to prove that curried application preserves the source result, closure environment and resource ownership?

## Evidence

The original integration emitted a body similar to `:noname { a c } a c pass ;` and returned 5 for `scalarAdd 20 5`. That failure is fixed for the tested addition path: `ToForth.hs` now lowers saturated primitives and builtin Nat addition/subtraction to ABI adapters, and CI executes the generated scalar fixture. The generic `pass` word remains generic application, not a numeric operator. This follow-up tests the non-commutative Nat-subtraction boundary and found that raw/raw monus dispatch used signed `-`; `ABI-MONUS-OR-LEGACY` now routes raw values through `ABI-SUB-RAW` to preserve natural-number truncation.

## Acceptance criteria

- State a formal source/Treeless application rule and the exact Forth stack/closure-state transition.
- Prove translation preserves normal results, exceptional outcomes and linear/modal capture ownership.
- Keep generated addition, subtraction/monus in both operand orders, multiplication, equality, comparison and Boolean-branch regressions running on CI. In particular, `20 - 5 = 15` and `5 - 20 = 0` test operand order and saturation.
- Keep the Haskell exception limited to `src/Agda/Compiler/ToForth.hs`; every other `.hs` file remains pinned. Do not claim whole-backend end-to-end completion from scalar-fragment tests.
