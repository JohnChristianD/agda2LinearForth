---
id: source-fragment-contract
type: grilling
status: in_progress
blocked_by: []
---

## Decisions established

- No IO sites. Reachable IO, FFI, and effectful runtime operations are rejected before emission.
- Do not add --safe. Preserve existing Agda option and axiom policy.
- Classify all pinned Agda builtins, primitives, and Treeless constructors; do not force every builtin into executable Forth. Each is lowered, erased with Agda evidence, compile-time/elaboration-only, or explicitly rejected.
- Preserve strict Laurent MALLP resource discipline. No hidden weakening, contraction, or exponentials.
- Avoid whack-a-mole additions: settle source-language boundary and typed-core primitive contracts before broadening support. Unknown nodes fail closed.

## Proposed initial admitted fragment

Keep a deliberately small first theorem:
- Closed terms only; no free variables, function parameters, recursive definitions, user calls, constructors, general cases, IO, FFI, or effects.
- Only Agda Nat values and operations explicitly validated by type-aware lowering and bounded-target preconditions.
- First runtime candidates: decimal Nat literals, Nat addition, Nat monus, Nat multiplication. Add comparisons and branches only after guard semantics and stack joins are proved.
- Nat in Agda remains unbounded. The bounded Gforth target is sound only when every source literal and every intermediate node is proved <= the configured target MALLP-MAX-NAT. For the initial closed expression grammar, compute the exact Nat value recursively and carry a proof/certificate that all nodes fit. A target overflow exception is not an Agda source result; if the range proof is absent, reject at compile time or switch to arbitrary-precision limbs.
- Treeless PSub is signed integer subtraction, not a Nat monus synonym. Nat monus is a separate builtin and must be recognized by resolved identity and type, never primitive spelling.
- Unsupported reachable constructs must cause a compilation error; module definitions must not silently disappear.

## Remaining decision

Confirm exact inclusion rules for top-level definitions and compile-time-only declarations, plus how the compiler proves the no-free-variable/no-effect contract for each emitted definition. Derive a source usage judgment before extending beyond the closed fragment.
