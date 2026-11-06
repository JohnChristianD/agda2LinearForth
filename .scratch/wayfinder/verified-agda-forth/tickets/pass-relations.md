---
id: pass-relations
type: task
status: open
blocked_by:
  - agda-2-8-0-2-inventory
  - gforth-runtime-semantics
  - source-fragment-contract
  - frontend-trust-boundary
  - hamano-scott-bridge
---

## Question

Implement the smallest compositional compiler core and Agda mirror whose pass relations cover the settled accepted fragment.

Use PureCake's relation-first method: define syntax relations and prove each relation preserves the selected source/target semantics; then prove each concrete Haskell transformation inhabits the relation. Avoid one bespoke top-level correctness theorem per builtin.

## Required result

A compiler-owned typed source core; total Treeless decoder/classifier; explicit resource-usage judgment; indexed target stack AST; and a composed theorem from accepted Treeless execution to formal Forth execution. Add ThunkLang/EnvLang/StateLang-like stages only if the settled source fragment needs laziness, closures, or sharing. Every accepted IO/effect site remains absent by construction and by a checked empty-effect property.
