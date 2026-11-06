---
id: agda-2-8-0-2-inventory
type: research
status: open
blocked_by: []
---

## Question

What is the exhaustive compiler-facing language contract for the exact Agda v2.8.0.2 source pin?

Inventory, from the pinned source tree, every constructor of:
- `BuiltinId` and `PrimitiveId`;
- Treeless `TPrim`, `TTerm`, `TAlt`, `CaseType`, `CaseInfo`, and `TError`;
- argument-use and evaluation-strategy metadata consumed by `toTreeless`.

Trace builtin translation and the `compilerPipeline` stages that produce Treeless. Distinguish surface/internal primitive identities from backend `TPrim` constructors.

## Required result

A machine-readable or source-checked manifest with one row per constructor and exactly one disposition: runtime lowering, proof-justified erasure, compile-time/elaboration-only, or compile-time rejection. Every runtime row names a core operation, target family, semantic rule, and proof relation. No wildcard “other” classification; unknown constructors fail closed.

Add a version-drift check that fails when Agda 2.8.0.2's inventory changes. Record all trusted boundaries and avoid claiming the Agda frontend is verified by this inventory.
