---
id: frontend-trust-boundary
type: grilling
status: open
blocked_by:
  - agda-2-8-0-2-inventory
---

## Question

What source-to-core theorem is claimed, and what remains in the trusted computing base?

The backend currently receives Agda's Treeless representation after Agda type checking and compiler transformations. Decide the initial theorem boundary and what evidence is needed before making claims about original Agda source programs.

## Required result

For the first milestone, define the theorem over pinned Treeless inputs and explicitly list the trusted Agda frontend/typechecker/translation components. Specify a later extension point for a relation between checked Agda terms and Treeless. Do not imply that `--safe` proves the frontend or backend correct; `--safe` remains absent by explicit project policy.
