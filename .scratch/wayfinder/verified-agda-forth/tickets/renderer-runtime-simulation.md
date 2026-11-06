---
id: renderer-runtime-simulation
type: task
status: open
blocked_by:
  - pass-relations
  - gforth-runtime-semantics
---

## Question

How is the typed Forth AST rendered into exact tokens and shown to preserve the target interpreter's behavior?

## Required result

One canonical renderer from the typed Forth AST; a token/parse round-trip or direct rendering relation; a formal interpreter for the used Forth subset; a simulation theorem from AST execution to rendered-token execution; and Gforth integration tests for arithmetic, parser boundaries, overflow, malformed literals, and stack/return-stack balance. No IO or FFI words may enter the emitted program.
