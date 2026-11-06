---
id: gforth-runtime-semantics
type: research
status: open
blocked_by: []
---

## Question

What exact operational semantics must the compiler model for the Forth words it emits and includes from `data/FLib.fth`?

Inspect the checked Gforth version and its documented cell model, locals, arithmetic, exception/`THROW` behavior, string parsing, dictionary definitions, and data/return-stack effects. Trace every word reachable from the current generated fixture and runtime.

## Required result

Specify a small formal target language and its state: data stack, return stack only when used, memory only when needed, dictionary/runtime words, and explicit error outcomes. State cell width and `MALLP-MAX-NAT` exactly. Prove stack effects for each primitive and model `MALLP-PARSE-NAT`, overflow, negative values, and malformed literals. Separate model-level semantics from tests against real Gforth.

Keep the first target model minimal. Do not model heap, closures, strings, or FFI until an accepted source feature requires them.
