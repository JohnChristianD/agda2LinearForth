# Decision ticket: Choose representations and the compiler-correctness boundary

Type: grilling

## Question

How should conaturals, dyads, linear resources, and Forth execution be represented so the project can prove an actual end-to-end refinement theorem rather than accumulate local runtime guards?

## Required evidence

- Distinguish an infinite/coinductive conatural from a finite observation or approximation that can be executed on a conventional Forth runtime.
- Distinguish exact dyadic rationals from their finite encoding and prove normalization/equality/order laws for the chosen representation.
- State whether compactness/searchability is part of the executable target or only a metatheoretic result.
- Define source states, target stack states, observable results/errors, and the compiler relation.
- Choose a single root theorem connecting well-typed source execution to generated Forth execution, with explicit assumptions and finite-cell constraints.
- Identify the existing emitter/runtime paths that must be covered by that theorem.

## Resolution format

Types and interfaces first, then the proposed simulation/refinement statement and its limits. Include concrete counterexamples for invalid choices (e.g. silently treating infinite objects as finite cells).
