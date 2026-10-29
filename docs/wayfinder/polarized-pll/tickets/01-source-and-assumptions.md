# Decision ticket: Source and assumption audit

Type: research

## Question

What exact definitions and assumptions from TypeTopology's compact-type material, CoNaturals, and Dyadics are relevant to this project, and which can be re-expressed in the repository's safe, no-standard-library Agda style without importing unrelated machinery?

## Required evidence

- Inspect the exact upstream source modules, not only their descriptions.
- Record each candidate type's representation, eliminators/recursors, operations, key laws, imports, options, and postulates/axioms.
- Separate CompactTypes' notion of compactness/searchability from the CoNaturals and Dyadics number representations.
- Identify licensing/attribution requirements for any adapted code.
- State which dependencies are compatible with `--safe` and the project's no-stdlib constraint.

## Resolution format

A concise source-to-local mapping with a dependency/assumption table and a recommendation to port, adapt, or exclude each candidate. Do not implement the port in this ticket.
