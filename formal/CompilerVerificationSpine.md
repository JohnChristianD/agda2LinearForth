# Compiler verification spine: CakeML and PureCake adaptations

This document records the proof architecture to reuse from the HOL4-side CakeML and PureCake developments. The intent is to adopt their **proof decomposition and semantic interfaces**, not to copy HOL4 tactic scripts into Agda or claim that the existing Forth backend is already verified.

## 1. What CakeML contributes

CakeML separates the semantics of source programs from the compiler implementation and closes the pipeline with a top-level theorem. Its proof tree is layered:

1. Parsing is related to the parser used by the source semantics.
2. Type inference is related to the declarative type system, with soundness and completeness obligations.
3. The compiler backend is proved against a target-machine semantics.
4. The final theorem combines those results under explicit initial-state, configuration, installed-code, and resource-limit hypotheses.

The critical engineering pattern is that the final theorem is not a large monolithic argument about strings. It composes independently stated results, and states what a successful compiled artifact means when run by the target machine. Parse failure and type failure are kept distinct from execution behavior. The backend theorem also has an explicit installed-code premise and a machine semantics relation.

For this project, the corresponding terminal statement should quantify over the concrete generated Forth program and a concrete runtime state, not only over a manually mirrored expression tree.

## 2. What PureCake contributes

PureCake is especially relevant because its source language is lazy while its later compiler languages use call-by-value evaluation. It does not hide that mismatch in a vague claim that values are equivalent.

The proof side gives each intermediate language its own syntax and semantics, then relates adjacent stages. Its pure-to-thunk relation makes the evaluation strategy explicit:

- variable lookup is followed by `Force`;
- function arguments are wrapped in `Delay`;
- constructor fields are suspended;
- recursive bindings are represented by suspended closures or delays;
- projection forces the selected field to weak-head form;
- operations with special evaluation behavior receive dedicated translation clauses.

`thunkLang` has explicit `Delay`, `Force`, and thunk values, with a call-by-value semantics. The proof relates it back to PureLang's lazy behavior. Subsequent passes connect thunk language to environment-based execution, state-based execution, and finally CakeML. The end-to-end PureCake theorem composes these pass results and preserves an interaction-tree observation, including effects and divergence, rather than merely comparing one returned value.

The reusable design is therefore:

`source semantics` → `pass relation` → `intermediate semantics` → ... → `target semantics`

Each arrow carries its own well-formedness side conditions and semantic-preservation theorem. The top-level theorem is composition of those theorems.

## 3. First implemented slice in this repository

`formal/LinearModalSafety.agda` already contains a deliberately restricted Nat source grammar, an emitted-fragment mirror, a stack instruction sequence, and an inductive stack execution relation. The new additions make the target side executable and package the proof as a compositional pass:

- `runNatStackProgram` is the operational semantics of the selected Nat instruction language, including an explicit stack-underflow result.
- `natStackExecSound` connects the older relational execution proof with that interpreter.
- `StackSemanticPass` records a lowering function plus equality of source and target stack observations.
- `composeStackSemanticPass` composes adjacent pass-correctness proofs by equality transitivity.
- `natStackCompilerPass` proves the current `NatExpr → NatStackProgram` lowering preserves the denotation and caller stack suffix.
- `NatCompilationCertificate` packages the fragment-meaning theorem, fragment-to-instruction projection theorem, executable stack simulation, and finite-cell representability witness.

This is a real proof about the stated Agda models. It is still a small, manually maintained Nat fragment. It does **not** establish that the Haskell emitter emits the certified instruction sequence, that rendered Forth parses as that sequence, or that Gforth's concrete runtime implements the interpreter.

## 4. Target proof graph

The intended graph is:

```text
Agda source in declared supported subset
  │  Agda type checker / erasure boundary (trusted until separately related)
  ▼
Supported typed source IR
  │  source-to-IR semantic preservation
  ▼
Canonical expression IR
  │  per-pass preservation (desugaring, closure conversion, demand/laziness)
  ▼
Typed Forth instruction IR
  │  emitter correctness: Haskell output corresponds to IR
  ▼
Rendered Forth source
  │  serializer / parser correspondence
  ▼
Abstract Forth machine semantics
  │  runtime ABI simulation, including errors and allocation state
  ▼
Concrete Gforth execution
```

The order matters. A typed target IR must become the specification consumed by the printer; otherwise Agda and Haskell can silently drift as the current hand-maintained mirrors do. The printer should be a small final serializer, not a second compiler.

The eventual top-level theorem should have a shape similar to:

```text
compile source = success forth
and source is in the supported subset
and initial runtime state satisfies ABI invariants
imply
  observations(source semantics)
    are related to observations(Gforth execution of forth)
```

The observation relation must include normal return, catchable failure, divergence or fuel exhaustion, and externally visible effects whenever the supported source subset includes them. A finite-result equality alone is insufficient for a language with effects or laziness.

## 5. Forth-specific obligations

### Typed target IR

Replace direct construction of untyped `FthForm` values as the semantic compiler boundary with a small typed instruction language. Each instruction should declare its stack input/output shape and any heap, exception, or control-flow effect. The Agda semantics and Haskell emitter should share the same opcode inventory. Raw Forth strings should exist only after the typed program has been constructed.

### Runtime state and allocation

The current Agda allocation model and runtime inventory are monotone-allocation models. A no-GC implementation still needs a reclamation story. A later runtime proof should model bounded slots, live/free state, generation-tagged handles, stale-handle rejection, and atomic failure when capacity is exhausted. Runtime descriptor creation must use that allocator; compile-time `:noname` execution tokens are a separate static-code concern.

The concrete proof must relate allocator transitions to the Forth words that actually mutate memory. A proof about an abstract allocator does not prove a dictionary-based `HERE ... ALLOT` implementation safe.

### Lazy evaluation

PureCake's key lesson is to make delay/force behavior explicit in both the target language and the correctness relation. In this repository, `makeDelay = id` and the ordinary variable path currently bypasses forcing. Therefore the existing lazy-evaluation path is not a proved lazy translation. Do not advertise it as semantics-preserving until the compiler has explicit delay/force rules and a pass theorem, or reject that mode and keep the currently verified subset strict.

For a linear-only target discipline, a thunk can be consumed at most once. General shared call-by-need memoization needs an explicit sharing capability and ownership semantics; it must not be inferred from the presence of a thunk constructor. Pure computations may sometimes be recomputed, but that changes cost and is only semantics-preserving under a suitable purity and termination argument.

## 6. Order of work

1. Freeze a small, exhaustive source allowlist. Every unsupported treeless constructor, primitive, literal, and pattern form must fail closed.
2. Define a typed target IR with executable semantics and declarative stack/heap/error effects.
3. Make the Haskell lowering construct that IR; prove each IR lowering pass preserves observations.
4. Add a serializer relation from typed instructions to exact Forth tokens, with golden tests generated from typed programs.
5. Define the runtime machine state, including the bounded allocator, and prove every supported Forth ABI word refines its Agda transition.
6. Connect generated Forth executions to the abstract machine using trace/observation tests and a clearly stated trusted computing base for Gforth.
7. Add PureCake-style lazy compilation only as a separate verified pass with explicit `Delay`/`Force` semantics.

## 7. Deliberate non-claims

- The current Nat certificate is not a proof of `ToForth.hs`.
- The checked Agda model is not a proof of arbitrary generated Forth.
- Gforth itself is not verified by this repository.
- The allocator model does not yet implement reclamation.
- The current lazy flag is not an established lazy semantics-preserving mode.
- Laurent MALLP's polarity shifts are not exponentials. MALLP has no structural weakening or contraction rules; no Seely comonad is needed for this fragment.

## References

The following proof developments supply the proof architecture and semantic interfaces adapted here:

- CakeML complete compiler correctness: https://github.com/CakeML/cakeml/blob/master/compiler/proofs/compilerProofScript.sml
- CakeML source semantics and program observation: https://github.com/CakeML/cakeml/blob/master/semantics/semanticsScript.sml
- PureCake end-to-end compiler correctness: https://github.com/CakeML/pure/blob/master/compiler/proofs/pure_compilerProofScript.sml
- PureLang-to-thunkLang simulation: https://github.com/CakeML/pure/blob/master/compiler/backend/passes/proofs/pure_to_thunk_1ProofScript.sml
- Explicit call-by-value thunk language: https://github.com/CakeML/pure/blob/master/compiler/backend/languages/semantics/thunkLangScript.sml
- Laurent's MALLP sequent calculus: https://perso.ens-lyon.fr/olivier.laurent/fullpolgames.pdf (section 3.1)
- Hamano and Scott, categorical semantics for polarized MALL: https://doi.org/10.1016/j.apal.2006.09.001
