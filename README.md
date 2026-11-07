# agda2MALLPForth

A proof-carrying, resource-sensitive compiler project: PureCake-style source programs are admitted when their operational behavior has a derivation in Laurent's **existing MALLP calculus**, then lowered to GNU Gforth. The compiler's intended boundary is semantic and proof-directed, not a hard-coded list of source syntax forms.

## Destination

Compile every source program in the PureCake/PureLang specification that can be represented by a valid MALLP derivation over an explicitly declared primitive signature, preserving its observable behavior in Gforth.

MALLP itself stays fixed. This project does not add exponentials, weakening, contraction, or recursive/fixed-point connectives. A primitive signature may describe Nat arithmetic, data constructors, eliminators, or a state operation, but each primitive must state its formula, operational meaning, resource effect, and proof obligation. Signature declarations do not add logical rules.

## Admission rule

The compiler accepts a source construct when all of the following are established:

1. Its resolved Agda Treeless form has a typed interpretation in the compiler-owned source core.
2. Its variable, field, argument, and state-token usage is justified by an MALLP derivation.
3. Its lowering preserves the relevant PureCake evaluation behavior.
4. Its Forth instructions have a precise stack/resource contract.
5. A simulation theorem relates the source meaning, formal Forth machine, and emitted target behavior.

This is a semantic boundary, not a syntax whitelist. A Treeless constructor that is not implemented yet is an implementation gap, not a proof that the construct is impossible in MALLP.

MALLP resource discipline:

- Tensor splits resources between premises.
- Additive choice uses a common context and executes one selected branch.
- Cut composes a produced value with one linear assumption.
- An open resource cannot be silently copied or discarded.
- Agda relevance/usage evidence may justify erasure.
- A closed, pure, total computation consumes no assumptions. Its proof tree may be omitted when unused or independently reconstructed at multiple uses. This duplicates a closed derivation, not a live resource.
- Repeated references to captured linear state require a resource-preserving representation. An implementation must prove that representation rather than insert `DUP`, `DROP`, or hidden sharing.

## PureCake semantic obligations

The reference language is [PureLang in CakeML/PureCake](https://github.com/CakeML/pure). Its lazy semantics and compilation pipeline are the specification to preserve, not optional features to approximate.

- **Functions and closures:** a closure owns its captured environment. Application consumes the function/argument resources according to the MALLP judgement.
- **Local bindings:** unused closed pure bindings can be skipped; closed pure bindings can be inlined at multiple uses. Bindings that capture resources need a usage proof.
- **Data and pattern matching:** constructors own their fields; elimination consumes the scrutinee; case alternatives must satisfy the additive branch contract.
- **Laziness:** delay/force and demand behavior must be modeled explicitly where they affect observations. A one-shot suspension is different from a memoized shared thunk.
- **Sharing and state:** call-by-need updates may be represented only with an explicit, linearly owned state/store token and a proved state simulation. Repeated aliasing cannot be smuggled in as contraction.
- **Recursion:** admit source recursion when a finite MALLP derivation and the PureCake semantics can justify it (for example, through a specified primitive recursor). General recursive/fixpoint behavior is not added as a new MALLP connective.
- **Effects:** monadic effects, arrays, exceptions, and FFI are not rejected merely by name. They require a declared operation signature, an explicit linear state/effect protocol, and a matching target semantics. Unsupported effects fail with a diagnostic.

## Current implementation

The checked end-to-end fragment remains intentionally small:

- Closed Nat literals; Nat addition, natural subtraction (monus), and multiplication.
- Nonrecursive closed Nat lets, including unused and multiply-used bindings. These are substituted before Forth rendering; multiple uses expand into separate copies of a closed expression.
- Unary `Nat → Nat` functions with exactly one use of their live argument. The compiler recognizes a one-argument Nat telescope, checks the Treeless lambda arity, and lowers argument references through an indexed stack contract. Both operand orders are supported; a closed left operand uses `SWAP`, which is exchange rather than duplication or discard.
- Closed Boolean constructors: `true` and `false`, represented by the additive MALLP formula `1 ⊕ 1` and emitted as Gforth `TRUE` / `FALSE` values.
- Pure `Unit`: the MALLP multiplicative unit `1`, compiled as an empty Forth word that preserves the caller's stack.
- Bounded-cell Gforth Nat runtime with explicit negative/overflow checks.

`TPrim PSub` remains rejected as Nat monus: it denotes signed integer subtraction. Nat monus is handled through Agda's Nat subtraction builtin.

The Agda specification contains Laurent's polarized MALLP proof-tree calculus, a focused Nat primitive theory, a linear unary Nat function proof (`NatLinearExpr`) with exactly one live assumption, an indexed Forth `SWAP` exchange, a Boolean encoding as the additive formula `1 ⊕ 1`, and Unit as the multiplicative formula `1`. `boolProofDerivation` builds the two Boolean introductions from `mallp-plus-left` / `mallp-plus-right` and `mallp-one`; `boolMALLP-forth-sound` proves the rendered Boolean token has the same value as its MALLP proof. `unitProof` is `mallp-one`, and `unitMALLP-forth-sound` proves the empty Forth lowering preserves the caller's residual stack. `natMALLP-forth-sound` proves the closed Nat AST, indexed Forth stack code, and abstract postfix-token interpreter agree while preserving the residual stack. `natLinearMALLP-forth-sound` connects a unary linear Nat function's one-assumption proof interpretation with its indexed Forth/token execution. The closed-local-let model adds `closedNatLocal-proof`, `closedNatLocal-proof-adequate`, and `closedNatLocal-forth-sound`: a closed PureLang-style let expression is inlined and receives a MALLP derivation without weakening or contraction.

This is not yet a proof that the Haskell decoder/printer or a real Gforth process implements the Agda model. The existing Gforth cell bound also differs from mathematical unbounded Agda Nat; the emitted runtime reports overflow rather than proving arbitrary-precision Nat semantics.

## Current expanded test slice

The Gforth fixture now includes unary identity, addition, monus in either operand order, and multiplication. The admitted unary function must consume its one Nat argument exactly once. An unused argument or a duplicated live argument is rejected; closed operands may be separately reconstructed.

This is not yet general higher-order PureCake support: no closure environment, multiple independent live parameters, user-defined call graph, finite ADT/list lowering, recursive semantics, stateful thunk sharing, or effect handlers are implemented. The Agda proof establishes the formal unary core and abstract token machine, not the Haskell printer or real Gforth implementation.

## Implementation frontier

These are implementation tasks, not categorical bans. Each feature graduates to supported only with a typed source representation, usage evidence, lowering, tests, and a semantic-preservation argument.

1. **Typed Treeless front end:** classify every pinned Agda 2.8.0.2 `TTerm`, `TAlt`, `TPrim`, `ArgUsage`, and evaluation-strategy constructor; preserve source types and relevance. Cover variables, lambdas, application, user definitions, and lets.
2. **MALLP term core:** give formulas and proof terms to linear functions, products, sums, units, closures, and branch-sensitive cases. Connect the source usage checker to the actual MALLP derivation; do not rely on ordinary Agda typing as a linearity proof.
3. **PureCake data and control:** add constructor layouts, consuming eliminators, finite ADTs, lists, and control flow with additive branch/resource joins.
4. **Lazy evaluation:** formalize demand, delay/force, closure environments, and the stateful thunk-update behavior needed to match PureCake. Prove resource ownership for every captured value.
5. **Recursion and effects:** identify the source constructs whose behavior admits finite MALLP derivations or declared primitive signatures; prove termination/productivity or state/effect simulation where required. Keep the logical calculus unchanged.
6. **Forth target:** replace direct text construction with a typed, stack-indexed instruction AST, canonical renderer, and explicit runtime contracts for data, state, exceptions, and resource failure.
7. **End-to-end correctness:** prove correspondence from typed Treeless through each lowering pass to the emitted Forth, then prove the relevant Gforth execution simulation.

## Formal and build boundaries

- Agda and the Haskell backend use pinned Agda **2.8.0.2** from `cabal.project`.
- `formal/MALLPForth.agda` contains the MALLP specification, Nat proof terms, and abstract Forth machine.
- `formal/SovereignRationalSEDPhysics.agda` remains a separate library and is not a compiler proof dependency.
- The MALLP proof options and existing postulate boundary are retained; this project does not claim an axiom-free or `--safe` development.
- The Agda theorem covers the formal ASTs and token interpreter. Haskell decoding/rendering and real Gforth behavior need separate correspondence proofs.
- CI checks repository provenance, both Agda files, the Haskell backend, the Nat/let fixture, generated-code restrictions, and the Gforth integration fixture.

## Wayfinder decisions

**Destination:** the full PureCake-compatible subset characterized by valid derivations in unchanged MALLP.

**Decisions settled:**

- MALLP is not expanded with exponentials, weakening, contraction, or recursive/fixed-point connectives.
- No feature is rejected merely because its Treeless constructor has not yet been implemented.
- Reusable closed pure computations may be re-derived independently; live linear assumptions and state tokens retain exact ownership.
- PureCake evaluation behavior is the semantic reference. Each accepted pass needs its own simulation.
- README is the sole tracked Markdown project map; the former standalone map is retired.

**Not yet specified:** exact typed source judgments and primitive signatures for higher-order functions, algebraic data, recursive definitions, lazy stateful thunks, and effectful operations; target memory/closure layout; proof of correspondence between Haskell output and the Agda renderer.

**Out of scope:** changing MALLP's logical rules to add exponentials or recursive/fixed-point connectives. Source programs requiring those additional logical resources are outside this compiler's admitted language unless they admit an alternative derivation in the unchanged calculus.

## Build

CI is the authoritative build gate. The local command sequence used by CI is:

```sh
cabal build Agda:exe:agda
cabal build agda2forth
"$(cabal list-bin Agda:exe:agda)" -i formal formal/MALLPForth.agda
"$(cabal list-bin Agda:exe:agda)" -i formal formal/SovereignRationalSEDPhysics.agda
```

The strict fixture is compiled by `agda2forth` and executed by Gforth in GitHub Actions. A green fixture verifies only the current tested slice; it does not imply whole-PureCake coverage.
