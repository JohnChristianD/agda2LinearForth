# agda2MALLPForth

A verified-compiler research project for Olivier Laurent's multiplicative-additive polarized linear logic (MALLP), Agda formal semantics, and GNU Gforth. The currently executable compiler slice is deliberately narrower: **strict, closed Nat expressions only**, lowered to postfix stack code. The broader goal is a compositional MALLP-to-Forth compiler with a proof-preserving semantics. The current Nat runtime has no heap, closure objects, thunk updates, garbage collector, descriptor table, or dynamic allocator; those are facts about this checked slice, not a claim that every future MALLP implementation must avoid closures or suspensions.

The project has two separate Agda files:

- `formal/MALLPForth.agda`: a `--with-K --rewriting --confluence-check --polarity --lossy-unification` compiler specification. It contains six foundational packages, constructive coinductive conaturals, Laurent's polarized MALLP sequent calculus, and indexed strict Forth stack-code semantics. The base calculus remains proof-tree syntax. A focused Nat theory adds computational proof terms for literals, binary primitive constants, and cut, with an explicit embedding into an MALLP-with-Nat-signature derivation.
- `formal/SovereignRationalSEDPhysics.agda`: the separate RSED physics library, checked by the same Agda 2.8.0.2 CLI under the with-K/rewrite/polarity option family. It remains separate and is not imported by the compiler proof.

Both Agda files and the Haskell backend use one pinned stable Agda source version, **2.8.0.2**, via `cabal.project`. CI builds the Agda CLI and `agda2forth` from that same Cabal source package; it does not install a separate Agda binary. Both specifications use `--with-K`, `--rewriting`, `--confluence-check`, `--polarity`, and `--lossy-unification`; neither is marked `--safe` or `--cubical`. The compiler file retains constructor-based guardedness, while the physics file retains guarded recursion and its existing instance-search/projection options. `--no-prop` is omitted because it is already the default. `--with-K` enables erased matches by default in Agda 2.8.0.2; the explicit `--erased-matches` flag is absent.

The compiler specification retains the original computational rewrite system from `SovereignRationalSED-MALLP.agda`: `μ-step-true`, `μ-step-false`, `sBR-stop`, `sBR-step`, and `lookup-tabulate`. The first four are postulated computation equations; `lookup-tabulate` is proved constructively. Two closed least-search witnesses check that the μ-rules reduce as intended.

Keep the counts distinct: the module contains seven formal components (six foundational packages plus Laurent polarized MALLP). The global `REWRITE` block registers four postulated computation equations: `μ-step-true`, `μ-step-false`, `sBR-stop`, and `sBR-step`. `lookup-tabulate` remains a constructive theorem, but is deliberately not registered as a global rewrite rule: its left-hand side overlaps the structurally recursive `tabulateList` and `lookupPrefix` equations, so global registration fails Agda's confluence check. Use the theorem explicitly where finite-list lookup reasoning needs it. Separately, five postulate blocks declare 20 assumptions, grouped conceptually into least-witness search/choice, cohesive retractions, quotient reflection, and symmetric bar recursion. They are retained as axioms by design. They are not derivable from MALLP, and the MALLP soundness boundary must state which results depend on them. They are not silently presented as an axiom-free or `--safe` proof.

## Execution path

```text
Agda source (closed Nat expressions)
        |
        v
Agda type checker and erasure
        |
        v
ToForth.hs: closed-expression Treeless checker
        |
        v
Gforth colon definition, postfix stack code
        |
        v
FLib.fth: three bounded Nat combinators
```


## Source language and builtin coverage

The source language is **the Agda 2.8.0.2 Treeless language accepted by this backend**, not all well-typed Agda. A builtin is not automatically executable merely because Agda knows its name. Agda distinguishes builtin bindings (BuiltinId) from compiler primitives (PrimitiveId); the pinned source of truth is [Agda 2.8.0.2, Agda.Syntax.Builtin](https://hackage-content.haskell.org/package/Agda-2.8.0.2/docs/Agda-Syntax-Builtin.html). The backend must classify both enumerations exhaustively for that exact version. A new Agda release changes the compiler contract and requires a fresh inventory and review.

The policy has five outcomes:

| Classification | Backend action | Correctness obligation |
| --- | --- | --- |
| Runtime value or operation | Lower into typed core and target instructions | Preserve its source value and evaluation behavior |
| Constructor or eliminator | Lower to a typed data representation and consuming case operation | Preserve constructor identity, field ownership, and selected-branch behavior |
| Erased proof or irrelevant argument | Erase only when Agda's relevance/usage information permits it | Prove erasure leaves observable computation unchanged |
| Type-level or compile-time construct | Consume during type checking / elaboration; emit no runtime word | Prove it cannot affect runtime observations |
| Unsupported runtime construct | Reject with the builtin name, type, and source location | Never silently omit a reachable definition |

The table below is the intended support boundary. **“Planned” is not implemented support.** At present the executable backend still accepts only closed Nat literals, addition, monus, and multiplication.

| Agda family | Builtins / primitive families in the pinned compiler | Target treatment | Current status |
| --- | --- | --- | --- |
| Natural numbers | Nat, zero, suc, plus, minus, times, div/mod helpers, equality, less-than, show | Exact natural value plus arithmetic/comparison/formatting words | Literals, plus, monus, and times only; current cell-bounded runtime |
| Signed integers | Integer, pos, negsuc, integer display | Canonical sign-and-magnitude value; arbitrary-precision arithmetic | Formal arithmetic is present in the separate RSED file; no Forth lowering |
| 64-bit words | Word64, conversions to/from Nat, conversion injectivity | Fixed-width bit-vector operations with specified wrap/conversion semantics | Unsupported |
| Floating point | Float; equality, inequality, ordering, classification, conversion, rounding, arithmetic, transcendental and display primitives | Gforth floating-point representation plus a target model for rounding, NaN, infinities, and signed zero | Unsupported |
| Characters and strings | Char, String; character equality/conversions, string equality/append/list conversion | Unicode scalar values and explicitly encoded string buffers | Unsupported |
| Finite algebraic data | Bool, Unit, Sigma, List, Maybe and their constructors | Tagged or stack-shaped values; constructors move fields, case consumes the scrutinee and selects one branch | Unsupported |
| Coinduction and strictness | ∞, ♯, ♭, primForce, primForceLemma | Explicit one-shot delay/force where required; strict force evaluates its suspended expression | Unsupported |
| Sizes and universes | Size, size relations and size constructors, Level, Prop, Set, universe/sort identifiers | Static checking or erasure; no runtime representation | Type-level only |
| Equality and rewriting | Equality, refl, rewrite support, erased equality primitives | Proof erasure / conversion; no runtime equality proof object | Erasure depends on Agda relevance information |
| Literal overloading | FromNat, FromNeg, FromString | Resolve during elaboration; compile the resulting value/operation, not the elaboration class | Unsupported beyond Nat literals |
| Reflection and metaprogramming | QName, Meta, reflection syntax, TCM and reflection constructors/primitives | Compile-time only; runtime occurrence is rejected | Unsupported at runtime |
| Cubical constructs | Path, PathP, interval, partial types, Glue, composition and related primitives | Outside this compiler configuration | Unsupported; the checked build uses --with-K, not a cubical target |
| Effects | IO and effectful primitives | Excluded from the pure backend | No IO sites are admitted; any reachable runtime IO use must fail compilation |

Additional distinctions matter:

- BuiltinId constructors such as BuiltinIntegerPos or BuiltinList identify Agda's canonical representation. PrimitiveId entries such as PrimNatPlus or PrimFloatPlus identify evaluator operations. A source operator can elaborate to a definition, a primitive, or a combination of both; dispatch must use resolved Agda names and actual Treeless nodes, not source spelling.
- FromNat, FromNeg, and FromString are elaboration mechanisms. They are not a blanket licence to treat every overloaded literal as a machine literal. The compiler must inspect the elaborated type and lower the resulting value under that type's representation.
- Equality proofs, size evidence, and levels may disappear only after the compiler has used Agda's relevance, forced-argument, and usage information. A proof-looking name is not sufficient grounds for erasure.
- Reflection and TCM are compile-time computation. They may influence the program produced by elaboration, but they are not a runtime service in this backend.
- The absence of IO is a source-language restriction, not a claim that Agda's builtin IO type is absent from the language.

The exhaustive manifest should live beside the backend as version-locked data or generated source, with one row per BuiltinId and PrimitiveId. CI should compare that manifest with the pinned Agda enumeration so an Agda upgrade cannot quietly introduce an unclassified constructor. Every runtime entry names its lowering function, target word(s), semantic test, and proof obligation. Every erased or compile-time entry names the reason it cannot survive into executable code. A catch-all “other primitive” branch is a compiler bug waiting to happen.

## Compiler architecture

The chosen architecture is a typed, staged pipeline rather than direct Treeless-to-text emission.

```text
Agda source
  │ type checking, builtin resolution, relevance/usage analysis
  ▼
Agda Treeless + compiler-owned erasure
  │ total classification; reject unsupported reachable runtime nodes
  ▼
Typed source core
  │ literals, calls, constructors, cases, primitives, delay/force
  ▼
Pure functional lowering
  │ explicit evaluation order and explicit recursive calls
  ▼
Thunk / environment / state IRs, only where demanded by the source
  │ delay/force → closure conversion → explicit ownership/store
  ▼
Formula- and stack-indexed Forth AST
  │ instruction semantics and resource transitions
  ▼
Canonical Forth renderer
  │ exact token correspondence and target-runtime contract
  ▼
Gforth
```

The pipeline adopts PureCake's most useful lesson: each pass has a source and target semantics, a local simulation/refinement relation, and a proof that the compiler pass stays inside that relation. The actual PureCake compiler uses PureLang, ThunkLang, EnvLang, and StateLang before CakeML; its ThunkLang makes delay/force explicit, EnvLang makes environments explicit, and StateLang makes updates/stateful operations explicit. Those stages are introduced because the source language is lazy and the target compilation strategy is strict. They are not mandatory ceremony for the present closed-Nat fragment. Add a stage only when a source feature needs it, then prove its pass.

The core interfaces should be narrow and total:

1. **Builtin inventory:** map every pinned Agda builtin/primitive to exactly one classification. Unknown or newly introduced identifiers fail closed.
2. **Treeless decoder:** turn Agda's internal Treeless nodes into a small compiler-owned AST. It owns source names, source types, argument-use facts, and an explicit diagnostic span.
3. **Typed source core:** represent each admitted operation with its source type and evaluation order. No raw strings or Forth snippets enter this layer.
4. **Evaluation/closure passes:** make laziness, delay, closures, environments, and state explicit only when needed. A pure Nat expression should pass through without acquiring a heap or thunk runtime.
5. **Linear target AST:** every word declares its exact input/output stack indices and owned values. A sequence composes only when adjacent indices agree. A branch consumes its condition once and both branches must return the same output contract.
6. **Renderer:** render only the target AST. Keep identifier escaping, literal formatting, runtime inclusion, and Forth syntax in one place. The rendered text is tested against the formal token renderer; manually maintaining two unrelated printers is not a proof.
7. **Target model:** model the exact Gforth primitives, cell width, arithmetic overflow, exceptions, memory allocation, string layout, and dictionary behavior used by emitted code.

The current ToForth.hs is much smaller than this architecture: compileNatTerm recursively accepts a literal or three binary Nat primitives, while compileDefinition turns Agda functions into eager Treeless and ignores non-function definitions. It builds RichSExpr Text directly. The Agda ForthCode model is a separate implementation and currently has only natCell. This separation is why a passing Haskell build and fixture do not establish that the Haskell backend implements the Agda compiler theorem. The next compiler step is to close that representation gap, not to add more ad-hoc cases to compileNatTerm.

### Data and arithmetic representations

Agda's mathematical Nat and Int are unbounded. A Gforth cell is finite. The existing Nat runtime therefore implements a bounded fragment and throws on values above MALLP-MAX-NAT; the Agda model does not yet model that exception. This is a known semantic mismatch, not a harmless implementation detail.

The target direction for exact integer arithmetic is normalized arbitrary-precision limbs:

- Nat is a non-negative, normalized little-endian limb sequence.
- Int is a sign plus a normalized magnitude; zero has one canonical representation and is never negative.
- Addition, subtraction, multiplication, comparison, conversion, and decimal parsing operate on limb sequences and specify allocation, ownership transfer, and exceptional/resource-exhaustion behavior.
- Each Forth arithmetic word consumes its owned operands and returns one owned result. Any copy or shared reference must be an explicit operation justified by the source usage judgment.
- A target execution theorem is conditional on successful memory allocation and valid target addresses; physical memory is finite even though the mathematical value is unbounded.

A fixed cell or double-cell integer is a useful fast path, but cannot by itself implement all Agda Nat or Int. Such a representation is sound only under a proved range invariant. The present runtime's overflow exceptions remain valid for its explicitly bounded slice; they are not the semantics of general Agda integers.

For Word64, the target must specify 64-bit modular operations and conversions independently from mathematical integer arithmetic. For Float, it must preserve the exact Agda primitive's floating-point behavior, including NaN, infinities, signed zero, comparison, and rounding. The Gforth floating-point word set must be checked against the pinned semantics rather than assumed equivalent by name. Characters require a Unicode scalar representation; strings need a defined encoding, length convention, allocation policy, and equality/concatenation semantics.

For Bool, Unit, Maybe, List, and Sigma, define constructor layouts and consuming elimination before adding backend support. In a case expression, the scrutinee is consumed once; only the selected branch receives the fields it owns. Recursive lists need a representation and a recursion/iteration lowering with a proof of termination or a semantics-preserving treatment of Agda's structurally recursive definitions. A data representation must not smuggle unrestricted copying or disposal into the runtime.

### Laziness, closures, and the MALLP resource discipline

PureCake's ThunkLang is stateless and re-evaluates a thunk when forced; the later StateLang pass implements sharing/update behavior. That distinction matters. A thunk is not automatically a shared memo cell, and a call-by-need update is not automatically linear.

MALLP has no weakening or contraction rules and no ! / ? exponentials. Therefore:

- A linear closure owns its captured environment. Application consumes that environment according to its formula-indexed typing.
- A one-shot suspension may own linear resources and be forced once.
- A memoized/shared thunk may be used repeatedly only when its captured environment is proved duplicable by an explicit extension/modality or when the semantics otherwise justifies sharing.
- A branch may choose one additive premise; it may not execute both premises using the same linear context.
- An unused computational value cannot silently vanish. It must be erased by Agda's checked relevance/usage rules, consumed by a target operation, or rejected.
- A value used more than once needs an explicit, proven duplication policy. The current MALLP calculus intentionally does not contain contraction.

The compiler must therefore establish a source usage judgment before treating unrestricted Agda terms as MALLP computations. Ordinary Agda typing alone does not prove linear usage. The judgment must cover variables, constructor fields, function arguments, recursive calls, pattern matches, and alternatives. Any source construct whose use behavior is not represented in that judgment is outside the admitted fragment.

## Verification architecture

The objective is a composed semantic-preservation theorem, not a collection of green smoke tests:

```text
Agda source typing + usage
  ──front-end correctness──▶ typed source core
  ──pass simulation────────▶ thunk / environment / state IR
  ──linear lowering────────▶ indexed Forth AST
  ──renderer soundness─────▶ emitted Forth tokens
  ──target simulation──────▶ Gforth execution model
```

Each arrow has its own theorem. The top-level theorem is their composition. Keep the proof boundaries explicit:

- **Front end:** every accepted Treeless definition corresponds to its typed source-core term; every unsupported runtime definition is diagnosed rather than omitted.
- **Erasure:** erased arguments and definitions are observationally irrelevant under Agda's relevance/forced/usage information.
- **Core passes:** each pass preserves evaluation (or a stated refinement relation) and resource ownership. This follows PureCake's syntactic-relation plus semantics-preservation approach, not a single giant proof.
- **MALLP denotation:** interpret each polarized formula and each rule in the Hamano–Scott setting: an ambient *-autonomous category with products and the reflective/coreflective polarized full subcategories related by adjunction. Prove each rule sound in that denotation. The categorical interpretation is a semantics of proofs; it does not by itself define executable closures, heaps, or Forth words.
- **Linear lowering:** prove tensor splits resources, additive choice preserves the common context without duplicating it, shifts preserve polarity, exchange permutes resources, and cut composition consumes the intermediate interface. If cut elimination is used instead, prove it and preserve the same denotation.
- **Forth AST and renderer:** prove each instruction's stack/resource effect; prove renderer output equals the formal token list; prove token execution matches the AST semantics and preserves the residual stack.
- **Gforth model:** formalize the subset of Gforth actually emitted, including finite cell width, exceptions, locals, allocation/free, strings, and load-time dictionary use. Prove a simulation for successful executions and characterize resource exhaustion.
- **Haskell connection:** show that Treeless decoding and emitted AST from ToForth.hs match the verified front end and target AST. The Haskell printer must not be an unverified parallel definition of the formal renderer.

Hamano–Scott's categorical model is for polarized MALL, not a blanket full-completeness theorem for full MALLP. Use it for sound denotation and resource-sensitive rule interpretation; do not claim that every Agda program is a MALLP proof, or that categorical soundness alone proves code generation. In particular, the base MALLP datatype remains proof-tree syntax. The Nat theory is a small computational extension with an explicit primitive signature, not a general lambda-calculus proof-term language. Its proof interpretation is related to the closed Nat Forth token model; general PureCake constructs remain outside this fragment.

## Coverage and regression strategy

The compiler's builtin inventory drives tests. Each runtime row gets at least:

- A minimal Agda source fixture that reaches the exact builtin after elaboration.
- A lowering test for its compiler-owned core node and target AST.
- Boundary/computation examples, including zero, negative values, overflow or wrap boundaries as appropriate, empty and singleton data, branch alternatives, and nested constructors.
- A semantic comparison between Agda evaluation and formal target evaluation.
- A Gforth integration check for emitted code and the declared target-runtime behavior.
- A negative test showing that unsupported or effectful source code fails with a diagnostic.

Numeric tests should include carry/borrow chains and values wider than one machine cell for arbitrary-precision Nat/Int; Word64 should test modular wraparound separately. Float tests should distinguish NaN equality/inequality, signed zero, infinities, and rounding. Unicode tests should cover multi-byte characters and string boundaries. Data tests should cover every constructor and case branch. Coinduction tests should check finite observations of productive streams without forcing an infinite computation eagerly. IO and cubical constructs should have explicit rejection tests.

The CI gate should be staged so failures identify the responsible layer: (1) pinned Agda CLI version; (2) Agda formal proofs and rewrite confluence; (3) Haskell backend build; (4) manifest exhaustiveness; (5) source-core lowering tests; (6) Forth AST/renderer theorem or differential check; (7) Gforth runtime fixtures; and (8) the composed compiler correctness gate. A green legacy fixture alone must never imply whole-language builtin coverage.

The admitted expression language is:

- Nat literal;
- addition;
- Agda Nat subtraction (monus);
- multiplication.

A source definition with a variable, lambda, capture, user-function call, constructor, case split, unsupported builtin, or other Treeless form is rejected. The backend has no alternate descriptor/thunk path. The sole supported output consists of pushes and three binary words.

## Linear stack semantics

The Agda target code is indexed by input and output stack shapes. Its constructors are:

- `pushNat`: adds one Nat cell;
- `binaryWord`: consumes two Nat cells and produces one;
- `sequence`: composes stack transitions whose intermediate stack indices agree.

There are no constructors for duplication, discard, heap access, closure creation, or implicit weakening/contraction. The execution function is indexed by the same stack shapes. The source-to-code theorem states that compiling an expression and executing its target code returns the source-evaluated Nat on top of the original untouched tail stack. A second theorem interprets the rendered postfix token list and proves it yields the same stack result, including residual-stack preservation.

The focused `MALLPNatProof` is indexed by its number of linear Nat assumptions. Literals are nullary axioms, binary primitives consume two assumptions, and cut composes proofs. `embedNatProof` maps the focused proof into `MALLPNatTheory`; `interpretMALLPNatProof` gives its Nat semantics. `natExprProof-adequate` proves agreement with `evalNatExpr`, and `natMALLP-forth-sound` composes this with indexed Forth execution and the formal postfix-token interpreter, preserving the residual stack. This covers the closed Nat expression fragment only; it is not a translation for arbitrary Agda terms or arbitrary Laurent MALLP derivations.

## MALLP semantics and runtime representations

The MALLP fragment follows Laurent's polarized syntax as studied by Hamano and Scott. Positive formulas use tensor, plus, and the positive unit/zero; negative formulas use par, with, and the negative units; the polarity shifts `↑` and `↓` connect the two classes. This is the linear fragment: the calculus has no `!`/`?` exponentials and no weakening or contraction rules. See [Hamano and Scott, *A categorical semantics for polarized MALL*](https://doi.org/10.1016/j.apal.2006.09.001).

Keep three layers separate:

1. **Logic:** MALLP formulas and derivations express polarized linear resource use.
2. **Denotation:** Hamano–Scott interpret MALLP in an ambient *-autonomous category with products, using reflective/coreflective polarized subcategories and their adjunctions.
3. **Execution:** closures, environments, thunks, stacks, and heaps are implementation representations. They are not MALLP connectives and do not follow automatically from the categorical model.

The base `MALLP` datatype is still a derivation tree. The Nat theory is a small computational extension with an explicit signature, not a general lambda-calculus proof-term language. A future higher-order extension may use closures when it represents proof terms as executable functions. Such a closure can be linear: its code and captured environment move together, and application consumes the captured linear resources according to the typing judgment. A duplicable closure that silently copies a captured linear environment would violate the calculus.

Thunks need the same distinction. A one-shot suspension may capture linear resources and be forced exactly once. A memoizing call-by-need thunk caches a result for repeated demands; sharing a thunk that owns linear resources would amount to reusing those resources. Such sharing needs an explicit unrestricted modality or a proof that the captured environment is duplicable. Otherwise use a one-shot thunk, evaluate eagerly, or defunctionalize the delayed computation into an explicit code-and-environment representation.

The additive `with` rule has two derivation premises over the same context because either branch may be selected. This is a choice, not permission to execute both branches with duplicated resources. A compiler translation must preserve that branch selection and its resource accounting. Tensor, by contrast, splits the context between its premises. The future intermediate language therefore needs rule-indexed resource semantics, not merely a collection of stack words.

Consequently, closures and thunks are **not universally required by MALLP**, but neither should they be prohibited by fiat. Their necessity depends on the chosen proof-term language and evaluation strategy. The present closed-Nat compiler can remain heap-free; a richer higher-order or non-strict source fragment must choose and prove an appropriate linear closure/suspension model.

## Forth runtime

`data/FLib.fth` contains only the bounded strict Nat runtime. Its validator consumes its input and returns no stack value, so callers need no `DROP`. CI rejects structural stack-duplication/discard words (`DUP`, `?DUP`, `2DUP`, `3DUP`, `OVER`, `2OVER`, `PICK`, `DROP`, `2DROP`, `3DROP`, `NIP`, `2NIP`, `TUCK`) in the runtime and generated output:

- `MALLP-PARSE-NAT` parses decimal literals and checks the signed-cell limit;
- `MALLP-NAT-ADD` checks overflow before addition;
- `MALLP-NAT-MONUS` implements saturating Nat subtraction;
- `MALLP-NAT-MUL` checks overflow before multiplication.

All three arithmetic words consume exactly two stack operands and return one result. Runtime words allocate no memory. There is no `HERE`, `ALLOT`, `:noname`, descriptor ABI, closure environment, thunk, or garbage collector.

Gforth still stores generated colon definitions in its dictionary when the output file is loaded. This project has no proof of a global dictionary-capacity bound; a sufficiently large generated source file can still exceed the interpreter's available dictionary. The no-allocation statement applies to runtime evaluation of the compiled fragment, not unlimited static code size.

## Baseline fidelity and proof boundary

The latest Library snapshot used as the structural baseline has
`--without-K` (and `--no-prop`) in its file header. This branch uses
`--with-K` because that was explicitly requested for the compiler and
physics checks. The source components and five registered rewrite equations
are retained, but the type-theoretic assumptions are therefore not identical:
a successful `--with-K` check does not establish that the same development
checks under the baseline's `--without-K`. The current CI has only the
with-K gate. Treat no-K compatibility as an explicit open proof obligation,
not an implied equivalence.

There is also a real arithmetic mismatch in the present Nat slice. Agda's
`Nat` and the proof's `+`/`*` are unbounded, while the Gforth runtime uses
finite signed cells and rejects values beyond `MALLP-MAX-NAT`. The Agda
`ForthToken` interpreter currently models unbounded `Nat` pushes and
arithmetic; it does not model the Forth parser's overflow exception. The
small fixture values fit, but `renderForth-sound` alone is not a refinement
proof for all Agda Nat expressions. A correct full statement must either
restrict inputs with a proved representability invariant or replace the
target representation with verified arbitrary-precision naturals. The
latter is the natural route for exact unbounded integers and rationals.

The previous gap between the MALLP sequent tree and `NatExpr` is now closed
for the declared Nat signature: `natExprProof` constructs an indexed proof
term, `embedNatProof` produces its MALLP-with-signature derivation, and the
semantic/token theorem proves the closed expression result. This does not
cover additive `with`, tensor, shifts, arbitrary MALLP derivations, or cut
elimination. Those require rule-specific resource and branch semantics.

The source comments identify Hamano–Scott's model as a separate obligation.
The current Agda file does not define the required ambient *-autonomous
category with products, its reflective/coreflective polarized subcategories,
or the adjunction connecting them. Those categorical structures should first
give a sound interpretation of every MALLP rule. That interpretation is
distinct from an executable target semantics. Hamano–Scott prove full
completeness for their multiplicative fragment, while showing that full
completeness fails for full MALLP in their model; a compiler correctness
argument needs soundness and a term interpretation, not an unsupported
full-completeness claim.

The infinite data in the RSED source also has a narrower meaning than an
exact real. `ConatStream Rational` provides productive observations and
finite-prefix folds over a stream of Rational values. The covariance orbit
is generated by shifting indices in a finite time model. The rational carrier
is an interface, and the source does not give a Cauchy modulus, a convergence
proof, or a completed real-number representation. Nat proofs alone cannot
supply signed-integer arithmetic, normalized rational arithmetic, or a
constructive real limit.

A complete verification chain should be layered and composed:

1. Give the source fragment a precise typing/usage judgment and operational semantics.
2. Give MALLP proofs computational terms plus a sound categorical interpretation.
3. Translate those terms into a formula-indexed linear intermediate language, proving preservation for every rule (including additives, shifts, exchange, and cut or a proved cut-elimination route).
4. Give the intermediate language an explicit Forth word AST and operational semantics; prove its renderer emits the exact token/text language consumed by Gforth.
5. Model the Gforth cell, exception, local-variable, memory, and dictionary behavior used by the output, then prove a simulation/refinement theorem from the formal Forth semantics to that target model.
6. Connect the Haskell Treeless traversal and printer to the verified specification. Prefer a generated or mechanically checked correspondence over a manually maintained parallel renderer.

This is the project-level proof boundary. The current PR adds a formal MALLP Nat-term semantic theorem through the abstract Forth token machine and retains the closed-Nat Gforth integration fixture. It still does not prove the Haskell backend or real Gforth semantics.

## PureCake / CakeML relationship

PureCake is a useful model for the *whole proof architecture*: it defines source and intermediate-language semantics, proves each compilation pass correct, and composes the results through CakeML to machine code. Its formal PureLang numeric carrier is HOL4's mathematical `int`, not merely `Nat`: the built-in semantics defines integer addition, subtraction, multiplication, division, remainder, and comparisons. Its examples include an unbounded lazy `[Integer]` stream and factorials over `Integer`. PureCake's source semantics uses call-by-name evaluation; its compiler then lowers through explicit intermediate languages, including call-by-value ThunkLang, EnvLang, and StateLang. Thunks are introduced and then optimized as part of that particular lazy-language compilation strategy.

That result does **not** supply an exact-rational or exact-real development. PureCake does not establish a rational quotient construction, an untruncated co-dyadic representation, a Cauchy/modulus theorem, or Escardó-style searchable-type results. Those mathematical structures and their equality/search principles still need their own formal definitions and proofs. PureCake can serve as a compiler-correctness blueprint for programs using such structures once they are defined, but its compiler theorem does not create those number systems for us.

The present RSED file is more limited than that target: `RationalRingInterface` is an abstract algebraic interface, and `ConatStream A` supports productive observations while `foldConatPrefix` deliberately consumes a finite observation budget. This is useful stream infrastructure, not yet a concrete rational implementation or a proof of an untruncated real/codyad representation.

PureCake's thunk pipeline is an architectural precedent, not a runtime recipe to copy wholesale. Its source/target evaluation strategies and explicit thunk transformations answer needs of a lazy functional source language. For MALLP, a shared thunk is sound only when its captured resources may be shared; a one-shot suspension or a defunctionalized representation may better preserve linear usage.

The Agda theorem now composes the MALLP Nat proof-term interpretation, closed-Nat lowering, indexed stack execution, and the abstract postfix-token interpreter, preserving the residual stack. `ToForth.hs` remains a separate Haskell implementation of Treeless decoding and textual rendering. CI compiles examples and executes their generated Gforth files, but there is not yet a kernel proof that the Haskell printer emits exactly `renderForth`, nor a formal refinement theorem for the Gforth interpreter. Therefore this is **not yet an end-to-end verified compiler in the PureCake sense**.

## Development tools and scope

The supported and CI-verified build path is **GHC + Cabal**. The workflow selects GHC 9.2.8 and Cabal 3.10.3.0, then builds both the Agda CLI and `agda2forth` with Cabal. `cabal.project` pins the Agda Git source tag `v2.8.0.2`; CI checks the built executable's numeric version before using it for both Agda files.

A root `stack.yaml` **does exist**, but it is a legacy configuration: it selects Stackage LTS 19.4 and pins `s-cargot-0.1.4.0`. That snapshot contains Agda 2.6.2.2, while this fork's `agda2forth.cabal` requires Agda `>= 2.8.0.2 && < 2.9`. The current Stack resolver therefore cannot satisfy this package's declared Agda bound. Stack itself is not obsolete and Agda 2.8.0.2 is available in modern Stackage snapshots (including LTS 24.65); what is stale is this repository's LTS 19.4 pin. Until a Stack resolver and its dependency plan are updated and tested against this fork, treat `stack.yaml` as **legacy and unsupported for this project**, not as a second verified build path.

The upstream repositories differ: current `jespercockx/agda2scheme` has a Cabal package and a Cabal-based GitHub Actions workflow, but no `stack.yaml`; the older `LMMilliken/agda2Forth` repository has both a `.cabal` package file and an LTS 19.4 `stack.yaml`. These files can coexist because the `.cabal` file describes package metadata/dependencies, while `stack.yaml` selects Stack's resolver and project plan. Coexistence does not mean both plans select the same Agda version. PureCake is a separate HOL4/PolyML/Holmake build, not a Stack project.

The proof files import only Agda's bundled `Agda.Builtin` modules. The project has no separate `agda-stdlib` Cabal dependency, and neither Agda proof imports the standard library. One source-checkout detail matters: Cabal clones the pinned Agda Git repository with its `cubical` and `std-lib` submodules, even though this project does not use those libraries. `agdarsec` is also absent. The Haskell backend does depend on `s-cargot` for its S-expression formatting, which is unrelated to Agda's parser. A cold CI run compiles the pinned Agda 2.8.0.2 Haskell package from source because the workflow uses a Cabal `source-repository-package`, rather than a prebuilt Agda executable. The 2026-11-06 PR #27 run had a cache miss: the Agda library build alone took about 9m55s, and the Agda CLI build step took about 16 minutes before saving a roughly 1.46 GB cache. CI caches both the Cabal store and `dist-newstyle`: Cabal treats the pinned `source-repository-package` as a local project package, so its in-place Agda build artifacts live under `dist-newstyle`, not the global store alone. CI saves this cache immediately after a successful Agda CLI build, before proof and fixture gates; later test failures therefore cannot discard the expensive cache seed. Repeated runs with the same GHC, Cabal, and project-file hash can restore it; cache misses and toolchain changes still require rebuilding. Schmitty is an optional SMT automation layer, not a replacement for MALLP semantics or Agda kernel checking. The published Schmitty setup example pins Agda 2.6.2.2, standard library 1.7.1, `agdarsec` 0.5.0, and Schmitty 1.0.1; importing that recipe unchanged would violate this repository's stable 2.8.0.2 pin. Emacs helps interactive proof development: `C-c C-l` loads and type-checks a file; `C-c C-n` normalizes a selected expression and is a computation aid, not a proof check. CI remains the reproducible gate.

Agda's `--polarity` enables its modal-polarity annotations; that is distinct from the project's own positive/negative MALLP formula grammar. `--lossy-unification` enables a unification heuristic; it is not a proof rule.

## Repository constraints

- One pinned stable Agda version (2.8.0.2) supplies both the Agda CLI and the backend's Agda library dependency; both Agda checks run through that CLI.
- Exactly two tracked `.agda` files: compiler semantics and separate physics.
- The tracked Markdown files are this README and `.scratch/wayfinder/verified-agda-forth/MAP.md`.
- No standalone shell/helper scripts and no additional workflow files.
- `src/Agda/Compiler/ToForth.hs` is the only Haskell source allowed to differ from the pinned Agda2Scheme source; CI checks Git blob identity for every other Haskell file.
- The only tracked compiler fixtures are `test/MALLPStrict.agda.src` and `test/gforth/mallp-strict.fs`.

## Verification

CI builds the Agda CLI and backend from the same stable Agda 2.8.0.2 source, type-checks both with-K, rewrite-enabled specifications with that CLI, compiles the closed-Nat fixture, rejects generated legacy-runtime words, and executes the generated program with Gforth. Passing CI establishes those checked properties and fixtures only; it does not prove arbitrary Agda compilation, full MALLP proof-to-code correspondence, or a static dictionary-size bound.
