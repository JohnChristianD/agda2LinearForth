# agda2MALLPForth

A deliberately restricted Agda-to-Gforth compiler. The checked compiler path is **strict, closed Nat expressions only**. It emits postfix stack code and has no runtime heap, closure objects, thunk updates, garbage collector, descriptor table, or dynamic allocator.

The project has two separate Agda files:

- `formal/MALLPForth.agda`: a `--with-K --rewriting --confluence-check --polarity --lossy-unification` compiler specification. It contains six foundational packages, constructive coinductive conaturals, Laurent's polarized MALLP calculus, and indexed strict Forth stack-code semantics.
- `formal/SovereignRationalSEDPhysics.agda`: the separate RSED physics library, checked by the same Agda 2.8.0.2 CLI under the with-K/rewrite/polarity option family. It remains separate and is not imported by the compiler proof.

Both Agda files and the Haskell backend use one pinned stable Agda source version, **2.8.0.2**, via `cabal.project`. CI builds the Agda CLI and `agda2forth` from that same Cabal source package; it does not install a separate Agda binary. Both specifications use `--with-K`, `--rewriting`, `--confluence-check`, `--polarity`, and `--lossy-unification`; neither is marked `--safe` or `--cubical`. The compiler file retains constructor-based guardedness, while the physics file retains guarded recursion and its existing instance-search/projection options. `--no-prop` is omitted because it is already the default. `--with-K` enables erased matches by default in Agda 2.8.0.2; the explicit `--erased-matches` flag is absent.

The compiler specification retains the original computational rewrite system from `SovereignRationalSED-MALLP.agda`: `μ-step-true`, `μ-step-false`, `sBR-stop`, `sBR-step`, and `lookup-tabulate`. The first four are postulated computation equations; `lookup-tabulate` is proved constructively. Two closed least-search witnesses check that the μ-rules reduce as intended.

Keep the counts distinct: the module contains seven formal components (six foundational packages plus Laurent polarized MALLP), but the global `REWRITE` block registers five rules, not seven. Four registrations (`μ-step-true`, `μ-step-false`, `sBR-stop`, `sBR-step`) are postulated computation equations; `lookup-tabulate` is a constructive theorem. Separately, five postulate blocks declare 20 assumptions, grouped conceptually into least-witness search/choice, cohesive retractions, quotient reflection, and symmetric bar recursion. They are retained as axioms by design. They are not derivable from MALLP, and the MALLP soundness boundary must state which results depend on them. They are not silently presented as an axiom-free or `--safe` proof.

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

This is a constructive linear stack-effect semantics inspired by MALLP's resource discipline. It is **not** a claim that arbitrary Agda terms have been translated into Laurent MALLP proofs. A general source typing/usage judgment and a translation from MALLP derivations into generated words remain future proof work.

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

The MALLP sequent tree and `NatExpr` are currently disjoint. MALLP rules
carry derivation evidence, but no computational proof terms or interpretation
that could be lowered into the Nat compiler. Additive `with` also has two
premises over the same context, so a future translation must model its
environment-controlled branching explicitly rather than assume the
multiplicative stack rule handles it. The code contains no arbitrary MALLP
derivation-to-Forth function, cut-elimination theorem, or semantic-preservation
theorem for such a function.

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

This is the project-level proof boundary. The current PR establishes only the closed-Nat model and integration fixture described above; it does not claim the composed theorem.

## PureCake / CakeML relationship

PureCake is a useful model for the *whole proof architecture*: it defines source and intermediate-language semantics, proves each compilation pass correct, and composes the results through CakeML to machine code. Its formal PureLang numeric carrier is HOL4's mathematical `int`, not merely `Nat`: the built-in semantics defines integer addition, subtraction, multiplication, division, remainder, and comparisons. Its examples include an unbounded lazy `[Integer]` stream and factorials over `Integer`. Thus PureCake is relevant to both signed-integer semantics and productive infinite lists; it does not derive integers from naturals as a separate theorem.

That result does **not** supply an exact-rational or exact-real development. PureCake does not establish a rational quotient construction, an untruncated co-dyadic representation, a Cauchy/modulus theorem, or Escardó-style searchable-type results. Those mathematical structures and their equality/search principles still need their own formal definitions and proofs. PureCake can serve as a compiler-correctness blueprint for programs using such structures once they are defined, but its compiler theorem does not create those number systems for us.

The present RSED file is more limited than that target: `RationalRingInterface` is an abstract algebraic interface, and `ConatStream A` supports productive observations while `foldConatPrefix` deliberately consumes a finite observation budget. This is useful stream infrastructure, not yet a concrete rational implementation or a proof of an untruncated real/codyad representation.

PureCake's call-by-need semantics also should not be transplanted wholesale into the strict Forth fragment. It introduces shared thunks and update state; this compiler currently rejects closures and sharing and uses stack combinators only.

The current Agda theorem covers the closed-Nat expression AST, its code AST, indexed stack execution and preservation of the residual stack. `ToForth.hs` is still a separate Haskell implementation of the lowering and textual printer. CI compiles examples and executes their generated Gforth files, but there is not yet a kernel proof that the Haskell printer emits exactly `renderForth`, nor a formal refinement theorem for the Gforth interpreter. Therefore this is **not yet an end-to-end verified compiler in the PureCake sense**.

## Development tools and scope

The proof files use only Agda's bundled `Agda.Builtin` modules. The Agda standard library package is omitted entirely; those builtin modules ship with Agda itself and are not the separately maintained standard library. `agdarsec` is also absent. The Haskell backend does depend on `s-cargot` for its S-expression formatting, which is unrelated to Agda's parser. A cold CI run compiles the pinned Agda 2.8.0.2 Haskell package from source because both the CLI and backend link against that release. CI now caches the Cabal store by GHC/Cabal and project pins, so later runs can reuse compiled packages; cache misses and toolchain changes still require a rebuild. Schmitty is an optional SMT automation layer, not a replacement for MALLP semantics or Agda kernel checking. The published Schmitty setup example pins Agda 2.6.2.2, standard library 1.7.1, `agdarsec` 0.5.0, and Schmitty 1.0.1; importing that recipe unchanged would violate this repository's stable 2.8.0.2 pin. Emacs helps interactive proof development: `C-c C-l` loads and type-checks a file; `C-c C-n` normalizes a selected expression and is a computation aid, not a proof check. CI remains the reproducible gate.

Agda's `--polarity` enables its modal-polarity annotations; that is distinct from the project's own positive/negative MALLP formula grammar. `--lossy-unification` enables a unification heuristic; it is not a proof rule.

## Repository constraints

- One pinned stable Agda version (2.8.0.2) supplies both the Agda CLI and the backend's Agda library dependency; both Agda checks run through that CLI.
- Exactly two tracked `.agda` files: compiler semantics and separate physics.
- Exactly one Markdown file: this README.
- No standalone shell/helper scripts and no additional workflow files.
- `src/Agda/Compiler/ToForth.hs` is the only Haskell source allowed to differ from the pinned Agda2Scheme source; CI checks Git blob identity for every other Haskell file.
- The only tracked compiler fixtures are `test/MALLPStrict.agda.src` and `test/gforth/mallp-strict.fs`.

## Verification

CI builds the Agda CLI and backend from the same stable Agda 2.8.0.2 source, type-checks both with-K, rewrite-enabled specifications with that CLI, compiles the closed-Nat fixture, rejects generated legacy-runtime words, and executes the generated program with Gforth. Passing CI establishes those checked properties and fixtures only; it does not prove arbitrary Agda compilation, full MALLP proof-to-code correspondence, or a static dictionary-size bound.
