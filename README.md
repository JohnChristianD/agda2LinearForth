# agda2MALLPForth

A verified-compiler research project for Olivier Laurent's multiplicative-additive polarized linear logic (MALLP), Agda formal semantics, and GNU Gforth. The currently executable compiler slice is deliberately narrower: **strict, closed Nat expressions only**, lowered to postfix stack code. The broader goal is a compositional MALLP-to-Forth compiler with a proof-preserving semantics. The current Nat runtime has no heap, closure objects, thunk updates, garbage collector, descriptor table, or dynamic allocator; those are facts about this checked slice, not a claim that every future MALLP implementation must avoid closures or suspensions.

The project has two separate Agda files:

- `formal/MALLPForth.agda`: a `--with-K --rewriting --confluence-check --polarity --lossy-unification` compiler specification. It contains six foundational packages, constructive coinductive conaturals, Laurent's polarized MALLP sequent calculus, and indexed strict Forth stack-code semantics. The calculus is currently a proof-tree syntax; it does not yet have computational proof terms, a Hamano–Scott categorical interpretation, or a derivation-to-Forth translation.
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

## MALLP semantics and runtime representations

The MALLP fragment follows Laurent's polarized syntax as studied by Hamano and Scott. Positive formulas use tensor, plus, and the positive unit/zero; negative formulas use par, with, and the negative units; the polarity shifts `↑` and `↓` connect the two classes. This is the linear fragment: the calculus has no `!`/`?` exponentials and no weakening or contraction rules. See [Hamano and Scott, *A categorical semantics for polarized MALL*](https://doi.org/10.1016/j.apal.2006.09.001).

Keep three layers separate:

1. **Logic:** MALLP formulas and derivations express polarized linear resource use.
2. **Denotation:** Hamano–Scott interpret MALLP in an ambient *-autonomous category with products, using reflective/coreflective polarized subcategories and their adjunctions.
3. **Execution:** closures, environments, thunks, stacks, and heaps are implementation representations. They are not MALLP connectives and do not follow automatically from the categorical model.

The current `MALLP` datatype is a derivation tree, not yet a term language. A future computational interpretation may use closures when it represents higher-order proof terms as executable functions. Such a closure can be linear: its code and captured environment move together, and application consumes the captured linear resources according to the typing judgment. A duplicable closure that silently copies a captured linear environment would violate the calculus.

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

PureCake is a useful model for the *whole proof architecture*: it defines source and intermediate-language semantics, proves each compilation pass correct, and composes the results through CakeML to machine code. Its formal PureLang numeric carrier is HOL4's mathematical `int`, not merely `Nat`: the built-in semantics defines integer addition, subtraction, multiplication, division, remainder, and comparisons. Its examples include an unbounded lazy `[Integer]` stream and factorials over `Integer`. PureCake's source semantics uses call-by-name evaluation; its compiler then lowers through explicit intermediate languages, including call-by-value ThunkLang, EnvLang, and StateLang. Thunks are introduced and then optimized as part of that particular lazy-language compilation strategy.

That result does **not** supply an exact-rational or exact-real development. PureCake does not establish a rational quotient construction, an untruncated co-dyadic representation, a Cauchy/modulus theorem, or Escardó-style searchable-type results. Those mathematical structures and their equality/search principles still need their own formal definitions and proofs. PureCake can serve as a compiler-correctness blueprint for programs using such structures once they are defined, but its compiler theorem does not create those number systems for us.

The present RSED file is more limited than that target: `RationalRingInterface` is an abstract algebraic interface, and `ConatStream A` supports productive observations while `foldConatPrefix` deliberately consumes a finite observation budget. This is useful stream infrastructure, not yet a concrete rational implementation or a proof of an untruncated real/codyad representation.

PureCake's thunk pipeline is an architectural precedent, not a runtime recipe to copy wholesale. Its source/target evaluation strategies and explicit thunk transformations answer needs of a lazy functional source language. For MALLP, a shared thunk is sound only when its captured resources may be shared; a one-shot suspension or a defunctionalized representation may better preserve linear usage.

The current Agda theorem covers the closed-Nat expression AST, its code AST, indexed stack execution and preservation of the residual stack. `ToForth.hs` is still a separate Haskell implementation of the lowering and textual printer. CI compiles examples and executes their generated Gforth files, but there is not yet a kernel proof that the Haskell printer emits exactly `renderForth`, nor a formal refinement theorem for the Gforth interpreter. Therefore this is **not yet an end-to-end verified compiler in the PureCake sense**.

## Development tools and scope

The supported and CI-verified build path is **GHC + Cabal**. The workflow selects GHC 9.2.8 and Cabal 3.10.3.0, then builds both the Agda CLI and `agda2forth` with Cabal. `cabal.project` pins the Agda Git source tag `v2.8.0.2`; CI checks the built executable's numeric version before using it for both Agda files.

A root `stack.yaml` **does exist**, but it is a legacy configuration: it selects Stackage LTS 19.4 and pins `s-cargot-0.1.4.0`. That snapshot contains Agda 2.6.2.2, while this fork's `agda2forth.cabal` requires Agda `>= 2.8.0.2 && < 2.9`. The current Stack resolver therefore cannot satisfy this package's declared Agda bound. Stack itself is not obsolete and Agda 2.8.0.2 is available in modern Stackage snapshots (including LTS 24.65); what is stale is this repository's LTS 19.4 pin. Until a Stack resolver and its dependency plan are updated and tested against this fork, treat `stack.yaml` as **legacy and unsupported for this project**, not as a second verified build path.

The upstream repositories differ: current `jespercockx/agda2scheme` has a Cabal package and a Cabal-based GitHub Actions workflow, but no `stack.yaml`; the older `LMMilliken/agda2Forth` repository has both a `.cabal` package file and an LTS 19.4 `stack.yaml`. These files can coexist because the `.cabal` file describes package metadata/dependencies, while `stack.yaml` selects Stack's resolver and project plan. Coexistence does not mean both plans select the same Agda version. PureCake is a separate HOL4/PolyML/Holmake build, not a Stack project.

The proof files import only Agda's bundled `Agda.Builtin` modules. The project has no separate `agda-stdlib` Cabal dependency, and neither Agda proof imports the standard library. One source-checkout detail matters: Cabal clones the pinned Agda Git repository with its `cubical` and `std-lib` submodules, even though this project does not use those libraries. `agdarsec` is also absent. The Haskell backend does depend on `s-cargot` for its S-expression formatting, which is unrelated to Agda's parser. A cold CI run compiles the pinned Agda 2.8.0.2 Haskell package from source because the workflow uses a Cabal `source-repository-package`, rather than a prebuilt Agda executable. The 2026-11-06 PR #27 run had a cache miss: the Agda library build alone took about 9m55s, and the Agda CLI build step took about 16 minutes before saving a roughly 1.46 GB cache. CI caches both the Cabal store and `dist-newstyle`: Cabal treats the pinned `source-repository-package` as a local project package, so its in-place Agda build artifacts live under `dist-newstyle`, not the global store alone. CI saves this cache immediately after a successful Agda CLI build, before proof and fixture gates; later test failures therefore cannot discard the expensive cache seed. Repeated runs with the same GHC, Cabal, and project-file hash can restore it; cache misses and toolchain changes still require rebuilding. Schmitty is an optional SMT automation layer, not a replacement for MALLP semantics or Agda kernel checking. The published Schmitty setup example pins Agda 2.6.2.2, standard library 1.7.1, `agdarsec` 0.5.0, and Schmitty 1.0.1; importing that recipe unchanged would violate this repository's stable 2.8.0.2 pin. Emacs helps interactive proof development: `C-c C-l` loads and type-checks a file; `C-c C-n` normalizes a selected expression and is a computation aid, not a proof check. CI remains the reproducible gate.

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
