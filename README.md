# agda2MALLPForth

A deliberately restricted Agda-to-Gforth compiler. The checked compiler path is **strict, closed Nat expressions only**. It emits postfix stack code and has no runtime heap, closure objects, thunk updates, garbage collector, descriptor table, or dynamic allocator.

The project has two separate Agda files:

- `formal/MALLPForth.agda`: a `--safe --without-K --cubical=no-glue`, builtin-only Laurent-style MALLP formula/sequent fragment plus an indexed Forth stack-code semantics for closed Nat expressions.
- `formal/SovereignRationalSEDPhysics.agda`: the separate RSED physics library. It is not a dependency of the compiler proof.

Both files are checked by the same pinned Agda source version, **2.9.0-rc3**, via `cabal.project` and CI. This is a release candidate, not the stable 2.8.0.2 release. The `--cubical=no-glue` option required by the physics file is supplied by that same compiler.

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

`data/FLib.fth` contains only the bounded strict Nat runtime:

- `MALLP-PARSE-NAT` parses decimal literals and checks the signed-cell limit;
- `MALLP-NAT-ADD` checks overflow before addition;
- `MALLP-NAT-MONUS` implements saturating Nat subtraction;
- `MALLP-NAT-MUL` checks overflow before multiplication.

All three arithmetic words consume exactly two stack operands and return one result. Runtime words allocate no memory. There is no `HERE`, `ALLOT`, `:noname`, descriptor ABI, closure environment, thunk, or garbage collector.

Gforth still stores generated colon definitions in its dictionary when the output file is loaded. This project has no proof of a global dictionary-capacity bound; a sufficiently large generated source file can still exceed the interpreter's available dictionary. The no-allocation statement applies to runtime evaluation of the compiled fragment, not unlimited static code size.

## PureCake / CakeML relationship

PureCake supplies a useful *proof architecture*: define each intermediate language, its operational semantics, and a semantic-preservation theorem for every compiler pass, then compose the theorems. Its lazy PureLang-to-ThunkLang path includes explicit thunk allocation, delay/force and memoized update semantics.

Those lazy semantics are not copied into this target. Shared call-by-need thunks permit multiple references and require a sharing/update heap; that is incompatible with this strict MALLP-only fragment unless an additional sharing discipline is introduced. This compiler instead rejects closures and sharing and uses stack combinators only.

The current Agda theorem covers the closed-Nat expression AST, its code AST, indexed stack execution and preservation of the residual stack. `ToForth.hs` is still a separate Haskell implementation of the lowering and textual printer. CI compiles examples and executes their generated Gforth files, but there is not yet a kernel proof that the Haskell printer emits exactly `renderForth`, nor a formal refinement theorem for the Gforth interpreter. Therefore this is **not yet an end-to-end verified compiler in the PureCake sense**.

## Repository constraints

- One pinned Agda version (2.9.0-rc3) is used by Cabal and both Agda checks.
- Exactly two tracked `.agda` files: compiler semantics and separate physics.
- Exactly one Markdown file: this README.
- No standalone shell/helper scripts and no additional workflow files.
- `src/Agda/Compiler/ToForth.hs` is the only Haskell source allowed to differ from the pinned Agda2Scheme source; CI checks Git blob identity for every other Haskell file.
- The only tracked compiler fixtures are `test/MALLPStrict.agda.src` and `test/gforth/mallp-strict.fs`.

## Verification

CI installs the pinned Agda release candidate, builds the Haskell backend, type-checks both safe Agda modules, compiles the closed-Nat fixture, rejects generated legacy-runtime words, and executes the generated program with Gforth. Passing CI establishes those checked properties and fixtures only; it does not prove arbitrary Agda compilation, full MALLP proof-to-code correspondence, or a static dictionary-size bound.
