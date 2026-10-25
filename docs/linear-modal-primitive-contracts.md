# Linear/modal primitive and builtin contracts

Status: inventory and admission policy. This file does not claim that the checked ABI or primitive wrappers described below have all been implemented.

## 1. Rule of admission

A checked module may only call compiler-emitted ABI words listed in the admitted table. Direct target words such as `+`, `-`, `*`, `/`, `mod`, `=`, `>=`, `<`, `IF`, `EXECUTE`, `@`, `!`, `ALLOT`, and dictionary/compilation words are not callable by generated checked terms. They remain fully available to ordinary GForth and legacy Forth sources.

Each ABI primitive contract must state (i) stack effect, (ii) accepted object kinds and modes, (iii) input-resource transition, (iv) output mode derivation, (v) mutation/aliasing effects, and (vi) exception postconditions. A stack-effect comment alone is not a linear/modal contract.

No operation may infer a managed object from a numeric threshold. An unknown handle at checked entry is an error.

## 2. Current backend inventory and policy

The existing backend maps the following Agda Treeless primitives to words in its preamble. Those existing words are legacy/unverified and do not become checked merely because they are named in this table.

| Agda/backend item | Existing lowering | Required checked ABI operation | Current admission status |
|---|---|---|---|
| Natural literal | Emits the numeral as a raw Forth cell | `ABI-MAKE-SCALAR ( cell mode -- handle )`, with mode evidence emitted by compiler | Not yet emitted by compiler |
| `PAdd` | `add`: forces both operands then calls native `+` | `ABI-NAT-ADD ( scalar scalar result-mode -- scalar )` | Forbidden until Nat semantics and overflow are defined |
| `PSub` | `sub`: forces both operands then native `-` | `ABI-NAT-SUB ( scalar scalar result-mode -- scalar )` if this is a Nat operation; otherwise typed signed subtraction is a separate primitive | Forbidden until source operation semantics are known |
| `PMul` | `mul`: forces both operands then native `*` | `ABI-NAT-MUL ( scalar scalar result-mode -- scalar )` | Forbidden until arbitrary-precision behavior or a sound bounded domain is implemented |
| `PQuot` | `quot`: native `/` | `ABI-NAT-QUOT ( scalar scalar result-mode -- scalar )` with nonzero divisor and specified rounding semantics | Forbidden until source semantics, division-by-zero and numeric domain are specified |
| `PRem` | `rem`: native `mod` | `ABI-NAT-REM ( scalar scalar result-mode -- scalar )` with nonzero divisor and specified sign semantics | Forbidden until source semantics, division-by-zero and numeric domain are specified |
| `PIf` | `iff`: native `IF/ELSE/THEN` | `ABI-IF ( bool thunk thunk -- result )`; validate Bool representation and consume/transfer only the chosen branch resources | Forbidden until branch evaluation and resource effects are specified |
| `PEqI` | `eq`: native `=` | `ABI-NAT-EQ ( scalar scalar result-mode -- bool-scalar )` | Forbidden until numeric representation/mode effects are specified |
| `PGeq` | `geq`: native `>=` | `ABI-NAT-GEQ ( scalar scalar result-mode -- bool-scalar )` | Forbidden until numeric representation/mode effects are specified |
| `PLt` | `lt`: native `<` | `ABI-NAT-LT ( scalar scalar result-mode -- bool-scalar )` | Forbidden until numeric representation/mode effects are specified |
| Built-in natural subtraction | Special-cased as `monus` | `ABI-NAT-MONUS ( scalar scalar result-mode -- scalar )` | Forbidden until exact Nat representation/semantics are implemented |
| Constructor/record | Allocates a Forth array and fills fields | `ABI-MAKE-CONSTRUCTOR ( tag fields... -- value )`; all field resource identities and modalities must be transferred/accounted for | Not yet emitted by checked compiler |
| Function/lambda | Forth word/XT plus `makeTHUNK`/capture helpers | `ABI-MAKE-CLOSURE`, with verified code identifier, input/effect contract and managed environment | Not yet emitted by checked compiler |
| Application/partial application | Emits `pass` | `ABI-PASS`; must derive closure mode and record exact linear capture transfer | Existing `pass` is legacy/unverified for complete end-to-end enforcement |
| Force/evaluation | Emits `dethunk` or `deepdethunk` in runtime paths | `ABI-FORCE`; contract includes result mode, capture accounting, and exceptional outcomes | Existing force path is not a proved checked implementation |
| Unsupported literal/primitive | Historically emitted a Forth word that printed an error and executed `bye` | Compiler error with a diagnostic and non-success compile status | Compile-time rejection has been changed in `ToForth.hs`; CI result for that change still needs verification |
| Unreachable Treeless branch | Runtime panic/error | `ABI-ERROR-UNREACHABLE ( -- )` uses a named Gforth exception code and `THROW` | Runtime word added; not yet CI-verified on the latest branch |

## 3. Required contracts for scalar operations

### Scalar representation

The current runtime now has a tracked scalar descriptor constructor, `ABI-MAKE-SCALAR ( value mode -- handle )`, plus a scalar kind and stable identity. This is still a trusted boundary: the supplied mode must come from a sound compiler emission/validation path. Forth code can manually lie about a mode, so this word alone is not a source-level proof.

A checked scalar contains a cell payload today. That representation is not equivalent to unbounded Agda `Nat`. A complete semantics-preserving ABI must choose one of:

1. an arbitrary-precision natural representation and arithmetic implementation; or
2. a restricted, explicitly declared numeric subset whose range proof is part of compilation and whose out-of-range cases are rejected before execution.

Using native cell arithmetic without overflow/division semantics is not an acceptable proof of Agda Nat correctness. Until the numeric representation and arithmetic are completed, the corresponding arithmetic primitives stay outside the claimed checked subset.

### Common operand transition

A future binary scalar wrapper must perform validation before mutating ownership:

1. Check both handles are registered, live, scalar-kind, and have known modes.
2. Check operand aliasing: the same linear token cannot fill both input positions.
3. Check divisor/other primitive-specific preconditions.
4. Compute or allocate the result without consuming inputs.
5. Construct a result with the output mode emitted by the compiler's checked contract.
6. Only after successful construction, mark linear input handles consumed. Modal input handles remain live.
7. If failure occurs after arbitrary effectful execution starts, follow a primitive-specific exceptional postcondition that accounts for every input and in-flight resource.

The output mode is not generally derived as “linear if either input is linear”. That rule is appropriate for some partial-application closures that capture linear resources, but a primitive's result mode is determined by its source contract and must be emitted by the compiler. Modal result constructors must be allowed only when the payload is modal-safe.

## 4. Bool and conditional contracts

The legacy representation uses numeric cells for booleans (`-1` and `0`). The checked ABI must not treat arbitrary numbers as booleans. It must validate a Bool tag/value and give Bool results an explicit mode/ownership contract.

The conditional wrapper must specify whether both branch closures are already created, whether the unchosen branch contains captured linear resources, and how those resources are disposed of. A linear value captured by an unchosen branch must not be silently leaked or silently consumed. Until this branch-resource rule is specified and tested, direct target `IF/ELSE/THEN` is forbidden in checked generated code.

## 5. Memory, closure, constructor and effectful words

The following words remain available to ordinary Forth programs but are forbidden in compiler-generated checked bodies except through a named, audited wrapper:

- Memory/dictionary: `@`, `!`, `+!`, `HERE`, `ALLOT`, raw address arithmetic, `MOVE`, `ERASE`.
- Execution/compilation: `EXECUTE`, `COMPILE,`, `POSTPONE`, `:`, `;`, immediate words, `IS`, and arbitrary execution-token registration.
- Stack/return stack: `DUP`, `DROP`, `SWAP`, `ROT`, `>R`, `R>`, `2R>` unless codegen is using an ABI wrapper whose contract tracks every value affected.
- I/O and external side effects: file, terminal, host, and environment words until their mode/effect/error contracts are stated.

This restriction applies only to the code the checked compiler emits or admits. It does not change GForth itself, and it does not make an arbitrary handwritten Forth word safe.

## 6. Legacy compatibility contract

The checked ABI is an additive interface. It must not redefine the semantics of existing GForth words. Existing `FLib.fth` words remain callable with their legacy stack effects for old clients, but they are not covered by the new checked guarantee unless a tested adapter proves that their use goes through the closed ABI.

Compatibility tests must cover:
- existing direct Forth clients and all documented legacy entry-word stack effects;
- supported old Agda fixtures compiled and run as before;
- checked output using only the versioned ABI and rejected if it uses an unsupported word;
- compiler errors for unsupported constructs, with no output artifact accepted as successful checked code.

A passing ordinary smoke test is not a proof that all of these compatibility conditions hold.
