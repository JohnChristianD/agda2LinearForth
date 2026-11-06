---
id: agda-2-8-0-2-inventory
type: research
status: in_progress
blocked_by: []
---

## Question

What is the exhaustive compiler-facing language contract for exact Agda v2.8.0.2?

Inventory every constructor of BuiltinId, PrimitiveId, Treeless TPrim/TTerm/TAlt/CaseType/CaseInfo/TError, plus argument-use and evaluation-strategy metadata. Trace builtin translation and the compiler pipeline. Keep surface/internal PrimitiveId distinct from backend TPrim.

## Evidence gathered

Exact v2.8.0.2 source counts:
- BuiltinId: 203.
- PrimitiveId: 111.
- TTerm: 14 — TVar, TPrim, TDef, TApp, TLam, TLit, TCon, TLet, TCase, TUnit, TSort, TErased, TCoerce, TError.
- TPrim: 23 — PAdd/PAdd64, PSub/PSub64, PMul/PMul64, PQuot/PQuot64, PRem/PRem64, PGeq, PLt/PLt64, PEqI/PEq64/PEqF/PEqS/PEqC/PEqQ, PIf, PSeq, PITo64, P64ToI.
- TAlt: TACon, TAGuard, TALit.
- CaseType: CTData, CTNat, CTInt, CTChar, CTString, CTFloat, CTQName.
- TError: TUnreachable, TMeta.
- CaseInfo fields: caseLazy, caseErased, caseType; ArgUsage: ArgUsed/ArgUnused; EvaluationStrategy: LazyEvaluation/EagerEvaluation.

Treeless invariants:
- TLet is demand-sensitive: bound expression is evaluated only when body uses it; sharing is optional.
- TCase scrutinee is a variable. Constructor alternatives are disjoint and tried before ordered guards.
- TACon binds the specified number of pattern variables; TAGuard binds none; TALit matches literals.
- TUnreachable has undefined/unreachable runtime behavior; compiler may assume unreachable. TMeta must report runtime compilation error.

Exact compiler pipeline:
1. translateBuiltins.
2. Fixed point (at most five iterations) of simplifyTTerm, eraseTerms, caseToSeq, recoverAsPatterns.
3. detectIdentityFunctions.
4. usedArguments fixed point, then stripUnusedArguments when unused args remain under EraseUnused.

Backend currently calls toTreeless EagerEvaluation. This is a semantic choice needing a source-to-core argument, not a consequence of target strictness.

Builtin translation:
- Nat zero/suc translate into integer literals/arithmetic.
- Nat plus/times/less/equality translate to PAdd/PMul/PLt/PEqI.
- Integer pos/negsuc translate into identity and signed arithmetic.
- PrimForce translates into a PSeq-guarded let.
- Nat minus deliberately remains distinct from PSub. Agda source comments: PSub is signed integer subtraction, Nat minus is monus.

Critical boundary:
Current compileNatTerm maps TPrim PSub directly to MALLP-NAT-MONUS, without type evidence. That disagrees with Agda's pinned translation contract. Reject PSub in initial Nat slice unless a typed proof licenses a specific Nat lowering. PAdd and PMul are shared compiler primitives too; lowering to bounded Nat requires source representation and range evidence.

## Remaining result

Create a machine-checked, version-generated manifest with one row per constructor and exactly one disposition: runtime lowering, proof-justified erasure, compile-time/elaboration-only, or runtime rejection. Runtime entries name core op, target family, semantics, and proof relation. Unknown constructors fail closed.

Add version drift check; record frontend and erasure trust boundaries. Inventory counts are not completion proof.

## Primary sources

- https://raw.githubusercontent.com/agda/agda/v2.8.0.2/src/full/Agda/Syntax/Builtin.hs
- https://raw.githubusercontent.com/agda/agda/v2.8.0.2/src/full/Agda/Syntax/Treeless.hs
- https://raw.githubusercontent.com/agda/agda/v2.8.0.2/src/full/Agda/Compiler/ToTreeless.hs
- https://raw.githubusercontent.com/agda/agda/v2.8.0.2/src/full/Agda/Compiler/Treeless/Builtin.hs
- https://raw.githubusercontent.com/agda/agda/v2.8.0.2/src/full/Agda/Compiler/Treeless/Erase.hs
- https://raw.githubusercontent.com/agda/agda/v2.8.0.2/src/full/Agda/Compiler/Treeless/Unused.hs
