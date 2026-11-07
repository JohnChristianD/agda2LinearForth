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

The reference pipeline is staged: PureLang source and interaction semantics lower through ThunkLang, then EnvLang, then StateLang, and finally CakeML. PureLang-to-ThunkLang makes delay/force explicit; ThunkLang-to-EnvLang introduces environment-based execution; EnvLang-to-StateLang makes mutable thunk allocation, forcing and update explicit. The PureCake proof development establishes preservation across those passes (including the PureLang-to-CakeML theorem chain). This project must mirror those semantic boundaries instead of treating them as a collection of syntax cases.

Reference source: [PureLang semantics](https://github.com/CakeML/pure/blob/master/compiler/backend/languages/semantics/pureLangScript.sml), [ThunkLang semantics](https://github.com/CakeML/pure/blob/master/compiler/backend/languages/semantics/thunkLangScript.sml), [PureLang-to-ThunkLang](https://github.com/CakeML/pure/blob/master/compiler/backend/passes/pure_to_thunkScript.sml), [ThunkLang-to-EnvLang](https://github.com/CakeML/pure/blob/master/compiler/backend/passes/thunk_to_envScript.sml), [EnvLang-to-StateLang](https://github.com/CakeML/pure/blob/master/compiler/backend/passes/env_to_stateScript.sml), and [PureCake correctness proofs](https://github.com/CakeML/pure/blob/master/compiler/backend/passes/proofs/pure_to_cakeProofScript.sml).

A stateless delayed expression and a stateful memoized thunk are different semantics: repeated forcing of a pure delayed expression may re-run it, while the stateful translation updates and reuses a stored result. The MALLP target must prove ownership of the state token whenever it represents this sharing. A closed-expression substitution is not a substitute for a memoized thunk.

- **Functions and closures:** a closure owns its captured environment. Application consumes the function/argument resources according to the MALLP judgement.
- **Local bindings:** unused closed pure bindings can be skipped; closed pure bindings can be inlined at multiple uses. Bindings that capture resources need a usage proof.
- **Data and pattern matching:** constructors own their fields; elimination consumes the scrutinee; case alternatives must satisfy the additive branch contract.
- **Laziness:** delay/force and demand behavior must be modeled explicitly where they affect observations. A one-shot suspension is different from a memoized shared thunk.
- **Sharing and state:** call-by-need updates may be represented only with an explicit, linearly owned state/store token and a proved state simulation. Repeated aliasing cannot be smuggled in as contraction.
- **Recursion:** admit source recursion when a finite MALLP derivation and the PureCake semantics can justify it (for example, through a specified primitive recursor). General recursive/fixpoint behavior is not added as a new MALLP connective.
- **Effects:** monadic effects, arrays, exceptions, and FFI are not rejected merely by name. They require a declared operation signature, an explicit linear state/effect protocol, and a matching target semantics. The target remains free of direct IO sites; effect behavior must be represented by a proved explicit protocol. Unsupported effects fail with a diagnostic.

## Agda 2.8.0.2 builtin and reflection choices

The backend and proof modules are pinned to Agda 2.8.0.2. Use the actual modules from that release rather than guessed module names:

| Need | Available module | Project decision |
|---|---|---|
| Universe levels | `Agda.Primitive` | No direct import is needed in `MALLPForth.agda` unless a declaration explicitly manipulates `Level`; `Agda.Builtin.Sigma` already imports it for universe-polymorphic pairs. |
| Empty type | No `Agda.Builtin.Empty` or `Agda.Primitive.Empty` | Keep the small local `⊥` definition; use standard-library `Data.Empty` only when the library is an explicit dependency. |
| Coercion | No `Agda.Builtin.Coercion` | Coercions are source/compiler constructs (for example, Agda's Treeless `TCoerce`), not a builtin source datatype to import. |
| Universe alias | No `Agda.Builtin.Universe` | Use `Agda.Primitive` for `Set`, `Level`, and level operations. |
| Pair / dependent pair | No `Agda.Builtin.Tuple` | Use `Agda.Builtin.Sigma` for dependent pairs, or an explicit project product type when its tensor/resource meaning matters. |
| Signed integers | `Agda.Builtin.Int` | The builtin is `Int`, with `pos` and `negsuc`; there is no `Agda.Builtin.Integer`. |
| Unit and lists | `Agda.Builtin.Unit`, `Agda.Builtin.List` | Use these canonical builtin declarations. |
| Coinduction | `Agda.Builtin.Coinduction` | Provides `∞`, `♯_`, and `♭`; productivity still needs guarded definitions and observation proofs. |
| Strings and parsing substrate | `Agda.Builtin.String`, `Agda.Builtin.String.Properties`, `Agda.Builtin.Char`, `Agda.Builtin.List` | `primStringToList` / `primStringFromList` expose characters; `primStringToListInjective` and `primStringFromListInjective` prove round-trip equality. These are representation lemmas, not a lexer or parser. |
| Reflection identities | `Agda.Builtin.Reflection`, `Agda.Builtin.Reflection.Properties` | `primQNameToWord64sInjective` and `primMetaToNatInjective` support propositional equality for reflected names/metavariables. They do not provide quotient formation or extensional equality. |
| Compile-time reflection | `Agda.Builtin.Reflection` | Available for macros that inspect resolved `Term`, `Type`, `Definition`, `Clause`, and `Pattern`, then generate typed declarations or witnesses. |

Reflection is a compile-time elaboration facility, not a replacement for a typed source IR or a semantics proof. `reflectDataShape` currently derives constructor-shape metadata; Agda then type-checks the generated witness. Runtime values, resource ownership, thunk updates, and Forth execution still require explicit syntax, interpretation, and simulation theorems. The Haskell backend already reads resolved Agda definitions, telescopes, and Treeless terms; reflection should remove duplicated metadata or proof boilerplate, not merely move a whitelist into a macro.

### Hofmann-style quotient types: audit result

The public sources inspected for this compiler and `JohnChristianD/Deep-Watkins-Monoid-LSTM` do **not** contain a Hofmann-style quotient type, quotient eliminator, quotient-induction interface, or a quotient-reflection implementation. In this compiler repository, `Foundations` is a nested module in `formal/MALLPForth.agda`, not a separate imported library directory. Its six publicly opened submodules are `ForsterEnumerability`, `MarkovLeastWitness`, `MacLaneCoherence`, `CohesiveRetractions`, `SymmetricBarRecursion`, and `LaurentPolarizedMALLP`. They expose the corresponding records, search/bar-recursion contracts, coherence normalizer, and Laurent proof rules; none defines quotient formation or quotient elimination. `ContextPermutation` is proof-relevant and explicit. Its nearby comment deliberately says contexts are presented without quotient equality or setoids.

The other public repository has an equality-substrate comment and reflection utilities, but the inspected main-branch sources do not supply the missing quotient construction either. Thus the earlier wording that grouped `reflectDataShape` or the `Foundations.*` surface with quotient reflection was inaccurate: metadata reflection and user rewrite rules are present; Hofmann quotient reflection is not.

This is a meaningful omission for faux-extensionality, quotient-normalized contexts, and reusable tactics. Hofmann-style quotients are a type-theoretic interface with a relation-respecting eliminator and computation principles; they are not furnished by `Agda.Builtin.Reflection`. Fiore, Pitts, and Steenkamp's QW-type development uses strictly positive Hofmann-style quotients together with UIP and size types, and its accompanying Agda development explicitly declares the quotient assumptions. That is a literature-backed design route, but importing a quotient interface also adds a trust boundary and coherence obligations. It should be introduced as a named quotient package with its equivalence relation, quotient map, eliminator, respectfulness, computation rules, and model/consistency assumptions—not simulated by an indiscriminate rewrite rule.

The compiler's current finite context permutation can remain proof-relevant for the first verified slice. A quotient of contexts by permutation may shorten client proofs, but the quotient must preserve the linear-resource action and transport each derivation/stack environment coherently. Quotient equality does not itself implement a permutation program or prove that Forth `ROLL` realizes it.

### MALLP parsing and string manipulation

The current frontend does **not** parse MALLP source text. `PolType`, `MALLP`, and `LinearTerm` are Agda datatypes; the backend consumes Agda's resolved definitions and Treeless terms. The Forth side uses a typed token AST and a renderer. `Agda.Builtin.String.Properties` is useful for proving that equal character lists imply equal strings (and vice versa through the corresponding injectivity theorem), but it supplies no tokenization, precedence handling, grammar, diagnostics, or parser-correctness theorem.

For textual MALLP input, tokenize `primStringToList input` into a character stream and parse directly into `PolType` or a surface AST. Prove at least parser soundness, a parse/print round trip on canonical syntax, and rejection/diagnostic behavior for malformed input. Keep pretty-printing separate from semantic normalization. Reflection can generate typed formulas from quoted Agda syntax; it is not a replacement for a parser of arbitrary text. The Haskell frontend's existing Treeless path should remain the source compiler input unless a separate textual MALLP frontend is explicitly added.

### Quotient reflection, rewrite systems, and the C-series

The public GitHub tree for this repository currently contains no `Foundations.*` module and no imported Hofmann-style quotient-reflection development. The earlier project map did not establish that such a library was absent from the author's separate/local RSED-MALLP Agda workspace; that workspace has not been compared with this checkout. Until its exact public repository, revision, and module paths are supplied or committed here, quotient reflection must be treated as an external dependency candidate, not as an already integrated project foundation.

The intended role of a Hofmann-style quotient construction is relevant: quotienting syntax by a specified equivalence can support extensional presentations and reduce proof duplication. It does not itself provide equality reflection for arbitrary functions, nor does it make an equivalence computationally decidable. The project must state the carrier, equivalence relation, quotient eliminator/recursor, respectfulness obligations, and any chosen representative/normal-form discipline. A tactic may use reflected syntax and proved quotient laws to synthesize a witness; the resulting witness still has to type-check against the exact MALLP judgement. Reflection is a proof-construction mechanism, not a new logical rule.

The C-series is the stronger organizing principle for compiler correctness here. BCI is a small basis of linear combinators: useful for illustrating identity, composition, and exchange, but underdetermined as a specification of the full polarized MALLP proof language, source semantics, target machine, or compiler. The C-series obligations instead name the correspondence chain that must be made explicit:
1. source typing and resource usage are represented by a typed source term and an actual MALLP derivation;
2. each accepted source construct is translated to a typed target instruction/AST with a resource contract;
3. a target-machine interpreter executes that AST while preserving the indexed stack invariant;
4. emitted Forth text is related to the formal target program by a renderer theorem;
5. concrete Gforth execution is connected to the formal target semantics by a separately established refinement/simulation theorem.

Each edge needs a theorem with explicit hypotheses and observable result. The current project has proofs and fixtures for selected Nat/Bool/Unit fragments and renderer text equality; it does not yet have the general source-decoder-to-MALLP correspondence or arbitrary-program Gforth refinement. C-series is therefore a better specification discipline than treating BCI as the compiler's completeness argument, but its full theorem chain remains work in progress.

### Builtin strings, parsing, and reflection scalability

Agda 2.8.0.2 does provide `Agda.Builtin.String.Properties`. It exposes primitive injectivity facts for conversion between strings and character lists; use it alongside `Agda.Builtin.String`, `Agda.Builtin.Char`, `Agda.Builtin.List`, and the required `Maybe`/`Sigma` builtins. The core string primitives include uncons, conversion to/from character lists, append, equality, and display. This is enough to build a small total scanner/parser over character lists and prove round-trip or injectivity properties. It is not a ready-made MALLP grammar, lexer, parser-combinator library, or normalization engine. Prefer parsing a typed/reflected Agda term directly when the input is already Agda syntax; use a string parser only for an external textual MALLP format, with an explicit grammar and parse-error result.

Importing more builtins can remove local boilerplate, but it does not shorten proofs automatically. Use builtin datatypes where their computational representation matches the intended meaning. Keep a distinct tensor/resource product when its ownership split matters; ordinary Sigma/product convenience must not erase that distinction.

Global `REWRITE` rules can make quotient laws and canonicalization equations available to conversion, and `--confluence-check` should be enabled when relying on global rewriting. Rule sets must be designed around overlaps and the triangle condition; imported rewrite rules are transitive and affect downstream type checking. Confluence checking is not a proof that a chosen quotient is the intended quotient, and rewrite rules should not be used as an unexamined substitute for a terminating canonicalizer. Local rewrite rules have different limitations and are not a drop-in replacement. For scalability, keep rewrite heads narrow, avoid overlapping orientations, normalize reflected syntax into a small canonical grammar, and make solver procedures return ordinary proof terms that Agda checks.

No project-wide quotient-reflection solver or confluent rewrite basis is claimed by the current checked implementation. Add such machinery only with tests for critical overlaps, type preservation, normalization behavior, and generated-proof correctness.

## Relational denotation of bare MALLP

The Agda module `MALLPRelationalDenotation` is now a proof-recursive, Set-valued relational interpretation parameterized by atomic meanings. It assigns positive and negative values compositionally: multiplicatives are paired resources, additives are tagged alternatives, `1`/`⊥` are interpreted by the unit object, `0`/`⊤` by the empty type, and polarity shifts exchange the positive and negative value interpretations.

`MALLPRelation` interprets every constructor of the existing `MALLP` datatype. Axiom uses the duality conversion; cut carries an explicit intermediate value witness; exchange reindexes an environment by the inverse context permutation; tensor splits its environment; plus introduces a tagged result; par unpacks a pair; with selects an alternative; bottom and top use their unit/empty denotations; down and up transport the value across the polarity shift. This gives a compositional relational meaning to arbitrary *bare MALLP derivations*, rather than relying on I/B/C combinators as a substitute for the logic.

This is a concrete relational semantics for the proof system, **not yet the full Hamano–Scott categorical model**. That model requires an explicit ambient *-autonomous category with products, reflective/coreflective full subcategories, and the adjunction data connecting the two polarities. The Agda development does not yet define those categories, functors, units/counits, naturality/coherence laws, or the completeness results from Hamano–Scott. Do not call the current relational interpretation a completed Hamano–Scott model.

The BCI witnesses remain useful examples of linear terms and explicit exchange. Their application contract still resides in `MALLPProtocolTheory` under `primitive-linear-apply`; those witnesses are not derivations of application from bare MALLP. The new relational interpretation supplies semantics for the actual MALLP proof rules, but does not silently discharge that separate application contract or connect it to Haskell closure code generation.

## Current implementation

The checked end-to-end fragment remains intentionally small:

- Closed Nat literals; Nat addition, natural subtraction (monus), and multiplication.
- Nonrecursive closed Nat lets, including unused and multiply-used bindings. These are substituted before Forth rendering; multiple uses expand into separate copies of a closed expression.
- Unary `Nat → Nat` functions with exactly one use of their live argument. The compiler recognizes a one-argument Nat telescope, checks the Treeless lambda arity, and lowers argument references through an indexed stack contract. Both operand orders with closed operands are supported.
- Binary `Nat → Nat → Nat` primitive functions whose body applies one declared Nat primitive to the two arguments exactly once each. The compiler checks the two-argument telescope and Treeless lambda arity, handles direct or exchanged de Bruijn argument order, and emits only the primitive operation plus `SWAP` when exchange is required.
- Three-or-more-argument Nat functions whose arithmetic expression tree consumes every top-level argument exactly once. Closed literals and nested binary primitives are supported, as are single-use local bindings capturing linear arguments. A depth-indexed `ROLL` moves each selected live resource above already-computed sibling results; a usage pass rejects missing, repeated, or out-of-scope resources before rendering.
- Acyclic first-order Nat helper calls are recursively lowered by inlining their Treeless bodies and substituting argument resource trees in de Bruijn order. The caller's final resource check proves each original argument is consumed once across the expanded call. Recursive and mutually recursive call graphs are diagnosed pending a separately proved primitive-recursion lowering.
- Closed Boolean constructors: `true` and `false`, represented by the additive MALLP formula `1 ⊕ 1` and emitted as Gforth `TRUE` / `FALSE` values.
- Linear Bool-argument functions with additive pattern matching. Treeless `TCase` branches and Agda 2.8.0.2's equal-branch `PSeq` lowering are reconstructed as an additive conditional: the scrutinee is consumed exactly once, and both branches receive the same residual resource context. The `chooseBool : Bool → Bool → Bool` fixture compiles as `SWAP IF ELSE THEN` and returns the other live Boolean on either branch.
- A two-field `BoolPair` product with a consuming pattern match and field swap. Agda's resolved datatype and constructor signatures establish the closed single-constructor product shape; the decoder checks both fields are used exactly once. Its function lowers as `SWAP`, and its source type is represented by MALLP tensor `Bool ⊗ Bool`; tensor introduction, exchange, and par introduction derive its proof without weakening or contraction.
- Pure `Unit`: the MALLP multiplicative unit `1`, compiled as an empty Forth word that preserves the caller's stack.
- Bounded-cell Gforth Nat runtime with explicit negative/overflow checks.

`TPrim PSub` remains rejected as Nat monus: it denotes signed integer subtraction. Nat monus is handled through Agda's Nat subtraction builtin.

The Agda specification contains Laurent's polarized MALLP proof-tree calculus, a focused Nat primitive theory, linear unary (`NatLinearExpr`) and binary (`NatBinaryLinearExpr`) Nat function proof terms with exactly one and two live assumptions respectively, plus a general count-indexed `NatResourceExpr` proof tree that partitions any finite number of live assumptions using MALLP cut and explicit exchange. The new `natResourceForthTokens` compiler and `natResourceMALLP-forth-sound` theorem establish a formal target-token simulation for every such finite resource tree, including arbitrary active sibling results and residual stack values. The indexed Forth model uses `SWAP` and depth-indexed `ROLL` for resource selection, a Boolean encoding as the additive formula `1 ⊕ 1`, and Unit as the multiplicative formula `1`. The formal module also includes a generic `LinearSourceType` / `LinearTerm` core (Nat, Int, Bool, Unit, tensor, sum, and linear-function types) with context-indexed variables, exchange, tensor introduction/elimination, additive introduction/case, cut, lambda introduction, and an environment-owning closure constructor; `deriveMALLP` translates each term constructor structurally into the existing MALLP rules. `boolProofDerivation` builds the two Boolean introductions from `mallp-plus-left` / `mallp-plus-right` and `mallp-one`; `boolMALLP-forth-sound` proves the rendered Boolean token has the same value as its MALLP proof. `boolCaseWithResidualMALLP` uses the additive `mallp-with` rule to give both exclusive branches the same live residual assumption; `compileBoolCaseWithResidual` lowers that case to `SWAP IF ... ELSE ... THEN`; `boolCaseWithResidualMALLP-forth-sound` proves its token execution preserves the selected residual value; and `boolCaseWithResidual-token-correspondence` identifies the formal control-flow tokens. The generated renderer certificate additionally compares the Haskell compiler's actual `chooseBool` token list with `mapBoolForthTokensAsText (renderBoolCode compileBoolCaseWithResidual)` by `refl`. `unitProof` is `mallp-one`, and `unitMALLP-forth-sound` proves the empty Forth lowering preserves the caller's residual stack. `natMALLP-forth-sound` proves the closed Nat AST, indexed Forth stack code, and abstract postfix-token interpreter agree while preserving the residual stack. `natLinearMALLP-forth-sound` connects unary linear Nat proof interpretation with indexed Forth/token execution; `natBinaryMALLP-forth-sound` does the same for two-argument primitive functions and their two-assumption MALLP derivations. The indexed target adds `StackAt`, `rollNat`, `rollStack`, `rollWord`, and `rollList-correct`, proving the ROLL permutation for every witnessed live stack depth. The closed-local-let model adds `closedNatLocal-proof`, `closedNatLocal-proof-adequate`, and `closedNatLocal-forth-sound`: a closed PureLang-style let expression is inlined and receives a MALLP derivation without weakening or contraction.

The generic Nat resource-tree and ROLL token proofs, the integrated Forth renderer, the Bool additive-case witness, and the BoolPair tensor-swap witness all type-check in CI. The generic LinearTerm layer now derives MALLP proofs for its supported constructors, including closure introduction with an explicitly owned environment. This does not yet prove that the Haskell Treeless decoder maps arbitrary source terms into those typed terms, that the Forth runtime refines the formal machine, or that concrete Gforth is covered by a mechanized simulation theorem. The existing Gforth cell bound also differs from mathematical unbounded Agda Nat; the emitted runtime reports overflow rather than proving arbitrary-precision Nat semantics.

## Current expanded test slice

The Gforth fixture includes unary identity, addition, monus in either operand order, and multiplication, plus binary addition, monus, reversed monus, and multiplication. It also exercises `invertBool` and `chooseBool` across both additive branches, with the second live Boolean preserved and returned. The admitted linear functions must consume each live argument exactly once on every branch. An unused argument or a duplicated live argument is rejected; closed operands may be separately reconstructed.

This is not yet general higher-order PureCake support: no closure environment, user-defined call graph, finite ADT/list lowering, recursive semantics, stateful thunk sharing, or effect handlers are implemented. The Agda proof establishes the formal unary core and abstract token machine, not the Haskell printer or real Gforth implementation.

## Merged PR #33: typed MALLP core and C-series witnesses

The merged PR added the relational MALLP denotation and one narrow backend case. Keep the distinction between a formal source model, an implemented decoder, and an end-to-end verified compiler explicit.

### C-series is the primary correctness architecture; BCI is a small witness fragment

The source type former `linearArrowType A B` is interpreted as the polarized MALLP formula
`↓(A⊥ ⅋ ↑B)`. The linear term core has context-indexed variables, exchange, tensor introduction/elimination, additive injection/case, unit, cut, lambda abstraction, and an environment-owning closure constructor. `deriveMALLP` maps the implemented `LinearTerm` constructors structurally to Laurent's existing rules.

The BCI witnesses are intentionally only examples within the larger C-series architecture. The C-series makes each compiler boundary and its preserved invariant explicit; BCI only describes a restricted combinator fragment and is not a basis for maximal strict Laurent MALLP expressivity or general closure compilation. Treating I/B/C completeness as a substitute for arbitrary MALLP derivations would underdetermine the target semantics.

The BCI witnesses represent:

- **I:** identity, with its sole input consumed once.
- **B:** composition, with three function/argument resources each used once.
- **C:** exchange, implemented by the explicit context permutation.

Application itself is represented in `LinearApplicationTerm` and interpreted through the explicitly declared `primitive-linear-apply` signature in `MALLPProtocolTheory`. This is a typed primitive operation over unchanged MALLP, not a new logical inference rule and not a claim that a Forth closure-call implementation is already verified. The I/B/C terms and their protocol derivations are Agda witnesses; Haskell does not yet compile general higher-order closures or application. The C-series remains the acceptance criterion: each admitted source feature needs a source judgment, exact resource derivation, typed target construction, target semantic theorem, renderer correspondence, and concrete runtime evidence.

This follows the resource interpretation associated with Henry Baker's permutation-stack work: an environment and its argument are owned resources, and stack permutations express exchange. The symmetric monoidal closed interpretation of tensor, unit and internal hom is the separate categorical semantics; Baker's stack-machine construction is not itself the Hamano–Scott categorical model. A full closure compiler still needs an executable closure layout, captured-environment relation, application semantics, and a pass simulation.

### Word64: exact source equality, deliberately narrow target support

The pinned Agda 2.8.0.2 API is `Agda.Builtin.Word`, not an `Agda.Builtin.Word64` module. The formal file imports `Word64`, `primWord64ToNat`, `primWord64FromNat`, and the primitive injectivity theorem `primWord64ToNatInjective`.

The Agda witness `word64EqualityByNat` establishes equivalence between equality of Word64 values and equality of their Nat denotations. `linearWord64IdentityMALLP` gives Word64 one atomic linear resource in the source calculus. The target model treats that source resource as two owned 32-bit cells; `word64IdentityCode-correct` proves the identity program preserves both cells, and `Word64Representation` records the required limb bounds and denotation equation.

The Haskell backend admits only the exact unary identity shape `Word64 → Word64`, emitting an empty body that preserves the two incoming cells. The Gforth fixture checks preservation of a pair of maximum 32-bit limbs. **Word64 literal construction, arbitrary Word64 arithmetic, conversions, division, comparison, and a total representation theorem for every Word64 are not implemented.** The representation record is conditional evidence, not a proof that every Word64 already has a valid pair of Gforth cells.

### Reflection, metaprogramming, and equality

The `reflectDataShape` Agda macro uses `Reflection.getDefinition`, `getType`, constructor metadata, `quoteTC`, and `unify` to inspect a resolved data declaration and construct a typed shape description. Agda then kernel-checks the generated witness. The pair and parameterized-box examples verify constructor arities and parameter/index counts by equality proofs.

This is compile-time metaprogramming over a quoted representation of Agda syntax. It is a useful homoiconic-style interface—programs can inspect and construct descriptions of programs—but reflection is not definitionally identical to object-language equality. The current macro establishes datatype-shape metadata, not arbitrary constructor layouts, linear usage, or a compiler derivation for every reflected datatype.

### Strictness, delay, and call-by-need

The file records Agda's strictness equation using `primForceLemma`: forcing a value before passing it to a continuation has the specified observable equation. PureCake distinguishes call-by-name PureLang evaluation, explicit delay/force in ThunkLang, environment-based execution in EnvLang, and stateful thunk allocation/update in StateLang. These are distinct semantic stages, not synonyms for one eager evaluator.

The project formalizes a total Nat-only `ThunkExpr`, suspended/memoized states, a linearly indexed store token, `forceThunk`, cache idempotence, and stable repeated observations after update. A separate one-token trace protocol specifies resource-preserving effect emission without placing Agda IO sites in the admitted source fragment. These are formal protocol examples, not yet a general PureCake ThunkLang/EnvLang/StateLang lowering in `ToForth.hs`; the current Forth runtime does not allocate or update general heap thunks.

### Data, lists, recursion, and effects

The Agda core derives tensor and sum rules from existing MALLP rules. It includes a Maybe-like `1 ⊕ A` identity witness, reflection-derived constructor-shape metadata, and a finite `NatListValue` with a structurally recursive fold and step/empty equations. The protocol theory contains declared list nil/cons/fold signatures. These establish useful formal vocabulary for linear ADTs and finite recursion.

The Haskell backend still does **not** compile arbitrary reflected ADTs, generic pattern matches, lists, folds, structurally recursive function definitions, delay/force, call-by-need heap updates, or effect protocols. The current list fold is an Agda formal model and signature, not an implementation of PureCake list compilation. General recursion and coinduction need a precise termination/productivity semantics and an admitted derivation/primitive-recursion contract; no new μ/ν connective is added to Laurent MALLP. An explicit state/effect token is the only current effect model; there are no direct IO sites or IO runtime operations.

### Rewrite-system boundary

The actual `formal/MALLPForth.agda` options enable `--rewriting` and `--confluence-check`, and the module imports `Agda.Builtin.Equality.Rewrite`. Four global rules are registered: `μ-step-true`, `μ-step-false`, `sBR-stop`, and `sBR-step`. The first pair unfolds the postulated least-search operator; the latter pair unfolds the symmetric bar-recursion contract. This is real Agda rewriting, not merely a README claim.

`--confluence-check` checks critical overlaps and the triangle condition for the registered system. It does **not** check termination. In particular, `μ-search` is intentionally unbounded when no witness exists, so type-level normalization using that rule can diverge. Agda's rewrite rules are also imported transitively, including rules declared in private scopes and submodules. Keep the global set small, oriented, and semantically justified; use ordinary equality rewriting for local proof steps. Do not turn rewrite rules into an all-purpose solver.

The `reflectDataShape` macro and the `apply-cong` style of tactic are separate mechanisms: reflection constructs candidate syntax/proofs, and the kernel checks the generated term. A scalable tactic should cache reflected declarations, avoid repeated `getType`/`getDefinition` calls, emit small proof terms, and keep expensive search out of global conversion.

The Haskell backend receives Agda's resolved/normalized Treeless output through `toTreeless`; it does not contain an independent, unproved symbolic rewrite engine. `FLib.fth` is the target's operational runtime library: its Nat words define executable arithmetic and error behavior, not Agda's type-theoretic conversion relation. A theorem must relate each admitted source rewrite equation to the denotation of its target operation. Adding rewrite-like text processing to `FLib.fth` would not establish confluence and would conflate compile-time conversion with runtime execution.

### What this PR proves, and what it does not

The new Agda declarations establish source-level equality/resource witnesses for Word64 identity, a BCI application theory, reflection shape examples, strict-force equality, a Nat-only stateful thunk protocol, explicit effect-token transitions, and finite Nat-list fold equations. The Haskell addition compiles only `Word64 → Word64` identity, in addition to previously supported Nat/Bool/BoolPair/Unit slices. CI's generated renderer certificate compares actual emitted definition text with the formal text renderer by `refl`; it does not prove that every Haskell Treeless decoder branch has a formal source derivation, that the Haskell resource analysis is sound for all terms, or that the whole upstream Gforth implementation refines the Agda machine.

The PureCake port remains incomplete. In particular, there is no general higher-order closure code generation, generic ADT/list code generation, certified recursive-call lowering, stateful thunk heap implementation, effect execution backend, or mechanized Gforth refinement theorem. The current PR must not be described as a complete PureCake compiler or an end-to-end verified compiler.

## Implementation frontier

These are implementation tasks, not categorical bans. Each feature graduates to supported only with a typed source representation, usage evidence, lowering, tests, and a semantic-preservation argument.

1. **Typed Treeless front end:** classify every pinned Agda 2.8.0.2 `TTerm`, `TAlt`, `TPrim`, `ArgUsage`, and evaluation-strategy constructor; preserve source types and relevance. Cover variables, lambdas, application, user definitions, and lets.
2. **MALLP term core:** give formulas and proof terms to linear functions, products, sums, units, closures, and branch-sensitive cases. Connect the source usage checker to the actual MALLP derivation; do not rely on ordinary Agda typing as a linearity proof.
3. **PureCake data and control:** add constructor layouts, consuming eliminators, finite ADTs, lists, and control flow with additive branch/resource joins.
4. **Lazy evaluation:** formalize demand, delay/force, closure environments, and the stateful thunk-update behavior needed to match PureCake. Prove resource ownership for every captured value.
5. **Recursion and effects:** identify the source constructs whose behavior admits finite MALLP derivations or declared primitive signatures; prove termination/productivity or state/effect simulation where required. Keep the logical calculus unchanged.
6. **Forth target:** replace direct text construction with a typed, stack-indexed instruction AST, canonical renderer, and explicit runtime contracts for data, state, exceptions, and resource failure.
7. **End-to-end correctness:** prove correspondence from typed Treeless through each lowering pass to the emitted Forth, then prove the relevant Gforth execution simulation.

## C-series correspondence chain

“C-series” is the primary compiler-correctness architecture: each transition preserves a named invariant, and the final identity is a theorem rather than a resemblance. This is more determinate than using BCI as the global logical account: BCI supplies a few linear combinator witnesses, whereas C0–C5 quantify the actual adjacent boundaries required for every admitted strict MALLP source term.

- **C0 — Source judgment:** resolve the pinned Agda 2.8.0.2 Treeless term and its result/argument types. The current decoder establishes this for the admitted Nat, Bool, and Unit cases.
- **C1 — Resource judgment:** associate live Nat and Bool arguments with labelled resources; check exact-once use on every additive Bool path and construct Laurent MALLP derivations over the declared primitive signatures. Closed pure values are closed derivations, not reusable live assumptions.
- **C2 — Target construction:** `natResourceForthTokens` structurally lowers every count-indexed `NatResourceExpr n` into a typed postfix token stream. A resource leaf emits no instruction, `SWAP`, or depth-indexed `ROLL` according to the number of already-computed sibling results; each binary node composes its two subprograms and primitive operation.
- **C3 — Target semantics:** `natResourceForthTokens-correct` proves execution for every count-indexed Nat resource tree, preserving arbitrary active sibling results and the residual stack. `natResourceMALLP-forth-sound` composes this with `natResourceProof-adequate`, connecting arbitrary-arity formal MALLP Nat derivations with the token machine. Bool and Unit retain their separate proofs.
- **C4 — Renderer identity:** Haskell emits `MALLPEmittedRenderer.agda`. For every generated word, Agda checks `actualWord ≡ renderForthWordText name tokens` by `refl`. For `chooseBool`, a second generated theorem, `chooseBoolTokenCorrespondence`, checks that the Haskell compiler's token sequence is exactly the token sequence rendered from the Agda `BoolForthCode` proof.
- **C5 — Concrete runtime:** Gforth executes the generated module and regression fixture. This is currently tested, not yet established by a mechanized refinement theorem for Gforth or the upstream runtime.

The chain is intentionally conjunctive: C4 does not prove C0/C1 correctness, and C5 does not by itself prove formal equivalence. The new general theorem covers count-indexed formal resource trees, but it does not yet prove that Haskell's arbitrary labelled `NatResourceExpr` decoder is reified into that Agda tree or that its `active + position` label selection is identical for every input permutation. Nor does it prove the pinned runtime → formal stack machine or that machine → concrete Gforth behavior. Those are still explicit C0/C1/C2 and C5 obligations.

## Formal and build boundaries

- Agda and the Haskell backend use pinned Agda **2.8.0.2** from `cabal.project`.
- `formal/MALLPForth.agda` contains the MALLP specification, generic linear source-term grammar and derivation function, coinductive Conat core, typed Forth token algebra, canonical text renderer, and abstract target machine. The former `formal/ForthRenderer.agda` has been retired so compiler terms and rendering witnesses share one module.
- `formal/SovereignRationalSEDPhysics.agda` remains a separate library and is not a compiler proof dependency.
- The MALLP proof options and existing postulate boundary are retained; this project does not claim an axiom-free or `--safe` development.
- The backend emits a generated `MALLPEmittedRenderer.agda` certificate beside the Forth module. For each emitted colon definition, the certificate records the actual string produced by Haskell `renderForm`, constructs the formal `ForthTextToken` stream, and asks Agda to prove by `refl` that the emitted definition equals `renderForthWordText`. CI type-checks this generated certificate with pinned Agda 2.8.0.2. This establishes exact text equality for emitted definitions in the fixture, including Nat literals, arithmetic tokens, SWAP, ROLL, Bool literals, and Unit words. For the `chooseBool` additive case, the same certificate also proves the compiler token list equals the text-token image of `renderBoolCode compileBoolCaseWithResidual`, linking the compiler's control-flow lowering to a typed Agda program and its MALLP proof.
- This renderer certificate is one link in the correspondence chain, not the whole compiler-correctness theorem. The new `natResourceMALLP-forth-sound` theorem covers every **count-indexed formal resource tree**, but the Haskell Treeless decoder's labelled-resource AST still lacks a kernel-checked reification theorem into that formal syntax, including its arbitrary context-index/`active + position` calculation. The upstream `FLib.fth` runtime and concrete Gforth execution also lack a formal refinement theorem. The generated equality theorem certifies actual emitted definition text against the Agda renderer, while Gforth fixtures validate concrete execution on tested examples.
- CI checks repository provenance, both tracked Agda files, the Haskell backend, the generated Agda renderer certificate, the Nat/let fixture, generated-code restrictions, and the Gforth integration fixture.

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
