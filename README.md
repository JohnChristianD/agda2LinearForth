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
| String primitives and injectivity | `Agda.Builtin.String`, `Agda.Builtin.String.Properties` | `primStringUncons`, `primStringToList`, and `primStringFromList` support scanning and conversion; the two injectivity lemmas prove round-trip identity, not parsing. |
| Reflection primitive properties | `Agda.Builtin.Reflection.Properties` | Supplies injectivity for `primMetaToNat` and `primQNameToWord64s`; useful for decidable equality on reflected identifiers. |
| Word primitive properties | `Agda.Builtin.Word.Properties` | Supplies `primWord64ToNatInjective`, already used by the Word64 equality proof. |
| Nat equality/properties | `Agda.Builtin.Nat` | Agda 2.8.0.2 has no `Agda.Builtin.Nat.Properties` module. Keep small constructor-injectivity proofs local; importing `Data.Nat.Properties` would require an explicit agda-stdlib dependency, which this project does not currently use. |
| Compile-time reflection | `Agda.Builtin.Reflection` | Available for macros that inspect resolved `Term`, `Type`, `Definition`, `Clause`, and `Pattern`, then generate typed declarations or witnesses. |

Reflection is a compile-time elaboration facility, not a replacement for a typed source IR or a semantics proof. `reflectDataShape` currently derives constructor-shape metadata; Agda then type-checks the generated witness. Runtime values, resource ownership, thunk updates, and Forth execution still require explicit syntax, interpretation, and simulation theorems. The Haskell backend already reads resolved Agda definitions, telescopes, and Treeless terms; reflection should remove duplicated metadata or proof boilerplate, not merely move a whitelist into a macro.

`Agda.Builtin.Word.Properties` is imported and used by `word64EqualityByNat`. `Agda.Builtin.Reflection.Properties` is now imported at real proof call sites: `reflectedNameInjective` uses `primQNameToWord64sInjective`, while `reflectedMetaInjective` uses `primMetaToNatInjective`. These establish injectivity of the builtin encodings; they do not make reflection metadata available at runtime or replace the typed compiler IR. The local Nat/Maybe constructor-injectivity lemmas remain short direct pattern proofs because the pinned builtin release has no matching `.Properties` modules.

### MALLP syntax and strings

There is **no textual MALLP lexer or parser** at present. The logical syntax is the Agda `MALLP` datatype and its constructors; the Haskell backend consumes Agda's resolved Treeless terms, not MALLP source strings.

String is already used at the correct compiler boundary: the Agda-side `ForthTextToken` algebra is rendered by `renderForthTokenText`, `renderForthTokensText`, and `renderForthWordText` into target source. `primShowNat` serializes numeric operands and `primStringAppend` assembles Forth words. The Haskell backend emits the actual `Text`; the generated `MALLPEmittedRenderer.agda` certificate embeds that output as an Agda `String` and checks equality with the Agda renderer by `refl`. Thus String participates in the formal source-rendering correspondence, rather than serving as an untyped substitute for the source AST.

String is not currently used to parse PureCake or MALLP source. The backend consumes Agda's resolved Treeless representation, so a string lexer is not needed for the existing compilation path. `primStringUncons` and `primStringToList` would become useful only for a future text front end; that front end would still need a parser, typed syntax, a context/resource checker, and a soundness proof into `MALLP`. Keep the typed IR and token algebra structured, converting to String only at the rendering boundary.

Agda 2.8.0 added `Reflection.checkFromStringTC : String → Type → TC Term`. It parses and type-checks **Agda source text** against a supplied expected type. It is useful for staged, kernel-checked Agda code generation, but it is not a parser for a separate MALLP grammar. See the [Agda 2.8.0 reflection reference](https://agda.readthedocs.io/en/v2.8.0/language/reflection.html) and the [Agda 2.8.0 release notes](https://github.com/agda/agda/releases/tag/v2.8.0).

## Idempotent extensional quotient reflection

The intended construction is an **idempotent, extensional, non-setoid quotient reflection monad**. Here “extensional” means that equality of quotient representatives corresponds to equality of canonical normal forms:
`qcanon f x ≡ qcanon f y ↔ canonicalize f x ≡ canonicalize f y`.
It does **not** mean global equality reflection for every Agda type, nor does it assume unrestricted function extensionality.

The mathematical ingredients are established in the literature, but they are separate results which must be assembled with a carefully chosen category:

- **Nuo Li / definable quotients.** A quotient is definable from a normalizer when related inputs have equal normal forms and every input is related to its normal form. This covers only quotients admitting such a normalizer; it is not a construction for every equivalence relation.
- **Cedille / quotients by idempotent functions.** Marmaduke, Jenkins, and Stump characterize definable quotients by idempotent endomaps. The quotient carrier is the type of fixed points, and the quotient map sends an input to its canonical fixed point. Cedille's erased dependent-intersection packaging is specific to Cedille; this Agda project deliberately keeps its Sigma witnesses proof-relevant.
- **Idempotent monads / reflections.** An idempotent monad is equivalent, in the usual categorical setting, to a reflective full subcategory. The criterion is that the multiplication `μ : T(T X) → T X` is an isomorphism. This theorem supplies the categorical mechanism, not the quotient carrier by itself.
- **Quotient types / higher inductive types.** A general set quotient can be presented with a point constructor, paths identifying related points, and a truncation constructor. This gives a genuine quotient type without representing the quotient carrier as a setoid, but it is a different type-theoretic feature from a normalizer-defined quotient.

### Literature and design matrix

| Candidate | What the mathematics gives | Non-setoid status | Fit under project Agda settings |
|---|---|---|---|
| Idempotent-function quotient (Cedille; Nuo Li normalizers) | A definable quotient when a sound and complete canonicalizer exists; fixed points form the quotient carrier. | Yes: quotient elements are a type, not a carrier paired with a stored relation. | Direct fit. The Sigma carrier and proofs are retained; no proof erasure is assumed. |
| Reflection from idempotent endomaps | Reflects `(A, f)` into the full subcategory of fixed-point objects `(Fix f, id)`; the unit is canonicalization and multiplication forgets a redundant fixed-point layer. | Yes at the object/carrier level. The category objects store an idempotent endomap, not a setoid relation. | Direct fit. Morphism equality is pointwise; this avoids assuming function extensionality. |
| Arbitrary set quotient as a higher inductive type | Generates paths for each related pair and truncates the quotient to a set. | Yes: equality in the quotient is its native identity type. | Not supplied by this project's ordinary non-cubical Agda core. A HIT/QIT implementation or additional principles would be a separate feature. |
| Extensional type theory | Equality reflection identifies propositional and judgmental equality; function extensionality follows. | Stronger than needed. | Deliberately not adopted: it changes the equality discipline and compromises decidable type checking. |
| General idempotent monad theorem | A fully faithful right adjoint induces an idempotent monad; conversely an idempotent monad determines a reflective subcategory up to equivalence. | Depends on the chosen category; it says nothing by itself about whether objects are represented by setoids. | Implemented for the category of idempotent-endomap presentations, rather than for a category of setoid presentations. |

### Agda contract

For `f : IdempotentEndomap A`, the implementation defines:

- `Quotient A f = Σ A (λ x → canonicalize f x ≡ x)`: the fixed points of `f`, represented by an ordinary Agda type.
- `qcanon f x`: the fixed-point representative `canonicalize f x`, together with its idempotence witness.
- `qcoerce`: projection from a quotient representative back to its carrier element. `qcoerce-qcanon` computes by `refl`; `qcoerce-fixed` exposes the fixed-point invariant.
- `QuotientRelation f x y = canonicalize f x ≡ canonicalize f y`: the kernel relation, derived from the normalizer rather than stored as the quotient object's equality.
- `quotientEquality`: proves that identity between canonical quotient representatives is equivalent to equality of their normal forms.
- `NormalizerFor A R ...`: Nuo Li's soundness/completeness contract. `normalization-idempotent` derives idempotence and `normalization-kernel-equivalence` proves that `R x y` is equivalent to equality of normal forms. `kernelNormalizer` constructs the converse presentation for each idempotent endomap.

This is a single quotient carrier, namely the fixed-point type. `NormalizerFor` remains as a comparison theorem connecting the Nuo Li presentation with the idempotent-function presentation; it is not the object type of the reflection category.

The reflection category now uses `IdempotentObject`, whose data are only a carrier and an idempotent endomap. Its morphisms commute with the normalizers. The reflector sends `(A , f)` to `(Quotient A f , id)`; its unit is `qcanon`, and its multiplication is `qcoerce` on the second fixed-point layer. The category and monad laws are stated using pointwise equality of morphisms, so no function-extensionality axiom is needed. The code packages this as `quotientReflectionMonad : IdempotentMonad idempotentObjectCategory`, and records both inverse laws for multiplication.

The source file uses Agda's existing `--with-K` option and leaves `--no-prop` and `--no-erasure` in force (the Agda defaults). `identityProofUnique` uses K to compare equality witnesses when proving paths in the Sigma fixed-point carrier. It does not use the `Prop` sort, proof erasure, an erased quotient primitive, or Cedille's zero-cost representation. This specific UIP dependency is visible and local; it is not a claim that the construction works unchanged under `--without-K`.

The construction is **non-setoid as a quotient representation**, but it is not a quotient for every equivalence relation: an idempotent normalizer, or equivalently a suitable canonical representative operation, must be supplied. Nuo Li's work explicitly notes that not every quotient admits such a normalizer. For arbitrary equivalence relations, an actual set-quotient HIT/QIT is a different solution. Neither the Cedille paper nor the abstract theorem about idempotent monads says that every quotient operation automatically becomes a monad.

### Rewrite boundary

`QuotientExpr` separates raw and canonicalized syntax. `normalizeQuotient` is a small syntax normalizer, and `quotient-raw` is a definitional `refl` fact that stays local. The semantic denotation and `quotient-raw-sound` theorem are abstract outside the module, so unfolding cannot expose an expanding rewrite over the canonicalizer. The single semantic rule `quotient-raw-sound` is registered in the outer `REWRITE` pragma, oriented from raw syntax to its canonicalized denotation. `quotientReflectionRewriteSmoke = refl` exercises the registered semantic rule.

Agda's `--confluence-check` checks the combined rewrite system; it does not prove termination, general quotient existence, or the categorical laws independently of the checked Agda terms. Operational `ContextPermutation` evidence must remain available wherever source-resource order affects `SWAP`/`ROLL`.

### Foundations module count

There are **seven direct `Foundations.*` submodules**: `ForsterEnumerability`, `MarkovLeastWitness`, `MacLaneCoherence`, `CohesiveRetractions`, `QuotientReflection`, `SymmetricBarRecursion`, and `LaurentPolarizedMALLP`. The first six are the foundational packages; the seventh is Laurent's logical calculus. `FiniteListComputation` is top-level helper code, outside `Foundations`.

### Builtin property modules and small proofs

`Agda.Builtin.Word.Properties` is imported and used by `word64EqualityByNat` through `primWord64ToNatInjective`. `Agda.Builtin.Reflection.Properties` is now imported at real Agda proof call sites: `reflectedNameInjective` uses `primQNameToWord64sInjective`, and `reflectedMetaInjective` uses `primMetaToNatInjective`. These establish injectivity of Agda's reflected encodings; they do not turn reflected identifiers or metavariables into runtime source values, and they do not replace the typed compiler IR. `Agda.Builtin.String.Properties` exists, but its injectivity lemmas have no current call site and are not imported.

There is no `Agda.Builtin.Nat.Properties` or `Agda.Builtin.Maybe.Properties` in the pinned builtin tree. Consequently, the small `suc` and `just` injectivity proofs, plus the disjoint-constructor proofs in `MarkovLeastWitness`, remain direct pattern matches. These proofs are already minimal; replacing them with guessed imports or adding an otherwise-unused standard-library dependency would make the project less accurate and less small.

### Literature alignment

Hofmann's work on extensional concepts and quotient models is important background for setoids, quotient types, and extensional reasoning in intensional type theory. It is not the source of the specific Cedille idempotent-function construction. Nuo Li's normalizer-based definable quotient account and the Cedille paper are the direct mathematical matches for this implementation. Maietti and Rosolini's elementary quotient completion is a distinct, categorical completion construction. Quotient Haskell is a separate Liquid Haskell design, not an Agda or Cedille implementation of this particular carrier.

References: Thorsten Altenkirch, Thomas Anberrée, and Nuo Li, [*Definable Quotients in Type Theory*](https://people.cs.nott.ac.uk/psztxa/publ/defquotients.pdf); Nuo Li, [*Quotient Types in Type Theory*](https://repository.nottingham.ac.uk/entities/publication/526e3896-f764-4153-99d8-6e3e5ef0e509) (2015); Andrew Marmaduke, Christopher Jenkins, and Aaron Stump, [*Quotients by Idempotent Functions in Cedille*](https://cshub.bc.edu/stumpaa/papers/tfp2019.pdf) (TFP 2019); Martin Hofmann and C. J. Rijsbergen, [*Extensional Constructs in Intensional Type Theory*](https://www.cs.ru.nl/~herman/onderwijs/2WI05/hofmann.pdf) (1997); Maria Emilia Maietti and Giuseppe Rosolini, [*Quotient Completion for the Foundation of Constructive Mathematics*](https://arxiv.org/abs/1206.0162) (2012); Hewer and Hutton, [*Quotient Haskell: Lightweight Quotient Types for All*](https://nottingham-repository.worktribe.com/output/27078391/quotient-haskell-lightweight-quotient-types-for-all) (POPL 2024). For the categorical distinction, see nLab's [idempotent monad](https://ncatlab.org/nlab/show/idempotent%2Bmonad) and [reflective subcategory](https://ncatlab.org/nlab/show/reflective%2Bsubcategory) entries.

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

The Agda specification contains Laurent's polarized MALLP proof-tree calculus, a focused Nat primitive theory, linear unary (`NatLinearExpr`) and binary (`NatBinaryLinearExpr`) Nat function proof terms with exactly one and two live assumptions respectively, plus a general count-indexed `NatResourceExpr` proof tree that partitions any finite number of live assumptions using MALLP cut and explicit exchange, indexed Forth `SWAP` exchange and depth-indexed `ROLL` resource selection, a Boolean encoding as the additive formula `1 ⊕ 1`, and Unit as the multiplicative formula `1`. The formal module also includes a generic `LinearSourceType` / `LinearTerm` core (Nat, Int, Bool, Unit, tensor, sum, and linear-function types) with context-indexed variables, exchange, tensor introduction/elimination, additive introduction/case, cut, lambda introduction, and an environment-owning closure constructor; `deriveMALLP` translates each term constructor structurally into the existing MALLP rules. `boolProofDerivation` builds the two Boolean introductions from `mallp-plus-left` / `mallp-plus-right` and `mallp-one`; `boolMALLP-forth-sound` proves the rendered Boolean token has the same value as its MALLP proof. `boolCaseWithResidualMALLP` uses the additive `mallp-with` rule to give both exclusive branches the same live residual assumption; `compileBoolCaseWithResidual` lowers that case to `SWAP IF ... ELSE ... THEN`; `boolCaseWithResidualMALLP-forth-sound` proves its token execution preserves the selected residual value; and `boolCaseWithResidual-token-correspondence` identifies the formal control-flow tokens. The generated renderer certificate additionally compares the Haskell compiler's actual `chooseBool` token list with `mapBoolForthTokensAsText (renderBoolCode compileBoolCaseWithResidual)` by `refl`. `unitProof` is `mallp-one`, and `unitMALLP-forth-sound` proves the empty Forth lowering preserves the caller's residual stack. `natMALLP-forth-sound` proves the closed Nat AST, indexed Forth stack code, and abstract postfix-token interpreter agree while preserving the residual stack. `natLinearMALLP-forth-sound` connects unary linear Nat proof interpretation with indexed Forth/token execution; `natBinaryMALLP-forth-sound` does the same for two-argument primitive functions and their two-assumption MALLP derivations. The indexed target adds `StackAt`, `rollNat`, `rollStack`, `rollWord`, and `rollList-correct`, proving the ROLL permutation for every witnessed live stack depth. The closed-local-let model adds `closedNatLocal-proof`, `closedNatLocal-proof-adequate`, and `closedNatLocal-forth-sound`: a closed PureLang-style let expression is inlined and receives a MALLP derivation without weakening or contraction.

The generic Nat resource-tree and ROLL token proofs, the integrated Forth renderer, the Bool additive-case witness, and the BoolPair tensor-swap witness all type-check in CI. The generic LinearTerm layer now derives MALLP proofs for its supported constructors, including closure introduction with an explicitly owned environment. This does not yet prove that the Haskell Treeless decoder maps arbitrary source terms into those typed terms, that the Forth runtime refines the formal machine, or that concrete Gforth is covered by a mechanized simulation theorem. The existing Gforth cell bound also differs from mathematical unbounded Agda Nat; the emitted runtime reports overflow rather than proving arbitrary-precision Nat semantics.

## Current expanded test slice

The Gforth fixture includes unary identity, addition, monus in either operand order, and multiplication, plus binary addition, monus, reversed monus, and multiplication. It also exercises `invertBool` and `chooseBool` across both additive branches, with the second live Boolean preserved and returned. The admitted linear functions must consume each live argument exactly once on every branch. An unused argument or a duplicated live argument is rejected; closed operands may be separately reconstructed.

This is not yet general higher-order PureCake support: no closure environment, user-defined call graph, finite ADT/list lowering, recursive semantics, stateful thunk sharing, or effect handlers are implemented. The Agda proof establishes the formal unary core and abstract token machine, not the Haskell printer or real Gforth implementation.

## PR #33: typed MALLP core and C-series witnesses

This PR adds several formal foundations and one narrow new backend case. Keep the distinction between a formal source model, an implemented decoder, and an end-to-end verified compiler explicit.

### BCI and the linear closure model

The source type former `linearArrowType A B` is interpreted as the polarized MALLP formula
`↓(A⊥ ⅋ ↑B)`. The linear term core has context-indexed variables, exchange, tensor introduction/elimination, additive injection/case, unit, cut, lambda abstraction, and an environment-owning closure constructor. `deriveMALLP` maps the implemented `LinearTerm` constructors structurally to Laurent's existing rules.

The new BCI witnesses represent:

- **I:** identity, with its sole input consumed once.
- **B:** composition, with three function/argument resources each used once.
- **C:** exchange, implemented by the explicit context permutation.

Application itself is represented in `LinearApplicationTerm` and interpreted through the explicitly declared `primitive-linear-apply` signature in `MALLPProtocolTheory`. This is a typed primitive operation over unchanged MALLP, not a new logical inference rule and not a claim that a Forth closure-call implementation is already verified. The I/B/C terms and their protocol derivations are Agda witnesses; Haskell does not yet compile general higher-order closures or application.

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

Agda's user rewrite declarations belong to source conversion/type checking. Agda checks the configured rewrite system for confluence and uses it during normalization; the Haskell backend receives Agda's resolved/normalized Treeless output through `toTreeless`. The backend does not contain an independent, unproved symbolic rewrite engine. `FLib.fth` is the target's operational runtime library: its Nat words define executable arithmetic and error behavior, not Agda's type-theoretic conversion relation. A theorem must relate each admitted source rewrite equation to the denotation of its target operation. Adding rewrite-like text processing to `FLib.fth` would not establish confluence and would conflate compile-time conversion with runtime execution.

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

“C-series” is used here as the compiler's correspondence chain: each transition preserves a named invariant, and the final identity is a theorem rather than a resemblance.

- **C0 — Source judgment:** resolve the pinned Agda 2.8.0.2 Treeless term and its result/argument types. The current decoder establishes this for the admitted Nat, Bool, and Unit cases.
- **C1 — Resource judgment:** the Agda `IndexedNatResourceExpr` retains live source-argument labels in left-to-right occurrence order. `IndexedNatResourceProgram n` carries an explicit `ContextPermutation` from those occurrences to canonical labels `0 .. n − 1`; `deriveIndexedNatResourceProgram` maps that evidence into the Nat primitive MALLP theory, and `indexedNatResourceProgram-adequate` relates proof interpretation to evaluation under the correspondingly permuted environment. This formal model rejects missing, repeated, and out-of-scope source resources by construction. The Haskell decoder does not yet emit this Agda AST/permutation certificate automatically, so the Haskell-decoder → Agda-witness boundary remains open. Additive Bool branches separately preserve a common residual context. Closed pure values are closed derivations, not reusable live assumptions.
- **C2 — Target construction:** `natResourceForthTokens` structurally compiles every count-indexed `NatResourceExpr n` into typed postfix tokens. A resource leaf emits no instruction, `SWAP`, or depth-indexed `ROLL` based on active sibling-result depth; binary nodes compose their subprograms and primitive operation. The labelled-source layer adds `IndexedNatResourceExpr` and `IndexedNatResourceProgram`; its explicit `ContextPermutation` maps each occurrence once onto canonical source-argument labels, and `deriveIndexedNatResourceProgram` constructs the corresponding focused MALLP Nat proof.
- **C3 — Target semantics:** `natResourceForthTokens-correct` proves execution for every count-indexed resource tree, preserving arbitrary active sibling results and residual stack values. `natResourceMALLP-forth-sound` composes that result with `natResourceProof-adequate`. The labelled layer separately proves proof/evaluation adequacy under its permuted environment. Bool and Unit retain their separate proofs.
- **C4 — Renderer identity:** Haskell emits `MALLPEmittedRenderer.agda`. For every generated word, Agda checks `actualWord ≡ renderForthWordText name tokens` by `refl`. For `chooseBool`, a second generated theorem, `chooseBoolTokenCorrespondence`, checks that the Haskell compiler's token sequence is exactly the token sequence rendered from the Agda `BoolForthCode` proof.
- **C5 — Concrete runtime:** Gforth executes the generated module and regression fixture. This is currently tested, not yet established by a mechanized refinement theorem for Gforth or the upstream runtime.

C-series is a boundary-by-boundary compiler-correctness architecture, not a competing logic or combinator basis. It is more determinate for compiler verification than a BCI-only account because it names the representations, maps, invariants, and proof obligations that connect source, proof, target, renderer, and runtime. BCI I/B/C remain useful linear examples inside that architecture; they do not characterize Laurent MALLP's expressive power or derive general application from bare MALLP. The maximal strict language is determined by the unchanged MALLP rules together with an explicitly declared primitive signature and a proof of each primitive's operational and resource contract. C-series records the correspondence obligations needed to verify its implementation; it does not, by itself, prove that a proposed source language is maximally expressive.

The chain remains conjunctive: C4 does not prove C0/C1 correctness, and C5 does not by itself prove formal equivalence. The formal labelled AST derives MALLP and proves environment-reindexing adequacy; the count-indexed resource tree has a general target-token execution theorem. Still open are automatic Haskell-decoder → `IndexedNatResourceProgram` certificates, proof that Haskell's dynamic `active + position` resource selection is reified by the same formal permutation, source-decoder-to-typed-term certificates for every accepted input, the pinned runtime → formal Forth-machine theorem, and formal-machine → concrete-Gforth simulation.

## Formal and build boundaries

- Agda and the Haskell backend use pinned Agda **2.8.0.2** from `cabal.project`.
- `formal/MALLPForth.agda` contains the MALLP specification, generic linear source-term grammar and derivation function, coinductive Conat core, typed Forth token algebra, canonical text renderer, and abstract target machine. The former `formal/ForthRenderer.agda` has been retired so compiler terms and rendering witnesses share one module.
- `formal/SovereignRationalSEDPhysics.agda` remains a separate library and is not a compiler proof dependency.
- The MALLP proof options and existing postulate boundary are retained; this project does not claim an axiom-free or `--safe` development.
- The backend emits a generated `MALLPEmittedRenderer.agda` certificate beside the Forth module. For each emitted colon definition, the certificate records the actual string produced by Haskell `renderForm`, constructs the formal `ForthTextToken` stream, and asks Agda to prove by `refl` that the emitted definition equals `renderForthWordText`. CI type-checks this generated certificate with pinned Agda 2.8.0.2. This establishes exact text equality for emitted definitions in the fixture, including Nat literals, arithmetic tokens, SWAP, ROLL, Bool literals, and Unit words. For the `chooseBool` additive case, the same certificate also proves the compiler token list equals the text-token image of `renderBoolCode compileBoolCaseWithResidual`, linking the compiler's control-flow lowering to a typed Agda program and its MALLP proof.
- This renderer certificate is one link in the correspondence chain, not the whole compiler-correctness theorem. The new `natResourceMALLP-forth-sound` theorem covers every **count-indexed formal resource tree**, and the labelled-source layer proves MALLP derivation and environment adequacy. The Haskell Treeless decoder's labelled-resource AST still lacks a kernel-checked reification theorem into `IndexedNatResourceProgram`, including its arbitrary context-index/`active + position` calculation. The upstream `FLib.fth` runtime and concrete Gforth execution also lack a formal refinement theorem. The generated equality theorem certifies actual emitted definition text against the Agda renderer, while Gforth fixtures validate concrete execution on tested examples.
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
