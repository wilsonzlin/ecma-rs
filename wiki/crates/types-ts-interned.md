# types-ts-interned

The pure type core: deterministic, interned TypeScript type representation plus the
relation (assignability) engine and the type-level evaluator. **No AST references, no
spans, no I/O** — this is the functional core of the checker, reusable by any typed
tooling. Theory background:
[compiler-theory § types](../theory/compiler-theory.md#3-types-what-typescripts-type-system-actually-is).

## TypeStore: interning and identity

`TypeStore::new()` / `with_options(TypeOptions)` → `Arc<TypeStore>`. Everything is
content-addressed: `TypeId`, `ShapeId`, `SignatureId`, `ObjectId`, `NameId` derive from
**128-bit domain-separated fingerprints** (two seeded 64-bit hashes per value; domains
`TYPE/SIGNATURE/SHAPE/OBJECT/NAME` keep cross-kind collisions structurally impossible),
so ID allocation is independent of insertion order and safe under parallel interning
(sharded `DashMap` + `parking_lot::RwLock` internals). Collision fallback is
deterministic salting — with the documented caveat that under an actual collision,
ID assignment becomes insertion-sequence-dependent; the `strict-determinism` feature
turns collisions into a loud failure instead. Full doctrine and fine print:
[determinism](../architecture/determinism.md#collision-semantics-the-fine-print).

Canonicalization happens *before* interning: unions/intersections flatten, sort
(`type_cmp` — a total order over types), dedup, and apply identities
(`T | never = T`, `T & unknown = T`) so equal-up-to-ACI types share one `TypeId` and
type equality is integer equality. Object intersections also reduce to `never`
when ≥2 members share a *required* property with definitely-disjoint types
(tsc `getIntersectionType`) — decided by an allocation-free structural check
(distinct primitive families / distinct literals), never by recursing into
`store.intersection`: doing so recursed back into the reduction per nested
object and was the `parserRealSource12` memory/time bomb (2026-07-28).
Exception (2026-07-30): `#`-private-identifier keys whose brands
(`declared_on`/`origin`) *differ* are distinct slots, not one conflicting
property — a derived class redeclaring `#x` carries both its own and the
base's slot, so `B & A` stays inhabited (`privateNamesAndFields`).
Callable props merge differently too (2026-07-30): duplicate same-name method
props concatenate their overload lists *in declaration order* instead of
intersecting — the intersection canonicalizer's `TypeId` sort scrambled
overload order, and tsc picks the first *applicable* overload in source
order (`typesWithSpecializedCallSignatures`).

## The type language (`TypeKind`)

34 variants covering the TS surface: primitives (`Any/Unknown/Never/Void/Null/
Undefined/Boolean/Number/String/BigInt/Symbol/UniqueSymbol`), literals (bool, number
via `OrderedFloat`, string via `NameId`, bigint), `This`, `Infer { param, constraint }`,
`Tuple(Vec<TupleElem { ty, optional, rest, readonly }>)`, `Array { ty, readonly }`,
`Union`/`Intersection`, `Object(ObjectId)` (shape: properties + call/construct
signatures + indexers + brand flags; `PropKey` distinguishes string/number/symbol
keys; `PropData` carries optional/readonly/method/accessibility/`declared_on`),
`Callable { overloads }`, **`Ref { def: DefId, args }`** (the lazy back-edge that makes
recursive types internable — never eagerly expanded), `TypeParam`, `Predicate`
(positional `PredicateParam::This | Param(n)` — positional because parameter *names*
are canonicalized away; predicates must survive that), `Conditional { check, extends,
true_ty, false_ty, distributive }`, `Mapped` (readonly/optional `MappedModifier`s,
`as_type` remapping, internal `name_type` retained for tsc fidelity but hidden from
display), `TemplateLiteral`, `Intrinsic` (`Uppercase/Lowercase/Capitalize/Uncapitalize/
NoInfer/BuiltinIteratorReturn`), `IndexedAccess`, `KeyOf`, and `EmptyObject` — the `{}`
type, distinct from the `object` keyword (empty structural object), with its
strictNullChecks-dependent semantics documented on the variant.

## Relation engine (`RelateCtx`)

Assignability/comparability/strict-subtype as a **coinductive** relation: pair cache
(`ShardedCache`, stats-instrumented), in-progress set treated as success (the greatest-
fixed-point reading), and explicit `RelationLimits` (depth 64, in-progress 128,
**`step_limit` default 50_000** — finite; use `UNLIMITED_STEP_LIMIT` / `usize::MAX`
only for explicit stress tests — indexer-key and template-literal matching budgets —
template matching is bounded automaton search: `max_template_match_states` 1024,
`max_template_atom_strings` 1024).
`RelationMode` flags: `BIVARIANT_PARAMS` (TS's method-bivariance exception),
`SKIP_NORMALIZE` — which exists to break the relate↔evaluate recursion when
conditional-type evaluation asks "is check assignable to extends?" mid-normalization —
and `COMPARABLE_OPTIONALITY` (2026-07-30: tsc `comparableRelation` — an
optional source property may satisfy a required target property and raw
types are compared without the undefined-wrap; used by the type-assertion
overlap check, `optionalProperties01.ts`).
`RelateHooks` injects checker policy without polluting the pure core: a lazy `Ref`
expander, `is_same_origin_private_member` (nominal-ish `private`/`protected`
compatibility), and optional `should_stop: Option<&AtomicBool>` for cooperative
cancellation (on stop: conservative success + `budget_exceeded`, never panic).
Intersection *sources* relate via the merged apparent type against object
targets (tsc `getApparentType`), *not* per-constituent — tsc rejects
`{} & {id: number}` → `{id?: string}` even though `{}` alone fits
(oracle-verified 2026-07-30). Same-spelled `#`-private slots from different
declarations survive the merge as separate entries
(`intern_shape` keeps both; `find_private_ident_property` picks the
brand-compatible slot), so `B & A → A` still holds when `B` redeclares `#x`
(`privateNamesAndFields`).
Failed relations can produce a bounded `ReasonNode` tree (depth 12, 256 nodes)
powering "explain why not assignable" diagnostics. Nested `normalize_type`
evaluation **shares** the remaining relation step budget (does not reset to a
fresh full limit).

Signature relating tracks tsc `compareSignaturesRelated` /
`signaturesRelatedTo` (2026-07-28): the arity floor is
`getMinArgumentCount(source) > getParameterCount(target)` — source *required*
count against target *total* count, so optional destination parameters absorb
source required ones (`(a: any) => any` matches `(a?: number) => number`;
`(a: number) => number` still fails it on `number | undefined`). Overload
sets relate per tsc's matrix: every target signature must be matched by some
source signature, and an unconstrained generic target is also compared in its
**erased-to-`any`** form (`getErasedSignature`) when exact instantiation
fails — the mechanism that accepts `b16 = a16` /
`assignmentCompatWithCallSignatures4.ts`-style shapes. `infer_type_args_into`
covers `(Callable, Object-with-call-signatures)` pairs for those
instantiations. CSI keeps a destination-mentioned shared type-param marker
instead of substituting its constraint (`I9 extends A` /
`callSignatureAssignabilityInInheritance3.ts`), and the different-arity
hard-false applies only when both sides are generic.

## Evaluator (`TypeEvaluator` / `TypeExpander`)

Lazy normalization of type-level computation: `Ref` expansion via the `TypeExpander`
trait (implementations must be pure; cycle detection and memoization are the
evaluator's job), substitution environments (sorted binding vectors, binary-searched),
conditional evaluation with distributivity and **deferral on indeterminate checks**
(free type params), mapped-type key iteration, template-literal
construction, intrinsic string mapping. Backed by `EvaluatorCaches` (+ stats), with
`EvaluatorLimits` bounding depth/steps (**default `step_limit` 50_000**, matching
`RelationLimits`; optional `should_stop`). Under an empty or type-param-only subst,
`evaluate_object` does not deep-walk nested object **properties** (call/construct
signatures and non-object props still reduce) so structural graphs cannot explode.
Conditional assignability delegates through `ConditionalAssignability` (default: a
`RelateCtx` in `SKIP_NORMALIZE` mode). The conditional-types hardening program that
produced this design is archived in the
[graveyard](../graveyard.md#completed-scratchpads).

`keyof` corner semantics (oracle-verified vs tsc 5.9.3, 2026-07-28): `keyof never`
is the keyof constraint type `string | number | symbol` (**not** `never`), so a
never-reduced intersection (`{ b: number } & { b: boolean }`) keys out to
`string | number | symbol`; `keyof unknown` and `keyof {}` remain `never`. The
`KeySet::Unknown` universal set implements this in the key algebra. ES private
identifier keys (`#foo`) are excluded from `keyof` object key sets
(`privateNamesAndkeyof.ts`), and `typeof`-narrowing classification recurses
into unions so literal-union-lowered enums classify by their members
(`typeof x === "number"` matches a numeric enum).

Mapped types (2026-07-29): `MappedType.homomorphic_var` records the
homomorphic variable at lowering (`{[P in keyof T]: X}` — eager substitution
would otherwise erase it). Evaluation implements tsc's
`instantiateConstituent`: instantiating the variable with a non-mappable
source (primitives, `never`, `void`, `null`, `undefined`) yields the source
itself (`DeepReadonly<number>` is `number`); mappable sources (AnyOrUnknown,
InstantiableNonPrimitive — type params, indexed access, conditionals, mapped
— Object, Intersection) map normally; union sources distribute per
constituent with primitives passing through. Indexed access over
intersections gathers the property across members (`(Z & {})["a"]` is
`number`). Covariant call-arg inference distributes argument unions only for
union/structured targets — a naked type parameter keeps the source union as
one candidate (`boxify(x)` with `x: A | B | undefined` infers
`T = A | B | undefined`).

Recursive generics (2026-07-29): `evaluate_ref` substitutes Ref arguments
structurally (`substitute_only`) instead of evaluating them eagerly — eager
arg expansion made recursive generics with growing args (`D<D<T>>`)
quadratic, since each nesting level re-walked the full chain below and
`(def, args)` cycle keys can never fire when args grow. tsc keeps type
arguments as references; downstream evaluation expands lazily on demand.
Expansion of `class D<T> { wrapped: D<D<T>> }` is thereby linear, and
alternating recursion (`Foo<T extends G<T>>` / `recursiveTypeInGenericConstraint`)
still closes its recursive-pair cycle exactly.

## Display and options

`TypeDisplay` renders human syntax (used by `Program::display_type`, CLIs, difftsc
type-facts). `TypeOptions` carries the semantics switches the pure layer needs
(derived `From<&CompilerOptions>` in the checker). An options-consistency invariant is
enforced — the store's options and the checker's options must agree (was task 49 of the
scratchpad program).

## Fuzzing

`fuzz_type_graph(&[u8])` (features `fuzzing` + `serde-json`; wired via
`fuzz/fuzz_targets/type_graph.rs`): deserializes arbitrary — possibly cyclic —
`TypeKind` graphs from JSON, interns them, then runs evaluation/normalization and
assignability with explicit limits. **Invariant: terminate, never panic.** Run with
`cargo fuzz run type_graph` (the workspace opts into `RUSTC_BOOTSTRAP=1` so the pinned
stable toolchain works; `cargo +nightly fuzz run type_graph` also fine).

## Known issues and directions

- **Unbounded evaluate_object / composite canon (fixed 2026-07-23):** upstream
  `parserRealSource12.ts` (shard 2/64) drove multi-GB RSS via recursive
  `evaluate_object` → `intern_shape` / intersection while
  `RelationLimits::step_limit` defaulted to `usize::MAX` (step tracking off) and
  cancel was not observed in relate/eval. Fix layers: (1) `should_stop` + finite
  `DEFAULT_STEP_LIMIT = 50_000` on relate/eval; (2) `sort_and_dedup` by
  content-addressed `TypeId` (not structural `type_cmp`); `MAX_COMPOSITE_MEMBERS`
  4096; (3) empty / type-param-only subst skips deep nested **object property**
  walks (still reduces call/construct signatures and `Callable`/`Ref` props);
  identity short-circuit when `!type_needs_evaluation`; no cache insert after
  `budget_exceeded`. See [typecheck-ts known issues](typecheck-ts.md#known-issues-and-directions)
  and `reports/shard2-pathology-handoff.md`.
- **NameInterner fairness deadlock (fixed 2026-07-23):** `compare_props` used to hold
  the `names` read guard across recursive `type_cmp`, deadlocking against
  `intern_name` writers under parking_lot fairness. Fix: compute key ordering in a
  scoped block and drop the guard before recursing (same pattern audited on other
  `names` sites; see comments in `store.rs`). Diagnosis preserved as teaching
  material:
  [determinism § case study](../architecture/determinism.md#case-study-the-nameinterner-deadlock).
  Regression: `types-ts-interned/tests/lock_stress.rs`.
- Cache eviction is config-present (`CacheConfig`) but policy-light; the performance
  program ([roadmap phase 4](../status/roadmap.md#4-performance-program)) owns
  measuring hit rates and adding bounds where profiles demand.
- Property tests (suite landed 2026-07-23 in
  `types-ts-interned/tests/properties.rs`, citing this page +
  [determinism](../architecture/determinism.md)): canonicalization idempotence
  (`canon(canon(t)) == canon(t)`); union ACI (commutativity, idempotence,
  `T | never = T`); intersection duals (`T & unknown = T`); `type_cmp`
  reflexivity / antisymmetry / transitivity / Equal⇔same TypeId; content-
  addressed determinism (same recipe → same TypeIds across fresh stores);
  relation stability under canonicalization (`is_assignable(a,b) ==
  is_assignable(canon(a), canon(b))`). Broader / complementary coverage also
  lives in `tests/proptests.rs` (termination on cyclic graphs, shape order-
  independence, evaluator/relation cache stability). Still worth adding per
  [theory § completing rigorously](../theory/compiler-theory.md#8-completing-the-implementation-rigorously):
  fingerprint collision fallback schedule-independence under
  `strict-determinism`, and assignability monotonicity lemmas on normalized
  forms (beyond the canon-invariance check above).
