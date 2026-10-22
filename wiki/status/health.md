# Health snapshot

**As of: 2026-07-30.** Dated snapshot, not evergreen
([how-to-write § evergreen](../meta/how-to-write.md#evergreen-style)). Re-verify before
trusting. Headline deltas below are absorbed from owning crate/roadmap pages and
spot-checked against `reports/` where cited; full workspace build/test green claims
remain the **2026-07-23 evening** verification unless a later date is named.
See [roadmap](./roadmap.md) for the phased program.

## 2026-07-30 slice

- **Conformance shard 50/64**: match **43/95**, unexpected **1 → 0
  (gap-xfailed)**, XPASS 5 pruned (`classExtendingClass`,
  `constructorWithExpressionLessReturn`, `ES5for-of32`, `forStatements`,
  `emptyTuplesTypeAssertion02`) — prune-only otherwise.
  Gap xfail (roadmap-recorded): `classWithStaticMembers.ts` — static-heritage
  gap: inherited static members do not resolve on the derived constructor
  (`D.foo`/`D.fn()` type as `unknown`; instance heritage works via
  `C & {bar}` but the ctor value type merges no base statics). Green span
  now **0–50**.

- **Conformance shard 49/64**: match **34/87**, unexpected **0**, XPASS 5
  pruned (`ES5SymbolProperty1`, `parserComputedPropertyName2`,
  `moduleExportAlias`, `spreadNonPrimitive`,
  `subtypingWithCallSignaturesWithRestParameters`) — prune-only. Green span
  now **0–49**.

- **Conformance shard 48/64**: match 34 → **37/95**, unexpected **4 → 3 fixed
  + 1 gap-xfailed**, XPASS 4 pruned (`iteratorSpreadInArray6`,
  `ExportFunctionWithInaccessibleTypesInParameterTypeAnnotation`,
  `jsDeclarationsFunctionPrototypeStatic`, `objectRestReadonly`).
  Fixes:
  (a) **`for await…of` iterates the async protocol** (`[Symbol.asyncIterator]`)
  when present, else the sync protocol, and *awaits* the element
  (`types.forAwait.es2018.1.ts`); the iterator walk now awaits `next()`'s
  `Promise<IteratorResult<T>>` before reading `value`.
  (b) **`declare module "name"` (string-literal) bodies are isolated ambient
  module scopes** (`ambientDeclarations.ts`).
  (c) **JSDoc `@callback Name` is parsed as a function type** — its
  `@param` / `@returns` route to the callback's signature, and it registers
  in the file typedef map so `@type {Name}` resolves
  (`callbackOnConstructor.js`).
  Regression tests: `tests/for_await_iterables.rs`,
  `tests/ambient_modules_and_callbacks.rs`.
  Gap xfail (roadmap-recorded): `privateNameInLhsReceiverExpression.ts` —
  class-expression member defs are not in the program def model, so
  class-expression member init types stay `unknown`.

- **Verified**: shards **0–47 all green** under `--fail-on new` (final
  post-destructuring sweep; batch FAILs on 5/6/14/16/18/24/27/32/36/42
  re-verified standalone as load flakes or fixed as noted below), difftsc
  **56/56**, fmt/clippy/guards clean.
- **Conformance shard 47/64**: match **41/84**, unexpected **0**, XPASS 6
  pruned (`for-of12`, `exportAssignTypes`, `interfaceThatHidesBaseProperty2`,
  `instantiatedModule`, `parservoidInQualifiedName1`,
  `objectTypeWithRecursiveWrappedProperty`) — prune-only, cured by the
  shard-42/46 fixes. Green span now **0–47**.

- **Generator function declarations type as `Generator<Y, R, N>`** (async:
  `AsyncGenerator`), built from the body's yield union —
  `infer_cached_callable_return_type` now consults
  `BodyCheckResult.yield_types` instead of leaving `() => void`
  (`function* gen() { yield 1; }` → `() => Generator<number, void, unknown>`;
  unannotated `[...gen()]` and `for (const s of gen())` get the precise
  element type, matching tsc). Roadmap gap closed. Regression tests:
  `tests/generator_decl_types.rs`.

- **Conformance shard 46/64**: match 45 → **47/103**, unexpected **2 → 0**,
  XPASS 5 pruned (`controlFlowDoWhileStatement`,
  `computedPropertyNames4_ES5`, `templateStringWithEmbeddedYieldKeyword`,
  `jsdocLinkTag9`, `subtypingWithObjectMembersOptionality4`).
  Fixes:
  (a) **For-in/of LHS assignment to an existing binding checks the element
  type against the *declared* type** (skipped for type-parameter targets,
  matching tsc) and narrows only the flow type — the loop no longer rebinds
  `declared_ty`.
  (b) **`this` in a function expression/declaration without a contextual
  `this` type is `any`** (`typeOfThisInFunctionExpression.ts`).
  (c) **Destructuring *assignments* preserve the declared type** — a new
  `destructuring_assignment` flag on the checker makes existing bindings
  check-assign and flow-narrow instead of rebinding with the pattern value's
  type (`({y: x = /a/} = {y: 1})` no longer turns `x`'s declared union into
  `number | RegExp`, exposed by (a) on `assignmentTypeNarrowing.ts`).
  (d) **Tuple rest elements stay positional** — `[...[a, b = 0]] = ["", 1]`
  destructures the inner pattern against the tuple `[string, number]`, not
  the union `string | number` (`restElementWithAssignmentPattern1.ts`); the
  declaration form keeps tsc's union behavior.
  (e) **Destructuring from iterables uses the protocol for element and rest
  types** — `[a, ...b] = new FooIterator` binds `a: Foo`, `b: Foo[]`
  (`iterableArrayPattern4.ts`).
  Regression tests: `tests/for_of_lhs_and_function_this.rs` (6);
  post-sweep XPASS pruned: `ES5For-ofTypeCheck11`, `for-of11`, `for-of17`,
  `inferringClassMembersFromAssignments6`.

- **Verified**: shards **0–45 all green** under `--fail-on new` (post
  union-spread/async-generator sweep; batch FAILs on 11/12/14/20/21/35/37/43
  all re-verified standalone as load flakes), difftsc **56/56**,
  fmt/clippy/guards clean.

- **Conformance shard 45/64**: match 37 → **38/91**, unexpected **1 → 0**,
  XPASS 4 pruned
  (`templateStringsWithTypeErrorInFunctionExpressionsInSubstitutionExpression`,
  `typeGuardOfFormFunctionEquality`, `intersectionTypeInference3`,
  `objectTypeWithCallSignatureHidingMembersOfFunctionAssignmentCompat`).
  Fix: **generator/async-generator `return` checks use the generator type's
  `TReturn` argument** (`annotated_generator_return_arg`) instead of
  `Awaited` of the whole generator object type — `return a` in
  `async function* f(): AsyncGenerator<T, T, T>` now checks `a` against
  `Awaited<T>` (`asyncGeneratorGenericNonWrappedReturn.ts`); wrong-type
  returns still error. Known follow-up (roadmap): `return Promise.resolve(a)`
  still mis-relates through the unevaluated `Awaited<T>` conditional for
  type-param `T`.
  Regression tests: `tests/async_generator_return.rs`.

- **Conformance shard 44/64**: match 33 → **35/76**, unexpected **1 → 0**,
  XPASS 3 pruned (`spreadUnion2`, `autoAccessor8`,
  `parserComputedPropertyName3`).
  Fixes:
  (a) **Union object spreads distribute** (tsc `getSpreadType`):
  `{ ...u }` with `u: A | B` is `spread(A) | spread(B)`, cross-producting
  across multiple union spreads (capped at 32 variants) and skipping nullish
  members entirely (`spreadUnion.ts`, `spreadUnion2.ts`).
  (b) **Later literal members replace earlier spread members** with the same
  key (`{ ...p, a: 'x' }` → `a: string`, previously intersected to `never`)
  — literal prop pushes now upsert like spreads already did.
  Regression tests: `tests/union_object_spread.rs`.

- **Conformance shard 43/64**: match 28 → **29/87**, unexpected **1 → 0**,
  XPASS 1 pruned (`constraintSatisfactionWithEmptyObject`).
  Fix: **`super` in static field initializers / static blocks uses the base
  constructor** — `resolve_super_type` now also consults the field-init
  context's `is_static` (member functions track it separately), so
  `super.a = 0`, `++super.a`, and `` super.a`` `` resolve against the static
  side (`thisAndSuperInStaticMembers2.ts`).
  Regression tests: `tests/super_member_access.rs` (+2).

- **Conformance shard 42/64**: match 44 → **45/103**, unexpected **1 → 0**,
  XPASS 4 pruned (`parserObjectCreation1`, `typeFromPropertyAssignment27`,
  `invalidMultipleVariableDeclarations`,
  `subtypingWithConstructSignaturesWithSpecializedSignatures`).
  Fixes (one conformance failure, three stacked root causes):
  (a) **`super` in member position is typed** — the base class constructor in
  static members, the base instance otherwise (`resolve_super_type` with an
  explicit `contextual_this_is_static` tracked alongside `contextual_this_ty`;
  was unconditionally `unknown`).
  (b) **Static and instance members never merge into one overload set** —
  `callable_overloads` is keyed by `(file, name, is_static)`; tsc treats them
  as distinct declaration spaces (`func(): string` instance and
  `static func(): number` had merged into `{ (): string; (): number }` on
  both sides).
  (c) **The getter "peek" no longer leaks TS2403 bookkeeping** —
  `infer_getter_return_type` re-checks the getter body inside the setter's
  checker; `established_var_bindings` (and the namespace map) are now
  saved/restored, so the setter's own `var x = …` no longer looks like a
  later redeclaration against a parent-seeded `undefined`
  (accessor bodies in `superPropertyAccessNoError.ts`).
  Regression tests: `tests/super_member_access.rs`.

- **Conformance shard 41/64**: match 48 → **50/96**, unexpected **2 → 0**,
  XPASS 8 pruned (`typeOfThisInMemberFunctions` (cured by the shard-40
  static-this fix), `symbolProperty12`, `parserES5ComputedPropertyName2`,
  `inferringClassMembersFromAssignments7`,
  `jsdocConstructorFunctionTypeReference`, `everyTypeWithInitializer`,
  `emptyTuplesTypeAssertion01`, `arrayLiteralsWithRecursiveGenerics`).
  Fixes:
  (a) **Object-literal getter/setter pairs fold into a semantic property
  type** — the property's type is the getter's return (setter's param when
  setter-only), writable when a setter exists; reads/writes no longer see
  the raw overloaded `(): R & (p: P) => void` callable produced by same-key
  interning (`object[0] **= …` chains,
  `emitCompoundExponentiationAssignmentWithIndexingOnLHS3`).
  (b) **Private-identifier grammar diagnostics survive the `checkJs: false`
  filter** (TS18016/TS18028/TS18030 are parser errors upstream;
  `privateNameUncheckedJsOptionalChain.js`).
  Regression tests: `tests/object_literal_accessors.rs`,
  `tests/check_js_grammar_filter.rs`.

- **Conformance shard 40/64**: match 31 → **33/89**, unexpected **6 → 2 fixed
  + 4 gap-xfailed**, XPASS 6 pruned (`classExtendingBuiltinType`,
  `derivedTypeDoesNotRequireExtendsClause`, `outFilerootDirModuleNamesSystem`,
  `asOperator1`, `localTypes3`, `validVoidValues`).
  Fixes:
  (a) **`for (k in obj)` accepts mapped types** — the for-in RHS check now
  admits `TypeKind::Mapped` (`keyofAndForIn.ts`; tsc treats mapped types as
  object types there).
  (b) **`this` in static members resolves to the real constructor value
  type** (construct signatures + statics) for class *declarations*, not just
  expressions — class defs are seeded into the span-keyed
  `class_expr_value_tys` map from the file's HIR defs, so
  `var t = this; new t(1)` is constructable even when the method body is
  checked outside the file-level scope chain (`typeOfThisInStaticMembers.ts`).
  Regression tests: `tests/for_in_mapped_rhs.rs`, `tests/static_this_constructor.rs`.
  Gap xfails (all roadmap-recorded): `typesWithOptionalProperty` +
  `commonJSAliasedExport` (function-expression return inference: object
  literals / JS closures infer `() => unknown`),
  `thisTypeInFunctions3` (polymorphic-this: `TypeKind::This` has no relate
  handling), `TwoInternalModulesThatMergeEachWithExportedModulesOfTheSameName`
  (merged-namespace duplicate var keeps last declaration; tsc keeps first).

- **Conformance shard 39/64**: match **32/82**, unexpected **0**, XPASS 2
  pruned (`classExpressionLoop`, `symbolProperty1`) — prune-only, cured by
  the shard-37/38 fixes. Green span now **0–39**.

- **Verified**: shards **0–38 all green** under `--fail-on new` (post
  evaluator-DAG-memo sweep; batch FAILs on 0/20/29/31/33 re-verified
  standalone as load flakes or fixed as noted below), difftsc **56/56**,
  fmt/clippy/guards clean, `types-ts-interned` tests pass.

- **Evaluator termination fix** (`types-ts-interned/src/eval.rs`):
  `substitute_only` now memoizes per `evaluate_ref` invocation. Interned
  types are DAGs, and self-similar intersection/mapped types
  (`OldDiff<keyof this, keyof A>` in `conditionalTypes1.ts`) made the
  structural substitution walk explode exponentially — the checker never
  finished the file (>58 minutes of CPU sampled in `substitute_only`;
  ~20s debug after). Regression: `tests/eval_subst_dag_termination.rs`.
- **Refine-pass ordering fix** (`ensure.rs`):
  `refine_class_static_field_types_from_assignments` must run before the new
  instance-field refine — the latter calls `type_of_def` on every field and
  would otherwise cache the still-unknown type (emitting TS7008) before the
  assignment-based synthesis registers it
  (`classStaticBlockUseBeforeDef2.ts`).

- **Conformance shard 38/64**: match 30 → **31/85**, unexpected **1 → 0**,
  XPASS 6 pruned (`iteratorSpreadInCall12`,
  `ExportObjectLiteralAndObjectTypeLiteralWithAccessibleTypesInMemberTypeAnnotations`,
  `tsxElementResolution1`, `inferringClassMembersFromAssignments8`,
  `jsObjectsMarkedAsOpenEnded`, `callSignaturesThatDifferOnlyByReturnType`).
  Fixes:
  (a) **Unannotated instance field initializers refine class instance types**
  (new `refine_class_field_property_types`): `three = 3` → `number`, numeric
  keys (`1 = ''`) included — previously only annotated fields carried their
  type and reads through the declared instance type stayed `unknown`,
  cascading TS2403 on same-name `var` redeclarations
  (`numericIndexingResults.ts`). The accessor patch helpers now match
  `PropKey::Number` by source spelling.
  (b) **Incremental TDZ for destructuring defaults** (`bindings.rs`): pattern
  defaults evaluate left-to-right, so `{ a1, a2 = a1 }` is legal but
  `{ a2 = a1, a1 }` and `{ a: x = x }` are TS2448 — `init_pats` now starts as
  the full declarator set and shrinks as sub-patterns complete; the outer
  initializer always sees the full set (`const { a } = a`). Fixes a
  regression where self-referential defaults lost their TDZ error entirely
  (top-level) or degraded to TS2304 (function scope).
  Regressions: `tests/field_init_instance_types.rs` (4);
  `tests/ts2454_residuals.rs` back to 25/25.

- **Conformance shard 37/64**: match 31 → **32/83**, unexpected **1 → 0**,
  XPASS 6 pruned (`autoAccessor10`, `superCallBeforeThisAccessing3`,
  `untypedModuleImport_vsAmbient`,
  `augmentedTypeAssignmentCompatIndexSignature`,
  `methodSignaturesWithOverloads2`,
  `subtypingWithCallSignaturesWithSpecializedSignatures`).
  Fixes (spreading / iterating non-array object types, `iteratorSpreadInArray7.ts`):
  (a) **`spread_element_type` / `for_of_element_type` walk the synchronous
  iterable protocol** (`[Symbol.iterator]().next().value`, new
  `iterable_protocol_element` in `flow_ops.rs`) instead of degrading to
  `unknown`. `done: true` union members (`IteratorReturnResult<TReturn>`) are
  skipped when a yielding member exists so `IteratorResult<T, TReturn>`
  iterates as `T`, and a `return this` fallback treats the input object as
  its own iterator when the method's return type is a stale snapshot.
  `[...new Map]()` / `[...new Set]()` / generator-object spreads now infer
  their declared element types; `[..."ab"]` is `string[]`.
  (b) **Inferred returns for computed well-known-symbol methods are stamped
  onto class instance shapes** — `refine_class_method_property_types` only
  matched `PropKey::String`, so `[Symbol.iterator]() { return this; }` kept
  its lowered `() => any`; computed keys are now resolved from the class
  body HIR (`Symbol.<name>` / `Symbol["<name>"]`) and patched via new
  symbol-keyed patch maps.
  Regressions: `tests/iterable_spread_protocol.rs` (6).
  Known gap recorded: **generator function declarations type as `() => void`
  without a contextual type** (`function* gen() { yield 1; }` — the yield
  union only flows through `refine_function_expr_with_expected`), so
  unannotated `[...gen()]` still infers `unknown[]`.

- **Conformance shard 36/64**: match 32 → **35/89**, unexpected **3 → 0**,
  XPASS 4 pruned (`es5DateAPIs`, `emitRestParametersFunctionProperty`,
  `mergedInterfacesWithMultipleBases3`, `subtypingWithObjectMembersOptionality2`).
  Fixes:
  (a) **Setter-only private accessor reads are TS2806**, not TS2339 — the
  accessor exists for visibility purposes (`privateNameSetterNoGetter.ts`).
  (b) **Missing type arguments fill their declared defaults**
  (`Iterator<Foo>` ≡ `Iterator<Foo, any, any>`) in both expanders
  (`expand::fill_default_type_args`) — partial refs never unified with their
  fully-applied form.
  (c) **Unannotated same-def generics compare with measured variance** (tsc
  `getStructuralVariancesOfTypeParameters`, simplified position analysis;
  method parameters stay bivariant) — replaces the blind invariant fallback
  that falsely rejected covariant interfaces (`Box<Bar> → Box<Foo>`,
  `IteratorYieldResult<Bar>`, `Generator<Bar> → Iterable<Foo>`), while
  invariant classes (`#foo: T` fields) stay invariant.
  (d) **Generator return inference aggregates the yield union** and relates
  it to the contextual return instead of adopting it blindly
  (`generatorTypeCheck25.ts`); generic inference through generators
  (`generatorTypeCheck45`) still works.
  (e) **Namespace-nested interfaces merge across files** (new pass in
  `ensure_interned_types` grouping by canonical namespace def — cross-file
  lib augmentation like `Intl.PluralRulesConstructor` in
  es2018/es2020 `.d.ts`, fixing `localesObjectArgument.ts`).
  Regressions: `tests/private_setter_only_read.rs`,
  `tests/default_type_args_and_variance.rs`,
  `tests/generator_yield_inference.rs`, `tests/nested_interface_merge.rs`.

- **Conformance shard 35/64**: match **31/78**, unexpected **0**, XPASS 1
  pruned (`arrayLiterals2ES6`).

- **Conformance shard 34/64**: match **33/78**, unexpected **0**, XPASS 5
  pruned (`computedPropertyNamesContextualType10_ES5`,
  `ExportFunctionWithAccessibleTypesInParameterAndReturnTypeAnnotation`,
  `literalTypesAndDestructuring`, `functionLiterals`, `bestCommonTypeOfTuple`).

- **Conformance shard 33/64**: match **40/96**, unexpected **0**, XPASS 3
  pruned (`propertyNameWithoutTypeAnnotation`,
  `instantiateGenericClassWithZeroTypeArguments`,
  `objectTypeWithRecursiveWrappedProperty2`) — cured by the shard-29/30
  slice fixes. Verified: shards 0–32 all green under `--fail-on new`,
  difftsc **56/56**, fmt/clippy/guards clean.

- **Conformance shard 32/64**: match 34 → **35/101**, unexpected **1 → 0**,
  XPASS 4 pruned (`typeOfThisInInstanceMember2`,
  `inferringClassMembersFromAssignments2`, `multipleDeclarations`,
  `classWithOptionalParameter`). Fix: **`any` arguments prefer `any`-parameter
  overloads** (`anyAssignabilityInInheritance.ts`) — tsc skips
  concrete-parameter overloads for an `any` argument when an `any`-parameter
  overload exists ("any is not a subtype of number … picks second; if truly
  ambiguous it would pick first"); applicable candidates with the most
  `any`→`any` position matches now win, first-match order otherwise unchanged.
  Regression: `tests/overload_any_argument.rs`.

- **Conformance shard 31/64**: match 44 → **45/86**, unexpected **1 → 0**,
  XPASS 4 pruned (`controlFlowBinaryAndExpression`,
  `computedPropertyNamesContextualType9_ES6`, `tsxElementResolution6`,
  `objectTypeWithRecursiveWrappedPropertyCheckedNominally`). Fix: **class
  expressions and arrows are expando bases in JS** — the expando gate only
  admitted `{}` and function expressions/declarations, but tsc
  `bindSpecialPropertyAssignment` treats `var Outer = class … {}` and
  `var Outer = (…) => …` as containers too (`Outer.Inner = class …` resolves
  in value and JSDoc-type positions, `salsa/typeFromPropertyAssignment.ts`).
  An earlier test asserted the opposite for arrows from a misread of tsc;
  inverted after oracle verification (tsc 5.9.3 clean on the exact shape).
  Regression: `tests/js_expando_members.rs` (+class/arrow base cases).

- **Conformance shard 30/64**: match 39 → **41/92**, unexpected **2 → 0**
  (one was a load-induced tsc timeout), XPASS 4 pruned
  (`interfaceWithPropertyOfEveryType`,
  `ExportInterfaceWithAccessibleTypesInTypeParameterConstraintsClassHeritageListMemberTypeAnnotations`,
  `subtypingWithConstructSignatures6`, `subtypingWithObjectMembers2`). Fix:
  **static private names do not participate in heritage** — the
  private-access heritage rule (receiver's nearest declarer derives from the
  lexical declarer ⇒ allowed) now applies only to instances: `typeof B`
  carries no inherited static privates, so `B.#foo` inside class `A` targets
  B's own private (TS18013) and `B.#bar` doesn't exist (TS2339), matching tsc
  `privateNamesAndStaticFields.ts`. New `is_static_class_receiver`
  discriminator (callable/constructable + nominal class). Regression:
  `tests/static_private_heritage.rs`.

- **Conformance shard 29/64**: match 44 → **47/106**, unexpected **3 → 0**,
  XPASS 6 pruned (`controlFlowBinaryOrExpression`,
  `destructuringArrayBindingPatternAndAssignment5SiblingInitializer`,
  `newWithSpreadES6`,
  `ExportObjectLiteralAndObjectTypeLiteralWithAccessibleTypesInNestedMemberTypeAnnotations`,
  `parametersWithNoAnnotationAreAny`, `assignmentCompatWithStringIndexer2`).
  Fixes:
  (a) **Nominal rule extended to construct signatures**
  (`constructSignatureAssignabilityInInheritance6.ts`, 6/7 → **7/7**) —
  `type_has_generic_signature` now counts generic *construct* signatures, so
  `interface I<T> extends A { a: new (x: T) => T[] }` is TS2430 like its
  call-signature sibling (shard-24 rule).
  (b) **Subsequent-property pass drains field-init re-check diagnostics**
  (`localTypes2.ts`) — `check_class_subsequent_property_types` re-checks
  field initializers with the *current* body's scope, which cannot see
  enclosing-function bindings of lexically nested classes (`class C { x = x; }`
  inside `function f(x)` falsely TS2304'd). The initializer body check owns
  those diagnostics with the correct lexical scope.
  (c) **Fractional numeric property keys are string keys**
  (`objectTypeWithNumericProperty.ts`) — `{ 1.1: string }` members were
  dropped (i64 parse failure → `None`) or collapsed to key `0` (flow-built
  object literals) across four lowering sites; they now fall back to
  `PropKey::String`, so `a[1.1]` resolves instead of `unknown`.
  Side discovery (roadmap): `check_assignable` blanket-skips `unknown`
  sources, which had masked (c) — recorded as a design-level gap.
  Regressions: `tests/interface_extends_generic.rs` (+construct case),
  `tests/nested_class_field_init_scope.rs`, `tests/fractional_numeric_props.rs`.

- **Conformance shard 28/64**: match **40/97**, unexpected **0**, XPASS 4
  pruned (`classWithNoConstructorOrBaseClass`, `iterableArrayPattern26`,
  `moduleWithStatementsOfEveryKind`, `constructorFunctions2`) — all cured by
  the shard-26/27 slice fixes (ambient-decl seeding, `in`-RHS flow types).

- **Conformance shard 27/64**: match 27 → **28/75**, unexpected **1 → 0**,
  XPASS 3 pruned (`emitClassDeclarationWithExtensionAndTypeArgumentInES6`,
  `parserComputedPropertyName17`, `functionLiteralForOverloads2`).
  Cross-shard wins: shard 10 49 → **50** (`controlFlowInOperator.ts`), shard 13
  33 → **34** (`controlFlowWithTemplateLiterals.ts`), shard 17 XPASS prune
  (`jsdocTemplateTag.ts` cured). Fixes:
  (a) **`in`-RHS checks use the flow type** (tsc `checkInExpression`) —
  bare-identifier RHS of `k in x` / `#priv in x` is now checked by the CFA pass
  with narrowed types, so `x !== null` silences TS18047
  (`privateNameInInExpression.ts`); the AST pass keeps non-identifier RHS
  (assertions like `(v as unknown)` stay TS2571). Bare-ident `unknown` RHS is
  **TS18046** (`'{x}' is of type 'unknown'`), not TS2571.
  (b) **Ambient declared types reach the flow pass** — the caller-seeded
  declared type of a module-level `declare const` now lands on the *local*
  flow binding of the top-level body (new `BindingTable.root_bindings`,
  deterministic; previously it was created as an unmatched *external* binding
  and the binding was rebound to `unknown`), and ambient/annotation-only
  declarators bind the seeded declared type instead of `unknown`. Side effect:
  this *exposed* a pre-existing intersection discriminant-path narrowing gap
  (`intersectionOfUnionNarrowing.ts`, shard 14 — manifested xfail, roadmap).
  (c) **No-substitution template literals are string literals for narrowing**
  — `` typeof x === `tag` ``, `` `k` in obj ``, and `x === `lit`` behave like
  their plain-string forms (flow + AST passes).
  Regressions: `tests/in_rhs_flow_type.rs`, `tests/template_literal_narrowing.rs`.

- **Conformance shard 26/64**: match 27 → **28/90**, unexpected **1 → 0**,
  XPASS 3 pruned (`es2023/intlNumberFormatES5UseGrouping`,
  `ExportInterfaceWithInaccessibleTypeInTypeParameterConstraint`,
  `parserArrowFunctionExpression6`). Fix: **empty-body contextual-return
  adoption** — `refine_function_expr_with_expected` no longer adopts a non-void
  contextual return when the body infers `void` (empty or `return;`-only
  bodies), so `() => {}` into `() => number` reports TS2322
  (`staticMemberAssignsToConstructorFunctionMembers.ts`); generators are exempt
  (a return-less generator still produces an Iterator/Generator result —
  `generatorTypeCheck45.ts`). Literal contextual returns (`() => 3 | 4`)
  still adopt. Regression: `tests/empty_body_contextual_return.rs`.
  Verified: shards 0–27 all green under `--fail-on new`, difftsc **56/56**,
  fmt/clippy/guards clean.

- **Conformance shard 25/64**: match 41 → **42/84**, unexpected **1 → 0**,
  XPASS 3 pruned (`computedPropertyNamesContextualType10_ES6`,
  `ExportFunctionWithInaccessibleTypesInReturnTypeAnnotation`,
  `tsxElementResolution17`). Fix: **template literals normalize CR/CRLF to LF**
  (ECMA-262 §12.9.6) — the cooked-value decoder kept source line terminators
  as-is, so a template containing a CRLF mismatched a `"…\n…"` string-literal
  annotation (`stringLiteralTypesWithTemplateStrings01.ts`). Regression:
  `tests/template_crlf_normalization.rs`.
  Verified: shards 0–25 all green under `--fail-on new`
  (48/39/46/43/51/28/43/41/40/37/50/45/36/34/35/37/34/44/29/40/51/43/46/40/38/42
  — shards 2 +1, 12 +2, 13 +1, 14 +1, 17 +3, 20 +1, 21 +1, 22 +2, 23 +1,
  24 +1, 25 +1; 0 unexpected, 0 XPASS), difftsc **56/56**,
  fmt/clippy/guards clean.

- **Conformance shard 24/64**: match 37 → **38/90**, unexpected **2 → 0**,
  XPASS 3 pruned (`logicalAssignment9`, `superCallParameterContextualTyping3`,
  `stringLiteralTypesOverloadAssignability05`). Fixes:
  (a) **Interface-extends generic nominal rule** (tsc
  `callSignatureAssignabilityInInheritance6.ts`, 0/7 → **7/7**) — an
  interface type parameter is nominal to its container and never unifies
  with a *method's* type parameter; a concrete member mentioning the
  interface's `T` cannot satisfy a generic base signature ("two different
  types with this name exist"). The extends check now treats that shape as
  incompatible instead of letting the method-generic instantiation unify the
  two `T`s. Regression: `tests/interface_extends_generic.rs`.
  (b) `TwoInternalModulesThatMergeEachWithExportedAndNonExportedInterfacesOfTheSameName.ts`
  **manifested as expected-xfail**: the externally-visible `A.Point` must be
  the *exported-only* shape (`{x, y, toCarth}`) — non-exported namespace
  members must not merge into it. Our namespace export-visibility model
  currently merges them (4 props), so the TS2403 redeclaration check misfires.
  Recorded as a namespace export-visibility model gap (see roadmap).

- **Conformance shard 23/64**: match 39 → **40/105**, unexpected **2 → 0**,
  XPASS 5 pruned
  (`taggedTemplateStringsWithTypeErrorInFunctionExpressionsInSubstitutionExpressionES6`,
  `intersectionTypeReadonly`, `stringLiteralTypesOverloadAssignability02`,
  `callGenericFunctionWithZeroTypeArguments`,
  `assignmentCompatWithNumericIndexer2`). Fixes:
  (a) **`new` on callables with error-recovery returns is void-compatible**
  (tsc `privateNameAccessorsCallExpression.ts`) — a getter returning an
  unannotated function expression infers `() => unknown`; the TS2350
  void-check now treats `unknown`/`any` returns as void-compatible (tsc is
  silent there under default options) while still flagging concrete non-void
  returns. Regression: `tests/new_void_compat.rs`.
  (b) `intersectionTypeOverloading.ts` **manifested as expected-xfail**:
  canonicalized intersections lose *source order* for callable overload
  resolution (`F & G` vs `G & F` — tsc resolves against the first-written
  member; our `TypeId`-sorted canonical order always picks the same first
  member). This is a determinism-doctrine tension (canonical order vs tsc
  source order) recorded on the roadmap, not a bug with a local fix.
  (c) **`shape_interning_is_order_independent` proptest rescoped** — same-name
  callable props (overloads) are order-*sensitive* per tsc (first-match
  resolution), so the proptest now asserts order-independence for non-overload
  props and determinism for overload props.

- **Conformance shard 22/64**: match 44 → **46/106**, unexpected **2 → 0**,
  XPASS 3 pruned (`conditionalOperatorWithIdenticalBCT`, `newWithSpreadES5`,
  `paramTagNestedWithoutTopLevelObject`). Fixes:
  (a) **Same-name methods across merged interface declarations form one
  overload set** (tsc `twoMergedInterfacesWithDifferingOverloads.ts`) —
  `merge_interned_decl_types` replaced the earlier declaration's callable
  prop wholesale (last-wins), so only the last declaration's overloads
  survived; callable props now concatenate overload lists with the *later*
  declaration's signatures first (tsc precedence). Merged *generic*
  interfaces unify type parameters positionally (TS2428 requires identical
  lists) — a second free `T` no longer leaks into overload resolution.
  Regression: `tests/interface_overload_merge.rs`.
  (b) **Namespace members are writable unless `const`** (tsc
  `exportAssignmentMergedModule.ts`) — the namespace/module object builders
  marked every member `readonly: true`, so `foo.Test.answer = …` on a
  `var` false-fired TS2540. Members now derive readonlyness from the
  declaration (`const` → read-only; `var`/`let`/functions writable).
  Regression: `tests/namespace_member_writable.rs`.

- **Conformance shard 21/64**: match 42 → **43/91**, unexpected **1 → 0**,
  XPASS 3 pruned
  (`destructuringObjectBindingPatternAndAssignment9SiblingInitializer`,
  `asOperatorNames`, `stringEnumInElementAccess01`). Fixes:
  (a) **Namespace-aware local def resolution** (`es2018IntlAPIs.ts`) — the
  HIR declaration lowerer's `local_defs` fallback was a flat
  name→def map, so a `var NumberFormat: NumberFormatConstructor` (VALUE)
  shadowed the same-named `interface NumberFormat` (TYPE) inside
  `declare namespace Intl`; construct-signature returns and `prototype`
  annotations interned as `Ref(var_def)`, typing `new Intl.NumberFormat()` as
  the *constructor* instead of the instance. `local_defs` is now a
  per-namespace `LocalDefIndex` (type/value/namespace slots, falling back
  only when the requested namespace has none). Regression:
  `tests/namespace_interface_var_merge.rs` (via agent-8).
  (b) **tsc erases `readonly` for property assignability** — the relate
  engine's prop-level `!dst.readonly && src.readonly → fail` rule (from the
  initial relation engine) wrongly rejected `as const` objects into writable
  targets (`{ localeMatcher: 'lookup' } as const` → `{ localeMatcher?: … }`).
  Removed; array/tuple readonlyness stays at the type-kind level.
  Regression: `tests/readonly_prop_assignability.rs`.

- **Conformance shard 20/64**: match 50 → **51/103**, unexpected **1 → 0**,
  XPASS 3 pruned (`parserRegularExpression6`,
  `subtypingWithObjectMembersOptionality`, `genericCallWithArrayLiteralArgs`).
  Fixes (tsc `privateNameStaticFieldDestructuredBinding.ts`):
  (a) **Destructuring defaults replace missing slots** — `{ a: X = 1 } = {}`
  gave `union(unknown, number)` = `unknown` (which then failed the target
  check); defaults now replace a missing/`undefined` slot with the default's
  type (tsc: binding = prop-minus-undefined ∪ default).
  (b) **Array literals in destructuring positions infer tuples** —
  `[x, [y]] = [1, [2]]` destructures positionally (was: union-element array
  `number | number[]` smeared across every target, false TS2322).
  (c) **Private-identifier access on `this.<unannotated field>` recovers the
  receiver** — `otherClass = A` stays `unknown` on the instance shape outside
  field-init contexts; the private-access check now recovers from the field's
  initializer before flagging TS2571.
  Regression: `tests/private_name_destructuring.rs` (4 tests).

- **Conformance shard 17/64**: match 41 → **44/92**, unexpected **3 → 0**,
  XPASS 9 pruned (`computedPropertyNamesContextualType8_ES5`,
  `taggedTemplateStringsWithTypeErrorInFunctionExpressionsInSubstitutionExpression`,
  `arrayLiteralInference`, `mergeTwoInterfaces2`, `importAliasIdentifiers`,
  `parserErrorRecovery_IncompleteMemberVariable1`, `parserRealSource2`,
  `inferingFromAny`, `tupleLengthCheck`). Fixes:
  (a) **Function-declaration expando bases** (tsc
  `bindSpecialPropertyAssignment`) — `function Outer() {}` joins
  `var Outer = {}` / `var Outer = function … {}` as expando bases under
  `checkJs`; the type-side qualified-name resolver now walks
  `qualified_def_members` from `DefKind::Function` heads too
  (`salsa/typeFromPropertyAssignment2.ts`, plus shard 2's
  `typeFromPropertyAssignment12.ts` from the var-function form).
  (b) **Overload sets preserve declaration order** — duplicate same-name
  method props merged via `store.intersection`, whose `TypeId` sort scrambled
  overload order: `c.foo('hi')` picked `(string) => Base` over
  `('hi') => Derived1` (false TS2741) depending on fingerprint luck.
  Callable props now concatenate overload lists in declaration order
  (`typesWithSpecializedCallSignatures.ts`; regression
  `tests/overload_declaration_order.rs`).
  (c) **Type-assertion overlap uses tsc's *comparable* relation** — new
  `COMPARABLE_OPTIONALITY` relate mode relaxes the strictNullChecks
  optionality gate (optional source prop may satisfy required target; raw
  types compared). `{required1, optional} as Foo` legal again
  (`optionalProperties01.ts`; regression `tests/assertion_comparable_overlap.rs`).

- **Workspace-suite archaeology (8 targets red since ~07-26/07-27, fixed)**:
  (a) **emit-js precedence constants** — the 07-26 `as`/`satisfies`
  precedence-level insertion shifted every operator up one; the
  hand-mirrored `CALL_MEMBER/PRIMARY/POSTFIX_PRECEDENCE` constants were
  stale (caught by their own `debug_assert_eq!`). Updated; emit-js green.
  (b) **emit-js bare fn-type params** — the 07-27 parser change (bare
  identifiers in function-type params are *names* with synthetic `any`, per
  tsc TS7051) made `(string) => void` print as `(string: any) => void`;
  test expectations realigned to the deliberate parser shape.
  (c) **vm-js NamedEvaluation order** — `eval_named_initializer` re-applied
  the inferred name *after* class evaluation, clobbering static `name()`
  methods (`var xCls2 = class { static name() {} }` → V8 says
  `typeof xCls2.name === "function"`); now only applies when no real name
  exists (anonymous `""` default still takes it). Two stale vm-js
  expectations realigned to spec (`cls.name === 'cls'` inferred name;
  `GetMethod` on primitives via `GetV` boxing).

- **Conformance shards 15–16/64**: match **37/87** and **34/80**, unexpected
  **0**, XPASS 7 pruned (`typeGuardsNestedAssignments`,
  `ExportClassWhichExtendsInterfaceWithInaccessibleType`,
  `jsDeclarationsReexportAliases`, `methodsReturningThis`,
  `classAppearsToHaveMembersOfObject`, `outFilerootDirModuleNamesAmd`,
  `constructSignaturesWithIdenticalOverloads`). No fixes needed — cleared by
  earlier work. **Shards 18–19/64** likewise: match **29/76** and **40/90**,
  unexpected **0**, XPASS 8 pruned (`taggedTemplateStringsWithTypedTagsES6`,
  `jsDeclarationsReusesExistingTypeAnnotations`,
  `subtypingWithConstructSignaturesWithOptionalParameters`, `asOperator2`,
  `mergeThreeInterfaces2`, `ExportVariableWithAccessibleTypeInTypeAnnotation`,
  `jsdocFunctionType`, `typeParameterAsTypeArgument`).

- **Conformance shard 14/64**: match 34 → **35/96**, unexpected **1 → 0**,
  XPASS 5 pruned (`emitCompoundExponentiationAssignmentWithIndexingOnLHS4`,
  `ExportVariableWithInaccessibleTypeInTypeAnnotation`,
  `parserAutomaticSemicolonInsertion1`,
  `objectTypeWithConstructSignatureHidingMembersOfFunctionAssignmentCompat`,
  `assignObjectToNonPrimitive`). Fix: **JSDoc `@this {…}` honored** (tsc
  `jsdoc/inferThis.ts`) — an explicit `@this` tag wins over the class-derived
  `this` type inside the annotated function's body; `@template T` +
  `@this {T}` + `@return {T}` checks `return this;` against `T` instead of
  false-TS2322 on the class instance/static type. Regression:
  `tests/jsdoc_this_tag.rs`.

- **Conformance shard 13/64**: match 33 → **34/90**, unexpected **1 → 0**,
  XPASS 2 pruned (`taggedTemplateStringsWithIncompatibleTypedTagsES6`,
  `subtypesOfAny`). Fix: **super call expressions type as `void`** (tsc
  `superCalls.ts`) — `check_call_expr` short-circuits `super(...)` to `void`
  after checking argument expressions; a `var p = super(''); var p = v();`
  redeclaration no longer false-fires TS2403. Regression:
  `tests/super_call_void.rs`.

- **Conformance shard 12/64**: match 34 → **36/75**, unexpected **2 → 0**,
  XPASS 5 pruned (`staticIndexSignature6`, `FunctionDeclaration8_es6`,
  `FunctionPropertyAssignments5_es6`, `emitRestParametersFunctionPropertyES6`,
  `jsdocReturnTag1`). Bonus: shard 2 gained
  `salsa/typeFromPropertyAssignment12.ts` (same expando mechanism; xfail
  pruned). Fixes:
  (a) **Shadowed private-identifier fields resolve lexically**
  (`privateNamesAndFields.ts`) — a derived class redeclaring `#foo` has two
  distinct slots (tsc keys private names by declaring class). `member_type`
  resolves a `#`-prop to the nearest enclosing class declaring the name,
  typed from that field's declaration — gated on *actual* shadowing (an
  ancestor also declares the name) so unshadowed members keep the
  structurally refined type (no TS2350 regression on
  `privateNameStaticFieldCallExpression`). Two companion fixes in
  `types-ts-interned`: the object-intersection `never`-collapse skips
  `#`-private keys whose brands differ (`B & A` stays inhabited), and an
  intersection *source* whose merged apparent type fails now falls through to
  the any-constituent rule (`B & A → A`; merged private brands are lost to a
  `declared_on` conflict). Regression: `tests/private_name_shadow_fields.rs`
  (5 tests).
  (b) **parse-js: arrow concise body excludes the enclosing comma**
  (ECMA-262 §14.2 ConciseBody is AssignmentExpression) —
  `(getX = (a: A) => a.#x, "_")` parses the comma at the enclosing sequence,
  not inside the arrow body (a real runtime-semantics mis-parse: `getX` would
  return `"_"`). One-line precedence fix (`expr_with_min_prec(2, …)`, the
  `class_heritage` idiom). Cleared `privateNameComputedPropertyName2/4`.
  (c) **JS expando function-expression-var bases** (tsc
  `bindSpecialPropertyAssignment`): `var Outer = function … {}` now registers
  as an expando base under `checkJs`, so `Outer.Inner = class …` resolves in
  value and JSDoc-type positions (`typeFromPropertyAssignment3.ts` shard 12,
  `typeFromPropertyAssignment12.ts` shard 2). Function *declarations* remain
  unmodelled (their type-side qualified-name resolution doesn't reach
  `qualified_def_members`; recorded gap). Regressions:
  `tests/js_expando_members.rs` (+3, incl. negative controls for arrows /
  function declarations).
  (d) Fixed a pre-existing workspace-clippy blocker in `vm-js`
  (`empty_line_after_doc_comments` at `map_set.rs:2021`).
  Verified: shards 0–22 all green under `--fail-on new`
  (48/39/46/43/51/28/43/41/40/37/50/45/36/34/35/37/34/44/29/40/51/43/46 —
  shards 2 +1, 12 +2, 13 +1, 14 +1, 17 +3, 20 +1, 21 +1, 22 +2; 0
  unexpected, 0 XPASS), difftsc **56/56**, fmt/clippy/guards clean.

## 2026-07-29 slice

- **Conformance shard 11/64**: match **45/97**, unexpected **0**, XPASS 4
  pruned (`derivedClassIncludesInheritedMembers`,
  `templateStringsWithTypeErrorInFunctionExpressionsInSubstitutionExpressionES6`,
  `interfaceWithMultipleBaseTypes2`, `everyTypeAssignableToAny`). Verified:
  shards 0–11 all green under `--fail-on new`
  (48/39/45/43/51/28/43/41/40/37/50/45, 0 unexpected, 0 XPASS, 0 timeouts),
  difftsc **56/56**, fmt clean.

- **Conformance shard 10/64**: match **47 → 50/109**, unexpected **3 → 0**,
  XPASS 5 pruned (`controlFlowInOperator`,
  `prototypePropertyAssignmentMergedTypeReference`,
  `awaitUsingDeclarationsWithAsyncIteratorObject`, `ES5For-of10`,
  `validUndefinedValues`). Verified: shards 0–10 all green under
  `--fail-on new` (48/39/45/43/51/28/43/41/40/37/50, 0 unexpected,
  0 XPASS), difftsc **56/56**, full suites **255/255 binaries green**,
  fmt/clippy clean.
  Fixes:
  (a) **Decorated class-expression ICE** — a decorated class expression
  (`@dec class {}`) inside a field initializer produced a `BodyKind::Class`
  HIR body whose only expr (the decorator) is inside the enclosing field
  initializer's span; `check_enclosing_class` skipped it via the
  field-initializer rule and then ICE'd "missing class body for checker"
  (17× ICE0002 in the fixture). Exprs covered by an enclosing field
  initializer are checked by that initializer's own body — they now count as
  covered for the missing-body decision
  (`esDecorators-classExpression-namedEvaluation.10`). Regression:
  `tests/decorated_class_expr.rs`.
  (b) **Context-sensitive bodies against unresolved generic signatures** —
  `new Promise((resolve) => { resolve({}) })` fired TS2345 against the free
  `T` while the executor body was checked with the uninstantiated signature.
  tsc binds unresolved type params as `unknown` (fallback) when checking
  context-sensitive bodies and validates against the instantiated signature
  afterwards. `refine_function_expr_with_expected` now substitutes the
  expected sig's free type params with `unknown` for the body check
  (`collect_mentioned_type_params` + `Substituter`); the post-resolution
  refine phase (instantiated sig) remains authoritative, so
  `new Promise<number>((resolve) => { resolve("s") })` and
  inference-resolved bodies still error correctly. Regression:
  `tests/context_sensitive_generic_body.rs`;
  `defaultExportInAwaitExpression01` matches.
  (c) **For-of head TDZ binding** — `for await (await using of of of)` fired
  TS2304 *and* TS2448 because the RHS was evaluated before the LHS bound.
  `using`/`await using` (and `let`/`const`) for-of heads now seed the loop
  pattern (TDZ) before evaluating the RHS, matching tsc's TS2448-only output
  (`awaitUsingDeclarationsInForAwaitOf.2`, issue #55555). Regression:
  `tests/for_of_head_tdz.rs`.

- **Recursive-generic expansion pathology fixed**
  (`statements/forStatements/forStatementsMultipleInvalidDecl.ts`, now
  **matching**; xfail pruned). Verified: shards 0–9 all green under
  `--fail-on new` (48/39/45/43/51/28/43/41/40/37, 0 unexpected, 0 XPASS),
  difftsc **56/56**, full suites green modulo two load-correlated flakes
  (`salsa_body_memo::body_edit_rechecks_only_the_edited_files_bodies` and
  harness `options::strict_null_checks_directive_reaches_rust_checker` —
  both pass standalone and single-threaded; the recheck-count assertion
  flakes only under the shared machine's heavy parallel load; the memo test
  flaked in suite runs before this work too).
  Three independent fixes, all oracle-verified:
  (a) **Structural arg substitution in `evaluate_ref`** — `new D<string>()`
  on `class D<T> { wrapped: D<D<T>> }` exploded (~190k `evaluate_ref` calls
  from 6 top-level relates; ~56s → baseline). Root cause: `evaluate_ref`
  expanded Ref *arguments* eagerly before caching/expanding, so each nesting
  level re-walked the full chain below it (quadratic); `(def, args)` cycle
  keys can never fire when args grow. Now args are substituted structurally
  via a new `substitute_only` walker (substitution without evaluation —
  tsc keeps type arguments as references; downstream evaluation expands
  lazily on demand). An earlier def-level deferral guard fixed the
  explosion but broke alternating recursion (`Foo<T extends G<T>>` with
  `G<T> { x: G<G<T>> }` — asymmetric deferral killed the recursive-pair
  cycle closure, false TS2344); the structural-args approach fixes the
  explosion *and* keeps recursive relates exact (both conformance cases
  verified matching: `forStatementsMultipleInvalidDecl`,
  `recursiveTypeInGenericConstraint`).
  (b) **TS2403 for-chain misses** — in a sequence of
  `for( var x = …;;){}` statements, every subsequent declaration after the
  first few went unchecked: seeded file bindings kept the *last*
  declaration's def (`and_modify` clobbering in
  `hir_align/defs.rs`), so the TS2403 "prev" type was the last decl's type
  instead of the first's. tsc keeps the FIRST declaration's type for a
  merged var; later `var` decls no longer clobber the first `var`'s def.
  (c) **Explicit type args vs non-generic overloads** —
  `new Array<number>()` fired TS2558 on lib `ArrayConstructor`'s
  non-generic `new (arrayLength?): any[]` overload; tsc silently excludes
  signatures without type parameters when explicit args are provided.
  Non-generic sigs are now skipped, and when *all* sigs are non-generic,
  TS2558 fires once and checking continues.
  Regressions: `tests/recursive_generic_perf.rs` (9 tests).

- **Conformance shard 9/64**: match **36/93**, unexpected **0**, XPASS 5
  pruned (`symbolType2`, `mergedInterfacesWithMultipleBases2`,
  `ExportClassWithAccessibleTypes…`, `jsdocTemplateClass`,
  `subtypingWithObjectMembersOptionality3`). Verified: shards 0–9 all green
  under `--fail-on new` (48/39/45/43/51/28/43/40/40/36, 0 unexpected,
  0 XPASS), difftsc **56/56**, fmt/clippy clean.
  `statements/forStatements/forStatementsMultipleInvalidDecl.ts` manifested
  as xfail (timeout): `new D<string>()` on a recursive generic class
  (`wrapped: D<D<T>>`) explodes evaluation — profiled with `perf` +
  counters (relate count is tiny; the ctor-resolution relate of
  instantiated-vs-generic descends the nested wrapped chain with unique
  RefKeys per level and eager arg re-walking). Root fix needs a dedicated
  perf slice; full mechanism recorded on the roadmap.

- **Conformance shard 8/64**: match **39 → 40/98**, unexpected **1 → 0**,
  XPASS 1 pruned (`salsa/constructorFunctionMethodTypeParameters`).
  Verified: shards 0–8 all green under `--fail-on new`
  (48/39/45/43/51/28/43/40/40, 0 unexpected, 0 XPASS), difftsc **56/56**,
  full suites **252/252 binaries green**, fmt/clippy clean.
  `types/mapped/mappedTypes4.ts` fixes (all oracle-verified):
  (a) **Naked-type-param union-source inference** — covariant inference
  distributed argument unions per member even for a naked `T`, then
  first-won one member (`boxify(x)` with `x: A | B | undefined` inferred
  `T = B`, false TS2345). tsc keeps the source union as a single candidate
  when the target is a bare type parameter (`inferFromTypes`); distribution
  now only happens for union/structured targets.
  (b) **Indexed access over intersections** — `(Z & {})["a"]` evaluated to
  `unknown` (no arm); now gathers the property across members
  (`(A & B)[K]` = `A[K] & B[K]` over declaring members) —
  `Clone<Z> = { [P in keyof (T & {})]: (T & {})[P] }` evaluates.
  (c) **Homomorphic mapped-type collapse** (`instantiateConstituent`) — new
  `MappedType.homomorphic_var` field (set at lowering; eager substitution
  can't erase it): instantiating the homomorphic variable with a
  non-mappable source yields the source itself (`DeepReadonly<number>` is
  `number`; mappable = AnyOrUnknown | InstantiableNonPrimitive (type
  params, indexed access, conditionals, mapped) | Object | Intersection —
  a *free* `T` is NOT collapsed). Union sources distribute per constituent
  with primitives passing through (`DR<A | undefined>` =
  `DR<A> | undefined`). Enables recursive homomorphic mapped types
  (`DeepReadonly<Foo>` → full deep shape; TS2403 identity
  `var x1: DeepReadonly<Foo>; var x1: DeepReadonlyFoo` suppressed).
  Regressions: `tests/mapped_instantiation.rs` (7), interned eval probe
  cases folded into eval suite runs.

- **JS expando property-assignment namespaces implemented** (tsc
  `bindSpecialPropertyAssignment`): `salsa/typeFromPropertyAssignment24.ts`
  and `jsdoc/jsdocTypeReferenceToMergedClass.ts` both match tsc (xfail
  manifest entries pruned). In `.js`/`.jsx` under `checkJs`,
  `Outer.X = class {…}` / `Outer.X = function …` (+ `Outer.X.prototype =
  {…}`) where `Outer` is a top-level `var Outer = {}` register `X` in the
  outer var's value+type namespaces: `new Outer.X()` gives the instance,
  `@type {Outer.X}` resolves (no more TS2694), and cross-file members merge
  onto the canonical global var def. Implementation:
  `typecheck-ts/src/program/state/analysis/expando.rs` (scanner +
  registration), a var-head fallback in
  `program/types/resolver/imports.rs`, and a binding-site assignability skip
  in `check/body/exprs.rs`. Regressions:
  `typecheck-ts/tests/js_expando_members.rs` (7 tests). Unmodeled: nested
  statics (`Outer.X.Y = …`, recorded but skipped), arrow/other RHS, computed
  names, prototype absence → `{}` instance. Feature implemented by a
  delegated subagent; review + full verification by the owning agent.
  Verified: shards 0–7 green under `--fail-on new` (48/39/45/43/51/28/43/40
  — shard 1 gained `typeFromPropertyAssignment24`, shard 7 gained
  `jsdocTypeReferenceToMergedClass`), difftsc **56/56**, fmt/clippy clean.
  Two stale test expectations realigned to the live oracle in the same pass:
  the `argument_count_error` litmus fixture (TS2554 anchors on the callee
  per tsc, not the args), harness `type_params.rs`
  (`conflicting_primitive_type_arguments_reject` — tsc takes the first
  candidate and rejects the second arg for unrelated primitives; no union),
  and the conformance-mini snapshot baselines re-blessed (they predate the
  `strictPropertyInitialization` forwarding in the harness tsc options map).
  Full suites re-verified: **250/250 binaries green**.

## 2026-07-28 slice

- **Conformance shards 6–7/64**: shard 6 **43/103** (already clean, 3 XPASS
  pruned: `asOpEmitParens`, `superCallParameterContextualTyping1`,
  `paramTagNestedWithoutTopLevelObject2`); shard 7 **39/95**, unexpected
  **1 → 0**, XPASS 5 pruned (`asyncQualifiedReturnType_es5`,
  `mergedInterfacesWithMultipleBases`, `mappedTypes3`,
  `recursiveTypeInGenericConstraint`,
  `subtypingWithCallSignaturesWithOptionalParameters`).
  `jsdoc/jsdocTypeReferenceToMergedClass.ts` manifested as xfail — the JS
  property-assignment-namespace feature gap (tsc
  `bindSpecialPropertyAssignment`; `Workspace.Project = function wp() {}`
  should register a value+type namespace member), same root as
  `salsa/typeFromPropertyAssignment24.ts` (roadmap). Verified: shards 0–7
  all green under `--fail-on new` (48/38/45/43/51/28/43/39, 0 unexpected,
  0 XPASS), difftsc **56/56**, fmt clean.
- **Pre-existing harness test failure fixed** —
  `expectations::tests::manifest_loads_from_fixture_path` asserted on the
  pre-sprint 13-line fixture manifest (`err/parse_error.ts`, `multi/**`),
  which the 3656-entry live conformance manifest replaced; now looks up two
  real ids. Harness suite green (102 passed).

- **Conformance shard 5/64**: match **26 → 28/78**, unexpected **2 → 0**.
  Verified: shards 0–5 all green under `--fail-on new`
  (48/38/45/43/51/28, 0 unexpected, 0 XPASS), difftsc **56/56**, full
  suites **225/225 binaries green**, fmt/clippy clean.
  Fixes:
  (a) **AsyncIterableIterator TS2318 is a lib-availability check** — the
  async-generator grammar check fired purely on `target ≤ es2017`; tsc checks
  whether the *global type* exists (`--target es2015 --lib esnext` accepts
  async generators; oracle-verified). Now resolves `AsyncIterableIterator`
  through the type resolver and only emits when actually missing.
  (b) **Derived-class private-name branding** — `this.#foo` in `class B
  extends A` (both declaring `#foo`) mis-branded to `A.#foo` (false TS18013,
  anchored at `super()`): `nominal_class_index_for_type` matched
  intersection members only by exact equality against each class's full
  instance type, so a derived class's own-shape member (`B & A`) never
  matched and the nominal fell back to the base. Now also accepts
  intersection-membership containment. Additionally, tsc allows `b.#foo`
  inside the base class when the receiver *derives from* the lexical
  declarer — the nominal comparison is now an extends-chain inclusion
  (`class_extends_chain_includes`) instead of exact declarer equality.
  Regressions: `tests/private_name_heritage.rs`;
  `privateNamesAndMethods` + `emitter.asyncGenerators.objectLiteralMethods`
  match.

- **Conformance shard 4/64**: match **49 → 51/101**, unexpected **2 → 0**,
  XPASS 6 pruned (`computedPropertyNamesContextualType9_ES5`,
  `jsdocParseParenthesizedJSDocParameter`, `parserES5ComputedPropertyName3`,
  `parserRegularExpressionDivideAmbiguity6`, `spellingUncheckedJS`,
  `ES5For-of9`). Cross-fix: shard 3 gained `objectLiteralContextualTyping`
  (now **43/98**, pruned). Verified: shards 0–4 all green under
  `--fail-on new` (48/38/45/43/51, 0 unexpected, 0 XPASS), difftsc
  **56/56**, full suites **224/224 binaries green**, fmt/clippy clean.
  Fixes:
  (a) **Method-key DA exemption** — tsc skips definite-assignment analysis
  for computed keys of *method* members (`{ [s]() {} }`, accessors, class
  members incl. fields) but still checks plain-property keys (`{ [s]: 1 }`);
  our flow binder DA-flagged all computed-key reads. The binding collector
  now marks idents inside method-member keys (function-valued `KeyValue`,
  getters/setters) via `suppress_use_before_assignment`. Regression:
  `tests/computed_key_da.rs`; `computedPropertyNames10_ES6` matches.
  (b) **`{}` type → object relate** — the fast path rejected every
  `EmptyObject → Object(shape)` relation; tsc assigns `{}` to shapes whose
  properties are all optional (incl. the `object` keyword and
  index-signature-only targets like `Record<string, T>`), rejecting only
  required props and call/construct signatures. `'a' in {}` is therefore
  legal while `'a' in 42` stays TS2322. Regression:
  `types-ts-interned` fast path + `tests/empty_object_relate.rs`;
  `parserForStatement9` matches.

- **Conformance shard 3/64**: match **39 → 42/98**, unexpected **3 → 0**,
  XPASS 4 pruned (`abstractPropertyInitializer`,
  `taggedTemplateStringsWithIncompatibleTypedTags`,
  `jsdocParseHigherOrderFunction`, `paramTagNestedWithoutTopLevelObject3`).
  Verified end-of-day: shards 0–3 all green under `--fail-on new`
  (48/38/45/42, 0 unexpected, 0 XPASS), difftsc **56/56**, full
  `typecheck-ts` + `types-ts-interned` suites **222/222 binaries green**,
  fmt/clippy clean.
  Fixes:
  (a) **Computed object-literal keys** — previously skipped entirely
  (`ClassOrObjKey::Computed(_) => continue`), so `{ [+"foo"]: "", [+"bar"]: 0 }`
  inferred `{}`. Now follows tsc (`checkComputedPropertyName` +
  `getIndexInfosOfIndexSymbol` / `getObjectLiteralIndexInfo`): string/number
  *literal* keys become named properties; non-literal keys assignable to
  `string`/`number`/`symbol` contribute to a synthesized index signature
  (`any` and numeric-enum keys take the numeric branch, mixed
  `string | number` unions the string branch); the string index unions in all
  named siblings, the number index numeric-named siblings. Shared helpers in
  `check/body/bindings.rs` (`classify_computed_obj_key` /
  `synthesize_computed_indexers`), wired into all three object-literal paths
  (AST non-contextual, AST contextual, HIR flow). Plus the relate rule: a
  **number** index signature satisfies a **string** target index signature
  (tsc `indexSignaturesRelatedTo`'s explicit fallback).
  Regressions: `tests/computed_object_keys.rs`,
  `computedPropertyNamesContextualType5_ES6` matches.
  (b) **TS2352 assertion overlap widen-first** — tsc `checkAssertionDeferred`
  widens the source expression type to its base literal form *before* the
  comparable check, so `"foo" as "bar"` (widened `string`, target `"bar"`
  comparable to it) is allowed; same for `1 as 2`,
  `fooOrBar as "baz"`, `"baz" as typeof fooOrBar`. Regression:
  `tests/type_assertion_overlap.rs` (+2); `stringLiteralsWithTypeAssertions01`
  matches.
  (c) **TS2403 structural identity** — subsequent-`var` comparison was
  `TypeId` equality; tsc uses `isTypeIdenticalTo` (structural identity), so a
  class instance and a structurally equal object type are "the same type".
  Now mutual assignability with an `any` guard (tsc identity treats `any`
  strictly). Regression: `tests/subsequent_var_identity.rs`.
  (d) **Merged ambient namespace+class resolution** — three fixes:
  (i) class/enum namespace members map through `value_defs` in
  `interned/ensure.rs` so `N.C` is the constructor (was the instance type —
  `new N.C(0)` fired TC2000 even single-file); (ii) cross-file decls of the
  same namespace no longer consume the shared member bucket for the first
  decl (the others built empty objects; which one a body seeded from was
  file-order dependent — the harness landed on the empty view);
  (iii) **cross-file ambient class value bindings** — `declare class C` in a
  `.d.ts` + `new C(...)` in another file fired TC2000 because every
  value-binding path used the class def's *instance* type; the salsa
  `BodyCheckContext` now carries `value_defs` and the three lookup sites
  (`db::check_body`'s `map_def_ty`, the heritage ctor materialization, and
  `ProgramState`'s `map_def_ty` / `dts_value_bindings` / `type_of_def`)
  remap class/enum defs through it. Regressions:
  `tests/namespace_class_merge.rs`;
  `AmbientModuleAndAmbientWithSameNameAndCommonRoot` matches.
  (e) Object-literal *method* return types are not inferred in expression
  position (`{ m() { return 1; } }.m` → `() => unknown`; tsc `() => number`)
  — pre-existing gap surfaced during (a), recorded on the roadmap.

- **Conformance shard 1/64**: match **35 → 38/97**, unexpected **4 → 0**, XPASS
  1 pruned (`mappedTypeConstraints`). Fixes:
  (a) **CSI marker identity** — generic-vs-generic signature relating fell into
  the different-arity block when one side's markers were already substituted
  away, and CSI's `(None, Some(constraint))` fallback substituted the
  constraint instead of keeping a destination-mentioned shared marker;
  `I9 extends A` (`callSignatureAssignabilityInInheritance3.ts`) now relates.
  The different-arity hard-false now applies only when both sides are generic.
  (b) **Lib-`Array` rest params** — `...callbacks: Array<(x: T) => any>` (lib
  interface form, interned as `Ref(Array, [elem])`) now normalizes to the
  intrinsic array at signature lowering, so rest-element expansion finds the
  element; tagged-template substitutions are contextually typed by it
  (`taggedTemplatesWithTypeArguments1.ts`).
  (c) **Empty-array binding positions (exact tsc rule)** — `const array = []`
  binds as `any[]` when `--noImplicitAny` is on (tsc `autoArrayType`; ours
  does not evolve per-push) *or* when `--strictNullChecks` is off
  (`undefinedWideningType` widens to `any` for declarations); under
  `--strictNullChecks` with `--noImplicitAny` off it keeps the synthesized
  `never[]` and `push` errors TS2345. Return/argument positions keep the
  `never[]` synthesis under `strictNullChecks`. Rule verified against tsc
  5.9.3 + `checker.ts` (`getTypeForVariableLikeDeclaration` /
  `checkArrayLiteral` / `getWidenedType`). Regressions:
  `tests/empty_array_binding.rs`, `tests/tagged_template_rest_args.rs`,
  `tests/rest_call_sig_assign.rs` (+I9 case).
  (d) **`checkJs` gate** — `.js`/`.jsx` files without `checkJs` are now
  parse-only (tsc `allowJs` semantics, oracle-verified: no semantic
  diagnostics, not even TS2304/TS2307; parse/grammar diagnostics survive).
  `CompilerOptions.check_js: Option<bool>` gates in
  `program/state/diagnostics.rs`; the harness maps `@checkJs`. This is what
  actually clears `computedPropertyNames52.ts` (`@allowJs` JS file, no
  `@checkJs` → tsc reports nothing). Regressions:
  `tests/check_js_commonjs_globals.rs`
  (`js_file_without_check_js_is_parse_only`,
  `js_file_without_check_js_keeps_parse_errors`); the 9 JS-exercising test
  files now set `check_js = Some(true)`.
  (e) `salsa/typeFromPropertyAssignment24.ts` manifested: JS
  property-assignment namespaces (`Outer.Inner = class {…}`) are a feature
  gap (tsc `bindSpecialPropertyAssignment`), recorded on the roadmap.
- **`keyof never` is `string | number | symbol`** — oracle-verified vs tsc
  5.9.3 (was `never`). `KeySet::Unknown` (the universal set) now models
  `Never` in the key algebra, so never-reduced intersections
  (`{ b: number } & { b: boolean }`) key out per tsc; `keyof unknown` /
  `keyof {}` stay `never`. Regressions: `types-ts-interned/tests/eval.rs`
  (renamed `keyof_never_is_never` → `keyof_never_is_string_number_symbol`,
  new `keyof_never_reduced_intersection_matches_tsc`). Detail:
  [types-ts-interned](../crates/types-ts-interned.md).
- **Stale type-param relate test** — `type_params_treated_as_unknown`
  contradicted the (2026-07-27) nominal-target semantics it predated;
  rewritten as `free_type_params_are_nominal_targets` with oracle-verified
  expectations (`number`/`unknown` ↛ `T`; `any` → `T`; `T` → `unknown`/`any`).
- **TS2715 nested-function false positive (pre-existing)** —
  `check_enclosing_function` resolved class membership by tightest
  *containing* member span, so functions nested inside a constructor
  inherited `constructor_class_index` and false-flagged `this.abstractProp`.
  Membership is now exact `Func.loc` match only (tsc
  `isNodeUsedDuringClassInitialization` quits at function boundaries).
  Regression: `tests/abstract_class_da.rs`
  (`nested_function_may_read_abstract_prop`). Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **difftsc floor restored 56/56** (was 53/56 on the dirty tree):
  (a) contextual lambda returns against *generic* call parameters are
  inference targets, not declared ones — hard return-assignability checks are
  deferred (`expected_return_defer_type_params`) until the call instantiates
  the signature; regression `tests/contextual_generic_return.rs`.
  (b) program-diagnostic dedupe collapsed the 8 per-name TS2318 "Cannot find
  global type" diagnostics into 1 (same code+span); dedupe is now
  code+span+message except TS2352 (display-variant);
  regression `tests/required_global_types.rs`.
- **Loop-variable typing** — the AST binding path seeded `for…in`/`for…of`
  variables as `unknown`, poisoning downstream assignment checks
  (`unknown` ↛ declared). `for…in` vars are now `string` (tsc), `for…of`
  vars take the iterated element type (`ES5For-of34.ts`'s `string` → number
  TS2322 correctly fires). Regressions: `tests/loop_variable_types.rs`.
- **Regex literals are `RegExp`** — were `string` (flow path) / `unknown`
  (AST path); both now resolve the global `RegExp` interface
  (`x: string | … | RegExp | Function = /a/` no longer false-TS2322s).
  Regression: `tests/regex_literal_type.rs`.
- **TS2352 assertion overlap uses tsc comparability** — `x as T` /
  `<T>x` overlap now includes tsc's `comparableRelation` literal relaxation
  (a primitive is comparable to a literal of its kind), so
  `str = t as string` / `t = <T>s` with `S = "a"|"b"`, `T = S[] | S` no
  longer false-fire. Regression: `tests/type_assertion_overlap.rs`
  (`union_assertion_overlaps_via_literal_comparability`).
- **Signature arity rule (tsc `compareSignaturesRelated`)** — the floor is
  `getMinArgumentCount(source) > getParameterCount(target)`: source *required*
  vs target *total* (was required-vs-required, over-strict). `(a: any) => any`
  now matches `(a?: number) => number`. Regression:
  `types-ts-interned/tests/relate.rs`.
- **Overload set → unconstrained generic target** — after exact
  instantiation fails, each non-generic source overload is also related
  against the *erased-to-`any`* target (tsc `signaturesRelatedTo` +
  `getErasedSignature`), and `infer_type_args_into` gained the
  `(Callable, Object-with-call-signatures)` arm. Cleared `b17 = a17`;
  `assignmentCompatWithCallSignatures4.ts` is down to one residual.
- **Conformance shard 0/64 re-measured vs live tsc**: match **45 → 48/105**,
  unexpected **3 → 0**, XPASS 4 pruned
  (`emitClassDeclarationWithTypeArgumentAndOverloadInES6`,
  `validBooleanAssignments`, `genericCallWithObjectTypeArgsAndStringIndexer`,
  `assignmentCompatWithCallSignatures4.ts` — the last fixed by the shard-1 CSI
  marker-identity work below, which **disproved the earlier erased-signature
  cache-poisoning theory**: the real mechanism was the different-arity
  hard-false plus constraint substitution breaking marker identity; the
  `a17 = b17` ordering effect was the same relate bug seen through a warmed
  cache entry, not cache corruption). **Shard 2/64 re-measured**: match
  **45/99**, unexpected **0**, timeouts **0** (pathology cleared), XPASS 4
  pruned (`emptyAssignmentPatterns02_ES5`, `generatorTypeCheck45`,
  `optionalChainingInference`, `innerTypeParameterShadowingOuterOne2`).
  All three shards green under `--fail-on new`; re-verified again after the
  empty-array rule correction + `checkJs` gate with identical floors
  (48/38/45, 0 unexpected, 0 XPASS) — `computedPropertyNames52` now matches
  via the gate. Full `typecheck-ts` suite re-verified the same day:
  **198/198 test binaries green**; difftsc **56/56**.
- **`parserRealSource12` pathology (sprint regression) fixed** — the
  2026-07-25 object-intersection never-reduction called
  `store.intersection(prop_types)` per shared property, which recursed back
  into `object_intersection_has_never_required_property` per nested object
  and rebuilt a `HashMap<PropKey, Vec<…>>` per intersection call — ~50 % of
  the run in malloc/free churn; the case (and the full `typecheck-ts` suite
  via `engine_budget.rs`) hung indefinitely (cancellation unobservable in
  that path). The reduction now uses an allocation-free structural
  disjointness check (distinct primitive families / distinct literals; the
  full relation is no longer consulted). `parserRealSource12.ts`:
  90 s+ timeout → **4.4 s match**; `engine_budget` 3/3 in 35 s;
  difftsc stays 56/56. Regression: existing
  `types-ts-interned/tests/canonicalization.rs` +
  `typecheck-ts/tests/engine_budget.rs`. Detail:
  [types-ts-interned](../crates/types-ts-interned.md).
- **Suite triage wave (16 failures, all oracle-verified)** —
  (a) TS2741/TS2739 code selection now treats `EmptyObject` as an analyzable
  empty shape in `object_like_properties`, so `{}` → `Record<K, any>` reports
  missing properties per tsc;
  (b) generic arrows keep their source type params on the refined signature
  so the relate engine's CSI instantiates them against non-generic targets
  (free `TypeParam` params in non-generic signatures are nominal and
  mis-fired — `rest_call_sig_assign.rs` 34/34);
  (c) `typeof x === "number"` classification recurses into unions so
  literal-union-lowered enums (`Color` → `0 | 1 | 2`) classify numeric again
  (`TypeGuardWithEnumUnion`-shaped TS2403s cleared);
  (d) qualified `typeof` member chains that are not namespace paths
  (`typeof window.document.title`) lower to nested `IndexedAccess` over the
  head value's type — the last-segment top-name fallback manufactured
  self-references;
  (e) the `type_of_def` cycle guard no longer *inserts* `any` into
  `interned_def_types` — genuine self-cycles land the same `any` at
  completion, while re-entrant lookups during in-flight resolution
  (`import Alias = N.x`) no longer poison the completion's replace check;
  (f) stale test expectations realigned to the live oracle: generic-call
  inference first-wins (`f<T>(a: T, b: T)` at `("", 0)` → `T = string`, tsc
  rejects the second arg), single-sig arity misses are TS2554 (not TC2000),
  `new () => T` lowers to an object carrying a construct signature (not
  `Callable`), and destructuring from an unresolved RHS emits only TS2304
  under `--noImplicitAny` (no extra TC3000).
- **Dead API removal** — `semantic_js::assoc::js::JsAssocTables` + its 8
  helpers deleted (no producer or consumer anywhere in the workspace).
- **Docs** — testing.md's stale "blanket test262 xfail" claim corrected
  (precise per-cluster manifest since 2026-07-23); workflows.md deps-graph
  path corrected to `wiki/architecture/deps.md`.
- **rustfmt** — repo-wide normalization (331 files); the tree now passes the
  CI `fmt` gate.

## 2026-07-27 slice

- **Object spread props + Object method apparent type** — `{ ...x }` now merges
  enumerable own properties into the literal shape (was `{}` → false TS2741);
  `EmptyObject` / interface member lookup falls back to lib `interface Object`
  (`hasOwnProperty`, …) so `--noImplicitAny` no longer TC3000 on prototype
  methods. Exact XPASS: `intersectionIncludingPropFromGlobalAugmentation`.
  Manifest: **3682 → 3681** `status = "xfail"`. Regression:
  `typecheck-ts/tests/object_spread_props.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **TS2454 bare `true`/`false` unreachable branches** — tsc binder marks the
  opposite branch of a bare `TrueKeyword`/`FalseKeyword` as `UnreachableFlow`
  (no TS2454); parenthesized `(true)` does not. HIR now preserves
  `Expr.parenthesized`; flow sets `Env.suppress_da` on dead branches of `?:`,
  `&&`/`||`, `if`/`while`/`for`/`do`. Exact XPASS:
  `bestCommonTypeOfConditionalExpressions2`. Manifest: **3683 → 3682**
  `status = "xfail"`. Regressions: `typecheck-ts/tests/ts2454_residuals.rs`,
  `hir-js/tests/lowering.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **TS2352 type-assertion overlap** — `<T>e` / `e as T` emits **TS2352** when
  neither type is assignable to the other (unions overlap on any constituent);
  program diagnostics dedupe by code+span. Exact XPASS:
  `objectTypesIdentityWithNumericIndexers2`,
  `objectTypesIdentityWithStringIndexers2`, `typeAssertionsWithUnionTypes01`.
  Manifest: **3686 → 3683** `status = "xfail"`. Regression:
  `typecheck-ts/tests/type_assertion_overlap.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **enumAssignability** — Global boxed primitives (`Number`/`String`/…) lower
  to their primitive types for assignability (`var p: Number = e`). Exact
  XPASS (22× TS2322). Manifest: **3687 → 3686** `status = "xfail"`. Regression:
  `typecheck-ts/tests/enum_to_number_object.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **enumAssignabilityInInheritance** — First-match overload order (no
  SignatureId re-sort); subsequent-`var` TS2403 compares to the first
  declarator's type; enum member access is the enum `Ref` with distinct enums
  nominal before normalize. Exact XPASS (2× TS2403 @ 2185/2281). Manifest:
  **3688 → 3687** `status = "xfail"`. Regressions:
  `typecheck-ts/tests/subsequent_var_enum_overload.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **assignmentCompatWithNumericIndexer3** — Top-level type-decl seeding now
  only enters `namespace`/`Block` spans that enclose the body being checked,
  and those nested decls overwrite file-root same-named types (so
  `namespace Generics { class A<T> }` shadows outer `class A`). Exact XPASS:
  `assignmentCompatWithNumericIndexer3`. Manifest: **3689 → 3688**
  `status = "xfail"`. Regressions: `typecheck-ts/tests/ns_class_shadow.rs`,
  `typecheck-ts/tests/numeric_indexer3.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **NumericIndexer3 partial + typeParameterAssignability2** — Free type params
  are nominal as assignment *targets* (only `any` / same param); annotated
  non-union bindings keep `declared_ty` as the post-assign flow type (no RHS
  subtype rewrite); type-param *sources* expand to constraints when the param
  is absent from the destination. Exact XPASS: `typeParameterAssignability2`.
  Manifest: **3690 → 3689** `status = "xfail"`. Regressions:
  `types-ts-interned/tests/relate.rs`,
  `typecheck-ts/tests/numeric_indexer3.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **undefined/null AssignableToEveryType** — `null`/`undefined` ↛ type params
  under `strictNullChecks`; annotated `void` bindings use normal assignability
  (`var g: void = null` → **TS2322**). Exact XPASS:
  `undefinedAssignableToEveryType`, `nullAssignableToEveryType`. Manifest:
  **3692 → 3690** `status = "xfail"`. Regressions:
  `types-ts-interned/tests/relate.rs`,
  `typecheck-ts/tests/undefined_assignable_to_type_param.rs`,
  `typecheck-ts/tests/null_to_void.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **typeParameterAssignability3 + tuple/array XPASS** — Nested arrows inside
  class field initializers now inherit class `this` and class type-param scope,
  so `this.t = this.u` for unrelated `T`/`U` emits **TS2322** (no false
  **TC2008**). Also pruned already-exact
  `assignmentCompatBetweenTupleAndArray`. Exact XPASS:
  `typeParameterAssignability3`, `assignmentCompatBetweenTupleAndArray`.
  Manifest: **3694 → 3692** `status = "xfail"`. Regression:
  `typecheck-ts/tests/type_param_assignability3.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **optionalPropertyAssignableToStringIndexSignature** — Optional props vs
  *string* indexers check as `T` (not `T | undefined`); numeric indexers keep
  optionality. Assignment writes use `Binding.declared_ty` so a prior OK assign
  cannot narrow away the declared index signature. `undefined!` strips to
  `never`; `T <: T | U` no longer short-circuits in `assignable_special`. Exact
  XPASS: `optionalPropertyAssignableToStringIndexSignature`. Manifest:
  **3695 → 3694** `status = "xfail"`. Regressions:
  `types-ts-interned/tests/relate.rs`,
  `typecheck-ts/tests/optional_prop_string_index.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Bare function-type params `(x) => T`** — Parser treated a bare identifier
  before `)`/`,` as a type reference; now it is a parameter name with
  synthetic `any`, clearing false **TC2008**. Exact XPASS:
  `anyAssignableToEveryType2`, `anyAssignabilityInInheritance`. Manifest:
  **3697 → 3695** `status = "xfail"`. Regressions:
  `parse-js/tests/regressions/bare_fn_type_param.rs`,
  `typecheck-ts/tests/fn_type_param_in_index.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **nullAssignedToUndefined TS2539** — Assignments to ambient globals
  `undefined` / `NaN` / `Infinity` (assignment LHS is `IdPat`) emit **TS2539**;
  `typeof undefined` resolves to the undefined primitive (no false TS2304).
  Exact XPASS: `nullAssignedToUndefined`. Manifest: **3698 → 3697**
  `status = "xfail"`. Regression: `tests/null_assigned_to_undefined.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **EnumIndexer / enum member literals** — HIR enum members now carry numeric/
  string constant values (with auto-increment); enum types lower to literal
  unions so `Record<E, any>` expands to required properties. Also stopped
  skipping assignability checks when the destination is a mapped type. Exact
  XPASS: `assignmentCompatWithEnumIndexer`. Manifest: **3699 → 3698**
  `status = "xfail"`. Regressions: `hir-js/tests/types_lowering.rs`,
  `typecheck-ts/tests/enum_record_empty.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **GenericCallSignatures CSI expand fallback** — When equal-arity type-param
  identity mapping rejects, expand each type param to its constraint and
  compare erased signatures so `<S extends C[]>(x: S)` ↔ `<T extends C>(x: T[])`
  both ways. Exact XPASS: `assignmentCompatWithGenericCallSignatures`. Also
  pruned already-exact `assignmentCompatWithConstructSignaturesWithOptionalParameters`.
  Manifest: **3701 → 3699** `status = "xfail"`. Regression:
  `tests/rest_call_sig_assign.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **ObjectMembers5 TS2741 code selection** — AST assignment mismatch sites now
  route through `assignability_mismatch_code` (already used by HIR
  `check_assignable`), so `foo` vs `fooo` reports **TS2741** instead of
  **TS2322**. Exact XPASS: `assignmentCompatWithObjectMembers5`. Manifest:
  **3702 → 3701** `status = "xfail"`. Regression:
  `typecheck-ts/tests/object_members5_codes.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).

## 2026-07-26 slice

- **Nested namespace interface seeding (TC2008)** — HIR now registers
  interface/alias AST nodes in `node_to_def` and lowers them to
  `StmtKind::Decl`, so body-check `seed_type_decls_*` resolves nested
  `var b: Base` annotations. Exact XPASS:
  `constructSignatureAssignabilityInInheritance`. Manifest: **3703 → 3702**
  `status = "xfail"`. Regressions: `hir-js/tests/interface_stmt_decl.rs`,
  `typecheck-ts/tests/nested_iface_var_ann.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **GenericCallSignatures4 recursive constraints** — Equal-arity generic
  signature relating now maps source type params onto the destination first,
  then checks constraints with one-level expansion of destination type params
  to their constraints (`T extends I2<T>` ⇒ `I2<T> <: I2<I2<T>>`). Clears false
  **TS2322** on `x = y` while keeping `y = x`. Exact XPASS:
  `assignmentCompatWithGenericCallSignatures4`. Manifest: **3704 → 3703**
  `status = "xfail"`. Regression: `tests/rest_call_sig_assign.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Interface-extends TS2430 (call/construct sig inheritance)** — Interfaces
  intern as `Own & Base…` (always a subtype of each base); added a post-pass
  that checks own-only object properties against each `extends` base and emits
  **TS2430** on the derived interface name. Exact-match XPASS:
  `callSignatureAssignabilityInInheritance{,3,6}`,
  `constructSignatureAssignabilityInInheritance{3,6}` (base construct file
  still xfail: residual **TC2008**). Manifest: **3709 → 3704**
  `status = "xfail"`. Regression: `tests/interface_extends_assign.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Construct-signature assignment ratchet (ConstructSig 3–6 closed)** —
  `new (…) => R` now lowers to object construct signatures (not call
  `Callable`); object construct relating reuses CSI/overload rules with
  strict param variance. Exact-match XPASS:
  `assignmentCompatWithConstructSignatures{3,4,5,6}`. Manifest: **3714 →
  3710** `status = "xfail"`. Regression: `tests/rest_call_sig_assign.rs`.
  Detail: [typecheck-ts](../crates/typecheck-ts.md).
- **Call-signature assignment ratchet (CS3–CS6 closed)** — Follow-on after
  CS3: different-arity instantiate-source-only (+ constraint subst);
  `STRICT_TYPE_PARAMS` on generic↔generic compares; CSI clamps
  constraint-supertype return inferences; namespace sibling class value
  seeding + per-namespace `var` TS2403 scopes. Exact-match XPASS:
  `assignmentCompatWithCallSignatures{3,4,5,6}`. Manifest: **3717 → 3714**
  `status = "xfail"`. Regression: `tests/rest_call_sig_assign.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Call-signature assignment ratchet (CS3)** — Rest/optional/generic-arrow
  refine landed earlier (+4 XPASS). Follow-on: lib `Array`/`Promise`/… get
  default `out` variance; signature eval leaves named `Ref`s opaque under
  empty subst; CSI + overload-set → unconstrained generic. Exact-match XPASS:
  `assignmentCompatWithCallSignatures3`. Manifest was **3718 → 3717**.
  Regression: `tests/rest_call_sig_assign.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **typeRelationships / typeGuards ratchet (post-privateNames)** —
  (1) Pruned stale XPASS in `assignmentCompatibility` /
  `typeAndMemberIdentity` / `typeInference` / `typeGuards` (surgical only).
  (2) Naked type-param union inference: `T | Concrete` now infers from
  unmatched source constituents (`f1(e1)` → `T = number | boolean`), clearing
  false **TS2345** on `unionAndIntersectionInference2`. (3) AST `if` typeof
  binding overrides + enum-ref typeof classification (expand Ref for match
  only) clear false **TS2403** on `TypeGuardWithEnumUnion`. Manifest:
  **3762 → 3722** `status = "xfail"`; privateNames still **0**. Regressions:
  `tests/union_naked_param_inference.rs`, `tests/typeof_enum_narrow.rs`.
  Floors re-verified: `builtins-collections` **1620/1620**. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (last 2 parse residuals → 0)** —
  Nested-arrow speculation no longer sticky-commits on successful inner
  `(a)=>…` defaults inside `(getX=…, "_")` computed keys (**PS0002** → parse-ok
  + **TS2454**). `C[#bar]` recovers as array `C[]` with soft **PS0013** `]` /
  `,` + **PS0031**↔**TS1134**, then `C["#bar"]` is **TS2339** (private string
  index). Exact vs tsc. +2 XPASS: `privateNameComputedPropertyName2`,
  `privateNamesAndIndexedAccess`. Manifest: **−2** (then **3762**
  `status = "xfail"`; privateNames xfails **0**). Regressions:
  `parse-js` `tests/regressions/private_name_parse_recovery.rs` +
  `typecheck-ts` `tests/private_name_residual_next.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md) / [parse-js](../crates/parse-js.md).
- **Private-name residual burn-down (generic dual-instantiation / construct)** —
  Shared root cause for the last two semantic privateNames xfails: (1) deferred
  `C<U>` refs cached during `C<T>` instantiate → false **TS2339**; (2) structural
  relate of `C<number>`/`C<string>` cycle-assumed mutual assignability; (3) failed
  `a = b` overwrote binding so `b = a` vanished; (4) `new C(3)` inferred `C<3>`
  so `a.baz = 5` was false **TS2322**. Exact vs tsc. +2 XPASS:
  `privateNamesAndGenericClasses-2`, `privateNamesInGenericClasses`. Manifest:
  **−2** (then **3764** `status = "xfail"`; privateNames xfails **2**, both
  parse residuals). Regression: `tests/private_name_residual_next.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (class-`T` TC2008 on member anns)** —
  Class type-param scope for subsequent-property / SPI / HIR
  `declared_type` + value function signatures clears false **TC2008** on
  `#foo: T` / `#bar(): T` / accessors (noise cleared; full XPASS landed in
  generic dual-instantiation slice above).
- **Private-name residual burn-down (computed-key / useDefine brands / ctor-chain)** —
  Class-body computed keys set `enclosing_class_index` (lexical walk to outer
  `#`); duplicate named class-expr brands prefer lexical homonyms over
  `classes_by_name`; `extends Parent<T>` Instantiation heritage + class
  type-param scope clears false LOWER0003/TC2008. Exact vs tsc. +3 XPASS:
  `privateNameComputedPropertyName3`,
  `privateNameWhenNotUseDefineForClassFieldsInEsNext`,
  `privateNamesConstructorChain-2`. Manifest: **−3** (then **3766**
  `status = "xfail"`; privateNames xfails **4**). Regression:
  `tests/private_name_residual_next.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (bare `#` TS1127 + object-rest TS2339)** —
  Bare `#` PrivateIdentifier → soft **PS0030** (↔ **TS1127**); object-binding
  rest types drop private/`#` members (non-nominal) so `rest.#x` is **TS2339**.
  Exact vs tsc. +2 XPASS: `privateNameHashCharName`,
  `privateNameAndObjectRestSpread`. Manifest: **−2** (then **3769**
  `status = "xfail"`; privateNames xfails **7**). Regression:
  `tests/private_name_hash_rest.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (ctor-sig / TS1029 / getClass / contextual init)** —
  Keep interface `new (): C` on merged instance + sync VALUE ctor returns;
  `new` on void call-only methods allowed (non-void → **TS2350**); field
  initializers use annotation as contextual expected (clears false TC3000);
  parse + grammar **TS1029** for `async static`; class-expr initializer
  matching prefers HIR `body.span` (no steal of nested `const b = this.#priv`);
  refine stale circular `return AA` snapshots so `getClass().#m` keeps void.
  Exact vs tsc. +4 XPASS: `privateNameConstructorSignature`,
  `privateNameStaticMethodAsync`, `privateNameStaticMethodCallExpression`,
  `privateNamesAssertion`. Manifest: **−4** (then **3771** `status = "xfail"`;
  privateNames xfails **9**). Regression: `tests/private_name_residual_probe.rs`.
  Detail: [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (TS7022 circular initializers)** —
  Field-init type resolution stack detects self/mutual `this.#x` /
  `this["#x"]` cycles; emits **TS7022** (not TS7008) under `--noImplicitAny`
  with tsc name spans (`#foo`, `["#bar"]`); returns `any` to clear TS2571
  cascades; TS2729 use-before-init keeps the declaring field's member index.
  Exact vs tsc. +2 XPASS: `privateNameAndIndexSignature`,
  `privateNameCircularReference`. Manifest: **−2** (then **3775**
  `status = "xfail"`; privateNames xfails **13**). Regression:
  `tests/private_name_circular_init.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (modifiers / AndAny / ambient NIA)** —
  TS18010/18019/1024/1031/1042 on private-identifier modifiers (keyword
  spans); checkJs `@public`/`@private`/`@protected` → TS18010 with tsc
  `@tag`…`*/` spans; getter→setter param contextual typing (no false
  TC3000); `unknown` receivers → **TS18046**; ambient `#` fields skip
  NIA while concrete emit **TS7008** (not TC3000). Exact vs tsc. +4 XPASS:
  `privateNameAndAny`, `privateNameAmbientNoImplicitAny`,
  `privateNamesIncompatibleModifiers{,Js}`. Manifest: **−4** (then
  **3781** `status = "xfail"`; privateNames xfails **15**). Regressions:
  `tests/private_name_{and_any,ambient_nia,modifiers}.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **`privateNameClassExpressionLoop` empty-`[]` → `never[]`** — bare `[]`
  synthesizes `never[]` under `strictNullChecks` (tsc `checkArrayLiteral`);
  `array.push(class C {…})` is **TS2345** on the class name; contextual
  `T[] = []` / call args still accept `[]` via `never` <: `T`;
  `--noImplicitAny` empty-array bindings use `autoArrayType` (`any[]`).
  Exact vs tsc. +1 XPASS: `privateNameClassExpressionLoop`. Manifest:
  privateNames xfails **19** (full manifest regenerated from shard
  `after.json` + residual privateNames prune after a truncate; total
  `status = "xfail"` now **3785** — may include a few stale non-privateNames
  entries that will XPASS under `--fail-on new`). Regression:
  `tests/empty_array_literal.rs`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (TS2554 / field assign / static unmatched)**
  — single-sig arity miss emits **TS2554** on the callee name (not TC2000);
  unannotated `#field = lit` recovers widened initializer type for
  assignability (TS2322); constructable types skip `#` keys in unmatched
  properties (tsc `getUnmatchedProperties`). Exact vs tsc. +4 XPASS:
  `privateNameMethod`, `privateNameStaticMethod`, `privateNameFieldsESNext`,
  `privateNamesAndStaticFields`. Manifest: **−4** (then **3748**
  `status = "xfail"`; privateNames xfails were **20**). Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **`privateNameDeclarationMerging`** — class+interface `new (): D` merge keeps
  uncontextualized `new C()` as class instance (construct-sig dedup includes
  return type; interface must not clobber class VALUE binding; construct sigs
  move to VALUE side). Exact vs tsc. +1 XPASS:
  `privateNameDeclarationMerging`. Manifest: **−1** (then **3754**
  `status = "xfail"`; privateNames xfails were **24**). Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name residual burn-down (TS2339 / BadSuper / nested)** — nested
  `class` Decl value binding (no overwrite of top-level interned types);
  TS2376+TS17009 for `this` before `super()` when privates/initialized fields
  (TS2376 suppressed under native class fields). Exact vs tsc. +7 XPASS:
  `privateNameImplicitDeclaration`, `privateNamesConstructorChain-1`,
  `privateNamesInNestedClasses-{1,2}`, `privateNameBadSuper`,
  `privateNameBadSuperUseDefineForClassFields`, `privateNamesAndkeyof`.
  Manifest: **−7** (then **3757** `status = "xfail"`; privateNames xfails
  were **25**). Residual cleared: `privateNameDeclarationMerging`. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Tagged-template type-arg inference + TS2403** — shared-`T` inference
  first-wins when no common supertype; `any` among lowers wins; void-return
  contexts skip assignability; enclosing type-param returns reject `null`
  (TS2322 on `return`); `var` merge emits TS2403. Exact vs tsc. +2 XPASS:
  `taggedTemplateStringsTypeArgumentInference{,ES6}`. Manifest: **−2**
  (then **3764** `status = "xfail"`). Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Tagged-template DA + TemplateStringsArray packing** — flow evaluates tag /
  substitutions (TS2454); AST packs `(TemplateStringsArray, …subs)` with
  first-rest TS2345 only. Exact vs tsc. +5 XPASS:
  `taggedTemplateWithConstructableTag02`,
  `taggedTemplateStringsWithTypedTags{,ES6}`,
  `taggedTemplateStringsWithIncompatibleTypedTags{,ES6}`. Manifest: **−5**
  (then **3766** `status = "xfail"`). Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Private-name placement grammar** — TS18009/18012/18024/18028/18029/18030
  for illegal `#` positions (params, `#constructor`, enum members, ES5 target,
  var bindings, optional-chain). Exact match vs tsc. +7 XPASS:
  `privateNameNotAllowedOutsideClass`,
  `privateNamesNotAllowedInVariableDeclarations`,
  `privateNamesNotAllowedAsParameters`, `privateNameConstructorReserved`,
  `privateNameEnum`, `privateNameES5Ban`,
  `privateNameUncheckedJsOptionalChain`. Manifest: **−7** (then **3771**
  `status = "xfail"`; privateNames xfails were **32**). Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **Template / tagged-template TS2349 (not callable)** — `LitTemplate` was
  typed as `unknown` (silencing call resolution); now string / string-literal,
  with tagged-template tag callability + callee-span TC2000↔TS2349. +5 XPASS:
  `templateStringInCallExpression{,ES6}`,
  `templateStringInTaggedTemplate{,ES6}`,
  `taggedTemplateWithConstructableTag01`. Follow-ons: `in` RHS skips excess
  props; `var` hoist seed for initializer self-refs. Manifest: **−5** (then
  **3778** `status = "xfail"`). Detail: [typecheck-ts](../crates/typecheck-ts.md).
- **Nested private-name shadowing TC2008** — nested class self-name
  (`x: Derived`) now resolves via Decl seeding in body `binding_defs` (imperative
  + salsa paths). Clears rust_extra TC2008 / cascading TS2339 while keeping
  TS18014. +3 XPASS: `privateNameNestedClass{Method,Field,Accessors}Shadowing`.
  Manifest: **−3** nested-shadowing xfails cleared (then **3787** `status = "xfail"`).
  Detail: [typecheck-ts](../crates/typecheck-ts.md).
- **Static private missing-on-type TS2339** — `typeof Derived` lacks base
  `static get #prop` (TS2339×2, not TS18013); instance `this.#staticField` is
  TS2339. +2 XPASS: `privateNameStaticAccessorssDerivedClasses`,
  `privateNameStaticFieldAccess`. Manifest: **−2** (then **3785**
  `status = "xfail"`). Detail: [typecheck-ts](../crates/typecheck-ts.md).
- **Nested method access** — named class-expression self-name binding
  (`return class D { new D() }`) + any-like undeclared `#` → TS2339. Exact
  TS18014+TS2339 vs tsc. +1 XPASS: `privateNameNestedMethodAccess`.
  Manifest: **−1** (then **3784** `status = "xfail"`). Detail:
  [typecheck-ts](../crates/typecheck-ts.md).
- **`#x in` transform / assign-to-`in`** — parse-js stops before `=` when LHS
  is not LeftHandSideExpression; soft PS0013 (→TS1005) + continue typecheck;
  `in` LHS/RHS assignability TS2322; shift → `number`; grammar diags suppressed
  when parse errors present. Exact match vs tsc. +1 XPASS:
  `privateNameInInExpressionTransform`. Manifest: **−1**. Detail:
  [typecheck-ts](../crates/typecheck-ts.md).

## 2026-07-24 session

Concise deltas (cite owning pages for detail):

- **Checker aggregate** — upstream conformance hash shards **0–63/64** vs live tsc:
  **2049/5898 = 34.74%** exact-match (`reports/conformance-upstream-shard{0..63}of64-after.json`).
  Prior floor was 1828/5165 = 35.39% on shards 0–55; shards 56–63 add 221/733.
  Ratchet manifest covers shards **0–63** (nightly matrix 0–63; full /64). Owning
  detail: [typecheck-ts](../crates/typecheck-ts.md),
  [roadmap §3](./roadmap.md#3-correctness-program).
- **Checker ICE fix (2026-07-24 late)** — `lookup_interned_property_type` now
  cycle-guards `expand_ref` no-progress/`Ref` results. Clears harness aborts on
  `privateNamesInGenericClasses.ts` + `mergedInterfacesWithInheritedPrivates{,2}.ts`
  (former shard 6/7/9 `rust_ice` skips removed). Regression:
  `typecheck-ts/tests/generic_class_cross_instantiation.rs`.
- **Checker robustness** — cancel hooks + finite budgets; per-body type-growth →
  `TC4000` (landed 2026-07-23; pathology notes in `reports/shard2-pathology-handoff.md`).
- **Checker gap rungs closed** — JSDoc `@type` / `@param` / `@returns` /
  `@typedef` / `@template` (+ `@property`) / **inline object+function type
  literals** under checkJs (+1 XPASS: `jsdocTypeTagParameterType`);
  `TS2304` + CommonJS ambients; TS2454 for-in/of DA exemptions (`any`/`unknown`/…);
  TS2454 residuals (type-alias DA, `for (let v of v)` → TS2448, `x!`);
  TS2454 destructuring sibling defaults (`{ a, b = a }` / rest+sibling, +3 XPASS);
  TS2454 ambient `declare let` DA (+2 XPASS: `literalTypesAndDestructuring`,
  `logicalAssignment9`);
  TS2454 `(x)!` paren distinction (no upstream XPASS; unit-oracle’d vs tsc);
  abstract-class property DA (TS2715/TS1267/field-init TS2729; +1 XPASS:
  `abstractPropertyInitializer`);
  annotated class-field `declared_type` (clears TC3000); `privateNameField.ts`
  exact-match vs tsc. Cornerstone litmus: six fixtures (const/`satisfies`, excess
  props, CFA, distributive conditionals, `keyof`/mapped, overload) — all six
  match tsc baselines (excess_props: TS2353 on property key; const/`satisfies`:
  TS2322 on property key). JSDoc `new:` / `@constructor` cleared (`jsdocFunctionType` XPASS);
  typedef export/qualified names cleared (`checkJsdocTypedefOnlySourceFile`
  XPASS);
  nested `@param opts.x` sugar + TS8032 cleared
  (`paramTagNestedWithoutTopLevelObject{,2,3,4}` XPASS);
  class `@template` construct call-site instantiation cleared
  (`jsdocTemplateClass` XPASS);
  unmatched root `@param` TS8024 cleared
  (`jsdocParamTagTypeLiteral`,
  `checkJsdocParamOnVariableDeclaredFunctionExpression` XPASS);
  TS2454 imported/generic type-alias DA (+1 XPASS:
  `intersectionMemberOfUnionNarrowsCorrectly`). Residual inventory (TS2454
  forward-ref → TS2448; conditional/mapped alias DA; TS2564 residuals
  (computed keys / assertion grammar); TS2540 residuals (JSDoc `@readonly`,
  readonly arrays/tuples); deeper `@template`
  (typedef/variance/defaults/`@constructor`); TS8024 mixed fixtures / CJS
  JSDoc) on
  [typecheck-ts](../crates/typecheck-ts.md#conformance-gap-categories-2026-07-23-pass).
  TS2564/`strictPropertyInitialization` **exact match** vs tsc 2026-07-25
  (XPASS; ctor `this.prop` + string-enum TC3000 follow-ons cleared);
  non-ctor instance/static `this` typing (+1 XPASS:
  `inferringClassMembersFromAssignments7`);
  class getter/setter declared-type TC3000 cleared (+2 XPASS:
  `privateNameStaticsAndStaticMethods`, `privateNamesAndStaticMethods`);
  private-name accessor **TS2540** cleared (+2 XPASS:
  `privateNameAccessors`, `privateNameStaticAccessors`);
  private-name write-only accessor **TS2806** cleared (+2 XPASS:
  `privateWriteOnlyAccessorRead`, `privateNameSetterNoGetter`);
  private-name method assign **TS2803** cleared (+3 XPASS:
  `privateNameMethodAssignment`, `privateNameStaticMethodAssignment`,
  `privateNameReadonly`);
  private-name illegal decls **TS18016** cleared (+4 XPASS:
  `privateNameInObjectLiteral-{1,2,3}`, `privateNameAndPropertySignature`);
  private-name any-like *access* **TS18016**;
  private-name undeclared `#` **TS2339** cleared (+2 XPASS:
  `privateNameBadDeclaration`, `privateNameJsBadDeclaration`);
  bare-callable **`Function.prototype: any`** cleared (+1 XPASS:
  `privateNameBadAssignment`);
  checkJs CommonJS `exports` ambient gated on `commonJsModuleIndicator`
  cleared (+1 XPASS: `privateNameJsBadAssignment`);
  private-name `delete` **TS18011**/**TS2790** cleared (+1 XPASS:
  `privateNamesNoDelete`);
  private-name uniqueness cross-file `import()` **TS18013** cleared (+1 XPASS:
  `privateNamesUnique-2`; VALUE export `value_defs` remap keeps `new` constructable);
  static-block unannotated field TC3000 / TS2729 (+4 XPASS:
  `classStaticBlockUseBeforeDef{1,2,4,5}`; residual UseBeforeDef3 FOO TDZ);
  never-intersection object property collapse → `never` (+2 XPASS:
  `neverIntersectionNotCallable`, `commonTypeIntersection`); write-indexed
  `T[A|B]`→`T[A]&T[B]` + `any`↛`never` (+2 XPASS cleared:
  `intersectionReduction{,Strict}`, exact vs tsc).
- **Incremental bench** — `incremental_recheck` rewritten onto a live `Program` +
  `set_file_text` / `body_check_count()`; sample `body_local_edit` on
  `small_project`: **25→9** body checks (debug and release; ~91 ms → ~33 ms on the
  loaded box). [roadmap §4](./roadmap.md#4-performance-program).
- **Nightly ratchet** — `ts-conformance-ratchet` job wired in
  `.github/workflows/nightly.yaml` (hash shards 0–63/64, manifest, `--fail-on new`).
- **VM ladder** — Function ctor; async generators + `for await`; minimal `RegExp` +
  `CreateAsyncFromSyncIterator`; wrapper-method cluster **+262**; hybrid wide
  BigInt **+36**; destructuring/iterator-protocol **+320**; manifest **437**.
  Current suite floors:
  [vm-js § test262](../crates/vm-js.md#test262-status) (operators **1079**,
  equality-relational **957**, statements-control **919**, types-coercion **257**,
  asi **134**, builtins-basics **771**, builtins-collections **1620**,
  generators-async **1133**, smoke **174**).
  Primary suites + smoke + builtins-collections exit 0 under `--fail-on new`.
  Language-core manifest **21** (honest TCO only); builtins-collections
  manifest empty (groupBy / getOrInsert* + Set composition unlocked).
- **Early SyntaxError burn-down (parser/binder)** — switch CaseBlock redeclaration
  + labelled-fn / for-head / async formals-body clusters: **76** language-core
  xfails cleared (Annex B async/generator lexical fix in `semantic-js` +
  `bind_js_for_runtime` in the semantic harness). **Follow-up (2026-07-24 eve):**
  escaped `await`/`yield` StringValue decode + strict reserved words; module
  negative-parse path; do-while `;` before `while`; duplicate `default`;
  ClassStaticBlock `await`; `let`+`await` no-ASI; FDI body env for parameter
  expressions (`let arguments`). Parser “early SyntaxError not detected”
  bucket essentially cleared (manifest **194**).
  [semantic-js](../crates/semantic-js.md), [parse-js](../crates/parse-js.md).
- **Parser / minify (earlier arc + today)** — test262-parser arc completed
  2026-07-23 (manifest → 36 precise entries, unexpected 0; see below). Minify
  **block unwrap** done 2026-07-24 (safe inert blocks + single-stmt control-flow
  bodies). [minify-js](../crates/minify-js.md), [roadmap §5](./roadmap.md#5-product-programs).
- **LocalId migration** — Wave 3 **done** (2026-07-24): params/vars/catch are
  LocalId-only (no body-local `DefKind::Param`/`Var`, no `compat_def`);
  `Program::type_of_local` for checker queries. Module/namespace member vars
  keep DefIds. [hir-js](../crates/hir-js.md#the-id-scheme-the-crates-core-idea).
- **Docs** — `AGENTS.md` living-docs reconcile done (conservative); further
  slimming needs owner sign-off ([roadmap decisions](./roadmap.md#decisions-needing-an-owner),
  [sources](../meta/sources.md)).
- **Harness convergence** — `typecheck-ts-harness` now uses `conformance-harness`
  for expectations / `FailOn` / index+hash `Shard` (roadmap 2.6).
- **Parser early errors** — `PS0027` (`??`/`&&`/`||` mix); `PS0028` (optional
  chain + tagged template). Early-error burn-down also cleared switch CaseBlock
  redeclaration + labelled-fn clusters (~76 ids). See [parse-js](../crates/parse-js.md).
- **VM ladder** — `$262.createRealm` harness host + foreign-realm eval restore
  cleared the last non-TCO language-core gaps (manifest **21** TCO-only).
  **Map/Set** + **WeakMap/WeakSet** + Set composition + Map.groupBy /
  getOrInsert* + minimal TypedArray / WeakRef → `builtins-collections`
  **1620**/1620 (manifest empty).
  Re-measured floors (2026-07-25 late): smoke **174**, types-coercion **257**,
  builtins-basics **771**, builtins-collections **1620**, equality-relational **957**,
  statements-control **919**, generators-async **1133**, operators **1079**,
  asi **134**; all unexpected **0**.
  Earlier: private-in / `#x in`, `Object.defineProperties`, non-writable global
  `var`, `instanceof` @@hasInstance-first, IfStatement `UpdateEmpty`, resumable
  array/object literal frames, FDI body env, mapped `arguments`, compound
  assignment, BigInt↔String in `==`/`IsLessThan`.
- **Checker** — JSDoc `@typedef`/`@template`; HIR-only `class_typing` +
  declared-type/type-alias span slices; binder type-alias seeds `unknown` when HIR
  is present; body var / assertion / Instantiation / function param+return
  annotations prefer HIR; JSX prefers HIR `JsxElement` (AST residual);
  `check/type_expr.rs` quarantined;
  TS2454 residuals; parse→emit fixpoint + 1-vs-N determinism tests.
- **Conformance widen** — shards **0–63/64** reported (**2049/5898 = 34.74%**;
  full /64 matrix). Former shard 6/7/9 ICE skips removed after property-lookup
  cycle fix; mismatches for shards 2–63 manifested as `xfail` (shards 56–63
  +512 `xfail` on 2026-07-25; prior 52–55 +258). Nightly ratchet widened to
  **0–63**.
- **Determinism / emit hygiene** — megatest parse→emit text fixpoint
  (`emit-js/tests/megatest_fixpoint.rs`) + checker 1-vs-N rayon snapshot
  (`typecheck-ts/tests/determinism.rs`); both named in CI. Details:
  [determinism](../architecture/determinism.md#determinism-as-a-test-target),
  [emit-js](../crates/emit-js.md#verification).

## Build

Verified **2026-07-23 evening** (clean `master` checkout at the time):

- **`vm-js` library + dependents green** — duplicate `Realm::id` / `Completion::Throw`
  fixes; post-migration stragglers in `webidl-vm-js` / `test262-semantic` /
  `runtime-js` migrated. `--all-targets` green for those crates.
- **Guards green** — diagnostic-code registry (`VMJS####` registered); UTF-8 guard
  excludes `third_party/**`.

## Tests

Verified runs **2026-07-23 evening** (loaded shared machine; timings approximate):

- **Pass**: `semantic-js`, `types-ts-interned`, `minify-js`, `optimize-js`,
  `parse-js`, `hir-js`, `emit-js` — full crate suites green after the evening
  fix sequence (debugger/`new` optional-chain spans, `PS0017`, emit parens helpers,
  NameInterner deadlock — see below).
- **NameInterner deadlock: fixed 2026-07-23 evening.** `compare_props` scopes the
  `names.read()` guard; regression stress test
  `types-ts-interned/tests/lock_stress.rs`. Full `typecheck-ts` suite green in
  ~649 s on the loaded box. Doctest `E0460` under concurrent agent builds was a
  shared-`target/` race, not code. Case study:
  [determinism](../architecture/determinism.md#case-study-the-nameinterner-deadlock).
- **`vm-js` unit suite** — fully green after retained-AST fix (~489 tests at that
  capture; later 2026-07-24 programs added more — see crate page).

## Docs/hygiene drift

Resolved 2026-07-23 (evening) + 2026-07-24 living-docs pass:

- `docs/deps.md` → wiki generator; root `Cargo.toml` members deduplicated;
  `planner_scratchpad.md` / `notes/*` absorbed and deleted ([ledger](../meta/sources.md)).
- `AGENTS.md` living-docs table + conflict rule (2026-07-24).

## Correctness baselines (history + current floors)

### Checker (current floor: 2026-07-25)

- **difftsc vs live tsc 5.9.3** (curated): **56/56** matched
  (`reports/difftsc-baseline.json`).
- **conformance-mini**: 5 match + 1 expected mismatch
  (`reports/conformance-mini-baseline.json`).
- **Upstream shards 0–63/64**: **2049/5898 = 34.74%** exact-match (see session
  section). Per-shard includes 56:26/78, 57:30/110, 58:23/98, 59:40/96,
  60:30/96, 61:26/85, 62:21/82, 63:25/88; former ICE aborts in 6/7/9 fixed
  (property-lookup cycle guard).
- Ratchet manifest **3717** upstream `xfail` entries (was **3718** after
  call-sig rest wave / **3722** after typeRelationships/typeof /
  **3762** after privateNames→0 / **3849** after shards 56–63; net **−5** this
  call-sig arc including `…CallSignatures3`). Cleared this arc:
  DA/JSDoc/SPI/template/`this`/accessor/
  private-name/`#x in`/TS2769/TS2741/CJS-exports/nested-class/tagged-template/
  never-intersection/write-indexed-access/modifiers/AndAny/TS7022/
  generic-dual-instantiation/parse-recovery/typeAndMemberIdentity XPASS/
  `T|Concrete` inference/enum-typeof-TS2403 clusters; all **6** cornerstone
  litmus fixtures graduated vs tsc. **0** privateNames xfails remain. All
  shards 0–63 green under `--manifest --fail-on new`. Nightly job covers
  0–63 (full /64 matrix). Exact-match % not remeasured end-to-end (prior
  report still **2049/5898 = 34.74%**; expect ~+40 from this prune/fix wave).
- Earlier floors: 0–4 only 180/500 = 36.0%; 4-shard sample without shard 2 was
  35.4% (142/401).

### test262-parser (floor from 2026-07-23 arc)

Day's arc: blanket ~457 xfails → **36 precise** manifest entries (regex `u`-flag
grammar 4, Annex B escape residue, small `fail-other` set), **unexpected 0**
throughout. Intermediate reports under `reports/test262-parser-*.json`; early-errors
+ binder over-strictness notes in
`reports/semantic-js-binder-overstrictness-2026-07-23.md`. Owning narrative:
[parse-js](../crates/parse-js.md), [semantic-js](../crates/semantic-js.md).

### VM test262 (current floors: 2026-07-25 late — Map.groupBy / getOrInsert* XPASS)

Authoritative per-suite numbers and residual inventory live only on
[vm-js § test262 status](../crates/vm-js.md#test262-status). Snapshot after
Map.groupBy + Map/WeakMap getOrInsert* unlocked into builtins-collections
(language-core manifest **21** TCO-only; builtins-collections manifest empty):

| Suite | Passed (floor) |
| --- | --- |
| operators | **1079** |
| equality-relational | **957** |
| statements-control | **919** |
| types-coercion | **257** |
| asi | **134** |
| builtins-basics | **771** |
| builtins-collections | **1620** |
| generators-async | **1133** |
| smoke | **174** |

Earlier same-day / prior-evening ladders (operators/relational fixes, Reference
model, built-ins, sync generators + async functions, Function ctor, async gen /
for-await, RegExp+AFSI, wrapper +262, wide BigInt +36, dstr/iterator +320) are
recorded on that page; do not treat the intermediate floors in older prose as
current.

## Checker structural refactor (2026-07-23; still the standing shape)

Increments 1–3 landed: salsa-first body checking, `hir_body` decomposition,
AstIndex de-pointering. Dual-brain remainder (imperative decl types) and
“checker consumes HIR only” are still open — sequenced after LocalId step 5
([roadmap §2](./roadmap.md#2-structural-refactors),
[engine.md](../architecture/engine.md)).

## Unmeasured (known unknowns)

- Performance targets ([vision § success criteria](../vision.md#success-criteria)):
  bench baselines exist in CI artifacts; aside from the incremental
  `25→9` sample above, **no current end-to-end perf numbers** are recorded here
  (vision medium-project / incremental latency targets remain unverified in
  this snapshot).

## Environment note

The 2026-07-23 verification machine was heavily loaded (unrelated tenants);
wall-times above are not benchmarks. The NameInterner deadlock reproduction is
*more* likely under load — quiet machines hide concurrency bugs.
