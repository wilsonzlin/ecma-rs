# Roadmap

The ordered program of fixes, refactors, and completion work. Phases are dependency-
ordered (each unblocks the next), but items within a phase can proceed in parallel with
disjoint scopes. Every item names its acceptance criterion — "done" means the
criterion is verified, not that code merged. Keep this page current per the
[update loop](../meta/how-to-write.md#the-update-loop-continuous-absorption); move
completed items' knowledge into the owning pages and their history into the
[graveyard](../graveyard.md) when appropriate. (Baseline plan derived from
`AGENTS.md`'s phases + verified findings of 2026-07-23; item statuses updated through
2026-07-24 — dated build/test floors live in [health](./health.md).)

## 0. Restore green

The workspace-green invariant is broken; nothing else can be trusted until this lands.

| Item | Fix sketch | Acceptance |
| --- | --- | --- |
| ~~`vm-js` compile errors~~ | **Done 2026-07-23** (two-worker sequence): library fixed (duplicate `id` removed incl. a wrong slot-ID derivation; `thrown_at_stmt` at the three Throw sites), then the VmHost-migration stragglers in dependents (stale promise test, `webidl-vm-js` call sites + four more old-arity `NativeCall`s, `HarnessMode` variant) | ✔ vm-js/webidl-vm-js/test262-semantic/runtime-js all green (`--all-targets`) |
| ~~NameInterner deadlock~~ | **Done 2026-07-23**: guard scoped in `compare_props`; store-wide audit clean; lock-rule comments at hazard sites; `lock_stress.rs` regression test | ✔ full typecheck suite green at default parallelism (~649 s loaded); stress test green; doctest E0460 build-race noted for quiet re-verify |
| ~~`emit-js` `new a?.()`~~ | **Done 2026-07-23**: shared `needs_parens_before_optional_chain`/`new_callee_needs_parens` helpers, both backends, full sibling matrix; original test expectation corrected from grammar (`new a?.()` parses as `(new a)?.()`) | ✔ emit-js/minify-js/optimize-js green |
| ~~Parser: reject illegal optional chains around `new`~~ | **Done 2026-07-23**: `PS0017` in all dialects (member/computed/call/type-arg chain forms); legal forms verified (`new (a?.b)`, `(new a)?.()`, `new a()?.b`, `new (a?.b).c()`); emit tests moved to constructed ASTs preserving defensive coverage | ✔ parse-js/emit-js/hir-js/optimize-js green; one minify-js test straggler handed to the active pass program (source string uses the now-illegal form) |
| ~~`hir-js` debugger span~~ | **Done 2026-07-23**: convention decided (spans include terminator; ASI ends at last token), parser consumed the `;` into the statement (killing a spurious EmptyStmt), documented in crates/hir-js.md | ✔ `hir-js` + `minify-js` green |
| ~~Parser statement-termination follow-ups~~ | **Done 2026-07-23**: labeled break/continue consume `;` (no spurious EmptyStmt); EOF treated as ASI boundary for break/continue AND `return` (incl. a statement-list EOF stop so ASI'd `return` at EOF errors on the missing `}` instead of a phantom expression); `new.target` no longer allowed via arrows without an enclosing non-arrow function (Ecma dialect rejects; Ts/Js keep recovery acceptance — deliberate, documented in crates/parse-js.md) | ✔ parse-js/hir-js/minify-js green incl. previously-failing `strict_ecma_rejects_ts_only…` |
| ~~`docs/deps.md` stale~~ | **Done 2026-07-23**: generator repointed into the wiki (`wiki/architecture/deps.md`), regenerated, CI/justfile updated | ✔ verified idempotent |
| ~~`Cargo.toml` duplicate members~~ | **Done 2026-07-23**: deduplicated | ✔ `cargo metadata` clean |

Then: record a full single-threaded vs parallel `cargo test --workspace` result in
[health](./health.md). First targeted 1-vs-N checker snapshot + megatest emit
fixpoint landed 2026-07-24 (see [determinism](../architecture/determinism.md#determinism-as-a-test-target));
workspace-wide byte-diff remains open.

## 1. Wiki migration completion

**Done 2026-07-23** (verified: stubs in place, notes/scratchpad deleted after
verbatim absorption, generator repointed, wiki links green).

- ~~`AGENTS.md` reconcile~~ — **done 2026-07-24** (conservative): Living docs table +
  conflict rule; slimmed only wiki-owned ops/history duplication (test commands,
  `symbol-js` narrative, workspace inventory notes); principles, playbook A–F, and
  coding standards kept. Further slimming remains an owner decision below.

## 2. Structural refactors

The [overview assessment](../architecture/overview.md#assessment-is-the-current-structure-ideal)
items, in recommended order:

1. ~~**Checker salsa-first**~~ — **done 2026-07-23** (`check_body_tracked`; seeding
   path deleted; context-input + tracked-wrapper backdating firewall; parallelism
   preserved via `map_with(db.snapshot())`; `Program::body_check_count()` metric;
   `tests/salsa_body_memo.rs` proves no-edit ⇒ zero re-checks, body edit ⇒
   file-granular re-check, decl change ⇒ correct invalidation; conformance-mini +
   difftsc byte-identical to pre-refactor baselines; two latent bugs fixed en route:
   span→def HashMap-order nondeterminism, `ts_semantics`→`lower_hir` diagnostic
   coupling). **Remaining half of dual-brain**: decl types still imperative; a decl
   change re-checks all bodies — next tightening is per-file context slices.
2. ~~**Decompose `check/hir_body.rs`**~~ — **done 2026-07-23**: 11,196-line monolith
   → 10 modules (`ast_index` 866, `hir_body/mod` 1473 glue+types, `body/{stmts 1171,
   exprs 1981, call 930, jsx 1128, bindings 699, flow 1484, flow_ops 1699}`), largest
   1,981 lines; behavior-frozen (suite green, conformance-mini summary identical,
   zero test edits, public surface unchanged). Deviations from the drawn map were
   sensible and documented (FlowBodyChecker split in two for the line cap; shared
   helpers kept in the module root).
3. ~~**De-pointer `AstIndex`**~~ — **done 2026-07-23** (borrowed `AstIndex<'ast>`
   built per query; `ProgramState.ast_indexes` cache and `ast_index_for` query
   removed; bonus: `DbHost` raw pointer → narrow `DeclHost` trait, re-entrancy guard
   `*mut` → `Arc<Mutex<HashSet<BodyId>>>`; zero `unsafe impl Send/Sync` in crate).
4. **Checker consumes HIR only** — vertical slices **done 2026-07-24**:
   - **class members / `class_typing`**: HIR helpers over `ClassMemberSig` /
     `DefData.declared_type`; no AST class-body walk.
   - **declared-type / type-alias span paths**: `declared_type_for_span` and
     `type_alias_type_for_span` are HIR-only (`DefData.declared_type` +
     `DefTypeInfo::TypeAlias` via `HirDeclLowerer`); module/ambient vars now
     populate `declared_type` in hir-js. Deleted the AST statement walk
     (VarDecl / AmbientVar / Namespace / TypeAlias); residual in
     `span_types/declared.rs` is binder-only `TypeParameter` /
     `type_from_type_expr`. Binder type-alias path now seeds `unknown` when
     HIR is present (recompute in `type_of_def`).
   - **binder param/return annotations**: when HIR present, binder leaves
     `FuncData` annotations unset; `function_type` lowers from
     `hir_js::FunctionData` (`lower_value_function_signature`).
   - **`collect_function_decl_types`**: TS/TSX/DTS with HIR lower top-level
     function/overload/`declare function` signatures from `FunctionData`
     (`has_body` for overload filtering); JS/JSX keep AST+JSDoc. hir-js now
     always allocates Function bodies for bodiless signatures.
   - **binder ambient var annotations**: when HIR present, binder
     `AmbientVarDecl` leaves `VarData.typ` unset; `type_of_def` lowers from
     `DefData.declared_type` (module `declare var` already used `typ: None`).
   - **body var annotations (AstIndex)**: `check_var_decl` /
     initializer bodies prefer HIR `VarDeclarator.type_annotation` for
     primitives through mapped/conditional/function/object/`typeof` (body
     `TypeResolver` + scope bindings); AstIndex AST annotation is residual
     for `typeof import(...)` / JSDoc.
   - **body type assertion / `satisfies` / `as const`**: `check_expr` prefers
     HIR `TypeAssertion`/`Satisfies` (`TypeExprId` + `const_assertion`) via
     the same body lowerer; AST residual for `import(...)` / missing arenas.
   - **body Instantiation type args**: `hir-js` `ExprKind::Instantiation`
     carries `Vec<TypeExprId>`; body checker prefers HIR via
     `hir_lower_type_expr_id` / `TypeResolver`. AST residual for
     `import(...)` type args / missing arenas.
   - **body function param/return annotations (2026-07-25)**:
     `bind_params` / enclosing return / body-matched `function_type` prefer
     `FunctionData` `TypeExprId`s (type-param ids seeded from AST scopes).
     `check/type_expr.rs` documented as AST quarantine. Residual AST:
     `typeof import(...)`, JSDoc, type-param *registration*, nested fn-expr
     synthesis on outer body, AstIndex class-field/SPI. Binder AST
     `type_from_type_expr` when HIR missing.
   - **body JSX element structure (2026-07-25)**: `check_jsx_elem` prefers
     `hir_js::JsxElement` for tag/attrs/children; nested JSX via HIR
     `ExprId`. Residual AST `JsxElem` walk when HIR missing; nested non-JSX
     expr values still AST-by-span. Next: HIR type-param registration;
     shrink AstIndex class-field annotation walks; drop residual JSX AST
     walk when HIR coverage is complete. Prior inventory remainder:
     `ast_index` / `hir_body` / `body/*` (expr structure), `program/state.rs`,
     `db/queries.rs`, residual `check/type_expr.rs`, binder AST walks,
     residual JSX AST fallback.
5. ~~**Body-local `DefId` → `LocalId`**~~ — **done 2026-07-24** (Wave 3):
   `Body.locals` holds params + body vars + catch; no body-local
   `DefKind::Param`/`Var` DefIds; `compat_def` removed; checker uses
   `type_of_local`. Module/namespace member vars keep DefIds — see
   [hir-js](../crates/hir-js.md#the-id-scheme-the-crates-core-idea).
6. ~~**Harness convergence**~~ — **done 2026-07-24**: `typecheck-ts-harness` depends on
   `conformance-harness` for `Expectations`/`FailOn`/`Shard`/`ShardStrategy` (hash
   sharding + FNV reference vectors moved into the shared crate). Thin
   `Expectations` wrapper maps I/O to `HarnessError::Manifest`. Runner-specific
   report structs and process timeouts remain local (tsc child lifecycle ≠
   cooperative `TimeoutManager`). Acceptance: one implementation of manifest +
   shard semantics (XPASS included) in the workspace.

## 3. Correctness program

Oracle-driven completion of the checker and parser
([theory § completing rigorously](../theory/compiler-theory.md#8-completing-the-implementation-rigorously)):

- ~~**Baselines first**~~ — **done 2026-07-23** in two passes: quick baselines, then
  the ratchet program's honest aggregate. **Widened 2026-07-25** to the full hash
  matrix **0–63/64** (5898 cases, **2049/5898 = 34.74%** exact-match vs live tsc;
  reports under `reports/conformance-upstream-shard{0..63}of64-after.json`).
  Manifest ratchet covers **0–63**/64 (shards 56–63 mismatches manifested
  2026-07-25; +512 `xfail`; prior 52–55 +258). Prior floor 0–55 was
  1828/5165 = 35.39%.
  ~~Stack-overflow ICEs in shards 6/7/9~~ — **fixed 2026-07-24 late**
  (`lookup_interned_property_type` cycle guard; skips removed; see
  [testing](../engineering/testing.md#upstream-conformance-baseline-shards-vs-live-tsc)).
  Mismatches for shards 2–63 recorded as `xfail`. Numbers in [health](./health.md).
  ~~Wire ratchet into nightly~~ — **done 2026-07-24** (widened to **0–63** on
  2026-07-25; full /64 matrix).
- ~~**Checker robustness**~~ — **done 2026-07-23**: `RelateHooks::should_stop` +
  evaluator/instantiation cancel; finite defaults (50k steps); per-body type-growth
  cap → `TC4000`; evaluator object-walk guard; `TypeId` composite sort.
  (`reports/shard2-pathology-handoff.md`, `tests/engine_budget.rs`). ~~Re-include
  shard 2~~ — **done 2026-07-24** vs live tsc (38/99, aggregate 180/500).
- **Checker next gap-rungs** (from the honest baseline): remaining JSDoc
  (deeper `@template` beyond class construct instantiation; TS8024 mixed
  fixtures still needing TS2339/parse codes; richer CJS namespace graphs);
  TS2454 remainder (forward-ref destructuring → TS2448; conditional/mapped
  alias DA); TS2564 residuals (computed keys / assertion grammar);
  TS2540 residuals (JSDoc `@readonly`, readonly arrays/tuples, bundled
  assertion fixtures).
  ~~TS2564 strictPropertyInitialization (core + TC3000 follow-ons)~~ —
  **done 2026-07-25** (exact match / XPASS
  `strictPropertyInitialization.ts`; ctor `this.prop` + string enum member
  typing),
  ~~non-ctor instance/static `this` typing~~ — **done 2026-07-25**
  (+1 XPASS: `inferringClassMembersFromAssignments7`),
  ~~class getter/setter declared-type TC3000~~ — **done 2026-07-25**
  (+2 XPASS: `privateNameStaticsAndStaticMethods`,
  `privateNamesAndStaticMethods`),
  ~~static-block unannotated field TC3000~~ — **done 2026-07-25**
  (+4 XPASS: `classStaticBlockUseBeforeDef{1,2,4,5}`),
  ~~private-name accessor TS2540~~ — **done 2026-07-25**
  (+2 XPASS: `privateNameAccessors`, `privateNameStaticAccessors`),
  ~~private-name write-only accessor TS2806~~ — **done 2026-07-25**
  (+2 XPASS: `privateWriteOnlyAccessorRead`, `privateNameSetterNoGetter`),
  ~~private-name method assign TS2803~~ — **done 2026-07-25**
  (+3 XPASS: `privateNameMethodAssignment`,
  `privateNameStaticMethodAssignment`, `privateNameReadonly`),
  ~~private-name illegal decls TS18016~~ — **done 2026-07-25**
  (+4 XPASS: `privateNameInObjectLiteral-{1,2,3}`,
  `privateNameAndPropertySignature`),
  ~~private-name any-like access TS18016~~ — **done 2026-07-25**
  (no full XPASS at the time),
  ~~private-name undeclared `#` TS2339~~ — **done 2026-07-25**
  (+2 XPASS: `privateNameBadDeclaration`, `privateNameJsBadDeclaration`;
  follow-on 2026-07-26 +2: `privateNameStaticAccessorssDerivedClasses`,
  `privateNameStaticFieldAccess`),
  ~~bare-callable `Function.prototype: any`~~ — **done 2026-07-25**
  (+1 XPASS: `privateNameBadAssignment`),
  ~~checkJs CommonJS `exports` ambient over-seed~~ — **done 2026-07-25**
  (+1 XPASS: `privateNameJsBadAssignment`; seed only when
  `commonJsModuleIndicator` — public `exports.foo=` / `module.exports=` /
  `require(...)`; `exports.#…` does not count),
  ~~private-name `delete` TS18011/TS2790~~ — **done 2026-07-25**
  (+1 XPASS: `privateNamesNoDelete`),
  ~~private-name uniqueness cross-file import() TS18013~~ — **done 2026-07-25**
  (+1 XPASS: `privateNamesUnique-2`),
  ~~`#x in` transform / assign-to-`in` (PS0003 vs TS1005/2322)~~ —
  **done 2026-07-26** (+1 XPASS: `privateNameInInExpressionTransform`),
  ~~private-name placement grammar (TS18009/12/24/28/29/30)~~ —
  **done 2026-07-26** (+7 XPASS: `privateNameNotAllowedOutsideClass`,
  `privateNamesNotAllowedInVariableDeclarations`,
  `privateNamesNotAllowedAsParameters`, `privateNameConstructorReserved`,
  `privateNameEnum`, `privateNameES5Ban`,
  `privateNameUncheckedJsOptionalChain`),
  ~~private-name TS2554 arity / `#` field assign / static unmatched~~ —
  **done 2026-07-26** (+4 XPASS: `privateNameMethod`,
  `privateNameStaticMethod`, `privateNameFieldsESNext`,
  `privateNamesAndStaticFields`),
  ~~private-name ClassExpressionLoop empty `[]`→`never[]`~~ —
  **done 2026-07-26** (+1 XPASS: `privateNameClassExpressionLoop`),
  ~~`privateNameClassExpressionLoop` empty-`[]` → `never[]` / TS2345~~ —
  **done 2026-07-26** (+1 XPASS: `privateNameClassExpressionLoop`),
  ~~private-name modifiers / AndAny / ambient NIA~~ —
  **done 2026-07-26** (+4 XPASS: `privateNameAndAny`,
  `privateNameAmbientNoImplicitAny`,
  `privateNamesIncompatibleModifiers{,Js}`),
  ~~private-name bare `#` TS1127 + object-rest TS2339~~ —
  **done 2026-07-26** (+2 XPASS: `privateNameHashCharName`,
  `privateNameAndObjectRestSpread`),
  ~~private-name computed-key / useDefine brands / ctor-chain~~ —
  **done 2026-07-26** (+3 XPASS: `privateNameComputedPropertyName3`,
  `privateNameWhenNotUseDefineForClassFieldsInEsNext`,
  `privateNamesConstructorChain-2`),
  ~~private-name class-`T` member-ann TC2008~~ —
  **done 2026-07-26** (noise cleared),
  ~~private-name generic dual-instantiation / construct~~ —
  **done 2026-07-26** (+2 XPASS: `privateNamesAndGenericClasses-2`,
  `privateNamesInGenericClasses`),
  ~~private-name last parse residuals (`ComputedPropertyName2` /
  `AndIndexedAccess`)~~ — **done 2026-07-26** (+2 XPASS:
  `privateNameComputedPropertyName2`, `privateNamesAndIndexedAccess`;
  privateNames xfails **0**),
  ~~TS2454 imported / generic type-alias DA~~ — **done 2026-07-25**
  (+1 XPASS: `intersectionMemberOfUnionNarrowsCorrectly`),
  ~~JSDoc typedef export / qualified names (`exports.Foo`)~~ — **done 2026-07-25**
  (+1 XPASS: `checkJsdocTypedefOnlySourceFile`),
  ~~abstract-class property DA (TS2715/TS1267)~~ — **done 2026-07-25**
  (+1 XPASS: `abstractPropertyInitializer`),
  ~~JSDoc `new:` / `@constructor` construct signatures~~ — **done 2026-07-25**
  (+1 XPASS: `jsdocFunctionType`),
  ~~JSDoc inline object/function type literals~~ — **done 2026-07-25**
  (+1 XPASS: `jsdocTypeTagParameterType`),
  ~~JSDoc nested `@param opts.x` sugar + TS8032~~ — **done 2026-07-25**
  (+4 XPASS: `paramTagNestedWithoutTopLevelObject{,2,3,4}`),
  ~~JSDoc class `@template` construct call-site instantiation~~ — **done 2026-07-25**
  (+1 XPASS: `jsdocTemplateClass`),
  ~~JSDoc unmatched root `@param` (TS8024)~~ — **done 2026-07-25**
  (+2 XPASS: `jsdocParamTagTypeLiteral`,
  `checkJsdocParamOnVariableDeclaredFunctionExpression`),
  ~~TS2454 `(x)!` paren distinction~~ — **done 2026-07-25** (no upstream XPASS;
  pattern rare in corpus),
  ~~TS2454 ambient `declare let` DA~~ — **done 2026-07-25** (+2 XPASS:
  `literalTypesAndDestructuring`, `logicalAssignment9`),
  ~~TS2454 destructuring sibling defaults
  (`{ a, b = a }` / rest+sibling)~~ — **done 2026-07-25** (+3 XPASS),
  ~~TS2454 residuals (type-alias DA, `for (let v of v)` → TS2448, `x!`)~~,
  ~~TS2454 for-in/of `any`/`unknown`/… exemptions~~, ~~JSDoc `@type` first
  slice~~, ~~JSDoc `@param`/`@returns` on functions~~, ~~JSDoc
  `@typedef`/`@template` (+ `@property` object shapes)~~,
  ~~`TC0005`→`TS2304` + CommonJS ambients~~, and ~~class-field annotation
  consumption~~ — **done 2026-07-24**.
- **Cornerstone litmus ladder**: six fixtures under
  `typecheck-ts/tests/litmus/cornerstone_*` +
  `typecheck-ts-harness/fixtures/cornerstones/` — const/`satisfies`, excess
  props, CFA narrowing, distributive conditionals, `keyof`/mapped, overload
  selection ([list](../theory/compiler-theory.md#the-typescript-cornerstones)).
  All six match tsc baselines (2026-07-25: CFA; excess_props TS2353 on key;
  const/`satisfies` TS2322 on key via `check_assignable`). Widen further
  cornerstones (union identities, indexed access, method bivariance, …).

- **Known semantic gaps** (from crate pages): `semantic-js` TS-mode module
  augmentation + general `export =`; compiler-options coverage audit (each option
  reaching its semantics site + recorded in query signatures); early-error ownership
  table (parser vs binder vs VM); parser rejection coverage (test262 `fail/`/`early/`
  manifest currently blanket-xfailed — burn it down). Parser *acceptance* coverage:
  ~~five pass-corpus gap categories~~ — **all fixed 2026-07-23** (CoverInitializedName
  via the existing cover-grammar reinterpretation; parenthesized assignment targets
  looking through the `ParenthesizedExpr` marker; nested array-rest destructuring;
  sloppy `for (let in …)`; escaped directives no longer engage strict mode);
  test262-parser at 4336/5363, 0 unexpected.
- ~~Small queued items~~ — **done 2026-07-23**: `StringLiteralContainsEscapes`
  marker + binder proxy replacement; harness binds all pass/early corpora;
  bonus: yield-in-params cluster (−33 manifested) via parameter-context clearing.
- **Property/fuzz expansion**: ~~canonicalization idempotence, relation stability
  under canonicalization, `type_cmp` total-order laws~~ — **done 2026-07-23**
  (`types-ts-interned/tests/properties.rs`, 14 properties, all laws verified against
  the wiki's stated identities). ~~parse→emit→parse fixpoint (megatest)~~ +
  ~~1-vs-N rayon determinism guard in CI~~ — **done 2026-07-24**
  (`emit-js/tests/megatest_fixpoint.rs`; `typecheck-ts/tests/determinism.rs`
  `check_outputs_identical_under_1_vs_n_rayon_threads`; named CI steps). Remaining:
  fuzz-corpus fixpoint; broader harness JSON 1-vs-N byte-diff.
- ~~**JS property-assignment namespaces** (`salsa/typeFromPropertyAssignment24.ts`,
  manifested 2026-07-28): tsc's `bindSpecialPropertyAssignment` registers a
  namespace member for `Outer.Inner = class {…}` in JS files (value + type
  namespaces)~~ — **done 2026-07-29**: `program/state/analysis/expando.rs`
  scans JS/JSX sources under `checkJs` for `var Outer = {}` + `Outer.X = …`
  (class/function RHS) and `Outer.X.prototype = {…}`, registers
  `qualified_def_members[(outer, X, TYPE|VALUE)]` (class defs reused;
  synthetic def pair for function RHS), augments the outer var's type, and
  skips the binding-site assignability check. Both conformance cases match
  tsc; regressions in `typecheck-ts/tests/js_expando_members.rs`. Extended
  2026-07-30: `var Outer = function … {}` and `function Outer() {}` bases
  (clears `typeFromPropertyAssignment3.ts` shard 12,
  `typeFromPropertyAssignment12.ts` shard 2, and
  `typeFromPropertyAssignment2.ts` shard 17; the type-side resolver walks
  `qualified_def_members` from `DefKind::Function` heads too). Still
  unmodeled: nested statics (`Outer.X.Y = …`), arrow/other RHS members,
  computed names.
- ~~Recursive-generic instantiation expansion pathology~~ (surfaced 2026-07-29,
  `statements/forStatements/forStatementsMultipleInvalidDecl.ts`) — **done
  same day**: `evaluate_ref` no longer expands Ref arguments eagerly
  (structural `substitute_only` instead — the eager arg walk was the
  quadratic driver); `new D<string>()` on `class D<T> { wrapped: D<D<T>> }`
  went ~56s → baseline, and alternating recursion
  (`recursiveTypeInGenericConstraint`) still closes its recursive-pair cycle
  exactly. Regression: `typecheck-ts/tests/recursive_generic_perf.rs`.
- **Object-literal method return inference** (surfaced 2026-07-28): in
  expression position, `{ m() { return 1; } }.m` types as `() => unknown`
  (tsc: `() => number`) — literal shape construction runs before the method
  body's return inference completes, and the result is never patched up.
  Affects plain object literals (computed and named keys alike). Owner:
  `check/body/exprs.rs` (`object_literal_type*`) vs body-check ordering.
- **Discriminant-path narrowing on intersections** (surfaced 2026-07-30):
  `q: X & ({a: object; b: undefined} | {a: undefined; b: object})` does not
  narrow `q.a` after `q.a !== undefined` (TS18048 fired on `q.a.aProp`; tsc
  fixed this exact upstream bug and the case asserts the fixed behavior).
  Manifested xfail (`types/intersection/intersectionOfUnionNarrowing.ts`,
  shard 14). Exposed by ambient-type seeding — previously masked by `unknown`.
- **AST-pass assignment checks don't see equality/typeof-neq narrowing**
  (surfaced 2026-07-30, pre-existing): `if (x === 'foo') { const y: "foo" = x }`
  and `if (typeof u !== 'string') { const n: number = u }` both emit TS2322 —
  the flow pass narrows correctly but AST-pass assignment checks run before the
  CFA merge (`check/body/stmts.rs` if-handling only applies typeof-equality
  overrides). Not template-specific (plain quotes behave identically).
- **`check_assignable` blanket-skips `unknown` sources** (surfaced 2026-07-30,
  design-level): `check/hir_body/mod.rs` `check_assignable_with_code` returns
  early when src is `Any | Unknown`, so `const s: string = u` with
  `u: unknown` (param/ambient/local) never errors at the declarator — tsc
  reports TS2322 (`unknown` is only assignable to `unknown`/`any`). Recovery
  `unknown` (uncomputed types) and user-written `unknown` are conflated in one
  `TypeId`, so removing the exemption naïvely cascades false positives; the
  fix needs a real-vs-recovery distinction (or tsc-style `errorType`).
  Masked the fractional-numeric-key bug for weeks: `a[1.1]` was `unknown` but
  no diagnostic surfaced until the TS2403 redeclaration comparison.
- **Class-expression member defs are not in the program def model** (surfaced
  2026-07-30, broadens the class-expression `this` gap below): `new class {
  s = 'prop' }` types `s` as `unknown` — class-expression member fields/methods
  get HIR defs but no `ProgramState::def_data` entries, so neither field-init
  nor method-return refinement reaches the instance type
  (`privateNameInLhsReceiverExpression.ts` xfail: `obj[unknown].#y` cascades
  to TS2571). Owner: `hir_align` def_data population for class-expression
  members, or a class-expression instance synthesis that consumes member
  bodies.
- **Private accessors missing from class-expression `this` shapes**
  (surfaced 2026-07-30): `const C = class { get #x() {…} set #x(x) {} m() {
  this.#x } }` reports TS2339 — the synthesized instance type of a class
  expression only includes public members, so accessor reads miss. Class
  declarations work. Owner: class-expression instance-type synthesis.
- **Static members do not merge onto the derived constructor's value type**
  (surfaced 2026-07-30, static-heritage gap): `class D extends C {}` does
  not resolve `D.foo` / `D.fn()` for base `C` statics — they type as
  `unknown` and derived-ctor static reads false-fire vs tsc
  (`classWithStaticMembers.ts` xfail, shard 50). Instance heritage works via
  the `C & {…}` instance intersection; the ctor value type merges no base
  statics. Owner: value-type static-property merge in the class heritage
  path — must not pollute the derived construct signature.
- ~~Generator function declarations type as `() => void` without a contextual
  type~~ — **done 2026-07-30**: `infer_cached_callable_return_type` builds
  `Generator<Y, R, N>` / `AsyncGenerator<Y, R, N>` from the body's yield
  union (`BodyCheckResult.yield_types`), so `function* gen() { yield 1; }` is
  `() => Generator<number, void, unknown>` and unannotated `[...gen()]` is
  `number[]` (regression: `typecheck-ts/tests/generator_decl_types.rs`).
- **Function-expression return inference never reaches the value's type**
  (surfaced 2026-07-30): `var f = () => ''` and `{ baz: () => '' }` both
  infer `() => unknown` — the function expression's body infers its return,
  but the *binding / property* type is captured from the pre-inference
  callable and never patched (unlike class methods, which have a refine
  pass). Masks widely via the unknown-skip gap but surfaces in relates
  (`typesWithOptionalProperty.ts`, `commonJSAliasedExport.ts` xfails).
  Owner: `decl_types/type_of_def.rs` var-init path vs a post-inference patch.
- **Polymorphic-this is not modeled** (surfaced 2026-07-30):
  `TProp extends this` constraints and `let x: this = this` fail —
  `TypeKind::This` has no relate handling and is never substituted with the
  enclosing instance (`thisTypeInFunctions3.ts` xfail). Needs a this-type
  resolution story in relate + constraint checking.
- **`return Promise.resolve(x)` in async generators / async functions fails to
  relate through `Awaited<T>` for type-param `T`** (surfaced 2026-07-30):
  `awaited_type` on `Promise<T>` or bare `T` leaves an unevaluated
  `Awaited<T>`-shaped conditional instead of reducing to `T`, so the return
  check false-fires TS2322 (tsc accepts). The plain `return a` case works
  (shard 45); the promise-wrapped form needs the awaited conditional to
  evaluate through the promise's `then` resolution for generic signatures.
- **Merged-namespace duplicate vars keep the last declaration** (surfaced
  2026-07-30): `namespace A.B { export var x: number }` merged with
  `module A { namespace B { export var x: string } }` resolves `A.B.x` to
  `string`; tsc keeps the *first* declaration silently
  (`TwoInternalModulesThatMergeEachWithExportedModulesOfTheSameName.ts`
  xfail). Owner: namespace-scope merge order in the binder.
- ~~Merged ambient namespace+class resolution~~ — **done 2026-07-28**
  (conformance `AmbientModuleAndAmbientWithSameNameAndCommonRoot` matches):
  class/enum namespace members map through `value_defs` (constructor value,
  not instance type), cross-file decls of one namespace share the combined
  member view, and cross-file ambient class value bindings remap through
  `value_defs` at all three lookup sites (salsa `BodyCheckContext` now
  carries it). Regression: `typecheck-ts/tests/namespace_class_merge.rs`.

## 4. Performance program

Targets from [vision § success criteria](../vision.md#success-criteria); measure
before touching:

- Stand up trend lines from the existing bench JSON artifacts (pipeline stages,
  relation-cache hit rates, allocation counters); regressions fail nightly.
- ~~**Fix the incremental bench**~~ — **done 2026-07-24**: `incremental_recheck`
  now keeps one live `Program`, applies the edit via `Program::set_file_text`, and
  reports `full_body_checks` / `edit_body_checks` from `body_check_count()` so
  edit-vs-full can observe salsa reuse. Sample (`body_local_edit`): debug 25→9
  body checks; release 25→9 (~91 ms → ~33 ms on the loaded box).
- Arena adoption in body checking where the alloc benches say it pays
  (`check_body_alloc` is the scoreboard).
- Parallel scaling audit *after* the deadlock fix: lock-contention profile of the
  store's interners under high-core `check()`; shard or snapshot as data dictates.
- Cache bounds: eviction policy for relation/evaluator/instantiation caches where
  hit-rate data justifies (`CacheConfig` exists; policy is the missing piece).

## 5. Product programs

- **VM**: ~~exec/realm refactor~~ (phase 0, done); **test262 ladder first pass done
  2026-07-23** (+596 cases across six curated suites; five spec-cited operator fix
  families; 775-entry grouped manifest; all suites green under `--fail-on new` —
  numbers in `wiki/crates/vm-js.md`). ~~Reference-model program~~ — **done
  2026-07-23** (optional-chain short-circuit §13.3.9 incl. the parens-preserve-`this`
  subtlety; GetV autoboxing without wrapper allocation; +122 cases; manifest
  775 → 714 with precise residual reasons). ~~Built-ins program~~ — **done
  2026-07-23** (+187: Object introspection unblocking `propertyHelper.js`
  corpus-wide, `Math`, parse functions/Number statics, `String.fromCharCode`,
  BigInt bitwise over the inline 128-bit representation, catchable `valueOf`
  errors; manifest 714 → 620). ~~Async/generators program~~ — **landed 2026-07-23
  (Fable)**: dual-path step-interpreter, sync generators + async functions fully
  verified, manifest → 546 with a corrected xpass sweep (+68 latent passes).
  Boundary manifested: async generators, `for await`, exotic yield positions.
  ~~Follow-ups~~ — **done 2026-07-23**: `eval_catch` GC rooting; switch CaseBlock
  scoping for gen/async decls; `flags:[async]` `$DONE` wiring; new
  `generators-async` suite (732 floor); `let`-newline ASI fixed in parse-js
  (manifest −8).   ~~Function constructor~~ — **done 2026-07-24** (+32 cases;
  16/17 ids). ~~Async generators / `for await`~~ — **done 2026-07-24** (+20;
  dual-path AsyncGenerator + for-await over `@@asyncIterator`). ~~Minimal
  `RegExp` + `CreateAsyncFromSyncIterator`~~ — **done 2026-07-24** (native-call
  typeof; for-await over sync iters). ~~Wrapper-method cluster~~ — **done
  2026-07-24** (+262; `Array.isArray` + rest `ArrayCreate`, Number/Boolean
  prototype `[[*Data]]`, `toExponential`/`toPrecision`/`split`, wrapper
  `toString` tags; residual ~37). ~~>128-bit BigInt~~ — **done 2026-07-24**
  (hybrid inline `u128` + immortal `num_bigint`; +36 cases; manifest 614 → 601;
  Annex B nested gen/async leak fixed). ~~Destructuring/iterator-protocol~~ —
  **done 2026-07-24** (Array `@@iterator`, IteratorClose/elision/rest/fn-name;
  +320 cases; manifest 601 → 437; residual ~36 class/ToString). Remaining rungs:
  wrapper residue (~37); then module loading completion and WebIDL hardening. ~~Queued design fix: call-time snippet
  re-parse~~ — **done 2026-07-23**: functions retain their parsed AST; re-parse
  eliminated; vm-js fully green (~489 tests incl. 4 un-ignored stale tests).
  Hazard-site note carried forward: the retained-AST design stores a
  `NonNull<Node<Func>>` into the `Arc`-owned tree (documented unsafe, sound while
  the Arc lives and the AST stays immutable at runtime) — same pattern family as
  the checker's `AstIndex` being de-pointered in phase 2; when HIR-side stable IDs
  or an owned code representation become available to the VM, migrate this the same
  direction.
- **Typed optimization** (`optimize-js` typed feature): thread checker facts into
  passes (const-enum folding, property-shape assumptions, devirtualization
  experiments) — gated on checker stability; semantic-equivalence testing via the VM
  once it can execute megatest programs.
- **Minifier compression passes**: **first slice done 2026-07-23** — ownership table
  written into the crate pages; four passes landed with trap tests (nullish `&&`
  dual → `!= null`; resolution-gated `typeof x === "undefined"` → `x === void 0`;
  trailing bare-`return` trimming; `if/else return` → ternary with bottom-up chain
  folding); `const`→`let` **declined** fail-closed (observable TypeError semantics +
  compression evidence — see graveyard). Discovery: minify-js already had a mature
  undocumented `opt/` peephole layer — now documented in its wiki page.
  ~~Block unwrapping~~ — **done 2026-07-24** (safe inert blocks + single-stmt
  control-flow bodies; refuses lexicals/function decls/directive promotion).
  Remaining: declaration combining, constant folding ownership with optimize-js,
  single-use inlining.

## Decisions needing an owner

Load-bearing, not unilaterally decidable
([how-to-work § design and ambiguity](../meta/how-to-work.md#design-and-ambiguity)):

- `AGENTS.md` further slimming (harness contract) — reconcile done 2026-07-24;
  deeper cut to “working rules + pointer only” still needs owner sign-off.
- Statement-span convention (include terminator?) — small but ecosystem-visible via
  SpanMap consumers.
- `strict-determinism` in CI: always-on for tests, or opt-in? (Cost: panics on
  fingerprint collision; benefit: collision events become visible.)
- Whether `typecheck-ts-harness`'s private mechanics converge on
  `conformance-harness` (phase 2.6) before or after the salsa-first refactor — both
  touch runner plumbing.
