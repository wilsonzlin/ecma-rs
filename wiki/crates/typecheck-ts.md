# typecheck-ts

The TypeScript checker: the workspace's flagship product and largest crate. Public
facade `Program` + `Host`; internally a salsa query database plus a (transitional)
imperative program state; body checking is flow-sensitive and parallel. Target
operating model: [architecture/engine.md](../architecture/engine.md). Theory:
[compiler-theory §§ 3–5](../theory/compiler-theory.md).

## Public API

```rust
let program = Program::new(host, roots /* Vec<FileKey> */);
let diagnostics = program.check();                     // parse→lower→bind→check, sorted
let result = program.check_body(body_id);              // Arc<BodyCheckResult>, cached
program.type_of_def(def) / type_of_local(body, local) / type_of_expr(body, expr) / display_type(ty)
program.exports_of(file) / body_of_def(def) / file_id(&key)
program.type_at(file, offset) / symbol_at(file, offset) / expr_at(file, offset)
program.span_of_def(def) / span_of_expr(body, expr)
program.cancel();                                      // cooperative, CANCEL#### diags
```

- **`FileKey`** (`Arc<str>` newtype) is the host's stable name for a file; `Program`
  owns the `FileKey ↔ FileId` mapping so host keys can't collide with bundled libs or
  virtual files.
- **`Host`** supplies `file_text`, `resolve(from, spec)`, `compiler_options`,
  `lib_files`, `file_kind`. `MemoryHost` (in `lib.rs`) is the reference
  implementation: explicit `link()` edges first, then a deterministic relative-path
  fallback resolution (parent-dir join, `.ts` default extension,
  `normalize_ts_path`).
- Offset queries return the smallest covering entity; all offsets are UTF-8 bytes.
- `serde` feature: snapshot types with `schema_version` (see
  `examples/json_snapshot.rs`); `symbols` module exposes `SymbolInfo`/
  `SymbolOccurrence` for IDE-ish consumers; `TypeQueries`/`explain` API surfaces
  assignability reasoning (`ExplainTree`).

Features: `bundled-libs` (default; embeds TS 5.9.3 `lib.*.d.ts`), `serde`,
`serde-json`, `fuzzing`, `resolve` (Node/TS-style resolution helpers used by the CLI).

## Bundled libraries

`typecheck-ts/fixtures/typescript-libs/5.9.3/` vendors the lib files from the official
`typescript@5.9.3` npm package (with `LICENSE.txt` + third-party notices), selected via
`lib_support` (`CompilerOptions { target, lib, … }` → `LibSet`; `LibManager` caches
parsed/lowered libs across `Program`s with `CacheMode`/`CacheOptions`). Keep the vendored
version in lockstep with the harness's pinned `typescript` (difftsc oracle) — both say
5.9.3 as of 2026-07.

## Internal structure

Two cooperating layers (the "dual brain" — transitional, though body checking is
now salsa-side; see assessment in
[overview](../architecture/overview.md#assessment-is-the-current-structure-ideal)):

- **Salsa database** (`src/db/`): inputs (file text/kind, roots, compiler options,
  module resolutions, type store, cancellation, body-check context) + derived
  queries (`parse`, `lower_hir`, `sem_hir`, `module_specifiers/deps`,
  `reachable_files`, `ts_semantics`, `decl_types`, span indices,
  `def_to_file`/`body_to_file`, and — since 2026-07 — `check_body`).
  Query-count metrics (`parse_metrics` etc., `Program::body_check_count`) exist to
  test memoization behavior.
- **`ProgramState`** (`src/program/state.rs` + submodules): orchestrates analysis
  (`state/analysis` — lib collection, HIR alignment, semantic diagnostics), binding
  (`state/bind` — binder over HIR + ambient modules + type imports), declared types
  (`state/decl_types` — `type_of_def`, function types), interning/merging
  (`state/interned`, `state/merging` — canonical interned types for named defs,
  interface/namespace/overload merging), module exports, and span→type queries
  (`state/span_types`).

### Salsa-first body checking (2026-07)

Final-grade body checking is a salsa tracked query
(`db/queries/body_check.rs::check_body_tracked`); the old seeding path
(`Database::set_body_result` / `clear_body_results`, `BodyCheckDb`) is deleted.
How the pieces fit:

- `ProgramState` still computes declaration-grade facts imperatively, then
  publishes a **`BodyCheckContext`** (interned def types, bindings, exports,
  semantics — deliberately *no per-file syntax*) into the DB as an input
  (`set_body_context`). A tracked wrapper (`body_context_tracked`) turns the
  input write into a backdating firewall: the context's semantic `PartialEq`
  decides whether downstream body checks can be reused.
- `check_body_tracked(db, body)` reads the context plus the per-file queries
  (`parse`, `lower_hir`), so invalidation is file-granular: a body-only edit
  re-checks only the edited file's bodies (see `tests/salsa_body_memo.rs`).
  The `AstIndex` over the parsed AST is rebuilt inside the query (cheap, one
  pass over the file) rather than cached, because it borrows from the AST.
- Two supporting invariants, both load-bearing for backdating:
  - `ts_semantics` must not read `lower_hir` directly (parse/lower diagnostics
    are aggregated by `program_diagnostics` instead), so a body edit backdates
    at `sem_hir` and the `Arc<TsProgramSemantics>` identity survives.
  - The context's `(file, span) → def` map picks a deterministic winner when
    defs share a span (`Var` beats `VarDeclarator`, then lowest id) — this was
    previously HashMap-order nondeterminism.
- Parallelism: `program_diagnostics` warms top-level bodies sequentially, then
  rayon-`map_with(db.snapshot())` over the rest; salsa shares in-flight memos
  across threads. `ProgramState.local_body_results` remains only as a local memo
  for inference-grade re-checks and snapshot loading.
- Debugging: set `DEBUG_BODY_CTX_EQ=1` to print which context fields defeated
  backdating after an edit.
- The context also carries `value_defs` (class/enum type-def → synthetic
  value def). The class def stores the *instance* type in
  `interned_def_types`; every value-binding lookup (salsa `map_def_ty`, the
  heritage ctor materialization, `ProgramState`'s binding seeders and
  `dts_value_bindings`/`type_of_def`, and the namespace member build in
  `interned/ensure.rs`) remaps class/enum defs through it so `new C(...)` /
  `N.C` / cross-file ambient classes see the constructor (2026-07-28;
  `tests/namespace_class_merge.rs`).

### Body checking (`src/check/`, mapped into `program::state::check`)

`check_body` builds a CFG (`cfg.rs`: `BlockId`/`BlockKind`, loops, try/catch edges),
then `FlowBodyChecker` runs the flow-sensitive pass: environments of
`FlowKey → TypeId` facts (`flow.rs`, `flow_bindings.rs`), narrowing
fact-transformers (`flow_narrow.rs`: `typeof`/`instanceof`/`in`/literal/
discriminant-path/nullish/truthy/user-guard/assertion), bidirectional expression
typing with contextual types, generic call inference (`infer.rs` — variance-directed
candidate collection), instantiation with caching (`instantiate.rs`: `Substituter`,
`InstantiationCache`), overload resolution (`overload.rs` — arity filtering,
contextual trials, literal-specificity), widening (`widen.rs`), TS type-expression
lowering to interned types (`type_expr.rs`: `TypeLowerer` + `TypeResolver`), class
instance/static shapes from HIR `DefTypeInfo::Class` / `ClassMemberSig`
(`check/decls.rs::HirDeclLowerer`; `class_typing.rs` is HIR span/annotation
helpers only — no `parse_js::ast`), module/namespace member resolution
(`modules.rs`), per-body caches (`caches.rs`: `CheckerCaches`/`BodyCaches`
+ stats). Nominal `private`/`protected` hooks are injected via `check::relate_hooks()`.

HIR body checking is split across `hir_body/` + `body/` (no 11k-line monolith):

- `ast_index.rs` — borrowed `AstIndex<'ast>` (+ class/var/function index builders)
- `hir_body/mod.rs` — entrypoints (`check_body*`), `Checker`/`BindingTypeResolver`
  state, shared assignability/expand helpers, free span/await helpers
- `body/stmts.rs` — statement/driver methods on `Checker` (enclosing bodies, decls, pats)
- `body/exprs.rs` — expression synthesis/checking on `Checker` (literals, members, ops)
- `body/call.rs` — `check_call_expr` / `check_new_expr` + call helpers
- `body/jsx.rs` — JSX element/props/children typing (HIR `JsxElement` preferred)
- `body/bindings.rs` — `FlowBodyChecker` type + binding table/collector
- `body/flow.rs` — `FlowBodyChecker` core (`new`/`run`/`process_block`/`eval_*`)
- `body/flow_ops.rs` — optional-chain, member/assign, switch narrowing ops

`BodyCheckResult` carries expression/pattern type tables, resolved symbols, spans, and
diagnostics; it is `Arc`-shared, cached per body, and reused by offset queries.

Return-position assignability checks distinguish *declared* from *contextual*
targets (2026-07-28): a lambda checked against a generic call parameter gets
`expected_return_defer_type_params`, which defers the hard return diagnostic
when the contextual return mentions a type parameter — tsc validates such
returns only after the call instantiates the signature, and free type params
are nominal targets (`number` ↛ `U`). Declared return annotations (and
instantiated signatures) keep the nominal check. Generic function expressions
keep their source type params on the refined signature so the relate engine's
CSI instantiates them against non-generic targets (free `TypeParam` params in
non-generic signatures are nominal and misfire). Regression:
`tests/contextual_generic_return.rs`, `tests/rest_call_sig_assign.rs`.

Empty-array bindings follow tsc exactly (2026-07-28): `const a = []` binds
`any[]` when `--noImplicitAny` is on (`autoArrayType`; no per-push evolution)
or when `--strictNullChecks` is off (`undefinedWideningType` widens to `any`
for declarations); otherwise (SNC on, NIA off) it keeps the synthesized
`never[]` and `push` errors TS2345. Return/argument positions always
synthesize `never[]` under SNC. Regression: `tests/empty_array_binding.rs`.

JS-file checking is gated on `CompilerOptions.check_js` (2026-07-28): tsc
`allowJs` without `checkJs` is parse-only — `.js`/`.jsx` files produce no
semantic diagnostics at all (not even TS2304/TS2307; oracle-verified), only
parse/grammar diagnostics survive. The filter runs in
`program/state/diagnostics.rs`; the harness maps `@checkJs`. Regression:
`tests/check_js_commonjs_globals.rs`.

`AstIndex` maps HIR stmt/expr IDs back to AST nodes for the checker. Since 2026-07 it
is a borrowed structure (`AstIndex<'ast>` holding `&'ast Node<…>`) built on demand
from the parsed AST — no raw pointers, no `unsafe impl Send/Sync` anywhere in the
crate. The only remaining `unsafe` is `unsafe impl salsa::Update` on DB input
wrappers (salsa's designed extension point; the impls just delegate to semantic `==`).

### Support modules

`codes.rs` (structured `TC####` registry — see
[diagnostics](../architecture/diagnostics.md#checker-specific-conventions)),
`triple_slash.rs` (`/// <reference path|lib|types>` scanning + specifier
normalization), `expand.rs` (`ProgramTypeExpander` bridging the store's `Ref`s to
declared types), `profile.rs` (`QueryStatsCollector`, `--profile` JSON),
`snapshot.rs`, `error.rs` (`FatalError`/`HostError`/`IceContext`), `files.rs`
(`FileRegistry`, `FileOrigin: Source|Lib`), `fuzz.rs`.

## CLI (`typecheck-ts-cli`)

`typecheck <files|--project tsconfig.json>` with: `--type-at file:offset`,
`--symbol-at`, `--exports`, `--explain-assignability`, `--lib`/`--no-default-lib`/
`--target`, `--node-resolve` (node_modules walking; default resolution checks
`<spec>.{ts,d.ts,tsx,js,jsx}` + `index.*`), `--json` (versioned schema; paths
normalized via `normalize_ts_path` — forward slashes, lowercased drive letters,
collapsed dots), `--trace`/`--profile` (JSONL spans on stderr). `tsconfig.rs` handles
compiler options, file discovery, and `baseUrl`/`paths`. Human diagnostics render via
`diagnostics::render`; exit 1 on any error diagnostic.

## Verification surface

129 integration test files under `tests/` (narrowing, classes, generics, decl merging,
modules, JSX, cancellation, db memoization, litmus fixtures...), examples
(`memory_host_basic`, `json_snapshot`), benches (`bench/typecheck-ts` — pipeline,
alloc-counting, incremental edit scenario on a live `Program` via `set_file_text`
+ `body_check_count`), and the conformance/difftsc harness
([testing](../engineering/testing.md)). Metrics counters (`parse_call_count`,
`lower_call_count`, `decl_types_call_count`) let tests assert caching behavior.

## Known issues and directions

- **Dual-brain unification**: body checking is salsa-first as of 2026-07 (see
  above), but declaration types (`type_of_def`, interning/merging) are still
  computed imperatively in `ProgramState` and enter salsa only via the published
  context input. Migrating decl types into tracked queries is the remaining half
  ([roadmap phase 2](../status/roadmap.md#2-structural-refactors)).
- **Context granularity**: the body-check context is program-wide, so a
  declaration change (or any span shift from a length-changing edit) currently
  re-checks all bodies. Splitting per-file slices out of the context would
  tighten this.
- **Residual direct AST pattern-matching** in the checker (the raw-pointer
  `AstIndex` was made safe/borrowed in 2026-07, but body expression structure /
  residual `check/type_expr.rs` still consume AST nodes; JSX prefers HIR
  structure (AST residual when missing); declared-type +
  type-alias span lookup and class-member typing are HIR-only as of 2026-07-24;
  body var / assertion / Instantiation / **function param+return** annotations
  prefer HIR as of 2026-07-25 — see below;
  [roadmap](../status/roadmap.md#2-structural-refactors)).
- **Parallel-checking deadlock** via `types-ts-interned` (not this crate's code, but
  this crate's workload triggers it) — workaround `RAYON_NUM_THREADS=1`; see
  [determinism case study](../architecture/determinism.md#case-study-the-nameinterner-deadlock).
- Conformance pass-rate baseline (2026-07-24 late): **532/1521 = 34.98%** exact-match
  on upstream hash shards **0–15/64** vs live tsc (was 417/1173 = 35.55% on 0–11;
  earlier 4-shard sample without shard 2 was 35.4%). See the
  [baseline table + ratchet commands](../engineering/testing.md#upstream-conformance-baseline-shards-vs-live-tsc).

### Conformance gap categories (2026-07-23 pass)

Fixed (checker):
- **TC3000 implicit-any false positives on defaulted parameters** — a parameter
  with an initializer (`function f(bar = foo ?? "bar") {}`) infers its type from
  the widened initializer, so `--noImplicitAny` must not flag it. Fixed in both
  emission sites: body checking (`check/body/stmts.rs::bind_params`) and declared
  function-signature typing (`program/state/merging/interned_named.rs`).
  Regression test: `tests/no_implicit_any.rs::parameter_default_value_suppresses_implicit_any`
  (cites `expressions/nullishCoalescingOperator/nullishCoalescingOperator6.ts`).
- **Annotated class-field implicit-any false positive** — `#name: string` /
  `x: string` were flagged TC3000 because `type_of_def` only consulted
  `declared_type_for_span` (statement walk; no class bodies) and `VarData.typ`
  (always `None` for fields). Fixed by reading HIR `DefData.declared_type` via
  `hir_declared_type_for_def` / span lookup, wiring those paths into
  `type_of_def`, body binding, and interned-type ensure.
  Regression: `tests/no_implicit_any.rs::annotated_class_fields_suppress_implicit_any`.
  Upstream harness vs tsc: `privateNameField.ts` **exact match** (2026-07-24).
- **HIR-only class member typing slice (2026-07-24)** — deleted the unused
  AST-walking `class_typing` module; replaced with HIR helpers
  (`hir_class_member_type_at_span` over `ClassMemberSig`).
  `declared_type_for_span` no longer descends into `ClassDecl` /
  `AmbientClassDecl` / class-expression AST (ambient + param-prop fields resolve
  via class `DefTypeInfo::Class` member list). Shapes still come from
  `HirDeclLowerer::lower_class_instance_and_value`. AST-use in that subsystem
  **15 → 1** (non-class `TypeParameter` on var/alias fallback).
- **HIR-only declared-type / type-alias slice (2026-07-24)** — removed the AST
  statement walk from `declared_type_for_span` and `type_alias_type_for_span`.
  Module/ambient `let`/`const`/`var` annotations lower from
  `DefData.declared_type` (populated in hir-js for declarators, simple Id
  bindings, and ambient vars); type aliases recompute via
  `HirDeclLowerer::lower_type_info` on `DefTypeInfo::TypeAlias`. Qualified refs
  (e.g. `Foo.Bar` after `import = require`) use `ProgramTypeResolver` hooked into
  `HirDeclLowerer::with_type_name_resolver`.   Residual AST in `span_types/declared.rs`:
  binder-only `TypeParameter` / `type_from_type_expr`. Regression:
  `hir-js/tests/types_lowering.rs::lowers_module_var_and_ambient_declared_types`.
- **HIR-only binder type-alias seed (2026-07-24)** — when `hir_lowered` is already
  present for the file, binder `TypeAliasDecl` (module + ambient) stores
  `unknown` instead of walking the AST type expression; `type_of_def` always
  recomputes from HIR `DefTypeInfo::TypeAlias` when the seed is `unknown`.
  Avoids mid-bind HIR lowering with incomplete semantics/bindings.
- **HIR-only binder param/return annotations (2026-07-24)** — binder
  `lower_function` / `lower_param` leave `FuncData` param/return types unset
  when HIR is present (no AST `type_from_type_expr`). `function_type` /
  `type_of_def` lower from `hir_js::FunctionData` via
  `HirDeclLowerer::lower_value_function_signature` (params, optional/rest,
  return, type params, `this`, type predicates). Overload collection and
  cached-return inference consult HIR for “has return annotation” when
  binder `return_ann` is unset. Regression: `tests/hir_function_annotations.rs`.
- **HIR-only `collect_function_decl_types` (2026-07-25)** — for TS/TSX/DTS
  files that already have HIR + a parsed AST entry, top-level named
  `function` / `declare function` signatures (including overload sets) lower
  from `hir_js::FunctionData` via `HirDeclLowerer::lower_value_function_signature`
  (no AST `TypeLowerer`). Scoped to `HirFile.items` (skips arrow/`<arrow>`
  expression defs) and to `self.asts` keys (does not re-lower lib `.d.ts`).
  Overload implementation filtering uses `FunctionData.has_body`. Body checking
  skips AstIndex lookup for signature-only bodies (`has_body: false`) so
  `declare function` / overloads do not ICE. Residual AST path: JS/JSX (JSDoc
  `@param`/`@returns`/`@template`) and files without HIR.   Residual binder AST
  `type_from_type_expr`: type-alias fallback when HIR missing (+ function
  param/return when HIR missing). Body checking still uses AST for expression
  structure (JSX prefers HIR `JsxElement`); Instantiation type args / `as` /
  `satisfies` / `as const` prefer HIR (see below). Regressions:
  `tests/hir_function_annotations.rs` (overloads + `declare function`),
  `hir-js/tests/lowering.rs::lowers_function_overload_has_body_flags`.
- **HIR-only binder ambient var annotations (2026-07-25)** — binder
  `AmbientVarDecl` leaves `VarData.typ` unset when HIR is present (no AST
  `type_from_type_expr`). `type_of_def` / body seeds lower from
  `hir_js::DefData::declared_type` via `hir_declared_type_for_def` (same path
  as module `let`/`const`/`declare var` which already bind with `typ: None`).
  Residual binder AST `type_from_type_expr`: type-alias + function param/return
  fallbacks when HIR missing. Regression: `tests/hir_ambient_var_annotations.rs`.
- **HIR-only body var annotations (2026-07-25)** — `check_var_decl` /
  `check_matching_initializer` prefer HIR `VarDeclarator.type_annotation`
  (`TypeExprId` via body type arenas + `HirDeclLowerer::lower_body_annotation`)
  for primitives/literals/unions/arrays/tuples, **named type refs**,
  **`typeof`**, **function/constructor types**, **object type literals**,
  **mapped / conditional / template-literal / infer / predicate** types
  (body `TypeResolver` via `with_type_resolver` + live scope bindings via
  `with_typeof_bindings`). AstIndex `VarInfo.type_annotation` / AST
  `TypeLowerer` is residual for **`import(...)` / `typeof import(...)`**
  (body lowerer has no host) and JSDoc `@type`. Regression:
  `tests/hir_body_var_annotations.rs`.
- **HIR-only body type assertion / `satisfies` / `as const` (2026-07-25)** —
  `check_expr` prefers HIR `ExprKind::TypeAssertion` /
  `ExprKind::Satisfies` (`const_assertion` flag + `TypeExprId`) via the same
  body `hir_lower_type_expr_id` path as var annotations (named refs / `typeof`
  / function / object / mapped / conditional / … via body `TypeResolver`).
  AST `TypeLowerer` is residual for **`import(...)` / `typeof import(...)`
  assertion targets** and missing arenas. Regression: `tests/hir_body_assertions.rs`.
- **HIR-only Instantiation type arguments (2026-07-25)** — `hir-js` keeps
  `ExprKind::Instantiation { expr, type_args: Vec<TypeExprId> }` (no longer
  erases to the inner expr). Body `check_expr` prefers those HIR type args via
  the same `hir_lower_type_expr_id` / body `TypeResolver` path as var
  annotations and assertions. AST `TypeLowerer` is residual for
  **`import(...)` / `typeof import(...)` type args** and missing arenas.
  Emit/optimize/flow treat Instantiation as a transparent wrapper.
  Regressions: `tests/hir_body_instantiation.rs`,
  `hir-js/tests/lowering.rs::lowers_instantiation_type_args`.
- **HIR-only body function param/return annotations (2026-07-25)** —
  `bind_params`, enclosing-function return expected-type, and body-matched
  `function_type` prefer `hir_js::FunctionData` param/return `TypeExprId`s via
  `hir_lower_type_expr_id` (seeded with AST `TypeLowerer` type-param ids so
  `f<T>(x: T)` shares the same `TypeParamId`s). Gated by param-pattern span
  match so nested function-expression refine/synthesis on an outer body does
  not steal the outer `FunctionData`. Residual AST `TypeLowerer`:
  **`typeof import(...)`**, missing arenas, JSDoc `@param`/`@returns`,
  **function type-parameter registration** (`register_type_params`), nested
  function-expression signature synthesis when the enclosing body is not the
  function being typed, and AstIndex class-field / SPI / subsequent-property
  annotations. `check/type_expr.rs` is documented as the AST quarantine.
  Regression: `tests/hir_body_param_return.rs`.
- **HIR-preferred JSX element structure (2026-07-25)** — `check_jsx_elem`
  prefers `hir_js::JsxElement` (`ExprKind::Jsx`) for tag resolution, attrs,
  and children via the body expr map. Nested JSX children recurse on HIR
  `ExprId`s (AstIndex does not index nested `JsxElem` as expressions). Empty
  expression containers use HIR `JsxExprContainer.expr: None`. Residual AST
  `JsxElem` walk when HIR is missing at the element span; nested non-JSX
  attr/child values still resolve AST by span for `check_expr` / excess
  property. No AST `TypeLowerer` / `TypeExpr` in `body/jsx.rs`. Regression:
  `tests/hir_body_jsx.rs` (+ existing `tests/jsx.rs`).
- **Property-lookup cycle guard (2026-07-24 late)** — `lookup_interned_property_type`
  tracks seen `TypeId`s and stops when `expand_ref` returns the same/`seen` ref
  (in-progress cycle break). Fixes harness process aborts on generic-class
  dual-instantiation member access (`privateNamesInGenericClasses.ts`,
  `mergedInterfacesWithInheritedPrivates{,2}.ts`). Regression:
  `tests/generic_class_cross_instantiation.rs`.

Fixed (harness fidelity, `typecheck-ts-harness`):
- **Spurious TS6504** (30/401 of the before-baseline) — the harness dropped
  `@allowJs`/`@checkJs` directives, so tsc refused to check `.js` fixtures. Now
  forwarded to the tsc options map, exposing the fixtures' real diagnostics.

Fixed (name resolution / checkJs ambients, 2026-07-24; gated 2026-07-25):
- **`TS2304` code parity + CommonJS ambients** — user-facing unresolved identifiers
  emit tsc-shaped `TS2304` "Cannot find name '{0}'." (body checker, JSX tags, decl
  type lowering); legacy `TC0005` remains only for intentional internal emitters.
  CommonJS ambient values (`require`/`module`/`exports`) are seeded as `any` for
  `.js`/`.jsx` file bindings **only when** the AST sets tsc's
  `commonJsModuleIndicator` (`require(...)`, `module.exports =`, public
  `exports.foo =` / `exports["foo"] =`); `exports.#private =` does **not** count.
  `globalThis` is always present. Tests: `check_js_commonjs_globals.rs`.
  Remaining: resolver misses on some declared names (`Base`/`Derived`); typed
  `require` / `module.exports` shapes (still `any`).

Fixed (JSDoc `@type` first slice, 2026-07-24):
- **JSDoc `@type` on var declarations (checkJs / `.js`/`.jsx`)** — because
  `parse-js` lexes/skips comments and does **not** attach them to AST nodes, the
  checker scans source text for the `/** … */` (or `/* … */`) block immediately
  preceding a declaration `Loc`, parses `@type {…}`, and applies it as the
  declared type when there is no TypeScript annotation. Bad initializers emit
  **TS2322**. Module: `src/jsdoc/`; wired in `check_var_decl` /
  initializer-body checking when `FileKind` is `Js`/`Jsx`. Minimal type
  lowering: primitives, idents, `A|B`, `T[]`/`Array<T>`, `?T`/`T?`.
  Regression: `tests/jsdoc_type.rs`.

Fixed (JSDoc `@param` / `@returns`, 2026-07-24):
- **`@returns {T}` / `@return {T}`** on function declarations/expressions under
  checkJs — applied as `expected_return` when there is no TS return annotation
  (bad returns → **TS2322**). Also feeds callable signatures
  (`Checker::function_type`, `lower_function_signature`) so call-site checking
  sees the declared return.
- **`@param {T} name`** (aliases `@arg` / `@argument`; optional `[name]` /
  `{T=}`) — applied as the parameter binding type when there is no TS
  annotation; bad assignments / uses → **TS2322**, bad call args → **TS2345**
  (or TS2322). Leading comment is taken from immediately before `function`/`=>`,
  or from the enclosing `var`/`let`/`const` when the initializer is a
  function/arrow expression.
  Regression: `tests/jsdoc_param_returns.rs` (plus existing `jsdoc_type.rs`).

Fixed (JSDoc `@typedef` / `@template` slice, 2026-07-24):
- **`@typedef {T} Name`** (and `@typedef Name` + `@type {T}` on the same
  comment) — file-scope aliases collected by scanning all block comments in
  checkJs sources; names resolve when lowering later `@type` / `@param` /
  `@returns` tags (cycle-safe). Bad uses → **TS2322** / **TS2345**.
- **`@typedef {Object}` + `@property` / `@prop`** — builds interned object
  shapes (optional `[name]` / `{T=}` / name-before-brace forms). Enough for
  common `Opts`-style typedefs used in `@param`.
- **`@template T` / `@template {Constraint} T`** (comma-separated names) —
  when a function has no TS type-parameter list, templates are registered as
  real `TypeParam`s for param/return JSDoc lowering and callable signatures.
  Regression: `tests/jsdoc_typedef.rs` (module unit tests in `src/jsdoc/`).
  Optional harness filter: `--filter "*jsdoc*Typedef*"` /
  `"*/jsdoc/checkJsdocTypedef*"`.

Fixed (JSDoc `new:` / construct signatures, 2026-07-25):
- **Closure `function(new: T, …)`** lowers to an object type with a
  construct signature (return = `T`; trailing `: R` ignored, matching tsc
  `isJSDocConstructSignature`).
- **`@constructor` / `@class`** — synthesize constructable value types +
  instance typedef aliases from `this.prop = param` assignments; JS class
  constructors also contribute instance props the same way.
- **`this:` contextual typing** on function expressions; function types
  parsed before union split so `function(): A | B` stays atomic.
- Class-method JSDoc loc uses the member span (fixes `@param` on
  `constructor`).
- Regression: `tests/jsdoc_inline_types.rs` (`jsdoc_new_*`, `this:`, literal
  unions) + unit tests in `src/jsdoc/`.
- Cleared XPASS: `jsdoc/jsdocFunctionType.ts`.

Fixed (JSDoc inline object / function types, 2026-07-25):
- **Inline object type literals** — `{ a: string, b?: number }` (and
  `@type {{…}}` double-brace form after brace strip) lower to interned object
  shapes in `@type` / `@param` / `@returns` / `@typedef`.
- **Function type literals** — Closure `function(string): number` /
  `function(boolean, string, ...*): void` and TS-in-JSDoc
  `(s: string) => void`; bare `function`/`Function` → loose callable.
  String/number/boolean literals supported in unions.
- **`@type` as whole-signature context** — on function decls and via var
  annotation contextual typing; AST `lower_function_signature` uses `@type`
  callables so `--noImplicitAny` does not emit **TC3000** when params are
  covered. Identifier assignment **TS2322** spans anchor on the LHS name
  (tsc parity).
- Regression: `tests/jsdoc_inline_types.rs` (+ unit tests in `src/jsdoc/`).
- Cleared XPASS: `jsdoc/jsdocTypeTagParameterType.ts`.

Fixed (JSDoc typedef export / qualified names, 2026-07-25):
- **`@typedef {T} exports.Foo`** (dotted namepaths, incl. nested
  `exports.ns.Foo`) — stored under the full path; `@type {exports.Foo}`
  resolves for assignability (**TS2322** on bad inits).
- **Nameless `@typedef {T}` + `exports.Foo = …` /
  `module.exports.Foo = …`** — registers short `Foo` and the full path.
- **Bare `exports.Foo;` host (no assignment)** — not registered as a
  namespace export; `@type {exports.Foo}` emits **TS2694** with the primary
  span on the rightmost segment (tsc parity).
- Regression: `tests/jsdoc_typedef.rs` + unit tests in `src/jsdoc/`.
- Cleared XPASS: `jsdoc/checkJsdocTypedefOnlySourceFile.ts`.

Fixed (JSDoc nested `@param opts.x` sugar, 2026-07-25):
- **Nested `@param name.prop` / `opts.x` property sugar** — `@param {object} opts`
  followed by `@param {T} opts.x` (and recursive / `opts[]` element paths) folds
  into an object (or array-of-object) type for the root parameter. Missing an
  immediate `@param {object}` parent emits **TS8032** (upstream
  `paramTagNestedWithoutTopLevelObject{,2,3,4}`).
- Regression: `tests/jsdoc_param_returns.rs` + unit tests in `src/jsdoc/`.
- Cleared XPASS: `jsdoc/paramTagNestedWithoutTopLevelObject{,2,3,4}.ts`.

Fixed (JSDoc class `@template` call-site instantiation, 2026-07-25):
- **Class-level `@template T` + constructor `@param {T}`** — when a JS class has
  no TS type-parameter list, leading `@template` tags are registered as real
  `TypeParam`s; constructor `@param` types resolve those names; `this.prop = param`
  instance props pick up the param types; class type params are attached to the
  **construct signature** so `new Foo(arg)` infers/instantiates (same attach fix
  helps TS generic classes). Cross-instance assigns like `f.a = g.a` after
  `new Foo(1)` / `new Foo(false)` emit **TS2322**.
- Regression: `tests/jsdoc_typedef.rs` + `src/jsdoc/` class/ctor tag locators.
- Cleared XPASS: `jsdoc/jsdocTemplateClass.ts`.

Fixed (JSDoc unmatched root `@param` / TS8024, 2026-07-25):
- **TS8024** for root `@param {T} name` with no matching identifier parameter
  (tsc `checkUnmatchedJSDocParameters`: binding-pattern index exclusion;
  suppress when the root absorbed nested `name.prop` children / `isNameFirst`).
  Multi-declarator `var a = function…, b = function…` shares the statement
  JSDoc (second initializer can XPASS-match tsc).
- Regression: `tests/jsdoc_param_returns.rs` + unit tests in `src/jsdoc/`.
- Cleared XPASS: `jsdoc/jsdocParamTagTypeLiteral.ts`,
  `jsdoc/checkJsdocParamOnVariableDeclaredFunctionExpression.ts`.

Deferred (JSDoc / checkJs remainder):
- **Deeper `@template` parity** — typedef `@template` + indexed access
  (`jsdocTemplateTagNameResolution`), variance/`in`/`out` on templates
  (`jsdocTemplateTag8`), defaults, `@constructor` function templates, callback-
  nested templates; function `@template` call-site already works for identity-
  style cases.
- **TS8024 mixed fixtures** — still xfail where other codes dominate
  (`jsdocParamTag2` needs TS2339 on bad1; `paramTagWrapping` /
  `jsdocPrefixPostfixParsing` / `typedefInnerNamepaths` mix parse errors).
- **parse-js comment attachment** — optional future; current design intentionally
  uses source-text scan so the parser stays comment-free.
- Remaining upstream jsdoc/salsa fixtures beyond this slice (cross-module
  typedef merges, `@callback`, deeper CJS namespace graphs).

Fixed (object spread + Object apparent members, 2026-07-27):
- **Object-literal `...spread` merges own properties** into the inferred shape
  (AST + HIR flow). Previously `ObjMemberType::Rest` / `ObjectProperty::Spread`
  only type-checked the operand and left the literal as `{}`, so
  `const t: T = { ...source }` falsely reported TS2741.
- **`EmptyObject` / missing own props fall back to lib `interface Object`** in
  `member_type` (`object_interface_type`), restoring `hasOwnProperty` /
  `toString` / etc. under `--noImplicitAny` while keeping the global `Object`
  → `{}` assignability shortcut. Exact XPASS:
  `intersectionIncludingPropFromGlobalAugmentation`. Manifest **3682 → 3681**.
  Regression: `tests/object_spread_props.rs`.

Fixed (TS2454 bare `true`/`false` unreachable branches, 2026-07-27):
- **Dead opposite branch of bare boolean conditions skips TS2454** — tsc binder
  `createFlowCondition` returns `UnreachableFlow` for the false side of
  `TrueKeyword` / true side of `FalseKeyword` (not parenthesized). Identifiers
  under unreachable flow keep the declared type (no `| undefined`), so no
  TS2454. HIR `Expr.parenthesized` preserves the parse-js assoc marker; CFA sets
  `Env.suppress_da` on dead branches of `?:`, `&&`/`||`, and
  `if`/`while`/`for`/`do` tests. Exact XPASS:
  `bestCommonTypeOfConditionalExpressions2` (extra `derived2` TS2454). Manifest
  **3683 → 3682**. Regression: `tests/ts2454_residuals.rs` +
  `hir-js` `lowers_expr_parenthesized_flag_on_boolean_literal`.

Fixed (TS2454 for-in/of DA slice, 2026-07-24):
- **TS2454 used-before-assignment on for-in/of RHS with DA-exempt types** —
  tsc only emits TS2454 under `strictNullChecks`, and suppresses it when the
  declared type is `any`/`unknown`/`void` or includes `undefined`
  (`assumeInitialized` / `containsUndefinedType` in `checker.ts`). Our CFA was
  flagging e.g. `let obj: any; for (let y in obj)` and
  `var x: any; for (var v of x)` (upstream `controlFlowForInStatement.ts`,
  `for-of24.ts`). Fix: record exemptions from HIR `VarDeclarator.type_annotation`
  (via body-owner `TypeArenas`) in `FlowBodyChecker`, and gate emission in
  `should_report_use_before_assignment`. for-in/of LHS assignment remains
  definite inside the loop body and not after (unchanged CFG edges).
  Regression: `tests/ts2454_for_in_of.rs`.

Fixed (TS2454 residuals / TDZ / `x!`, 2026-07-24):
- **Type-alias DA exemptions** — expand same-file `TypeRef` annotations via
  `DaTypeAliasMap` (cycle-safe) so `type A = any` / `type U = T | undefined`
  match tsc's resolved-type `assumeInitialized` / `containsUndefinedType`.
- **`for (let v of v)` → TS2448** — BindingCollector marks for-in/of RHS (and
  self-init) uses of the head binding as TDZ; flow emits
  `BLOCK_SCOPED_USED_BEFORE_DECLARATION` and suppresses TS2454 on for-head RHS
  (`for-of55.ts`).
- **`x!` suppresses TS2454** — `NonNull` evaluates the operand with
  `suppress_uninit` (tsc `node.parent.kind === NonNullExpression`).
  Regression: `tests/ts2454_residuals.rs`.

Fixed (TS2454 `(x)!` paren distinction, 2026-07-25):
- **`(x)!` still reports TS2454** — parse-js marks parenthesized operands with
  `ParenthesizedExpr` (no distinct AST node). HIR now records
  `NonNull.operand_parenthesized`; CFA only suppresses DA when that flag is
  false (`x!` / `(x!)`), matching tsc's parent-kind check. No upstream XPASS
  (pattern nearly absent from conformance corpus).
  Regression: `tests/ts2454_residuals.rs` + `hir-js` `lowers_nonnull_operand_parenthesized_flag`.

Fixed (TS2454 destructuring sibling defaults, 2026-07-25):
- **Left-to-right pattern binding marks prior siblings Assigned** before later
  defaults run — matches tsc/JS evaluation order for
  `const { a, b = a } = …`, `const [a, b = a] = …`, and
  `let [{ ...a }, b = a] = …`. Root cause: `bind_pat_with_mode` evaluated all
  defaults while the whole pattern was still `Unassigned`, then
  `mark_pat_state(Assigned)` ran only after the full bind. Fix: mark
  `InitState::Assigned` at Ident / AssignTarget leaves during bind (declarators
  without initializers still overwrite to `Unassigned` afterward).
  Cleared XPASS xfails: `*SiblingInitializer*` (object+array) and
  `destructuringEvaluationOrder.ts`. Regression: `tests/ts2454_residuals.rs`.

Fixed (TS2454 ambient `declare let`, 2026-07-25):
- **`declare let/var` assumed initialized** — parse-js dropped the `declare`
  keyword on `VarDecl` (unlike `ClassDecl.declare`), so HIR/`DefData.is_ambient`
  only covered `.d.ts` via `FileKind`, and CFA marked bare `declare let x`
  as `Unassigned` → spurious TS2454 on every use. Fix: thread
  `VarDecl.declare` parse → HIR, set `DefData.is_ambient`, and treat
  `decl.declare` as `InitState::Assigned` in `bind_var_declarators`.
  Cleared XPASS: `literalTypesAndDestructuring.ts`, `logicalAssignment9.ts`.
  Regression: `tests/ts2454_residuals.rs` (+ HIR ambient assert).

Fixed (abstract-class property DA / init flow, 2026-07-25):
- **TS2715 / TS1267 / field-init TS2729** — parse-js seeded every member of an
  `abstract class` with `abstract_=true` (ambient class-body flag), so concrete
  fields looked abstract. Fix: `abstract_` only from the keyword; body-less
  methods still allowed via `allow_no_body = abstract_ || ambient`. Checker
  tracks unresolved abstract instance props (inheritance-aware), emits TS2715
  on `this` access during constructor/field-init (plus TS2729 in field inits),
  TS1267 for `abstract prop = …`, and wires `HirDefKind::Field` into
  `var_initializer` so `@strict`+`@declaration` infers `prop = 1` (no TC3000).
  Cleared XPASS: `abstractPropertyInitializer.ts`. Codes match on
  `abstractPropertyInConstructor.ts` (one object-binding span ±2). Regression:
  `tests/abstract_class_da.rs`.
- **TS2715 nested-function boundary (2026-07-28)** — `check_enclosing_function`
  resolved a body's class member by tightest *containing* member span, so a
  function nested inside a constructor inherited `constructor_class_index` and
  false-flagged `this.abstractProp` reads. Membership is now exact `Func.loc`
  match only (both maps share the span space, so exact hits iff the body *is*
  the member), matching tsc `isNodeUsedDuringClassInitialization` quitting at
  function boundaries. Regression: `tests/abstract_class_da.rs`
  (`nested_function_may_read_abstract_prop`).

Fixed (TS2454 imported / generic type-alias DA, 2026-07-25):
- **Generic alias subst** — `DaAliasBody` now carries `type_params`; DA exemption
  expands `Id<any>` / `Just<string|undefined>` / defaults (`type Id<T = any> = T`)
  with cycle-safe param chasing (`type V<T> = Id<T>`).
- **Imported aliases** — body-check builds a cross-file `DaTypeAliasMap` (export
  graph + re-export `type_id` nullary fallback) so `import type { A }` / `Box<T>`
  match tsc `assumeInitialized` / `containsUndefinedType`.
  Cleared XPASS: `intersectionMemberOfUnionNarrowsCorrectly.ts` (stale
  `declare let` + alias annotation extra TS2454). Regression:
  `tests/ts2454_residuals.rs` (`generic_alias_subst_da_exemptions`,
  `imported_alias_da_exemptions`).

Fixed (TS2564 / `strictPropertyInitialization`, 2026-07-25):
- Wired `CompilerOptions::strict_property_initialization` (default off; `@strict` /
  `strict` preset and explicit `@strictPropertyInitialization` / tsconfig enable
  it). Requires `strictNullChecks` (tsc rule). In query signatures via
  `BodyCheckContext`.
- Top-level analysis emits **TS2564** for non-static instance props (identifier /
  private) without initializer/`!`/abstract, whose type is not any/unknown and
  does not contain `undefined`, when not assigned on every constructor exit path
  (param props + path-sensitive `this.x =` / `this.#x =`). Ambient/`declare class`
  and string/numeric literal keys skipped.
- Constructor body tracking emits **TS2565** for `this` reads of those props
  before assignment.
- Conformance `strictPropertyInitialization.ts`: **exact match** vs tsc
  (7×TS2564 + 3×TS2565); xfail cleared 2026-07-25 (XPASS).
- Follow-on (same day): ctor `this` gets the class instance type (construct
  return / ClassInfo field shape) so `let x = this.a` is not unknown→TC3000;
  HIR `EnumMember` defs get string/number/`any` declared types instead of bare
  untyped `Var`s (string enum `A`/`B` TC3000).
  Regression: `tests/strict_property_initialization.rs`
  (`ctor_this_prop_and_string_enum_no_tc3000`).
- Follow-on (same day): non-ctor `contextual_this_ty` for instance methods,
  instance field initializers, static methods/fields/static blocks (instance vs
  static side). Clears checkJs `inferringClassMembersFromAssignments7` XPASS
  (`var self = this` no longer unknown→TC3000). Regression:
  `method_and_field_initializer_this_prop_no_tc3000`.
- Follow-on (same day): class **getter/setter** no longer align as bare `Var`s
  (`HirDefKind::Getter`/`Setter` → `DefMatchKind::Function`); after interned
  class shapes land, unknown accessor properties are refined from inferred
  getter return / setter param types so `get g()` / `let x = this.g` are not
  TC3000 under `--noImplicitAny`. Unannotated setter params still TC3000
  (tsc TS7006). Cleared XPASS: `privateNameStaticsAndStaticMethods.ts`,
  `privateNamesAndStaticMethods.ts`. Regression:
  `class_getter_setter_no_spurious_tc3000`.
- Follow-on (same day): unannotated **static fields** initialized in static
  blocks (and auto-accessors) infer from `this.prop = …` / field-init order
  (tsc static evaluation); `<static_block>` defs are void (not TC3000); assignment
  LHS in static blocks emits **TS2729** when the field is declared later.
  Cleared XPASS: `classStaticBlockUseBeforeDef{1,2,4,5}.ts`. Residual:
  `classStaticBlockUseBeforeDef3.ts` (FOO TDZ TS2448/TS2454). Regression:
  `static_block_assigned_fields_no_spurious_tc3000`,
  `static_block_use_before_field_decl_is_ts2729`.
- Follow-on (same day): **TS2540** on assign to readonly properties /
  getter-only accessors (including private `#roProp` / static `#roProp`).
  Shape merge treats a property as writable if any declaration is writable
  (getter+setter). Ctor/`this` may still assign `readonly` *fields*;
  getter-only accessors never. Cleared XPASS: `privateNameAccessors.ts`,
  `privateNameStaticAccessors.ts`. Regression: `tests/readonly_assign.rs`.
- Follow-on (same day): **TS2806** on read of setter-only private accessors
  (`set #x` without `get #x`) — plain reads, compound `+=`, nested
  `this.#x.prop`, and nested destructuring reads. Definite writes
  (`this.#x = …`, destructuring / array targets) stay quiet. Cleared XPASS:
  `privateWriteOnlyAccessorRead.ts`, `privateNameSetterNoGetter.ts`.
  Regression: `tests/private_write_only_accessor.rs`.
- Follow-on (same day): **TS2803** on assign to private methods (`#m() {}`) —
  definite `=`, destructuring targets, and `++`/`--` (including on `any`).
  Does not suppress TS2322 when the RHS is also mistyped. Call checking now
  allows excess arguments (tsc/JS), which cleared the ASI-glued
  `() => {}(…)` false TC2000 on the method-assignment fixtures. Cleared XPASS:
  `privateNameMethodAssignment.ts`, `privateNameStaticMethodAssignment.ts`,
  `privateNameReadonly.ts`. Regression: `tests/private_method_assign.rs`.
- Follow-on (same day): **TS18016** for illegal private-name *declarations*
  outside class bodies — object-literal fields/methods/accessors, and
  type/interface/object-type property & method signatures (including nested
  ambient literals). Parser type-member spans now include the key and trailing
  `;` so method-signature primary spans match tsc. Cleared XPASS:
  `privateNameInObjectLiteral-{1,2,3}.ts`, `privateNameAndPropertySignature.ts`.
  Cleared XPASS (later same day with undeclared-`#` TS2339):
  `privateNameBadDeclaration` / `privateNameJsBadDeclaration`. Regression:
  `tests/private_name_illegal_decl.rs`.
- Follow-on (same day): **TS18013** / **TS18014** private-identifier visibility
  — outside defining class, derived-class, and cross-class access (fields /
  methods / accessors); nested-class same-spelling shadowing (TS18014). Primary
  span is the private name. Cleared XPASS: `privateNameNotAccessibleOutsideDefiningClass`,
  `privateName{Field,Methods,Accessorss,StaticField}DerivedClasses`,
  `privateName{Method,Accessors,StaticAccessors}Access`,
  `privateNamesInterfaceExtendingClass`. Nested shadowing fixtures still
  `rust_extra` TC2008. Regression: `tests/private_name_access.rs`.
- Follow-on (same day): **TS18016** for private-name *access* outside a class on
  any-like receivers (`any` / `never` / unresolved error-recovery `any`) when no
  lexical private is in scope — tsc
  `checkPropertyAccessExpressionOrQualifiedName` any-like branch. Unresolved
  names now recover as `any` (tsc `errorType`).
- Follow-on (same day): **anonymous class-expression private members** —
  `AstExpr::Class` now takes the HIR-lowered constructor value type (privates on
  instance/static shapes); unannotated method returns are refined from bodies so
  factories like `getInstance() { return new C(); }` are not stuck at `() => any`
  (which skipped TS18013). Cleared XPASS: `privateNameMethodClassExpression.ts`,
  `privateNameStaticMethodClassExpression.ts`. Regression:
  `tests/private_name_access.rs` (anon / getInstance / static twins).
- Follow-on (same day): **`delete` of private names** — TS18011 on
  `delete this.#x` (primary span: full access) plus TS2790 when the field is not
  optional under `strictNullChecks` (ClassInfo hint when synthesized `this`
  still has unannotated `#v` as `unknown`). Cleared XPASS:
  `privateNamesNoDelete.ts`. Regression: `tests/private_name_delete.rs`.
- Follow-on (same day): **undeclared `#` TS2339** on concrete receivers —
  when `checkPrivateIdentifierPropertyAccess` finds no same-spelling private on
  the receiver (and 18013/18014/18016 do not apply), emit TS2339 on the private
  name (tsc `reportNonexistentProperty` fall-through). Cleared XPASS:
  `privateNameBadDeclaration.ts`, `privateNameJsBadDeclaration.ts`. Residual
  at the time: `privateNameBadAssignment*` / checkJs `exports` (see follow-on).
  Regression: `tests/private_name_illegal_decl.rs` (constructor / `this` /
  instance undeclared-`#` cases).
- Follow-on (2026-07-26): **static private missing on receiver type** — same
  TS2339 path covers `typeof Derived` lacking base `static get #prop` (privates
  are not inherited onto the derived constructor type; Base’s own lexical
  `#prop` does not upgrade the diagnostic to TS18013) and instance `this.#static`
  reads. Cleared XPASS: `privateNameStaticAccessorssDerivedClasses.ts`,
  `privateNameStaticFieldAccess.ts`. Regression: `tests/private_name_access.rs`
  (`static_private_accessor_on_typeof_derived_is_ts2339`, own-access negative
  control, `static_private_field_via_instance_this_is_ts2339`).
- Follow-on (same day): **`Function.prototype` on bare callables** — `member_type`
  / `callable_prop_type` / `type_has_prop` expose `prototype: any` on
  `TypeKind::Callable` (lib.es5 `Function.prototype`), so `A.prototype.#no` is
  any-like → TS18016 only (no rust_extra TS2339 on `prototype`). Cleared XPASS:
  `privateNameBadAssignment.ts`. Regression:
  `function_prototype_private_access_is_ts18016_not_ts2339_on_prototype` in
  `tests/private_name_illegal_decl.rs`.
- Follow-on (same day): **checkJs CommonJS ambient gating** — seed
  `require`/`module`/`exports` only when
  `js_ast_has_commonjs_module_indicator` (tsc binder
  `commonJsModuleIndicator`); private `exports.#nope` leaves `exports`
  unresolved → TS2304 + TS18016. Cleared XPASS:
  `privateNameJsBadAssignment.ts` (exact vs tsc). Regression:
  `check_js_commonjs_globals.rs` +
  `checkjs_exports_private_access_is_ts2304_and_ts18016` in
  `tests/private_name_illegal_decl.rs`.
- Follow-on (same day): **private-name uniqueness** — TS2804 (static/instance
  same `#name`) and TS2300 (same-side duplicates, with binder-style dual
  report for method/accessor conflicts; getter+setter allowed). Private `#`
  members are branded `Accessibility::Private` + declaring-class `DefId` so
  cross-class assignability emits TS2322. Cleared XPASS:
  `privateNamesUnique-{1,3,5}.ts`. Follow-on (same day): **TS2741 / TS2739**
  when assignability fails due to missing required properties (tsc
  `reportUnmatchedProperty`); same-`#name` cross-class brands stay TS2322.
  Cleared XPASS: `privateNamesUnique-4.ts`. Follow-on (same day):
  **`privateNamesUnique-2`** — `import("./b").Foo` resolves to the type-side
  class DefId (instance brand with `#x`) so `other.#x` is TS18013; VALUE
  exports remap through synthetic `value_defs` so `new A()` / `new B()` stay
  constructable (no rust_extra TC2000). Cleared XPASS:
  `privateNamesUnique-2.ts`. Regression: `tests/private_name_uniqueness.rs`
  (`cross_file_import_type_private_access_is_ts18013`, imported-class
  constructability).
- Follow-on (same day): **TS2393 / TS2717 on class members** — duplicate
  method implementations (TS2393 on the whole overload group when ≥2 bodies)
  and subsequent field type identity vs the first same-name value declaration
  (TS2717; method then field with `() => void` vs `string`). Cleared XPASS:
  `privateNameDuplicateField.ts` (45×TS2300 + 32×TS2804 + 4×TS2393 + 2×TS2717).
  Regression: `tests/private_name_uniqueness.rs` (method dual-impl / method→field).
- Follow-on (same day): **`#x in obj`** (tsc `checkInExpression` /
  `narrowTypeByPrivateIdentifierInInExpression`) — lexical `#priv` on the
  LHS of `in` (no false TS2304); undeclared → TS2339; outside class →
  TS18016; parenthesized `(#priv)` → TS1451; RHS `unknown` → TS2571;
  nullish RHS → TS18047/TS18048 (flow-aware for bare idents after CFA);
  `for (#priv in …)` → TS2406; boolean for-in RHS → TS2407. CFA narrows
  `#priv in x` to the declaring class type (instance vs `typeof` for
  static).   Parser: `as`/`satisfies` precedence sits between `in` and
  equality so `#f in v as any` is `(#f in v) as any`. Cleared XPASS:
  `privateNameInInExpression.ts`, `privateNameInInExpressionUnused.ts`.
  Regression: `tests/private_name_in.rs`.
- Follow-on (2026-07-26): **`privateNameInInExpressionTransform`** — assign-to-`in`
  is a parse-js gap (Pratt formed `(… in …) = …` → PS0003). Fix: stop before
  assignment when the left is not a LeftHandSideExpression (tsc
  `parseAssignmentExpressionOrHigher`); soft-report `';' expected` (PS0013→TS1005)
  on `=` and skip it so the RHS becomes the next statement. Soft errors surface
  via `parse_with_options_*_detailed` so typechecking continues. Checker: `in`
  LHS ↛ `string|number|symbol` and RHS ↛ `object` (TS2322); shift ops widen to
  `number`; bare `#priv` uses TS1451/TS18016 (not TS2304); grammar diags
  suppressed when the file has parse errors (tsc `grammarErrorOnNode`). Cleared
  XPASS: `privateNameInInExpressionTransform.ts`. Regression:
  `tests/private_name_in.rs` (assign-to-`in`, prec TS2322, transform exact codes).
- Follow-on (2026-07-26): **`privateNameNestedMethodAccess`** — named
  class-expression self-name (`return class D { … new D() … }`) seeded into
  nested member body bindings via value-side ctor type (`value_defs` /
  same-span constructable); any-like receiver with no lexical private inside a
  class is TS2339 (tsc `reportNonexistentProperty`), not silent. Exact-match
  TS18014 + TS2339. Cleared XPASS: `privateNameNestedMethodAccess.ts`.
  Regression: `tests/private_name_access.rs` (nested method access / named
  class-expr self-name / any `#unknown`).
- Follow-on (2026-07-26): **template / tagged-template TS2349** —
  `AstExpr::LitTemplate` / `TaggedTemplate` fell through to `unknown` in
  `check_expr`, so `` `x`(…) `` and `` `tag` `body` `` skipped not-callable
  (resolve treats `unknown` as silently callable). Fix: type no-substitution
  templates as string literals and others as `string` (check substitutions);
  check tagged-template tags for call signatures; empty-candidate call
  diagnostics use the **callee** span (tsc TS2349). Cleared XPASS:
  `templateStringInCallExpression{,ES6}.ts`,
  `templateStringInTaggedTemplate{,ES6}.ts`,
  `taggedTemplateWithConstructableTag01.ts`. Follow-ons: `in` RHS assignability
  skips fresh-literal excess props; `var` hoist seed before initializer so
  `` var x = `a${x}` `` does not false-TS2304. Residual (pre-follow-on):
  template-in-object-literal / property-name fixtures still mix parse errors
  with 2349. Regression: `tests/template_not_callable.rs`.
- Follow-on (2026-07-26): **tagged-template DA + TemplateStringsArray packing** —
  HIR flow skipped `TaggedTemplate` children (`unknown`), so unassigned tags
  missed TS2454; AST path now packs `(TemplateStringsArray, …substitutions)`,
  resolves overloads, and emits first-rest TS2345 only (tsc). Exact match:
  `taggedTemplateWithConstructableTag02` (TS2349+TS2454),
  `taggedTemplateStringsWithTypedTags{,ES6}`,
  `taggedTemplateStringsWithIncompatibleTypedTags{,ES6}`. Cleared XPASS: **+5**.
  Residual (pre-follow-on): typed-tag inference / TS2403; template-in-object-literal /
  property-name + parse mixes.
  Regression: `tests/template_not_callable.rs` (constructable+DA; packing TS2345).
- Follow-on (2026-07-26): **tagged-template type-arg inference + TS2403** —
  covariant lower-bound combine: first-wins when candidates have no common
  supertype (`""` vs `0` vs `[]` → T=`""` + TS2345); `any` among lowers wins
  (`7`/`any`/`4` → `any`); nullish/object-like still union. Void-expected
  returns skip assignability (no false TS2322 on `() => null` into
  `(x: U) => void`). Enclosing naked type-param returns reject non-`any`
  (TS2322 on `return null` / `return` span). `var` redeclarations emit
  **TS2403** when a later declarator mismatches a type established earlier in
  the same body check. Exact match vs tsc. Cleared XPASS: **+2**
  (`taggedTemplateStringsTypeArgumentInference{,ES6}`). Residual:
  template-in-object-literal / property-name + parse mixes; plain
  `typeArgumentInference.ts` still carries broader call/inference extras.
  Regression: `tests/template_not_callable.rs` (shared-`T` inference + TS2403).
- Follow-on (2026-07-26): **private-name placement grammar** — pure
  `rust_missing` cluster for illegal `#` positions that tsc reports from
  parser/binder/grammar (parse-js recovers; checker emits). Codes: **TS18009**
  (params), **TS18012** (`#constructor`), **TS18024** (enum members),
  **TS18028** (`target` below ES2015), **TS18029** (variable bindings),
  **TS18030** (`?.#x`, before TS2339). Exact match vs tsc. Cleared XPASS:
  `privateNameNotAllowedOutsideClass.ts`,
  `privateNamesNotAllowedInVariableDeclarations.ts`,
  `privateNamesNotAllowedAsParameters.ts`,
  `privateNameConstructorReserved.ts`, `privateNameEnum.ts`,
  `privateNameES5Ban.ts`, `privateNameUncheckedJsOptionalChain.ts`.
  Regression: `tests/private_name_grammar.rs`.
- Follow-on (2026-07-26): **private-name residual burn-down** — nested `class`
  Decl value binding (skip when top-level interned type already seeded);
  undeclared `#` / static-not-inherited / `keyof` exclusion already matching;
  `this` before `super()` → **TS2376**+**TS17009** (TS2376 suppressed under
  native class fields). Exact match vs tsc. Cleared XPASS: **+7**
  (`privateNameImplicitDeclaration.ts`, `privateNamesConstructorChain-1.ts`,
  `privateNamesInNestedClasses-{1,2}.ts`, `privateNameBadSuper.ts`,
  `privateNameBadSuperUseDefineForClassFields.ts`, `privateNamesAndkeyof.ts`).
  Residual cleared follow-on: `privateNameDeclarationMerging.ts`. Regressions:
  `tests/private_name_super.rs`, `tests/private_name_implicit_js.rs`,
  nested/keyof/ctor-chain cases in `tests/private_name_access.rs`.
- Follow-on (2026-07-26): **`privateNameDeclarationMerging`** — class+interface
  merge (`interface C { new (): D }`) must not make uncontextualized `new C()`
  return `D`. Fixes: prefer `class` over `interface` in TYPE flat-defs /
  `def_priority`; do not let TYPE-only decls clobber class VALUE bindings /
  exports; move interface construct sigs from instance TYPE onto synthetic
  VALUE ctor; construct-signature collection dedupes by param shape **and**
  return type (preserving declaration order). Exact vs tsc. Cleared XPASS:
  `privateNameDeclarationMerging.ts`. Regression:
  `tests/private_name_access.rs`
  (`private_name_declaration_merging_new_returns_class_instance`).
- Follow-on (2026-07-26): **private-name modifiers / AndAny / ambient NIA** —
  `checkGrammarModifiers` for `#` members: **TS18010** (accessibility),
  **TS18019** (`declare`/`abstract` on fields), **TS1031** (`declare` on
  methods/accessors), **TS1024** (`readonly` on methods/accessors),
  **TS1042** (`async` get/set); primary spans on the modifier keyword.
  checkJs: JSDoc `@public`/`@private`/`@protected` → TS18010 with tsc span
  `@tag`…closing `*/`. Getter→setter param contextual typing (paired
  accessor return) clears false TC3000 on unannotated setter params.
  `unknown` receivers: **TS18046** then lexical/undeclared TS2339; `never`
  always TS2339. Ambient class `#` fields seed `any` (no diag); concrete
  unannotated fields emit **TS7008** (not TC3000). Exact vs tsc. Cleared
  XPASS: `privateNameAndAny.ts`, `privateNameAmbientNoImplicitAny.ts`,
  `privateNamesIncompatibleModifiers.ts`,
  `privateNamesIncompatibleModifiersJs.ts`. Residual privateNames xfails:
  **15**. Regressions: `tests/private_name_and_any.rs`,
  `tests/private_name_ambient_nia.rs`, `tests/private_name_modifiers.rs`.
- Follow-on (2026-07-26): **TS7022 circular field initializers** — while
  typing a field initializer, a resolution stack of `(class, prop)` detects
  self-refs (`["#bar"] = this["#bar"]`) and mutual cycles (`#foo`/`#bar`);
  emits **TS7022** with tsc display names / key spans and recovers `any`
  (clears TS7008 + TS2571 noise). Sibling-field inference temporarily
  switches `class_field_initializer` so TS2729 uses the correct member
  index. Exact vs tsc. Cleared XPASS: `privateNameAndIndexSignature.ts`,
  `privateNameCircularReference.ts`. Residual privateNames xfails: **13**.
  Regression: `tests/private_name_circular_init.rs`.
- Follow-on (2026-07-28): **re-entrant cycle guard** — the `type_of_def`
  cycle guard no longer *inserts* `any` into `interned_def_types` when the
  def is already on the resolution stack. Genuine self-cycles land the same
  `any` at completion anyway, while re-entrant lookups during in-flight
  resolution (`import Alias = N.x` resolving `N.x` while `x`'s initializer is
  being checked) no longer poison the completion's replace check — namespace
  member props keep their real types. Regression: `tests/import_equals.rs`.
- Follow-on (2026-07-28): **qualified `typeof` member chains** —
  `typeof window.document.title` (a value member chain, not a namespace path)
  lowers to nested `IndexedAccess` over the head value's type instead of
  resolving the last segment as a top-level name (which manufactured
  self-references). Regression: `tests/typeof_queries.rs`.
- Follow-on (2026-07-26): **ctor-sig / TS1029 / getClass / contextual init** —
  Merged class+interface keeps construct sigs on the TYPE instance and syncs
  VALUE ctor returns; Construct overload allows `new` on all-void call-only
  callables (else **TS2350**); class field inits check against annotations;
  `async static` parse recovery + **TS1029**; Initializer body var matching
  uses HIR pattern span (avoids nested `this.#priv` false TS2571/TS18016);
  post-refine rewrites stale `return Class` constructor snapshots. Exact vs
  tsc. Cleared XPASS: `privateNameConstructorSignature.ts`,
  `privateNameStaticMethodAsync.ts`, `privateNameStaticMethodCallExpression.ts`,
  `privateNamesAssertion.ts`. Residual privateNames xfails: **9**. Regression:
  `tests/private_name_residual_probe.rs`.
- Follow-on (2026-07-26): **bare `#` TS1127 + object-rest TS2339** — Lexer keeps
  bare `#` as `PrivateMember`; parse recovery soft-emits **PS0030** (harness ↔
  **TS1127**) per occurrence. Object-binding `...rest` builds a non-nominal
  public-only shape (drops `#` members / class origin) so `rest.#prop` is
  **TS2339** like `{ ...obj }.#prop`. Exact vs tsc. Cleared XPASS:
  `privateNameHashCharName.ts`, `privateNameAndObjectRestSpread.ts`. Residual
  privateNames xfails: **7**. Regression: `tests/private_name_hash_rest.rs`.
- Follow-on (2026-07-26): **computed-key / useDefine brands / ctor-chain** —
  Class-body non-field exprs set `enclosing_class_index` (nested `[obj.#name]`);
  duplicate `class Inner` brands prefer lexical homonyms; heritage
  `Parent<T>` Instantiation + class type-param scope for class-body
  Instantiation. Exact vs tsc. Cleared XPASS:
  `privateNameComputedPropertyName3.ts`,
  `privateNameWhenNotUseDefineForClassFieldsInEsNext.ts`,
  `privateNamesConstructorChain-2.ts`. Residual privateNames xfails: **4**.
  Regression: `tests/private_name_residual_next.rs`.
- Follow-on (2026-07-30): **JSDoc `@this {…}` honored** (tsc
  `jsdoc/inferThis.ts`) — an explicit `@this` tag wins over the class-derived
  `this` type inside the annotated function's body; `@template T` +
  `@this {T}` + `@return {T}` checks `return this;` against `T` instead of
  false-TS2322 on the class instance/static type. Regression:
  `tests/jsdoc_this_tag.rs`.
- Follow-on (2026-07-30): **super call expressions type as `void`** (tsc
  `superCalls.ts`) — `check_call_expr` short-circuits `super(...)` to `void`
  after checking argument expressions for their own diagnostics; redeclaring
  `var p = super(''); var p = v();` no longer false-fires TS2403. Regression:
  `tests/super_call_void.rs`.
- Follow-on (2026-07-30): **shadowed private-identifier *fields* resolve
  lexically** (`privateNamesAndFields.ts`, `privateNameComputedPropertyName4.ts`)
  — a derived class redeclaring `#foo` has *two* slots (tsc keys private names
  by declaring class): `member_type` on a `#`-prop now resolves to the nearest
  enclosing class declaring the name and types the access from that field's
  declaration, gated on *actual* shadowing (an ancestor also declares the
  name) so unshadowed statics keep the structurally refined type
  (`privateNameStaticFieldCallExpression.ts` stays clean). Companion fixes in
  `types-ts-interned`: the intersection `never`-collapse skips `#` keys with
  different brands (`B & A` stays inhabited), and the merged apparent shape
  keeps *both* private slots (`intern_shape` no longer intersects
  differently-branded `#` props) with a brand-aware lookup in relate
  (`find_private_ident_property`), so `B & A → A` holds via tsc's
  merged-apparent rule (no per-constituent fallback — tsc rejects
  `{} & {id: number}` → `{id?: string}`). Methods/accessors keep structural
  (overload-set) resolution. Regression:
  `tests/private_name_shadow_fields.rs`.
- Follow-on (2026-07-30): **template literals normalize CR/CRLF to LF**
  (ECMA-262 §12.9.6) — the cooked-value decoder kept source line terminators
  as-is, so a CRLF inside a template mismatched a `"…\n…"` string-literal
  annotation (`stringLiteralTypesWithTemplateStrings01.ts`). Regression:
  `tests/template_crlf_normalization.rs`.
- Follow-on (2026-07-30): **interface-extends generic nominal rule** (tsc
  `callSignatureAssignabilityInInheritance6.ts`, 0/7 → 7/7) — an interface
  type parameter is nominal to its container and never unifies with a
  *method's* type parameter; a concrete member mentioning the interface's
  `T` cannot satisfy a generic base signature ("two different types with this
  name exist"). Regression: `tests/interface_extends_generic.rs`.
- Follow-on (2026-07-30): **`new` on error-recovery-return callables is
  void-compatible** (tsc `privateNameAccessorsCallExpression.ts`) — the
  TS2350 void-check treats `unknown`/`any` returns as void-compatible (tsc is
  silent there under default options); concrete non-void returns still flag.
  Regression: `tests/new_void_compat.rs`.
- Follow-on (2026-07-30): **interface overload merging** (tsc
  `twoMergedInterfacesWithDifferingOverloads.ts`) — same-name methods across
  merged interface declarations form one overload set (later declaration's
  signatures first, tsc precedence); merged generic interfaces unify type
  parameters positionally (TS2428). Regression:
  `tests/interface_overload_merge.rs`.
- Follow-on (2026-07-30): **namespace members writable unless `const`** (tsc
  `exportAssignmentMergedModule.ts`) — namespace/module object builders no
  longer blanket `readonly: true`; `var`/`let`/function members are writable,
  only `const` is TS2540. Regression: `tests/namespace_member_writable.rs`.
- Follow-on (2026-07-30): **namespace-aware local def resolution** (tsc
  `es2018IntlAPIs.ts`) — `interface X` and `var X: T` inside `declare
  namespace N` collided in the HIR lowerer's flat name→def local index, so
  type references to `X` inside the namespace bound to the *var* (its
  annotation), typing `new N.X()` as the constructor instead of the instance.
  The local index is now namespace-slotted (`LocalDefIndex`), falling back
  across namespaces only when the requested one is empty. Regression:
  `tests/namespace_interface_var_merge.rs`.
- Follow-on (2026-07-30): **tsc erases `readonly` for property
  assignability** — removed the relate prop-level readonly-source rejection
  (initial-engine rule, wrong per tsc); `as const` objects assign to writable
  targets again. Regression: `tests/readonly_prop_assignability.rs`.
- Follow-on (2026-07-30): **destructuring-assignment typing** (tsc
  `privateNameStaticFieldDestructuredBinding.ts`) — destructuring defaults
  replace a missing/`undefined` slot with the default's type (no more
  `union(unknown, T)` absorbing to `unknown`); array literals in destructuring
  positions infer tuples (positional binding); and private-identifier
  accesses on `this.<unannotated field>` receivers recover from the field
  initializer before flagging TS2571. Regression:
  `tests/private_name_destructuring.rs`.
- Follow-on (2026-07-30): **overload sets preserve declaration order**
  (`typesWithSpecializedCallSignatures.ts`) — duplicate same-name method
  props merge by concatenating overload lists in `intern_shape` (the
  intersection canonicalizer's `TypeId` sort scrambled the order, so
  `c.foo('hi')` could pick `(string) => Base` over `('hi') => Derived1` and
  false-TS2741). Regression: `tests/overload_declaration_order.rs`.
- Follow-on (2026-07-30): **type-assertion overlap uses tsc's *comparable*
  relation** (`optionalProperties01.ts`) — `{required1, optional} as Foo`
  (Foo has `required2` + `optional?`) is legal because comparability relaxes
  the strictNullChecks optionality gate (new `COMPARABLE_OPTIONALITY` relate
  mode; raw property types compared). Genuine non-overlaps still TS2352.
  Regression: `tests/assertion_comparable_overlap.rs`.

Cornerstone litmus (started 2026-07-24; widened 2026-07-25):
- Unit/litmus: `tests/litmus/cornerstone_{const_satisfies,excess_props,cfa_narrowing,distributive_conditionals,keyof_mapped,overload_resolution}/`
- difftsc suite: `typecheck-ts-harness/fixtures/cornerstones/` (theory list in
  [compiler-theory](../theory/compiler-theory.md#the-typescript-cornerstones)).
  All six cornerstones green vs tsc baselines (overload graduated 2026-07-25:
  TS2769 on argument span; CFA graduated 2026-07-25: `typeofNarrow` return
  `number | string` via primitive→`String`/`Number` interface member lookup
  after narrowing; excess_props graduated 2026-07-25: TS2353 on property key
  span; `const_satisfies` graduated 2026-07-25: `satisfies` TS2322 primary
  span on object-literal property key via `check_assignable`). No remaining
  cornerstone difftsc xfails.

Identified but **not** fixed (honest remaining-gap inventory):
- **TS2454 remainder** — still open outside this slice:
  - forward/self-ref destructuring defaults still report TS2454 where tsc prefers
    TS2448 (`destructuringArrayBindingPatternAndAssignment3.ts`)
  - conditional / mapped alias DA (structural walk does not expand those kinds)
  - abstract-class ctor object-binding spans (±2 vs tsc on `"y"` elements)
- **TS2564 / class-`this` residuals** — computed property names; full CFA parity
  for loops/switches; definite-assignment assertion grammar (`prop!`) diagnostics
  beyond exemption;
  ~~unannotated static fields in static blocks rust_extra TC3000~~ (cleared
  2026-07-25; UseBeforeDef3 FOO TDZ residual remains)
- **TS2540 residuals** — JSDoc `@readonly` (`jsdocReadonly.ts`); readonly array /
  tuple element assigns (TS2542 cluster); `as const` / assertion fixtures that
  still bundle TS2540 with other missing codes
- **Private-name residuals (post-TS18013 / post-TS18016-access /
  post-class-expression / post-delete / post-undeclared-TS2339 /
  post-uniqueness / post-Function.prototype / post-nested-shadowing /
  post-static-derived-TS2339 / post-nested-method-access)** — still open in
  `classes/members/privateNames/`:
  ~~nested shadowing `rust_extra` TC2008~~ (cleared 2026-07-26; seed nested
  `class`/`enum`/`interface`/`type` Decl names into body `binding_defs` in both
  `ProgramState::check_body` and salsa `compute_body`; skip nested classes in
  TopLevel TS2717 subsequent-property signature lowering; +3 XPASS:
  `privateNameNestedClass{Method,Field,Accessors}Shadowing`);
  ~~`Function.prototype` on `A.prototype.#…`~~ (cleared 2026-07-25;
  `privateNameBadAssignment` XPASS);
  ~~checkJs CommonJS `exports` ambient over-seed~~ (cleared 2026-07-25;
  `privateNameJsBadAssignment` XPASS; gated on `commonJsModuleIndicator`);
  ~~derived static-accessor / static-on-instance TS2339~~ (cleared 2026-07-26;
  +2 XPASS: `privateNameStaticAccessorssDerivedClasses`,
  `privateNameStaticFieldAccess`);
  ~~nested method access~~ (cleared 2026-07-26; named class-expr self-name
  binding + any-like undeclared `#` → TS2339; +1 XPASS:
  `privateNameNestedMethodAccess`);
  ~~`#x in` transform / assign-to-`in`~~ (cleared 2026-07-26; non-LHS assign
  recovery + `in` assignability; +1 XPASS:
  `privateNameInInExpressionTransform`);
  ~~private-name placement grammar~~ (cleared 2026-07-26; TS18009 params,
  TS18012 `#constructor`, TS18024 enum members, TS18028 ES5 target,
  TS18029 var bindings, TS18030 optional-chain `#` — takes precedence over
  TS2339; +7 XPASS: `privateNameNotAllowedOutsideClass`,
  `privateNamesNotAllowedInVariableDeclarations`,
  `privateNamesNotAllowedAsParameters`, `privateNameConstructorReserved`,
  `privateNameEnum`, `privateNameES5Ban`,
  `privateNameUncheckedJsOptionalChain`; regression:
  `tests/private_name_grammar.rs`);
  ~~pure missing TS2339 / nested TS18014 TC3000 noise / BadSuper~~ (cleared
  2026-07-26; nested `class` Decl value binding without overwriting top-level
  interned class types; `this` before `super()` → TS2376+TS17009, TS2376
  suppressed under native class fields; +7 XPASS:
  `privateNameImplicitDeclaration`, `privateNamesConstructorChain-1`,
  `privateNamesInNestedClasses-{1,2}`, `privateNameBadSuper`,
  `privateNameBadSuperUseDefineForClassFields`, `privateNamesAndkeyof`;
  regressions: `tests/private_name_super.rs`,
  `tests/private_name_implicit_js.rs`, nested/keyof/ctor-chain cases in
  `tests/private_name_access.rs`).
  ~~`privateNameDeclarationMerging` extra TS2339~~ (cleared 2026-07-26;
  class-preferred TYPE merge + VALUE binding + construct-sig return-aware
  dedup; +1 XPASS: `privateNameDeclarationMerging`; regression:
  `private_name_declaration_merging_new_returns_class_instance` in
  `tests/private_name_access.rs`).
  ~~TS2554 arity / unannotated `#` field assign / static-private unmatched~~
  (cleared 2026-07-26; single-sig arity miss → **TS2554** on callee name;
  ClassInfo initializer widening when shape still has `unknown`;
  `getUnmatchedProperties`-style skip of `#` keys on constructable types;
  +4 XPASS: `privateNameMethod`, `privateNameStaticMethod`,
  `privateNameFieldsESNext`, `privateNamesAndStaticFields`; regression:
  `tests/private_name_call_arity.rs`).
  ~~`privateNameClassExpressionLoop` empty-`[]` → `never[]`~~ (cleared
  2026-07-26; bare `[]` synthesizes `never[]` under `strictNullChecks` so
  `push` is **TS2345**; named class-expression arg spans use the name
  (`getErrorSpanForNode`); `--noImplicitAny` empty-array bindings use
  `autoArrayType` (`any[]`) for push; +1 XPASS:
  `privateNameClassExpressionLoop`; regression:
  `tests/empty_array_literal.rs`).
  ~~bare `#` TS1127 / object-rest `#` TS2339~~ (cleared 2026-07-26; +2 XPASS:
  `privateNameHashCharName`, `privateNameAndObjectRestSpread`; regression:
  `tests/private_name_hash_rest.rs`).
  ~~computed-key / useDefine brands / ctor-chain~~ (cleared 2026-07-26; +3
  XPASS: `privateNameComputedPropertyName3`,
  `privateNameWhenNotUseDefineForClassFieldsInEsNext`,
  `privateNamesConstructorChain-2`; regression:
  `tests/private_name_residual_next.rs`).
  ~~class-`T` member-ann **TC2008**~~ (cleared 2026-07-26; class type-param
  scope on subsequent-property / SPI / HIR `declared_type` + value function
  signatures).
  ~~generic dual-instantiation / construct~~ (cleared 2026-07-26; +2 XPASS:
  `privateNamesAndGenericClasses-2`, `privateNamesInGenericClasses` — do not
  cache SkipSelf deferred refs; default invariant type-args for same-def
  unannotated generics; keep declared binding on failed assign; widen naked
  literal inferences for non-`const` type params so `new C(3)` → `C<number>`).
  ~~last parse residuals~~ (cleared 2026-07-26; +2 XPASS:
  `privateNameComputedPropertyName2`, `privateNamesAndIndexedAccess` —
  nested-arrow `arrow_parse_committed` save/restore; `C[#bar]` array soft
  **PS0013** + declarator **PS0031**↔**TS1134**; `C["#bar"]` **TS2339**;
  grammar suppress **TS18029** when file has parse errors). Residual
  privateNames xfails: **0**. Regression:
  `tests/private_name_residual_next.rs` + parse-js
  `tests/regressions/private_name_parse_recovery.rs`.
- **Shard-2 RSS / cancel gap (fixed 2026-07-23):** case
  `parser/ecmascript5/parserRealSource12.ts` grew past ~20 GB and ignored
  per-case timeouts. Mechanism: recursive `evaluate_object` / shape interning
  into a shared `TypeStore` without observing cancel, with relation step tracking
  off (`usize::MAX`). Fix: plumb `should_stop` into relate/eval; finite step
  budgets (50k) + per-body type-growth cap (5k) → `TC4000`; CFA flow step budget;
  evaluator object-walk guard for empty/typeparam-only subst; `TypeId`
  composite sort. Regressions: `tests/engine_budget.rs`. Shard 2 now completes
  under `--timeout-secs 20` (~22s, ~516 MB peak). Details:
  `reports/shard2-pathology-handoff.md`.
- **Parser error-recovery** (`PS0002`/`PS0013`) — several `rust_extra`/`missing`
  cases (template-in-module-name, using-as-identifier, index signatures) trace
  into `parse-js` (out of scope for this program).
- **TS2349 / tagged-template residuals (post-packing / post-inference)** —
  ~~`` `x`(…) `` / string-as-tag / constructable-only tag~~ (cleared 2026-07-26;
  +5 XPASS); ~~constructableTag02 DA + typed/incompatible TemplateStringsArray
  packing~~ (cleared 2026-07-26; +5 XPASS); ~~type-arg inference + TS2403~~
  (cleared 2026-07-26; +2 XPASS:
  `taggedTemplateStringsTypeArgumentInference{,ES6}`). Still open:
  template-in-object-literal / property-name fixtures mixing 2349 with parse
  errors.
- Follow-on (2026-07-26): **never-intersection reduction** — `TypeStore::intersection`
  collapses object intersections when a shared **required** property's types
  reduce to `never` (tsc `getIntersectionType`; optional-only conflicts stay
  `{ a?: never }`). Call sites expand alias/interface intersection members via
  `expand_callable_type` before re-intersecting; property access on `never` is
  **TS2339**. Cleared XPASS: **+2** (`neverIntersectionNotCallable.ts`,
  `commonTypeIntersection.ts`).
- Follow-on (2026-07-26): **write-indexed-access + `any` ↛ `never`** — computed
  assignment uses tsc write distribution (`T[A|B]` → `T[A] & T[B]`; may be
  `never`); relate checks `never` before `any` so `as any` into a `never` write
  target is **TS2322**. Cleared XPASS: **+2** (`intersectionReduction{,Strict}`;
  exact vs tsc: TS2339 + two TS2322 on `x1[k]`/`x2[k]`). Regressions:
  `tests/never_intersection.rs`, `types-ts-interned` relate `any`↛`never`.
- Follow-on (2026-07-26, post-privateNames): **naked `T | Concrete` inference** —
  tsc `inferFromTypes` unmatched-constituent path: infer `T` from source arms
  not assignable to non-naked union targets (`number | string | boolean` →
  `T | string` yields `T = number | boolean`). Clears false **TS2345** on
  `unionAndIntersectionInference2`. Regression:
  `tests/union_naked_param_inference.rs`.
- Follow-on (2026-07-26): **AST typeof binding overrides + enum Ref typeof** —
  AST `if` applies typeof narrow to bindings (HIR CFA merges too late for
  TS2403); `matches_typeof` expands `Ref` for classification only so numeric
  enums match `"number"` while keeping the enum ref in the yes set. Clears
  `TypeGuardWithEnumUnion`. Regression: `tests/typeof_enum_narrow.rs`.
- Follow-on (2026-07-26): **call-sig rest / optional / generic-arrow refine** —
  (1) dst rest absorbs higher src required arity; refine builds actual
  annotated params (not a clone of expected); successful assigns do not
  narrow function-like bindings (call/construct **or** methodful object
  types). (2) `refine_function_expr_with_expected` pushes type-param scope so
  `<T>(x: T) => 1` into interface `T` does not resolve the annotation to the
  interface. +4 XPASS:
  `assignmentCompatWithCallSignatures{,2,WithOptionalParameters,WithRestParameters}`.
  Regression: `tests/rest_call_sig_assign.rs`.
- Follow-on (2026-07-26): **`…CallSignatures3` exact** — (1) default `out`
  variance on lib containers (`Array`, `ReadonlyArray`, `Promise`, …) so
  `Array<Derived> <: Array<Base>`; (2) empty-subst signature eval leaves named
  `Ref`s opaque (Array method graphs no longer blow normalize / **TC4000**);
  (3) CSI generic→non-generic; (4) overload-set → unconstrained generic
  (keeps single-sig `b = a` as **TS2322**). +1 XPASS
  `assignmentCompatWithCallSignatures3`. Manifest **3718 → 3717**.
- Follow-on (2026-07-26): **`…CallSignatures{4,5,6}` exact** — (1) different-
  arity: instantiate source only (no dest-flip); constraint-subst for
  `a6`/`b6`; (2) `STRICT_TYPE_PARAMS` on generic↔generic signature compares
  (`string[]` ≰ `T[]`); (3) CSI clamps return inferences that are supertypes
  of `T extends C` (`a12 = b12`); (4) salsa body-check seeds namespace-nested
  class/enum value bindings for heritage; per-namespace `established_var`
  scopes kill false **TS2403**. +3 XPASS. Manifest **3717 → 3714**.
  Regression: `tests/rest_call_sig_assign.rs`.
- Follow-on (2026-07-26): **`…ConstructSignatures{3..6}` exact** — (1)
  `TypeExprKind::Constructor` / AST `ConstructorType` lower to object
  **construct** signatures (were wrongly `Callable` call sigs); (2) object
  construct relating reuses `relate_callable` CSI/overload rules; (3) strict
  (non-bivariant) params for construct compares. +4 XPASS. Manifest
  **3714 → 3710**. Regression: `tests/rest_call_sig_assign.rs`.
- Follow-on (2026-07-26): **TS2430 interface `extends`** — post-pass over
  interned interface types extracts the own-only object constituent of
  `Own & Base…` and relates each own property to the corresponding base
  member; primary span is the derived interface name. Exact XPASS:
  `callSignatureAssignabilityInInheritance{,3,6}`,
  `constructSignatureAssignabilityInInheritance{3,6}`. Manifest
  **3709 → 3704**. Regression: `tests/interface_extends_assign.rs`.
- Follow-on (2026-07-26): **`GenericCallSignatures4` exact** — equal-arity
  generic constraint checks bind source→dest type params first, then allow
  one-level expansion of destination type params to their constraints so
  recursive `T extends I2<T>` satisfies `I2<I2<T>>`. Exact XPASS:
  `assignmentCompatWithGenericCallSignatures4`. Manifest **3704 → 3703**.
  Regression: `tests/rest_call_sig_assign.rs`.
- Follow-on (2026-07-26): **nested namespace `var x: I` TC2008** — interface/
  alias defs register AST `node` in `node_to_def` and lower to
  `StmtKind::Decl` so `seed_type_decls_*` sees them inside namespace blocks.
  Exact XPASS: `constructSignatureAssignabilityInInheritance`. Manifest
  **3703 → 3702**. Regressions: `hir-js/tests/interface_stmt_decl.rs`,
  `tests/nested_iface_var_ann.rs`.
- Follow-on (2026-07-27): **`ObjectMembers5` TS2741** — AST `check_assignment`
  / assign-target pattern sites use `assignability_mismatch_code` so a single
  missing required property becomes **TS2741** (tsc `reportUnmatchedProperty`)
  rather than bare **TS2322**. Exact XPASS:
  `assignmentCompatWithObjectMembers5`. Manifest **3702 → 3701**. Regression:
  `tests/object_members5_codes.rs`.
- Follow-on (2026-07-27): **`GenericCallSignatures` expand-to-constraints** —
  equal-arity generic signature relating falls back to substituting each type
  param with its constraint when identity mapping fails, covering
  array-constraint vs `T[]` param shapes both ways. Exact XPASS:
  `assignmentCompatWithGenericCallSignatures`; also pruned already-exact
  `assignmentCompatWithConstructSignaturesWithOptionalParameters`. Manifest
  **3701 → 3699**. Regression: `tests/rest_call_sig_assign.rs`.
- Follow-on (2026-07-27): **`EnumIndexer` enum literal unions** — HIR
  `EnumMemberValue` stores numeric/string constants (auto-increment for bare
  members); `lower_enum_type` builds a literal union so mapped `Record<E, T>`
  requires those keys. Assignability no longer skips mapped destinations.
  Exact XPASS: `assignmentCompatWithEnumIndexer`. Manifest **3699 → 3698**.
  Regressions: `hir-js/tests/types_lowering.rs`, `tests/enum_record_empty.rs`.
- Follow-on (2026-07-27): **`nullAssignedToUndefined` TS2539** — assignment to
  `undefined`/`NaN`/`Infinity` (`IdPat` LHS) reports **TS2539**; `typeof
  undefined` in annotations resolves without TS2304. Exact XPASS:
  `nullAssignedToUndefined`. Manifest **3698 → 3697**. Regression:
  `tests/null_assigned_to_undefined.rs`.
- Follow-on (2026-07-27): **bare `(x) => T` function-type params** — parse-js
  now binds a bare identifier before `,`/`)` as a named param with implicit
  `any` (was wrongly a type ref → TC2008). Exact XPASS:
  `anyAssignableToEveryType2`, `anyAssignabilityInInheritance`. Manifest
  **3697 → 3695**. Regressions: `parse-js/tests/regressions/bare_fn_type_param.rs`,
  `tests/fn_type_param_in_index.rs`.
- Follow-on (2026-07-27): **`optionalPropertyAssignableToStringIndexSignature`**
  — string-index property checks strip optionality (`T` not `T|undefined`);
  numeric indexes keep it; writes validate against `Binding.declared_ty`;
  `undefined!` → `never`; `assignable_special` lets `T <: T|U` fall through to
  union-target rules. Exact XPASS:
  `optionalPropertyAssignableToStringIndexSignature`. Manifest **3695 → 3694**.
  Regressions: `types-ts-interned/tests/relate.rs`,
  `tests/optional_prop_string_index.rs`.
- Follow-on (2026-07-27): **`typeParameterAssignability3`** — nested arrows in
  class field initializers inherit class `this` + class type-param scope so
  unrelated `T`/`U` field assigns are **TS2322**. Also pruned already-exact
  `assignmentCompatBetweenTupleAndArray`. Manifest **3694 → 3692**. Regression:
  `tests/type_param_assignability3.rs`.
- Follow-on (2026-07-27): **`undefinedAssignableToEveryType` /
  `nullAssignableToEveryType`** — under `strictNullChecks`, `null`/`undefined`
  are not assignable to free type parameters; `check_assignable` no longer
  skips annotated `void` destinations (so `var g: void = null` is **TS2322**).
  Exact XPASS for both. Manifest **3692 → 3690**. Regressions:
  `types-ts-interned/tests/relate.rs`, `tests/undefined_assignable_to_type_param.rs`,
  `tests/null_to_void.rs`.
- Follow-on (2026-07-27): **type-param target nominality + assignment flow** —
  `(_, TypeParam) => only any`; annotated non-union bindings keep declared
  flow type after OK assigns; type-param sources expand to constraints when
  not shared with the destination. Exact XPASS: `typeParameterAssignability2`.
  Manifest **3690 → 3689**. Regressions:
  `types-ts-interned/tests/relate.rs`, `tests/numeric_indexer3.rs`.
- Follow-on (2026-07-27): **namespace class shadows outer class** — top-level
  type-decl seeding filters `StmtKind::Block` (namespace bodies) by enclosing
  body span and lets nested decls overwrite file-root same-named types. Exact
  XPASS: `assignmentCompatWithNumericIndexer3`. Manifest **3689 → 3688**.
- Follow-on (2026-07-27): **`enumAssignabilityInInheritance`** — Keep overload
  declaration order through `callable_signatures*` / binding merges; TS2403
  anchors on the first `var` declarator; enum members type as enum `Ref` with
  distinct-enum nominality before relate normalize. Exact XPASS. Manifest
  **3688 → 3687**. Regression: `tests/subsequent_var_enum_overload.rs`.
- Follow-on (2026-07-27): **`enumAssignability`** — bare global `Number` /
  `String` / `Boolean` / `BigInt` / `Symbol` type refs lower to primitives
  (same spirit as `Object` → `{}`), so numeric enums assign to `Number`. Exact
  XPASS. Manifest **3687 → 3686**. Regression: `tests/enum_to_number_object.rs`.
- Follow-on (2026-07-27): **TS2352 assertion overlap** — type assertions report
  **TS2352** when source/target do not overlap (either-direction assignability;
  unions distribute); program diagnostics dedupe by code+span. Exact XPASS:
  `objectTypesIdentityWithNumericIndexers2`,
  `objectTypesIdentityWithStringIndexers2`, `typeAssertionsWithUnionTypes01`.
  Manifest **3686 → 3683**. Regression: `tests/type_assertion_overlap.rs`.
- **privateNames conformance cluster: 0 xfails** (parse recovery + semantic
  burn-down complete 2026-07-26).
