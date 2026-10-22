# hir-js

Deterministic lowering from the `parse-js` AST into a semantic-friendly HIR: stable-ish
IDs for definitions and bodies, per-body expression/pattern/statement arenas, per-def
type arenas, and byte-offset→ID indices. This is the layer that lets everything
downstream (binding, checking, optimizing) traffic in small copyable IDs instead of AST
pointers.

## Entry points

```rust
lower_file(FileId, FileKind, &Node<TopLevel>) -> LowerResult
lower_file_with_diagnostics(...) -> (LowerResult, Vec<Diagnostic>)      // LOWER#### warnings
lower_file_with_diagnostics_with_cancellation(...)
lower_from_source(&str) / lower_from_source_with_kind(FileKind, &str)   // parse+lower convenience
```

`FileKind` = `Js | Jsx | Ts | Tsx | Dts` (maps 1:1 onto parser dialects).

`LowerResult` bundles: `hir: Arc<HirFile>` (items, bodies, imports/exports, `SpanMap`,
`def_paths`), `defs: Vec<DefData>`, `bodies: Vec<Arc<Body>>`, `types: TypeArenasByDef`,
`names: Arc<NameInterner>`, and `def_index`/`body_index` (`BTreeMap` for deterministic
iteration).

## The ID scheme (the crate's core idea)

Detailed doctrine in [determinism](../architecture/determinism.md#mechanisms-by-layer);
the mechanics:

- **`DefId(u64)`** = upper 32 bits `FileId`, lower 32 bits a stable FNV-1a hash of the
  def's **`DefPath`** `{ module, parent: Option<DefId>, kind: DefKind, name: NameId,
  disambiguator }`. Collisions rehash with an incrementing salt; the descriptor list is
  sorted before allocation so salting is deterministic. Packing makes cross-file
  collisions impossible while keeping the local part stable-ish across edits.
- **`BodyId(u64)`** — same construction over `BodyPath { owner: DefId, kind: BodyKind,
  disambiguator }`.
- **`ExprId`/`PatId`/`StmtId`/`LocalId`(u32)** — body-local arena indices; *not*
  stable across edits, cheap and dense — correct for per-body side tables.
  `LocalId` indexes `Body.locals` (`LocalData`: name, kind, span, optional pat /
  param index).
- **`TypeExprId`/`TypeParamId`/`TypeMemberId`(u32)** — local to the owning def's
  `TypeArenas`.
- **`NameId(u64)`** — content-addressed via `NameInterner` (hash of the text), so a
  name's ID never depends on what was interned before it.
- Sentinels `MISSING_DEF`/`MISSING_BODY` (`u64::MAX`) exist for lowering gaps; treat
  any that escapes to a consumer as a bug.
- Test hooks (`with_test_def_path_hasher`) let tests force collisions to exercise the
  salting path — keep that when touching allocation.

**`LocalId` migration (Wave 3)**: params, body vars, and catch bindings live in
`Body.locals` and **do not allocate DefIds**. Checker queries them via
`Program::type_of_local` / body check side tables (`type_at` / `pat_type`).
Module-level and namespace/module member `DefKind::Var` DefIds remain (exports /
`type_of_def`). Module-level `DefId`s stay stable under body-local param/var
edits (tested). Sequenced plan:

1. ~~Scaffold `LocalId` + `Body.locals` + param dual-write~~ (done 2026-07-24)
2. ~~Migrate checker/binder param resolution to `LocalId` (drop `compat_def` reads)~~ (done 2026-07-24)
3. ~~Dual-write body `var`/`let`/`const` + catch bindings~~ (done 2026-07-24; DefIds kept)
4. ~~Stop allocating body-local `DefKind::Param` DefIds; remove param `compat_def`~~ (done 2026-07-24)
5. ~~Stop allocating body-local `DefKind::Var` DefIds; remove `compat_def` entirely; migrate remaining var / `type_of_def` consumers to `LocalId`~~ (done 2026-07-24; `type_of_local` added)
6. Then batch “checker consumes HIR only” ([roadmap](../status/roadmap.md#2-structural-refactors) item 4)

## What lowering does

`lower.rs` (the bulk) normalizes syntax sugar into a smaller, checker-friendly surface:

- Statements/expressions/patterns become arena-allocated `StmtKind`/`ExprKind`/
  `PatKind` with spans, covering the full JS surface (including JSX) plus TS constructs
  the checker needs (`satisfies`, assertions, enums with member-value info
  `EnumMemberValue`, namespaces). Each `Expr` also carries `parenthesized`
  (parse-js `ParenthesizedExpr` assoc) so CFA can distinguish bare `true`/`false`
  from `(true)` for tsc-aligned UnreachableFlow / TS2454 behavior; `NonNull`
  still has its own `operand_parenthesized` for the `(x)!` case.
- Imports/exports become structured `Import`/`Export` records: ES imports (default /
  namespace / named, type-only flags, module attributes), `import =`
  (module-reference or entity-path targets), named/star re-exports with aliases,
  `export default` (expr vs hoisted class/function), `export =`, and
  `export as namespace` — each with spans and `local_def` links where a binding exists.
- `DefData` captures per-definition facts the binder needs: name, path, parent, span,
  decorators, `is_static`, `is_ambient`, `in_global`, `is_exported` (explicit *or*
  implicit via namespace/module membership), `is_default_export`, optional body,
  optional `DefTypeInfo`, and optional `declared_type` (value-side annotation for
  class fields and similar — lives in that def’s `TypeArenas`).
- `lower_types.rs` lowers TS type annotations into per-def `TypeArenas`
  (`TypeExpr`/`TypeMember`/`TypeParam`) — keeping type syntax out of body arenas.
- TS-only constructs that have no runtime meaning are erased or represented as type
  info rather than statements. Instantiation expressions (`expr<T>`) are kept as
  `ExprKind::Instantiation` with `TypeExprId` type args (for the checker); emit /
  optimize treat them as transparent wrappers.

## SpanMap

`span_map.rs` builds per-file indices from `TextRange` to IDs (defs, bodies, exprs,
pats, type exprs) supporting *smallest-covering* queries — the machinery behind
`Program::type_at`/`symbol_at` and harness marker lookups
(`expr_span_at_offset`, etc.). Spans are UTF-8 byte offsets throughout.
Statement spans include the terminating semicolon (ASI'd statements end at the last
token) — matching TypeScript compiler node ranges and `parse-js` `Loc`s.

## Determinism and stability guarantees

Same source text + same `FileId` ⇒ identical IDs, arena layouts, and map iteration
order, regardless of environment. Cross-edit stability is *best-effort by design*
("stable-ish"): a definition's ID survives unrelated edits (it depends only on its
path), but structural edits to the def or its ancestors change it — which is exactly
the invalidation boundary the incremental layer wants.

## Known issues and directions

- `fuzz_lower` (feature `fuzzing`) exists: parse+lower arbitrary text without panic.
  Keep it wired when adding lowering paths.
- LocalId Wave 3 step 5 is done: body-local vars are LocalId-only. Residual:
  top-level/`declare global`/namespace/module vars still allocate `DefKind::Var`
  (+ `VarDeclarator`) for exports/`type_of_def`; `DefKind::Param` enum variant
  remains unused.

### Resolved (2026-07-23): private class-field annotations

Diagnosed from checker TC3000 on `privateNameField.ts` (`#name: string`). The
parse-js AST already carries `ClassMember.type_annotation` for private names
(same path as public fields). Class-level `DefTypeInfo::Class` /
`ClassMemberSig` also already lowered those annotations.

What was missing for value-side consumers: **per-field** `DefData` had no
annotation of its own (`type_info` is type-side only; Field defs are not
`TypeSource`s). The checker’s `declared_type_for_span` also does not walk class
bodies, so `type_of_def` saw `var.typ == None` for both public and private
annotated fields.

**Fix (hir-js):** class fields now populate `DefData.declared_type` + a per-field
`TypeArenas` entry (and SpanMap) from `member.stx.type_annotation` in
`lower.rs` when the source is `DefSource::ClassField` — public and private
alike. Regression: `types_lowering.rs::lowers_private_class_field_annotations`.

**Checker (resolved 2026-07-24):** `typecheck-ts` consumes
`DefData.declared_type` and HIR `ClassMemberSig` span lookup (no AST class-body
walk); see [typecheck-ts](./typecheck-ts.md) (annotated class-field TC3000 fix +
HIR-only class_typing slice).

### Class member signatures for HIR-only checking (2026-07-24)

`DefTypeInfo::Class.members: Vec<ClassMemberSig>` is the checker’s sole class-shape
input (`HirDeclLowerer::lower_class_instance_and_value`). Field-like annotations
are reachable without AST:

- Ordinary / private fields → `DefData.declared_type` (per-field arenas) **and**
  `ClassMemberSig` on the class
- Constructor parameter properties (`constructor(public x: T)`) → extra
  `ClassMemberSigKind::Field` entries (same arenas as the class)
- Ambient class properties → `ClassMemberSig` via `lower_type_member_signatures`

Helper: `ClassMemberSig::field_type_annotation()`. Regressions in
`types_lowering.rs`: `lowers_private_class_field_annotations`,
`lowers_constructor_parameter_properties_as_field_sigs`,
`lowers_ambient_class_property_annotations`. Residual: `TypeMember` has no
`static_` flag (ambient static members not modeled yet — parse-js gap).

### Module / ambient var `declared_type` (2026-07-24)

Value-side annotations for checker `declared_type_for_span` / `type_of_def`
without AST walks:

- `DefSource::Var` (declarator) and `DefSource::VarBinding` (simple Id pattern)
  copy `type_annotation` onto `DefData.declared_type` + per-def `TypeArenas`
- Destructuring bindings keep `DefSource::None` (annotation types the pattern)
- `DefSource::AmbientVar` covers the legacy `AmbientVarDecl` AST shape; today’s
  parser emits `declare const/let/var` as ordinary `VarDecl` (ambient via
  `FileKind::Dts`)

Regression: `types_lowering.rs::lowers_module_var_and_ambient_declared_types`.
See [typecheck-ts](./typecheck-ts.md) (HIR-only declared-type / type-alias slice).

### Value function param/return for HIR-only checking (2026-07-24)

`FunctionData` on function/method bodies already carries `params[].type_annotation`,
`return_type`, and `type_params` (per-def `TypeArenas`). Checker binder no longer
AST-lowers those when HIR is present; `function_type` consumes this surface via
`HirDeclLowerer::lower_value_function_signature`. No new hir-js fields required.
Existing regression: `lowering.rs` function annotation coverage;
checker: `typecheck-ts/tests/hir_function_annotations.rs`.

### Function overload / `declare function` bodies (2026-07-25)

`DefSource::Function` always allocates a `BodyKind::Function` body (even when
the AST `body` is `None`), so overload signatures and `declare function` carry
`FunctionData` with param/return annotations. New flag
`FunctionData.has_body` is `true` iff the AST had an implementation body —
required to distinguish `function f() {}` from overload/`declare` signatures
(both can lower to `FunctionBody::Block([])`).

Regression: `lowering.rs::lowers_function_overload_has_body_flags`.
Checker `collect_function_decl_types` consumes this for HIR-only overload sets
(see [typecheck-ts](./typecheck-ts.md)).
