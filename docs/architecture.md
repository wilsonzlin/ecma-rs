# Workspace architecture

This repository is converging on a single, deterministic toolchain for parsing,
binding, checking, and rewriting JavaScript/TypeScript. The key crates below
represent the stable boundaries contributors should target during the rewrite.

## Data flow at a glance

```mermaid
flowchart TD
  source[UTF-8 source text]
  parse[parse-js<br/>AST (Node<TopLevel> + Loc + NodeAssocData)]
  hir[hir-js<br/>HIR + DefId/BodyId/ExprId + SpanMap]
  sem[semantic-js<br/>Scopes/Symbols/Exports]
  types[types-ts-interned<br/>TypeStore + TypeId/ObjectId/ShapeId]
  check[typecheck-ts<br/>Program + queries + diagnostics]
  emit[emit-js<br/>Emitter/EmitOptions]
  minify[minify-js<br/>JS minifier + renamer]
  optimize[optimize-js<br/>CFG/SSA optimizer]
  harness[typecheck-ts-harness<br/>conformance + difftsc runner]
  source --> parse --> hir --> sem --> check
  parse --> emit
  sem --> minify
  sem --> optimize
  types --> check
  check --> harness
```

### Where IDs and spans live

- **Diagnostics**: `diagnostics::FileId` wraps stable per-program file indices.
  `TextRange { start, end }` is always UTF-8 byte offsets; `Span { file, range }`
  is the shared diagnostic currency.
- **parse-js**: emits `Node<TopLevel>` with `Loc(start, end)`; mutable
  `NodeAssocData` can host attachments (e.g. scope IDs).
- **hir-js**: assigns deterministic `DefId`/`BodyId`/`ExprId`/`TypeExprId` from
  `DefPath` hashes and builds `SpanMap` indices for byte→ID lookups.
- **semantic-js**: JS mode writes `ScopeId`/`DeclaredSymbol`/`ResolvedSymbol`
  into `NodeAssocData`; TS mode returns immutable symbol tables/export maps keyed
  by deterministic `SymbolId`/`DeclId` plus export-name strings (ordered `BTreeMap`s).
- **types-ts-interned**: `TypeId`/`ShapeId`/`ObjectId`/`SignatureId` are derived
  from stable hashes of canonical data; no spans leak into this layer.
- **typecheck-ts**: diagnostics are emitted with `Span`, while public queries
  return opaque IDs (`DefId`, `BodyId`, `ExprId`, `TypeId`) plus per-body side
  tables.

## Crate responsibilities and key APIs

### diagnostics
Shared diagnostic model: `FileId`, `TextRange`, `Span`, and `Diagnostic`. All
other crates use this for structured errors and spans.

### parse-js
- Fast JS/TS/JSX parser: `parse(&str)` / `parse_with_options(&str, ParseOptions)`
  → `Node<TopLevel>`.
- `Dialect`/`SourceType` control TypeScript vs JS and module vs script parsing.
- `NodeAssocData` provides thread-safe slots for downstream IDs (scopes, spans,
  etc.). `Loc` carries byte offsets used by emitters and lowerers.

### hir-js
- Lowers `parse-js` AST into a deterministic HIR tuned for binding and checking.
- Stable IDs: `DefId`, `BodyId`, `ExprId`, `TypeExprId`, `TypeParamId`, `NameId`
  derived from `DefPath` hashes.
- `SpanMap` indexes `TextRange` → IDs for diagnostics and IDE lookups.
- Modules under `lower`/`lower_types` normalize syntax sugar and erase
  TypeScript-only constructs into a smaller, checker-friendly surface.

### semantic-js
- Unified semantics for both JS-only tooling and the TS checker.
- JS mode (`js` module):
  - `bind_js` (or `declare` + `resolve`) walks a mutable AST, attaches `ScopeId`,
    `DeclaredSymbol`, and `ResolvedSymbol` to `NodeAssocData`, and returns a
    deterministic `JsSemantics` snapshot.
  - Replaces the legacy `symbol-js` semantics for optimizers/minifiers; iteration helpers
    such as `ScopeData::iter_symbols_sorted` enforce stable ordering.
- TS mode (`ts` module):
  - `bind_ts_program` consumes lowered `ts::HirFile`s, merges namespaces, and
    produces `SymbolTable` + export maps keyed by stable `SymbolId`/`DeclId`
    with `BTreeMap<String, ...>` export names.
  - Deterministic by construction (BTreeMap-backed maps; declaration order is
    inherited from HIR).
- `assoc` helpers read the IDs written into `NodeAssocData` without exposing the
  internal arenas.

### types-ts-interned
- Deterministic type interner used by the checker and any typed IR work.
- `TypeStore::new()` / `TypeStore::with_options` returns an `Arc` that interns
  canonicalized `TypeKind`, `Shape`, `Signature`, and `ObjectType` into stable
  IDs (`TypeId`, `ShapeId`, `SignatureId`, `ObjectId`, `NameId`).
- Stable hashing (domain-separated fingerprints) ensures ID allocation is
  independent of insertion order and safe under parallel requests.
- Relation/normalization helpers: `RelateCtx`, `RelateHooks`, `RelationKind`,
  `TypeEvaluator`, `TypeExpander`, and `TypeDisplay`.
- Conditional type evaluation uses structural assignability via `RelateCtx` in
  `RelationMode::SKIP_NORMALIZE` (avoids relate ↔ evaluate normalization cycles)
  and is cache-backed by `TypeEvaluator` (`EvaluatorCaches`).
- Single maintained type representation for the workspace; the former
  placeholder `types-ts` crate was removed to avoid drift.

### typecheck-ts
- Public facade for TypeScript checking. `Program::new(host, roots)` wires a
  user-provided `Host` (file_text + module `resolve`) into the pipeline. Hosts
  operate on deterministic [`FileKey`]s (opaque strings/paths), while
  [`Program`] owns the mapping from keys to internal `FileId`s to avoid
  collisions with bundled libs or other virtual files.
- Core APIs:
  - `Program::check()` parses, lowers, binds, and type-checks all reachable
    files, returning diagnostics.
  - `Program::check_body(BodyId)` → side tables (expression types) +
    diagnostics, cached per body.
  - Queries for results: `type_of_def`, `type_of_expr`, `exports_of`,
    `body_of_def`, `display_type`.
- Internally splits work into coarse queries (parse → HIR → bind → check) to
  align with the incremental, deterministic principles in `AGENTS.md`. IDs and
  caches are opaque; outputs are copyable handles backed by immutable arenas.

### emit-js
- Deterministic emitter from `parse-js` AST back to JS/TS source.
- Entry points:
  - `emit_top_level` / `emit_top_level_stmt` write JS/TS statements from
    `TopLevel`.
  - `emit_top_level_diagnostic` returns a `Diagnostic` with a best-effort span on
    failure.
- `Emitter`/`EmitOptions` control whitespace, ASI handling, and statement
  separation. Uses `Loc` to point diagnostics at offending syntax.

### minify-js
- Single-file minifier built on the parser and JS semantics.
- `minify(top_level_mode, source, output)` parses, runs `semantic-js` JS mode to
  understand scopes, performs identifier renaming, and rewrites the buffer.
- Returns `Vec<Diagnostic>` on failure; respects `TopLevelMode` for module vs
  script semantics and disables renaming when semantics would change (e.g.
  `eval`/`with`).

### optimize-js
- SSA-based optimizer and decompiler for JS.
- Pipeline: parse → `hir-js` lowering + semantic analysis (`JsSymbols`/`VarAnalysis`) → IL →
  CFG/SSA → opt passes (value numbering, DCE, CFG prune) → optional
  decompilation (`program_to_ast` / `program_to_js` via `emit-js`).
- Legacy AST lowering has been removed in favor of the single HIR pipeline.
- Diagnostics use shared `Span`/`TextRange`; deterministic tests enforce stable
  symbol/CFG ordering.

### typecheck-ts-harness
- CLI + library harness that drives the checker against upstream TypeScript
  conformance suites and local differential tests.
- Commands:
  - `conformance`: run Rust checker vs upstream tests (requires TS submodule).
  - `difftsc`: compare checker diagnostics against `tsc` (or stored baselines).
- Uses `Program` APIs plus JSON outputs to make regressions reproducible in CI.

## Determinism and incremental-query principles

- **Same inputs → same IDs/exports/diagnostics**. Stable hashing
  (`types-ts-interned`), ordered maps (`semantic-js`), and `hir-js` hashing of
  `DefPath` avoid dependence on traversal order or thread scheduling.
- **Immutable outputs**. Parsers/lowerers return owned AST/HIR; semantic tables,
  type stores, and per-body check results are treated as snapshots (shared via
  `Arc` where needed).
- **Coarse-grained queries**. `typecheck-ts` groups work per file/definition/body
  (parse → hir → bind → check_body) instead of per expression to align with the
  incremental, parallel design in `AGENTS.md`.
- **Span discipline**. Only syntax layers own byte offsets; semantic/type layers
  traffic in IDs. Diagnostics attach `Span` at the boundary, enabling consumers
  to render errors without threading AST pointers through the system.
- **Regeneration and documentation**. Run `just docs` (or
  `scripts/gen_deps_graph.sh`) to refresh the dependency graph documented in
  `docs/deps.md` and keep this architecture view in sync with the workspace
  edges.
