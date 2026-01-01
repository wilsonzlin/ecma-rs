# semantic-js

Unified semantics layer for the ecma-rs toolchain. `semantic-js` is meant to be
the single place where scopes, symbols, and exports are defined so downstream
crates (optimizers, minifiers, and the TypeScript checker) agree on the
same model. It is the sole semantics layer in the workspace; the legacy
`symbol-js` crate has been removed entirely.

## Modes at a glance

- **JS mode**: `js::declare` + `js::resolve` walk a `parse-js` AST, build a
  lexical scope tree in the value namespace, and attach lightweight IDs
  (`ScopeId`, `DeclaredSymbol`, `ResolvedSymbol`) to `NodeAssocData`. This is the
  mode used by `minify-js`, `optimize-js`, and any other JS-only tooling.
- **TS mode**: `ts::bind_ts_program` consumes lowered `ts::HirFile` inputs,
  merges declarations across the value/type/namespace spaces, and produces
  deterministic symbol groups and export maps for a type checker or any
  TypeScript-aware tooling.

## Determinism

The binder and resolver must be repeatable: same inputs → same IDs and export
maps.

- JS mode uses stable hashing to content-address `ScopeId`/`SymbolId`/`NameId`
  from the `FileId`, scope ancestry, and source spans. The same source text
  therefore produces the same IDs regardless of traversal order. Scope symbol
  tables live in `BTreeMap<NameId, SymbolId>` for stable iteration; use
  [`js::ScopeData::iter_symbols_sorted`] or [`js::JsSemantics::scope_symbols`] to
  traverse them deterministically.
- TS mode similarly derives `SymbolId`/`DeclId` from stable content and stores
  exports and global symbol maps in `BTreeMap` for deterministic iteration.
  Declaration lists inside a symbol are sorted by their `order` (inherited from
  the input HIR) and then by ID.
- Stability still depends on caller-controlled inputs: changing `FileId`s,
  lowering spans, or module resolution results will change derived IDs and
  exports.

## Lock-free, immutable outputs

Binding runs locally without any global locks. JS mode mutates only
`NodeAssocData` during traversal; afterwards, all recorded scopes/symbols live
in owned maps keyed by stable IDs. TS mode builds `SymbolTable`s and export maps
in owned data structures and returns immutable snapshots (`Arc` is left to the
caller). Downstream consumers are expected to treat the returned IDs as opaque
handles and avoid mutating the underlying collections after construction.

## Integration points

- JS mode requires a mutable `parse-js` AST so it can write attachments to
  `NodeAssocData`. Use `js::bind_js` (or `declare`/`resolve` separately) and then
  query the IDs via helper accessors such as `scope_id`/`declared_symbol` or
  iterate deterministically with [`js::JsSemantics::scope_symbols`]. A complete
  example lives in `examples/semantic-js/README.md` and is mirrored as a
  doctest in `semantic-js`'s crate docs.
- TS mode expects one `HirFile` per source file, typically produced by `hir-js`
  (or another frontend). The caller supplies a `Resolver` to turn module
  specifiers into `FileId`s; the binder does not implement Node/TS resolution
  strategies itself.

## Migration from `symbol-js`

`symbol-js` provided scope information for optimizers but used mutable,
lock-backed scopes and opaque, non-deterministic IDs. `semantic-js` is the
replacement: deterministic IDs, immutable arenas, and a TS-aware export model.
Replace calls to the legacy `compute_symbols` helper with `semantic_js::js::bind_js`
and read back `ScopeId`/`SymbolId` attachments via `semantic_js::assoc::js`. JS mode
now covers the same surface (scope IDs + resolution) without global locks; deterministic
iteration via [`js::JsSemantics::scope_symbols`] is available for consumers that relied
on `symbol-js`'s map ordering, and downstream crates have been migrated to it.

## Known gaps

- JS mode does not emit diagnostics. It records hoisting and TDZ metadata (see
  [`js::ScopeData::hoisted_bindings`], [`js::ScopeData::tdz_bindings`], and
  `ResolvedSymbol::in_tdz`) and marks dynamic-scope hazards (`with` and direct,
  global `eval`) via [`js::ScopeData::is_dynamic`] /
  [`js::ScopeData::has_direct_eval`], but it does not currently:
  - report TDZ or re-declaration errors,
  - model runtime `with`/`eval` name resolution beyond hazard flags, or
  - bind top-level globals in `TopLevelMode::Global` (top-level declarations are
    intentionally skipped so hosts can map globals separately).
- TS mode does not bind inside statement bodies, nor does it track locals or
  contextual type-only exports beyond the provided flags. `export =` is rejected
  with a diagnostic, and module augmentation/global merging are not modeled.
- Determinism relies on caller-controlled inputs: changing file ids, HIR spans,
  or resolver results will change derived IDs.
