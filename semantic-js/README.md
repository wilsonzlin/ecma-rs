# semantic-js

Unified semantics layer for the ecma-rs toolchain. `semantic-js` is meant to be
the single place where scopes, symbols, and exports are defined so downstream
crates (optimizers, minifiers, and the future TypeScript checker) agree on the
same model.

## Modes at a glance

- **JS mode**: `js::declare` + `js::resolve` walk a `parse-js` AST, build a
  lexical scope tree in the value namespace, and attach lightweight IDs
  (`ScopeId`, `DeclaredSymbol`, `ResolvedSymbol`) to `NodeAssocData`. This is the
  migration target for current `symbol-js` users such as `minify-js` and
  `optimize-js`.
- **TS mode**: `ts::bind_ts_program` consumes lowered `ts::HirFile` inputs,
  merges declarations across the value/type/namespace spaces, and produces
  deterministic symbol groups and export maps for a type checker or any
  TypeScript-aware tooling.

## Determinism

The binder and resolver must be repeatable: same inputs → same IDs and export
maps.

- JS mode allocates `ScopeId`, `SymbolId`, and `NameId` sequentially while
  walking the AST. Resolution is deterministic, but scope member tables use
  `ahash::HashMap`; callers should not expose raw iteration over those maps in
  public APIs until they are replaced with ordered collections.
- TS mode stores exports and merged globals in `BTreeMap` so iteration is
  stable. Declaration lists inside symbols are sorted by the order they were
  encountered in the input HIR. Overall ordering is therefore determined by the
  supplied roots, the order of declarations inside each `HirFile`, and the host
  `Resolver`.
- No public API should rely on the iteration order of internal `HashMap`s or the
  random hash state used by `ahash`. If ordered output is required, collect keys
  into a deterministic structure before exposing it.

## Lock-free, immutable outputs

Binding runs locally without any global locks. JS mode mutates only
`NodeAssocData` during traversal; afterwards, all recorded scopes/symbols live
in plain `Vec`s. TS mode builds `SymbolTable`s and export maps in owned data
structures and returns immutable snapshots (`Arc` is left to the caller).
Downstream consumers are expected to treat the returned IDs as opaque handles
and avoid mutating the underlying collections after construction.

## Integration points

- JS mode requires a mutable `parse-js` AST so it can write attachments to
  `NodeAssocData`. Use `js::bind_js` (or `declare`/`resolve` separately) and then
  query the IDs via helper accessors such as `scope_id`/`declared_symbol`.
- TS mode expects one `HirFile` per source file, typically produced by a future
  `hir-js` lowering step. The caller supplies a `Resolver` to turn module
  specifiers into `FileId`s; the binder does not implement Node/TS resolution
  strategies itself.

## Migration from `symbol-js`

`symbol-js` provided scope information for optimizers but used mutable,
lock-backed scopes and opaque, non-deterministic IDs. `semantic-js` is the
intended replacement: deterministic IDs, immutable arenas, and a TS-aware
export model. JS mode already covers the same surface (scope IDs + resolution)
without global locks; downstream crates should migrate to it as new API
surfaces (e.g. deterministic iteration) become available.

## Known gaps

- JS mode is lexical-only: it does not model hoisting, TDZ errors,
  `with`/`eval`, or re-declaration diagnostics. `var` binds to the nearest
  closure (function or module), and top-level bindings are skipped entirely in
  `TopLevelMode::Global`.
- Iterating over `ScopeData::symbols` is not deterministic because it is backed
  by `ahash::HashMap`.
- TS mode does not bind inside statement bodies, nor does it track locals or
  contextual type-only exports beyond the provided flags. `export =` is rejected
  with a diagnostic, and module augmentation/global merging are not modeled.
- Determinism relies on caller-controlled inputs: changing root order, HIR
  declaration order, or resolver results will change allocated IDs.
