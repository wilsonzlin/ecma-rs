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
- When embedding `semantic-js` into a runtime / VM, prefer the runtime entry
  point and a script-friendly top-level mode so top-level declarations are
  bound and can be resolved:
  ```rust
  use semantic_js::js::{bind_js_for_runtime, TopLevelMode};

  let (sem, diagnostics) = bind_js_for_runtime(&mut ast, TopLevelMode::Script, file);
  ```
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

- JS mode emits basic deterministic diagnostics for common binding errors such as
  lexical redeclarations and TDZ violations via `BIND####` codes. It still:
  - models runtime `with`/`eval` name resolution only via hazard flags, and
  - supports multiple script-oriented top-level modes:
    - `TopLevelMode::Global` intentionally **skips** binding top-level
      declarations for tooling/minifiers so the host can map globals separately.
    - `TopLevelMode::Script` **binds** top-level declarations and should be used
      by executing runtimes/VMs that need resolvable top-level symbols.
- TS mode does not bind inside statement bodies, nor does it track locals or
  statement-level scopes. It focuses on module-level declaration merging and
  import/export maps:
  - `export = Identifier` is supported by synthesizing a `default` export entry;
    other export assignment expressions are rejected with a diagnostic.
  - Module augmentation/global merging semantics are still incomplete compared to
    TypeScript.
- Determinism relies on caller-controlled inputs: changing file ids, HIR spans,
  or resolver results will change derived IDs.
