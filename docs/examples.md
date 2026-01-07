# Runnable examples

The workspace ships a small set of compiled examples intended for copy/paste
setups in downstream tools. They avoid filesystem I/O by using in-memory hosts
and produce deterministic output (stable ordering of diagnostics and queries).

## `typecheck-ts`

```bash
cargo run -p typecheck-ts --example memory_host_basic
cargo run -p typecheck-ts --example json_snapshot
```

- `memory_host_basic` demonstrates `MemoryHost`, deterministic module resolution,
  rendering diagnostics, and common queries (`exports_of`, `type_at`, `symbol_at`,
  `display_type`).
- `json_snapshot` prints a minimal JSON payload (with a `schema_version`) that
  can be redirected to a file for snapshot tests.

## `hir-js`

```bash
cargo run -p hir-js --example basic_lowering
```

This example parses+lowers a small TypeScript snippet and shows how to use
`SpanMap` for byte-offset lookups.

## `minify-js`

```bash
cargo run -p minify-js --example basic
```

This example minifies a small TypeScript snippet and prints the emitted
JavaScript to stdout.
