# typecheck-ts benchmarks

Deterministic, small-input performance exercises for the TypeScript pipeline.

## Running

```
cargo bench -p typecheck-ts-bench
```

By default a human-readable summary is printed. To additionally emit structured
JSON (suitable for CI tracking), set `TYPECHECK_TS_BENCH_JSON=1` in the
environment. Passing `--json` directly to `cargo bench` is discouraged because
that flag is forwarded to all test binaries and may be rejected by libtest
harnesses.

## Coverage

- Parse only for representative TS/TSX snippets.
- HIR-style traversal counts (placeholder until real lowering hooks exist).
- Binding via `symbol-js` in module/global modes, including a tiny module graph.
- Type body simulations for control-flow heavy, union/intersection heavy, and
  generic/overload resolution patterns using a small toy type engine.
- Relations micro-bench: assignability with cold vs warmed caches.

All inputs live under `fixtures/` and are intentionally small to keep runs fast
and stable.
