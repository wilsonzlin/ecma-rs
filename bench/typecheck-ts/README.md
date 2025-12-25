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
- Lowering into real `hir-js` HIR with summary stats.
- Binding a tiny module graph via `semantic-js` (TS mode).
- Type checking representative fixtures through `typecheck-ts::Program`.
- Relations micro-bench: assignability with cold vs warmed caches using the
  `types-ts` relation engine.

All inputs live under `fixtures/` and are intentionally small to keep runs fast
and stable.
