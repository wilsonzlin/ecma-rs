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

## What is measured

All inputs live under `fixtures/` with deterministic ordering to keep the runs
stable:

- `parse/*`, `lower/*`, `parse_lower/*`: parser + HIR lowering micro-benches
  against fixed TS/TSX snippets.
- `bind/module_graph/*`: semantic-js binding of small module graphs.
- `type_of_def/exports/*`: `Program::type_of_def` across module graph
  definitions (export surface), including rendering via `display_type`.
- `check_body/*`: per-body type checking for control-flow-heavy and
  generics-heavy fixtures without re-checking the whole file.
- `typecheck/*` and `typecheck/module_graph/*`: end-to-end checking for single
  files and a small multi-file project.
- `relations/*`: assignability micro-bench (`types-ts-interned`) with cold vs warmed
  caches.

### Incremental scenario

`incremental/full/*` runs a complete check of the `small_project` fixtures,
then `incremental/edit/*` re-runs after a small text edit in
`project_text.ts` (changing the `SEPARATOR` constant). On a healthy incremental
engine, the edit pass should be noticeably cheaper because only the affected
queries are invalidated. The benchmarks run both phases with stable inputs so
regressions in invalidation or cache hit rates are easy to spot.
