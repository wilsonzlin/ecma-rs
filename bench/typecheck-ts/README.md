# typecheck-ts benchmarks

Deterministic, small-input performance exercises for the TypeScript pipeline.

## Running

```
cargo bench -p typecheck-ts-bench
```

By default a human-readable summary is printed. To additionally emit structured
JSON (suitable for CI tracking), set `TYPECHECK_TS_BENCH_JSON=1` in the
environment. When JSON output is enabled, the human-readable summary is emitted
to stderr and stdout is reserved for JSON so it can be redirected to a file.

All `typecheck-ts-bench` bench binaries accept `--json` as an alternative to the
environment variable (pass it after `--` to `cargo bench`). Using
`TYPECHECK_TS_BENCH_JSON=1` is preferred since Cargo forwards flags to every
benchmark/test binary and libtest harnesses may reject unknown arguments.

To keep CI runtime bounded, you can scale down the iteration counts by setting
`TYPECHECK_TS_BENCH_ITERS_SCALE` to a positive integer. Each benchmark's default
iteration count is divided by this value (clamped to a minimum of 1), preserving
deterministic ordering/format while reducing total work.

### Reproducing the nightly JSON report locally

```
cargo generate-lockfile
mkdir -p reports
TYPECHECK_TS_BENCH_JSON=1 TYPECHECK_TS_BENCH_ITERS_SCALE=10 \
  cargo bench -p typecheck-ts-bench --bench pipeline --locked \
  > reports/typecheck-ts-bench.json

TYPECHECK_TS_BENCH_JSON=1 \
  cargo bench -p typecheck-ts-bench --bench body_alloc --locked \
  > reports/typecheck-ts-body-alloc.json

TYPECHECK_TS_BENCH_JSON=1 \
  cargo bench -p typecheck-ts-bench --bench check_body_alloc --locked \
  > reports/typecheck-ts-check-body-alloc.json
```

Nightly CI uploads these JSON artifacts from `.github/workflows/nightly.yaml`:

- `typecheck-ts-bench.json` (artifact `typecheck-ts-bench`)
- `typecheck-ts-body-alloc.json` (artifact `typecheck-ts-body-alloc`)
- `typecheck-ts-check-body-alloc.json` (artifact `typecheck-ts-check-body-alloc`)

### Allocation bench JSON schema

`body_alloc` and `check_body_alloc` use a small, versioned schema so their
allocation counters can be archived/compared reliably:

```json
{
  "schema_version": 1,
  "results": [
    { "name": "control_flow", "allocations": 123, "diagnostics": 0 },
    { "name": "control_flow/evaluate", "allocations": 45, "diagnostics": 0, "exprs": 678 }
  ]
}
```

- `results` are sorted deterministically by `name`.
- `exprs` is only present for `check_body_alloc`.

If runtime becomes an issue (especially in CI), you can:

- limit which fixtures run by setting `TYPECHECK_TS_BENCH_ALLOC_FIXTURES` to a
  comma-separated list (e.g. `control_flow,generics`)
- skip allocation benches entirely with `TYPECHECK_TS_BENCH_ALLOC_SKIP=1`

## What is measured

All inputs live under `fixtures/` with deterministic ordering to keep the runs
stable:

- `parse/*`, `lower/*`, `parse_lower/*`: parser + HIR lowering micro-benches
  against fixed TS/TSX snippets (control flow narrowing, unions, generics,
  mapped/conditional types, TSX).
- `pipeline/parse_lower_bind/*`: parse + lower + TS binding of small module
  graphs to exercise module resolution/imports.
- `typecheck/*` and `typecheck/module_graph/*`: end-to-end checking for single
  files and a small multi-file project. Stage timings (parse/lower/bind/check
  body) and relation cache stats are included in the structured output.
- `type_of_def/exports/*`: `Program::type_of_def` across module graph
  definitions (export surface), including rendering via `display_type`.
- `check_body/cold/*` and `check_body/warm/*`: per-body type checking for
  control-flow-heavy and conditional/mapped-type-heavy fixtures with per-body
  caches vs warmed shared caches.
- `relations/*`: assignability micro-bench (`types-ts-interned`) with cold vs
  warmed caches and hit-rate reporting.
- `body_alloc` and `check_body_alloc`: allocation counters for full fixture
  checks and isolated `check_body` runs to track arena effectiveness.

### Incremental scenario

`incremental/full/*` runs a complete check of the `small_project` fixtures,
then `incremental/edit/*` re-runs after a small text edit in
`project_text.ts` (changing the `SEPARATOR` constant while leaving the mapped
type helpers intact). On a healthy incremental engine, the edit pass should be
noticeably cheaper because only the affected queries are invalidated. The
benchmarks run both phases with stable inputs so regressions in invalidation or
cache hit rates are easy to spot.
