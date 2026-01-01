# typecheck-ts-harness

Utilities for running the TypeScript conformance suites and differential tests
against `tsc`.

## Quick start

```
# 1) Bring in the upstream TS suite (submodule)
git submodule update --init --recursive parse-js/tests/TypeScript

# 2) Install Node prereqs (once)
cd typecheck-ts-harness && npm ci

# 3) Run the Rust conformance harness
cargo run -p typecheck-ts-harness --release -- conformance --filter "*/es2020/**" --shard 0/8

# 4) (Optional) Regenerate difftsc baselines for local fixtures
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --update-baselines
```

If setup fails because the TypeScript suite is missing or you see “cannot find
module `typescript`”, revisit the prerequisites below.

All fixtures are treated as UTF-8; discovery will fail fast on invalid encodings
to keep spans and offsets consistent.

## Prerequisites

### TypeScript upstream suite (submodule)

The conformance runner expects the upstream TypeScript repo to be checked out at
`parse-js/tests/TypeScript/` (submodule).

```
git submodule update --init --recursive parse-js/tests/TypeScript
ls parse-js/tests/TypeScript/tests/cases/conformance | head
```

- Default root: `parse-js/tests/TypeScript/tests/cases/conformance`
- If the submodule is missing/empty, `conformance` fails fast with a hint to run
  `git submodule update --init --recursive parse-js/tests/TypeScript`. Override
  the root with `--root <path>` to point at a different checkout or a reduced
  local corpus, or opt out of the check with `--allow-empty` (alias:
  `--allow-missing-suite`).

### Node.js + `typescript` npm package

The harness shells out to Node and loads the `typescript` package via
`scripts/tsc_runner.js` (an NDJSON, in-memory TypeScript runner).

```
node --version
cd typecheck-ts-harness && npm ci
node scripts/typescript_probe.js
```

- The harness ships a pinned `typecheck-ts-harness/package-lock.json`; `npm ci`
  installs the exact `typescript` version used for baselines.
- Use `--node /path/to/node` if `node` is not on `PATH` or you want a specific
  runtime.
- Missing Node / TypeScript:
  - `difftsc` only requires a live `tsc` (and therefore the `with-node` feature,
    a working Node.js binary, and the `typescript` npm package) when it needs to
    run `tsc` (e.g. verifying baselines, or `--update-baselines`).
  - Baseline-only differential runs (`--compare-rust --use-baselines`) do **not**
    require Node and will run even without `with-node`.
- Missing `typescript` package:
  - The harness logs a skip (or errors when updating baselines). Install via
    `cd typecheck-ts-harness && npm ci`.
  - To point at a different install, set `TYPECHECK_TS_HARNESS_TYPESCRIPT_DIR`
    to a directory containing `node_modules/typescript`.

## Conformance runner (`conformance`)

Runs the Rust checker against upstream TypeScript conformance cases.

```
# Default root, release build
cargo run -p typecheck-ts-harness --release -- conformance

# Filter (glob or regex) and shard
cargo run -p typecheck-ts-harness --release -- conformance \
  --filter "*/es2020/**" \
  --shard 3/16

# Larger timeout per test (seconds)
cargo run -p typecheck-ts-harness --release -- conformance --timeout-secs 30

# Ignore known failures via manifest + allow-only-new-failures
cargo run -p typecheck-ts-harness --release -- conformance \
  --manifest typecheck-ts-harness/fixtures/conformance_manifest.toml \
  --fail-on new
```

- Filters accept globs or regexes; they match the path under the root (e.g.
  `**/es2020/**`, `optionalChaining`).
- Shards are zero-based (`i/n`) and are applied after sorting cases by id; run
  each shard in a separate process/job for parallelism.
- `--extensions <csv>` controls which test files are discovered (default:
  `ts,tsx,d.ts`). Values are treated as file suffixes (leading `.` optional) and
  are matched using a longest-suffix-wins rule, so `types.d.ts` is **not**
  included by `--extensions ts` unless `d.ts` is also listed.
- Timeouts apply per test case (default 10s) and kill only the offending test,
  not the whole run.
- Execution is parallel by default; cap worker threads with `--jobs <n>` (default
  is the CPU count). Combine with sharding for coarse-grained CI splits.
- Comparison is configurable:
  - `--compare auto|tsc|snapshot|none` (default auto: prefer `tsc`, then
    snapshots, else none with a warning)
  - `--node /path/to/node` overrides the Node.js executable used for `tsc`
  - `--span-tolerance <bytes>` allows small span drift when diffing
- `--json` prints the machine-readable conformance report to stdout.
- `--trace` enables structured tracing logs on stderr (JSONL), keeping stdout
  parseable when `--json` is enabled. Redirect with `2> trace.jsonl`.
- `--profile` is forwarded to the checker.
- A tiny demo corpus lives at `typecheck-ts-harness/fixtures/conformance-mini`.

**GitHub Actions suggestion (`ubuntu-latest`, 2-core):**

Run 8–16 shards in parallel matrix jobs to keep wall time low:

```
matrix:
  shard: [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

run: cargo run -p typecheck-ts-harness --release -- conformance --shard ${{matrix.shard}}/16 --timeout-secs 20 --json
```

If the TypeScript suite is missing the command errors with setup instructions
instead of returning `Ran 0 test(s)`. Use `--allow-empty`/`--allow-missing-suite`
if you intentionally want to skip discovery.

## Differential testing (`difftsc`)

`difftsc` supports both baseline stability checks (tsc vs stored JSON) and true
differential testing (tsc vs the Rust checker).

```
# Regenerate baselines for the bundled suite
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --update-baselines

# Compare live tsc output against baselines
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc

# Differential mode: tsc vs Rust
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --compare-rust

# Differential mode using stored baselines instead of shelling out to tsc
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --compare-rust --use-baselines

# Allow small span drift (bytes)
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --span-tolerance 2

# Print raw tsc payloads for mismatches
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --print-tsc

# Limit parallel workers (defaults to CPU count)
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --compare-rust --use-baselines --jobs 4

# Emit JSON (includes diff details) and continue even if mismatches are found
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --compare-rust --json --allow-mismatches
```

- Node is discovered by running `node --version`; use `--node` to override.
- Baseline-only differential runs (`--compare-rust --use-baselines`) do not need
  Node and will run even without the `with-node` feature.
- If `difftsc` needs live `tsc` (baseline verification, updates, or runs without
  `--use-baselines`) and Node/TypeScript are missing, it logs `difftsc skipped`
  and exits successfully (or errors when updating baselines).
- TSC and Rust executions are parallelized across `--jobs` workers. Node
  invocations are concurrency-limited to keep process count bounded, and JSON
  output is stably ordered regardless of scheduling.
- Baselines are read from/written to `baselines/<suite>/<test>.json`, where the
  filename is the test id with `.json` appended (so single-file tests preserve
  their original extension, e.g. `match/basic.ts` → `baselines/conformance-mini/match/basic.ts.json`).
- The runner uses `ts.getPreEmitDiagnostics` with `noEmit`, `skipLibCheck` and
  writes `{ schemaVersion, metadata: { typescriptVersion, options }, diagnostics: [...] }`.

### Expectations manifests

Both `conformance` and `difftsc` accept `--manifest <path>` describing expected
skips or failures. Statuses are `skip`, `xfail`, or `flaky` (like `xfail` but
reported separately). Example (`toml` or JSON):

```
[[expectations]]
id = "err/parse_error.ts"
status = "xfail"
reason = "parser gaps"

[[expectations]]
glob = "flaky/**"
status = "flaky"
tracking_issue = "TICKET-123"
```

Use `--fail-on new|all|none` to control exit status (default `all`):
- `new` (default): only uncovered mismatches fail the run
- `all`: any mismatch fails
- `none`: always succeed (useful for generating reports)

Conformance test ids are the path under the suite root. `difftsc` ids include
the suite name (e.g. `difftsc/assignability`).

## Fixtures and baselines layout

- Fixtures live under `fixtures/<suite>/`:
  - Single-file tests are `<name>.ts/tsx/js/...`
  - Multi-file tests are directories (all TS/JS files inside are included).
  - Test names come from the file stem or directory name.
- Baselines live under `baselines/<suite>/<test>.json` (the test id plus `.json`,
  so single-file tests become e.g. `<name>.ts.json`).
- Baselines carry a schema version plus the `typescript` version/options used to
  generate them.
- To add/update tests:
  1. Drop files under `fixtures/<suite>/...`
  2. Regenerate baselines: `cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/<suite> --update-baselines`
  3. Commit both fixtures and baselines.

## CI: live `tsc` smoke run

CI runs a small `fixtures/difftsc` suite against a pinned npm TypeScript to keep
the Rust checker aligned with upstream diagnostics without relying on stored
baselines. The workflow installs `typescript@5.5.4` and executes:

```
RAYON_NUM_THREADS=2 cargo run -p typecheck-ts-harness --release --locked --jobs 2 -- \
  difftsc \
  --suite typecheck-ts-harness/fixtures/difftsc \
  --compare-rust \
  --manifest typecheck-ts-harness/fixtures/difftsc/manifest.toml \
  --json
```

- The suite is intentionally tiny to bound runtime.
- `RAYON_NUM_THREADS` caps Rust-side parallelism; the harness reuses a single
  `tsc` runner so upstream invocations stay serialized.
- The JSON report artifact captures both `tsc` and Rust diagnostics for
  mismatches.

To reproduce locally, install the pinned TypeScript package next to the harness
(`cd typecheck-ts-harness && npm install --no-save --no-package-lock --ignore-scripts typescript@5.5.4`)
before running the command above.
