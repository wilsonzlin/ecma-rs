# typecheck-ts-harness

Utilities for running the TypeScript conformance suites and differential tests
against `tsc`.

## Quick start

```
# 1) Bring in the upstream TS suite (submodule)
git submodule update --init --recursive parse-js/tests/TypeScript

# 2) Install Node prereqs (once)
npm install typescript

# 3) Run the Rust conformance harness
cargo run -p typecheck-ts-harness --release -- conformance --filter "*/es2020/**" --shard 0/8

# 4) (Optional) Regenerate difftsc baselines for local fixtures
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --update-baselines
```

If any step silently produces zero tests or fails with “cannot find module
`typescript`”, revisit the prerequisites below.

## Prerequisites

### TypeScript upstream suite (submodule)

The conformance runner expects the upstream TypeScript repo to be checked out at
`parse-js/tests/TypeScript/` (submodule).

```
git submodule update --init --recursive parse-js/tests/TypeScript
ls parse-js/tests/TypeScript/tests/cases/conformance | head
```

- Default root: `parse-js/tests/TypeScript/tests/cases/conformance`
- If the submodule is missing/empty, conformance discovery returns **zero**
  tests and the command prints `Ran 0 test(s)` (treat this as a misconfiguration,
  not success).
- Override the root with `--root <path>` to point at a different checkout or a
  reduced local corpus.

### Node.js + `typescript` npm package

The `difftsc` command shells out to Node and loads the `typescript` package via
`scripts/tsc_wrapper.js`.

```
node --version
npm install typescript          # or pnpm/yarn; install anywhere on Node's resolution path
node -p "require('typescript').version"
```

- Use `--node /path/to/node` if `node` is not on `PATH` or you want a specific
  runtime.
- Missing Node:
  - Built without `with-node` feature **or** `node --version` fails → `difftsc`
    logs a skip instead of failing.
- Missing `typescript` package:
  - `scripts/tsc_wrapper.js` will exit with a require error; install the package
    and re-run.

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
```

- Filters accept globs or regexes; they match the path under the root (e.g.
  `**/es2020/**`, `optionalChaining`).
- Shards are zero-based (`i/n`) and are applied after sorting cases by id; run
  each shard in a separate process/job for parallelism.
- Timeouts apply per test case (default 10s) and kill only the offending test,
  not the whole run.
- `--json` emits machine-readable results; `--trace`/`--profile` are forwarded to
  the checker.
- Harness execution is currently single-threaded; for CI parallelism use shards
  across jobs (example below).

**GitHub Actions suggestion (`ubuntu-latest`, 2-core):**

Run 8–16 shards in parallel matrix jobs to keep wall time low:

```
matrix:
  shard: [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

run: cargo run -p typecheck-ts-harness --release -- conformance --shard ${{matrix.shard}}/16 --timeout-secs 20 --json
```

If the TypeScript suite is missing you will see `Ran 0 test(s)`; check the
submodule before assuming green.

## Differential testing (`difftsc`)

Today `difftsc` runs `tsc` (via Node) on fixture suites, writes/reads structured
JSON baselines, and compares diagnostics.

```
# Regenerate baselines for the bundled suite
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --update-baselines

# Compare against committed baselines
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc

# Allow small span drift (bytes)
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --span-tolerance 2
```

- Node is discovered by running `node --version`; use `--node` to override.
- `with-node` feature disabled or missing Node → command logs `difftsc skipped`
  and exits successfully.
- Baselines are read from/written to `baselines/<suite>/<test>.json` (see below).
- The wrapper uses `ts.getPreEmitDiagnostics` with `noEmit`, `skipLibCheck` and
  writes `{ diagnostics: [{ code, category, file, start, end }] }`.

**Planned differential mode (once the Rust checker exposes matching JSON):**
- The same `difftsc` entry point will also run the Rust checker and diff directly
  against `tsc` without precomputed baselines.
- Expect a flag such as `--differential`/`--compare-rust` alongside `--suite`:
  `cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --differential`
- Until that lands, keep baselines up to date with `--update-baselines`.

## Fixtures and baselines layout

- Fixtures live under `fixtures/<suite>/`:
  - Single-file tests are `<name>.ts/tsx/js/...`
  - Multi-file tests are directories (all TS/JS files inside are included).
  - Test names come from the file stem or directory name.
- Baselines live under `baselines/<suite>/<test>.json`.
- To add/update tests:
  1. Drop files under `fixtures/<suite>/...`
  2. Regenerate baselines: `cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/<suite> --update-baselines`
  3. Commit both fixtures and baselines.
