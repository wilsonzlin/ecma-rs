# typecheck-ts-harness

Utilities for running the TypeScript conformance suites and differential tests
against `tsc`.

## Quick start

```
# 1) Bring in the upstream TS suite (submodule)
git submodule update --init --recursive parse-js/tests/TypeScript

# 2) Install Node prereqs (once)
npm install --prefix typecheck-ts-harness --no-save typescript

# 3) Run the Rust conformance harness
cargo run -p typecheck-ts-harness --release -- conformance --filter "**/es2020/**" --shard 0/8

# 4) (Optional) Regenerate difftsc baselines for local fixtures
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --update-baselines
```

If any step fails (e.g. missing tests or “cannot find module `typescript`”),
revisit the prerequisites below.

## Prerequisites

### TypeScript upstream suite (submodule)

The conformance runner expects the upstream TypeScript repo to be checked out at
`parse-js/tests/TypeScript/` (submodule).

```
git submodule update --init --recursive parse-js/tests/TypeScript
ls parse-js/tests/TypeScript/tests/cases/conformance | head
```

- Default root: `parse-js/tests/TypeScript/tests/cases/conformance`
- If the submodule is missing/empty, conformance discovery now errors. Pass
  `--allow-empty` only when intentionally running with an empty suite.
- Override the root with `--root <path>` to point at a different checkout or a
  reduced local corpus.

### Node.js + `typescript` npm package

The harness shells out to a long-lived Node helper (`scripts/tsc_runner.js`)
that loads the `typescript` package. Install it anywhere on Node's resolution
path for that script (installing under `typecheck-ts-harness/` works out of the
box):

```
node --version
npm install --prefix typecheck-ts-harness --no-save typescript
node -C typecheck-ts-harness -p "require('typescript').version"
```

- Use `--node /path/to/node` if `node` is not on `PATH` or you want a specific
  runtime.
- Missing Node:
  - Built without `with-node` feature **or** `node --version` fails → `difftsc`
    logs a skip instead of failing.
- Missing `typescript` package:
  - The Node helper returns a `crash` payload; install the package and re-run.

### Node TypeScript runner protocol

`scripts/tsc_runner.js` speaks NDJSON over stdin/stdout and serves files from
memory (no tempdirs). Each input line is:

```json
{ "rootNames": ["main.ts"], "files": { "main.ts": "const x: string = 1;" }, "options": { "strict": true } }
```

Output is one JSON object per line:

```json
{ "diagnostics": [{ "code": 2322, "file": "main.ts", "start": 22, "end": 23, "category": "error", "message": "Type '1' is not assignable to type 'string'." }] }
```

If the runner encounters an internal error, it sets a `crash` field on the
output. Paths are normalized relative to `/` for deterministic baselines.

## Conformance runner (`conformance`)

Runs the Rust checker against upstream TypeScript conformance cases.

```
# Default root, release build
cargo run -p typecheck-ts-harness --release -- conformance

# Filter (glob or regex) and shard
cargo run -p typecheck-ts-harness --release -- conformance \
  --filter "**/es2020/**" \
  --shard 3/16

# Larger timeout per test (seconds)
cargo run -p typecheck-ts-harness --release -- conformance --timeout-secs 30

# Include additional extensions
cargo run -p typecheck-ts-harness --release -- conformance --extensions ts,tsx,d.ts,js
```

- Filters accept globs or regexes; they match the path under the root (e.g.
  `**/es2020/**`, `**/*optionalChaining*`). Paths are normalized with `/` and do
  not include the absolute root prefix.
- Discovery includes `.ts`, `.tsx`, and `.d.ts` by default. Use
  `--extensions <comma-separated>` to add more.
- Shards are zero-based (`i/n`) and are applied after sorting cases by id; run
  each shard in a separate process/job for parallelism.
- Timeouts apply per test case (default 10s) and kill only the offending test,
  not the whole run.
- `--json` emits machine-readable results; `--trace`/`--profile` are forwarded to
  the checker.
- `--allow-empty` suppresses the default error when zero tests are discovered.
- Harness execution is currently single-threaded; for CI parallelism use shards
  across jobs (example below).

**GitHub Actions suggestion (`ubuntu-latest`, 2-core):**

Run 8–16 shards in parallel matrix jobs to keep wall time low:

```
matrix:
  shard: [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

run: cargo run -p typecheck-ts-harness --release -- conformance --shard ${{matrix.shard}}/16 --timeout-secs 20 --json
```

If the TypeScript suite is missing the command will fail fast; check the
submodule before assuming green or use `--allow-empty` for ad-hoc runs.

## Differential testing (`difftsc`)

`difftsc` supports both baseline stability checks (tsc vs stored JSON) and true
differential testing (tsc vs the Rust checker). It runs `tsc` via the reusable
`TscRunner` (`scripts/tsc_runner.js`) with in-memory virtual files and structured
JSON.

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

# Emit JSON (includes diff details) and continue even if mismatches are found
cargo run -p typecheck-ts-harness --release -- difftsc --suite fixtures/difftsc --compare-rust --json --allow-mismatches
```

- Node is discovered by running `node --version`; use `--node` to override.
- `with-node` feature disabled or missing Node → command logs `difftsc skipped`
  and exits successfully. Differential runs with `--use-baselines` can proceed
  without Node.
- Baselines are read from/written to `baselines/<suite>/<test>.json` (see below).
- The runner uses `ts.getPreEmitDiagnostics` with `noEmit`, `skipLibCheck` and
  writes `{ diagnostics: [{ code, category, file, start, end, message }] }`.

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
