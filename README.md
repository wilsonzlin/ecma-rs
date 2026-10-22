# ecma-rs

`ecma-rs` is a Rust workspace for a **deterministic** JavaScript/TypeScript toolchain.

Today the repo contains:

- **Parser**: `parse-js` (TS/TSX/JS/JSX → `Node<TopLevel>` + `Loc`)
- **HIR**: `hir-js` (lowered representation with stable-ish IDs for defs/bodies/exprs)
- **Semantics**: `semantic-js` (scopes/symbols/exports; JS mode used by minifier/optimizer)
- **TypeScript checker**: `typecheck-ts` (binder + checker + public `Program` API)
- **Emitter/printer**: `emit-js` (AST → text, deterministic formatting)
- **Minifier**: `minify-js` (+ `minify-js-cli`, + `minify-js-nodejs` package)
- **Optimizer**: `optimize-js` (SSA-based optimizer and decompiler)
- **VM stack**: `vm-js`, `runtime-js`, `webidl`, `webidl-vm-js`

## Documentation

The knowledge base is the [wiki](./wiki/index.md) (architecture, rationale, workflows,
testing, status). Agent working rules remain in [`AGENTS.md`](./AGENTS.md).

- Architecture: [wiki/architecture/overview.md](./wiki/architecture/overview.md),
  [engine.md](./wiki/architecture/engine.md)
- Setup / CI / examples: [wiki/engineering/workflows.md](./wiki/engineering/workflows.md)
- Diagnostics: [wiki/architecture/diagnostics.md](./wiki/architecture/diagnostics.md)
- Dependency graph (generated): [wiki/architecture/deps.md](./wiki/architecture/deps.md)
  — refresh with `just docs`

## Quick start

If you're setting up a checkout for TypeScript conformance / differential testing and you have [`just`](https://github.com/casey/just) + Node.js installed:

```bash
just setup
```

This bootstraps submodules + `typecheck-ts-harness` npm deps, generates `Cargo.lock`, and runs a small sanity check. Details: [wiki/engineering/workflows.md](./wiki/engineering/workflows.md).

This workspace intentionally does **not** commit `Cargo.lock` (it is gitignored). To run commands that match CI’s `--locked` behaviour, generate it first:

```bash
cargo generate-lockfile
```

If you have [`just`](https://github.com/casey/just) installed, the root `justfile` mirrors CI’s main checks:

```bash
just ci
```

Note: CI runs the same commands with `--locked` after generating `Cargo.lock`; the `just` recipes omit `--locked` for convenience.

`just ci` runs formatting, utf8/diagnostic guards, clippy, check, test, and regenerates
the dependency graph (then verifies `wiki/architecture/deps.md` is unchanged).

### Run the in-repo examples

```bash
cargo run -p typecheck-ts --example memory_host_basic
cargo run -p typecheck-ts --example json_snapshot
```

Full list: [wiki/engineering/workflows.md#runnable-examples](./wiki/engineering/workflows.md#runnable-examples).

### Run the CLIs

All tools treat input source as **UTF-8 text** (see [UTF-8 policy](#utf-8--source-text-policy)).

#### Parser CLI (`parse-js-cli`)

Reads from stdin and prints a JSON AST to stdout:

```bash
echo 'let x = 1 + 2' | cargo run -p parse-js-cli --locked -- --timeout-secs 2 > ast.json
```

#### Minifier CLI (`minify-js-cli`)

Minifies a single file (or stdin) and writes to stdout:

```bash
echo 'function add(a, b) { return a + b; }' | cargo run -p minify-js-cli --locked -- --mode global
```

#### Typechecker CLI (`typecheck-ts-cli`)

Type-check a file:

```bash
cargo run -p typecheck-ts-cli --locked -- typecheck fixtures/basic.ts
```

Query types/symbols by **byte offset** (UTF-8):

```bash
cargo run -p typecheck-ts-cli --locked -- typecheck fixtures/basic.ts --type-at fixtures/basic.ts:0
```

#### Harness (`typecheck-ts-harness`)

Run the small “conformance-mini” suite used by CI (no submodule checkout required):

```bash
cargo run -p typecheck-ts-harness --release --locked -- \
  conformance \
  --root typecheck-ts-harness/fixtures/conformance-mini \
  --compare snapshot \
  --manifest typecheck-ts-harness/fixtures/conformance-mini/manifest.toml \
  --json > typecheck-conformance-mini.json
```

Run `difftsc` against the stored baselines (no Node/`tsc` required):

```bash
cargo run -p typecheck-ts-harness --release --locked -- \
  difftsc \
  --suite typecheck-ts-harness/fixtures/difftsc \
  --compare-rust \
  --use-baselines \
  --manifest typecheck-ts-harness/fixtures/difftsc/manifest.toml \
  --json > difftsc-report.json
```

## Submodules and test corpora

This repo has two optional-but-important submodules:

- `parse-js/tests/TypeScript` — upstream TypeScript repo (conformance corpus + baseline files)
- `test262/data` — test262 parser tests corpus

Init them as needed:

```bash
git submodule update --init --recursive parse-js/tests/TypeScript
git submodule update --init test262/data
```

(Or `just submodules`; `just setup` also does this.)

Which CI jobs use them:

- `test262/data` is fetched by the **`test262-parser`** job in [`.github/workflows/ci.yaml`](./.github/workflows/ci.yaml).
- `parse-js/tests/TypeScript` is used by the nightly **`ts-conformance`** workflow in [`.github/workflows/nightly.yaml`](./.github/workflows/nightly.yaml) (and by local `typecheck-ts-harness conformance` runs targeting the upstream suite).

## UTF-8 / source-text policy

All “source text” APIs use `&str` / `Arc<str>` (valid UTF-8): spans are UTF-8 byte
offsets, identifier handling stays correct, and there is no bytes/text split-brain.
Enforced by [`scripts/check_utf8_apis.sh`](./scripts/check_utf8_apis.sh).

## Determinism, incremental queries, and profiling

High-level goals (full playbook: [`AGENTS.md`](./AGENTS.md); wiki:
[determinism](./wiki/architecture/determinism.md),
[engine](./wiki/architecture/engine.md)):

- **Determinism**: stable ordering/IDs/diagnostics regardless of parallelism.
- **Incremental-ready**: coarse-grained, query-based computation (parse → HIR → bind → check).

Profiling hooks:

- `typecheck-ts-harness conformance --profile --profile-out typecheck_profile.json` writes an aggregated profile report.
- `typecheck-ts-cli ... --profile` / `--trace` emits JSON tracing spans on stderr (redirect with `2> trace.jsonl`).
