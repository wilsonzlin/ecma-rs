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

## Architecture docs (start here)

- **North-star design**: [`AGENTS.md`](./AGENTS.md) — authoritative architecture + implementation playbook.
- **Current crate boundaries**: [`docs/architecture.md`](./docs/architecture.md) — what exists today and how the crates connect.
- **Local setup for conformance + difftsc**: [`docs/quickstart.md`](./docs/quickstart.md) (also links into [`typecheck-ts-harness/README.md`](./typecheck-ts-harness/README.md)).
- **Runnable examples**: [`docs/examples.md`](./docs/examples.md) — copy/paste `cargo run` examples for the core crate APIs.

The workspace dependency graph in [`docs/deps.md`](./docs/deps.md) is generated; run `just docs` to refresh it.

## Quick start

This workspace intentionally does **not** commit `Cargo.lock` (it is gitignored). To run commands that match CI’s `--locked` behaviour, generate it first:

```bash
cargo generate-lockfile
```

If you have [`just`](https://github.com/casey/just) installed, the root `justfile` mirrors CI’s main checks:

```bash
just ci
```

Note: CI runs the same commands with `--locked` after generating `Cargo.lock`; the `just` recipes omit `--locked` for convenience.

`just ci` runs:

- `cargo fmt --all --check`
- `cargo clippy --workspace --all-targets --all-features`
- `cargo check --workspace --all-targets`
- `cargo test --workspace`
- `./scripts/gen_deps_graph.sh` (then verifies `docs/deps.md` is unchanged)

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

Which CI jobs use them:

- `test262/data` is fetched by the **`test262-parser`** job in [`.github/workflows/ci.yaml`](./.github/workflows/ci.yaml).
- `parse-js/tests/TypeScript` is used by the nightly **`ts-conformance`** workflow in [`.github/workflows/nightly.yaml`](./.github/workflows/nightly.yaml) (and by local `typecheck-ts-harness conformance` runs targeting the upstream suite).

## UTF-8 / source-text policy

All “source text” APIs in this workspace use `&str` / `Arc<str>` (valid UTF-8). This keeps:

- spans/offsets consistent (byte offsets in UTF-8),
- identifier handling correct,
- and prevents a split-brain between “bytes” and “text” entrypoints.

The repo enforces this with [`scripts/check_utf8_apis.sh`](./scripts/check_utf8_apis.sh) (also exercised by `diagnostics/tests/utf8_api_guard.rs`).

## Determinism, incremental queries, and profiling

High-level goals (see [`AGENTS.md`](./AGENTS.md) for the full playbook):

- **Determinism**: stable ordering/IDs/diagnostics regardless of parallelism.
- **Incremental-ready**: coarse-grained, query-based computation (parse → HIR → bind → check).

Profiling hooks:

- `typecheck-ts-harness conformance --profile --profile-out typecheck_profile.json` writes an aggregated profile report.
- `typecheck-ts-cli ... --profile` / `--trace` emits JSON tracing spans on stderr (redirect with `2> trace.jsonl`).
