# Workflows

Setup, everyday commands, CI, guard scripts, and release mechanics. (Absorbed from
`CONTRIBUTING.md`, `docs/quickstart.md`, `docs/examples.md`, `README.md`, the
`justfile`, and `.github/workflows/`, 2026-07.)

## Setup

Toolchain is pinned via `rust-toolchain.toml` (Rust 1.92.0 incl. rustfmt/clippy) so
formatting and lints are reproducible. With [`just`](https://github.com/casey/just)
and Node.js installed, one command bootstraps a conformance-ready checkout:

```bash
just setup
```

which runs: submodule init (TypeScript + test262 parser corpus), `npm ci` in
`typecheck-ts-harness`, `cargo generate-lockfile`, a sanity
`cargo check -p typecheck-ts-harness --locked`, and a probe that the pinned
`typescript` npm package loads. Safe to re-run.

**Lockfile policy**: `Cargo.lock` is deliberately untracked (library workspace). CI
generates it fresh and then runs everything `--locked`; locally run
`cargo generate-lockfile` first if you want CI-identical resolution.

**Submodules** (all optional unless you need the corpus):

```bash
git submodule update --init --recursive parse-js/tests/TypeScript   # TS conformance corpus (~575MB)
git submodule update --init test262/data                            # parser tests (~21MB)
git submodule update --init --recursive test262-semantic/data       # full test262 (~235MB, VM)
```

## Everyday commands

```bash
just fmt / fmt-fix          # rustfmt check / apply (2-space; .rustfmt.toml)
just fmt-js / fmt-js-fix    # prettier over workflows, nodejs pkg, debugger UI, harness scripts
just utf8-apis              # guard: no public &[u8]/Vec<u8> source-text APIs
just diagnostic-codes       # guard: code prefix/collision hygiene
just clippy                 # correctness+suspicious denied; style/perf/pedantic allowed
just check                  # cargo check --workspace --all-targets
just test                   # cargo test --workspace
just docs                   # regenerate wiki/architecture/deps.md (dependency graph)
just lint                   # fmt + fmt-js + guards + clippy
just ci                     # the full local gauntlet + deps-graph drift check
```

The clippy stance is deliberate: `-D clippy::correctness -D clippy::suspicious`, with
style/complexity/perf/nursery/pedantic allowed — the signal stays actionable.

`./format` applies rustfmt and (when `npx` exists) prettier in one shot.

### Guard scripts (architecture rules as tests)

- `scripts/check_utf8_apis.sh` — forbids new public APIs taking `&[u8]`/`Vec<u8>` as
  source text (UTF-8 policy). Allowed exceptions: `pub fn fuzz_*` entrypoints and
  output buffers (`&mut Vec<u8>`). Exercised by `diagnostics/tests/utf8_api_guard.rs`
  too.
- `scripts/check_diagnostic_codes.sh` — scans all code-literal sites, validates
  prefixes against the [registry](../architecture/diagnostics.md#prefix-registry-repo-wide),
  and fails on malformed or cross-crate-colliding codes.
- `scripts/gen_deps_graph.sh` — regenerates the workspace dependency graph
  (`cargo metadata` → mermaid) into `wiki/architecture/deps.md`; CI diffs it, so
  structural changes must regenerate. Caveat: it includes optional deps as plain
  edges.

## Runnable examples

Compiled examples double as API documentation and CI compile-checks
(`cargo check --workspace --all-targets` builds them):

```bash
cargo run -p diagnostics --example diagnostics_basic        # build + render a Diagnostic
cargo run -p parse-js --example parse_js_basic              # parse with explicit options
cargo run -p hir-js --example basic_lowering                # lower + SpanMap lookups
cargo run -p semantic-js --example js_mode_basic            # bind/resolve + scope iteration
cargo run -p types-ts-interned --example types_ts_interned_basic  # intern + assignability
cargo run -p typecheck-ts --example memory_host_basic       # MemoryHost + queries
cargo run -p typecheck-ts --example json_snapshot           # versioned JSON snapshot
cargo run -p emit-js --example emit_js_basic                # minified emit
cargo run -p optimize-js --example optimize_js_basic        # SSA optimize + decompile
cargo run -p minify-js --example minify_js_basic            # end-to-end minify
```

All are in-memory (no filesystem I/O) and deterministic by design.

## CI

Workflows in `.github/workflows/` (summaries; YAML is authoritative):

- **`ci.yaml`** (push/PR): `fmt-js` (prettier); `test` — install pinned toolchain +
  ripgrep, generate lockfile, then `cargo fmt --check`, guard scripts, clippy (locked,
  all targets/features), `cargo check --workspace --all-targets --locked`,
  `cargo test --workspace --locked`, named hygiene re-runs (`emit-js` megatest
  fixpoint; `typecheck-ts` 1-vs-N determinism), deps-graph regeneration + drift
  check; a **`test262-parser`** job fetching `test262/data` and running the parser
  harness with manifest + `--fail-on new`, uploading the JSON report artifact.
- **`nightly.yaml`**: full validation (fmt/clippy/check/test/docs on a schedule),
  **ts-conformance** (upstream TS suite via the harness, sharded), a **difftsc live
  smoke** against pinned `typescript@5.9.3`
  (`RAYON_NUM_THREADS=2`, tiny suite, JSON artifact), and typecheck benches uploading
  `typecheck-ts-bench*.json` artifacts.
- **`bench.yaml`** — minify benchmark charts; **`cli.yaml`** / **`nodejs.yaml`** —
  release artifacts for the CLI/npm package; **`node-ci.yaml`** — Node-side checks.

CI parity locally = `just ci` (CI adds `--locked` after generating the lockfile).

## Release (minify-js product line)

`./version major|minor|patch` (Node script; absorbed from `version`): requires a clean
tree; pulls (when a remote exists); runs `cargo test`; bumps versions in lockstep
across `minify-js`, `minify-js-cli`, `minify-js-nodejs` (Cargo.toml + package.json)
and rewrites README version references (bench/CLI URLs); regenerates the lockfile;
runs `cargo test --workspace --locked`; commits with the version as message; tags
`v<version>`; `cargo publish -p minify-js` (CLI + Node bindings are `publish = false`);
pushes with tags. Other crates (`parse-js`, etc.) are versioned in their own
`Cargo.toml`s; workspace-internal deps are path+version via `[workspace.dependencies]`
so publishable crates can depend on each other cleanly.

## Conventions

- **UTF-8 everywhere**: source text is `&str`/`Arc<str>`; spans are UTF-8 byte
  offsets. Validate bytes at I/O boundaries.
- **Warning-free workspace**; match existing style (2-space rustfmt).
- **Deterministic outputs** at every public boundary — see
  [determinism](../architecture/determinism.md).
- Prettier (pinned 3.4.2) owns JS/TS/JSON formatting for: `version`, workflow YAMLs,
  the npm package, the debugger UI, harness scripts (`.prettierrc.json`,
  `.prettierignore`).
- Dependency changes are deliberate: workspace-level version pinning in the root
  `Cargo.toml` (note the reasoned `indexmap = "=2.5.0"` pin keeping one hashbrown);
  vendored patches live in `third_party/` (`derive-visitor` + macros, `socket2`) via
  `[patch.crates-io]`.
- Release profile: fat LTO, `codegen-units = 1`, stripped; `release-with-debug`
  inherits it with symbols for profiling.
