# Contributing

For an overview of the workspace and the intended architecture, start with
[`README.md`](./README.md), [`docs/architecture.md`](./docs/architecture.md), and
[`AGENTS.md`](./AGENTS.md).

This repository pins the Rust toolchain (including `rustfmt`) via `rust-toolchain.toml` so formatting output is reproducible across CI and developer machines. If `cargo fmt --all --check` fails unexpectedly, ensure you're using the pinned toolchain.

## Developer setup (recommended)

If you have [`just`](https://github.com/casey/just) and Node.js installed, start with:

- `just setup`

This bootstraps a clean checkout for TypeScript conformance work by:

- Initializing the required git submodules (TypeScript + test262 fixtures)
- Installing npm dependencies for `typecheck-ts-harness` (`npm ci`)
- Generating an untracked workspace `Cargo.lock`
- Running a cheap sanity check (`cargo check -p typecheck-ts-harness --locked`)
- Probing that the pinned `typescript` npm package is usable

This workspace is kept warning-free and treats `Cargo.lock` as a generated artifact (the repository is a library workspace). CI regenerates the lockfile and runs with `--locked`; generate one locally before running the same checks:

- `cargo generate-lockfile` (untracked because `Cargo.lock` is gitignored)
- `cargo fmt --all --check`
- `cargo clippy --workspace --all-targets --all-features --locked -- -A clippy::style -A clippy::complexity -A clippy::perf -A clippy::nursery -A clippy::pedantic -D clippy::correctness -D clippy::suspicious`
- `cargo check --workspace --all-targets --locked`
- `cargo test --workspace --locked`
- `./scripts/gen_deps_graph.sh` (or `just docs`) and ensure `git diff --exit-code docs/deps.md` is clean

To apply formatting fixes locally (as opposed to checking formatting), run `./format` (it runs `cargo fmt --all` and also runs prettier when `npx` is available).

Clippy focuses on correctness and suspicious lints while allowing the noisier style/complexity lints so the signal stays actionable.

If you have [`just`](https://github.com/casey/just) installed, the root `justfile` provides shortcuts:

- `just setup` bootstraps submodules + Node deps + lockfile + sanity checks
- `just submodules` fetches the required git submodules
- `just node-deps` installs `typecheck-ts-harness` npm dependencies
- `just lockfile` generates an untracked workspace `Cargo.lock`
- `just fmt` checks Rust formatting (CI uses the same check)
- `just fmt-fix` applies Rust formatting (`cargo fmt --all`)
- `just lint` runs formatting + sanity checks (`utf8-apis`, `diagnostic-codes`) + `clippy`
- `just ci` runs the full suite (`lint`, `check`, `test`, `docs`) and enforces `docs/deps.md` stays in sync
