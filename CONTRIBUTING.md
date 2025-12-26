# Contributing

This workspace is kept warning-free and treats `Cargo.lock` as a generated artifact (the repository is a library workspace). CI regenerates the lockfile and runs with `--locked`; generate one locally before running the same checks:

- `cargo generate-lockfile` (untracked because `Cargo.lock` is gitignored)
- `cargo fmt --all --check`
- `cargo clippy --workspace --all-targets --all-features --locked -- -A clippy::style -A clippy::complexity -A clippy::perf -A clippy::nursery -A clippy::pedantic -D clippy::correctness -D clippy::suspicious`
- `cargo check --workspace --all-targets --locked`
- `cargo test --workspace --locked`
- `./scripts/gen_deps_graph.sh` (or `just docs`) and ensure `git diff --exit-code docs/deps.md` is clean

Clippy focuses on correctness and suspicious lints while allowing the noisier style/complexity lints so the signal stays actionable.

If you have [`just`](https://github.com/casey/just) installed, the root `justfile` provides shortcuts:

- `just lint` runs `fmt` and `clippy`
- `just ci` runs the full `fmt` + `clippy` + `check` + `test` suite and enforces `docs/deps.md` stays in sync
