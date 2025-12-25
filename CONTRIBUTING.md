# Contributing

This workspace is kept warning-free. Before opening a PR, please run the same checks that CI enforces:

- `cargo fmt --all --check`
- `cargo clippy --workspace --all-targets --all-features -- -A clippy::style -A clippy::complexity -A clippy::perf -A clippy::nursery -A clippy::pedantic -D clippy::correctness -D clippy::suspicious`
- `cargo check --workspace --all-targets`
- `cargo test --workspace`

Clippy focuses on correctness and suspicious lints while allowing the noisier style/complexity lints so the signal stays actionable.

If you have [`just`](https://github.com/casey/just) installed, the root `justfile` provides shortcuts:

- `just lint` runs `fmt` and `clippy`
- `just ci` runs the full `fmt` + `clippy` + `check` + `test` suite
