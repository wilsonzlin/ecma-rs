# Contributing

This repository pins the Rust toolchain (including `rustfmt`) via `rust-toolchain.toml`
so formatting output is reproducible across CI and developer machines. If
`cargo fmt --all --check` fails unexpectedly, ensure you're using the pinned toolchain.

With [`just`](https://github.com/casey/just) and Node.js installed:

- `just setup` — submodules, harness npm deps, lockfile, sanity check
- `just ci` — full local mirror of the main CI checks (including the generated
  dependency graph under `wiki/architecture/deps.md`)

Everything else — workflows, conventions, examples, release flow, and engineering
doctrine — lives in the wiki:

- [wiki/engineering/workflows.md](./wiki/engineering/workflows.md)
- [wiki/meta/how-to-work.md](./wiki/meta/how-to-work.md)
