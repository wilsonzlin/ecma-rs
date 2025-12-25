default: lint

fmt:
  cargo fmt --all --check

clippy:
  cargo clippy --workspace --all-targets --all-features --
    -A clippy::style
    -A clippy::complexity
    -A clippy::perf
    -A clippy::nursery
    -A clippy::pedantic
    -D clippy::correctness
    -D clippy::suspicious

check:
  cargo check --workspace --all-targets

test:
  cargo test --workspace

docs:
  ./scripts/gen_deps_graph.sh

lint: fmt clippy

ci: fmt clippy check test docs
  git diff --exit-code docs/deps.md
