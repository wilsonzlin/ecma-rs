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

lint: fmt clippy

ci: fmt clippy check test
