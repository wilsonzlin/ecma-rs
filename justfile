default: lint

fmt:
  cargo fmt --all --check

fmt-fix:
  cargo fmt --all

utf8-apis:
  ./scripts/check_utf8_apis.sh

diagnostic-codes:
  ./scripts/check_diagnostic_codes.sh

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

lint: fmt utf8-apis diagnostic-codes clippy

ci: fmt utf8-apis diagnostic-codes clippy check test docs
  git diff --exit-code docs/deps.md
