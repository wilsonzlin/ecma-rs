default: lint

setup: submodules node-deps lockfile
  cargo check -p typecheck-ts-harness --locked
  node typecheck-ts-harness/scripts/typescript_probe.js

submodules:
  git submodule update --init --recursive parse-js/tests/TypeScript
  git submodule update --init test262/data

node-deps:
  cd typecheck-ts-harness && npm ci

lockfile:
  cargo generate-lockfile

fmt:
  cargo fmt --all --check

fmt-fix:
  cargo fmt --all

fmt-js:
  npx --yes prettier@3.4.2 --check
    'version'
    '.github/workflows/*.yaml'
    'minify-js-nodejs/**/*.{js,json,ts,d.ts}'
    'optimize-js-debugger/src/**/*.{ts,tsx,css,html}'
    'optimize-js-debugger/*.ts'
    'typecheck-ts-harness/scripts/*.js'

fmt-js-fix:
  npx --yes prettier@3.4.2 --write
    'version'
    '.github/workflows/*.yaml'
    'minify-js-nodejs/**/*.{js,json,ts,d.ts}'
    'optimize-js-debugger/src/**/*.{ts,tsx,css,html}'
    'optimize-js-debugger/*.ts'
    'typecheck-ts-harness/scripts/*.js'

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

lint: fmt fmt-js utf8-apis diagnostic-codes clippy

ci: fmt fmt-js utf8-apis diagnostic-codes clippy check test docs
  git diff --exit-code docs/deps.md
