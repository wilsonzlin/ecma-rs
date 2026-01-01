#!/usr/bin/env bash
set -euo pipefail

# Runs only the tests listed in typescript_conformance_failures.txt.
# Accepts extra arguments passed to the conformance runner after `--`.

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

cargo run -p parse-js --features conformance-runner --bin conformance_runner -- \
  --failures "${ROOT}/typescript_conformance_failures.txt" "$@"
