#!/usr/bin/env bash
set -euo pipefail

# Runs only the tests listed in typescript_conformance_failures.txt.
# Accepts extra arguments passed to the conformance runner after `--`.

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

cargo test -p parse-js --test conformance_runner --features conformance-runner -- \
  --failures "${ROOT}/typescript_conformance_failures.txt" "$@"
