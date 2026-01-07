#!/usr/bin/env bash
set -euo pipefail

# Guard against new public APIs that accept raw &[u8] or Vec<u8> as source text.
# UTF-8 validation should happen at IO boundaries, and fuzz entrypoints are the
# only allowed byte-oriented public functions. Output buffers like &mut Vec<u8>
# are allowed.

if ! command -v rg >/dev/null 2>&1; then
  echo "error: rg (ripgrep) is required for UTF-8 API checks" >&2
  exit 1
fi

repo_root="$(cd -- "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pattern_bytes='pub(?:\s*\([^)]*\))?(?:\s+(?:async|const|unsafe))*\s+fn\s+(?!fuzz_)[^(]+\([^)]*&\[u8\]'
pattern_vec='pub(?:\s*\([^)]*\))?(?:\s+(?:async|const|unsafe))*\s+fn\s+(?!fuzz_)[^(]+\((?![^)]*&mut\s*Vec<u8>)[^)]*Vec<u8>'

if rg --pcre2 --multiline -n "$pattern_bytes" "$repo_root" --glob '*.rs'; then
  echo "error: UTF-8 source-text API policy violation: public API taking \`&[u8]\` found" >&2
  echo "help: accept source text as \`&str\` or \`Arc<str>\` and validate/convert bytes at IO boundaries" >&2
  echo "note: \`pub fn fuzz_*\` entrypoints are allowed to accept bytes" >&2
  echo "note: byte output buffers like \`&mut Vec<u8>\` are allowed" >&2
  echo "note: run \`just utf8-apis\` (or \`./scripts/check_utf8_apis.sh\`) to reproduce locally" >&2
  exit 1
else
  status=$?
  if [[ $status -ne 1 ]]; then
    exit "$status"
  fi
fi

if rg --pcre2 --multiline -n "$pattern_vec" "$repo_root" --glob '*.rs'; then
  echo "error: UTF-8 source-text API policy violation: public API taking \`Vec<u8>\` found" >&2
  echo "help: accept source text as \`&str\` or \`Arc<str>\` and validate/convert bytes at IO boundaries" >&2
  echo "note: \`pub fn fuzz_*\` entrypoints are allowed to accept bytes" >&2
  echo "note: byte output buffers like \`&mut Vec<u8>\` are allowed" >&2
  echo "note: run \`just utf8-apis\` (or \`./scripts/check_utf8_apis.sh\`) to reproduce locally" >&2
  exit 1
else
  status=$?
  if [[ $status -ne 1 ]]; then
    exit "$status"
  fi
fi
