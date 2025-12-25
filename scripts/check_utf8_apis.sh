#!/usr/bin/env bash
set -euo pipefail

# Guard against new public APIs that accept raw &[u8] as source text. UTF-8
# validation should happen at IO boundaries, and fuzz entrypoints are the only
# allowed byte-oriented public functions.

if ! command -v rg >/dev/null 2>&1; then
  echo "error: rg (ripgrep) is required for UTF-8 API checks" >&2
  exit 1
fi

repo_root="$(cd -- "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pattern='pub(?:\s*\([^)]*\))?(?:\s+(?:async|const|unsafe))*\s+fn\s+(?!fuzz_)[^(]+\([^)]*&\[u8\]'

if rg --pcre2 --multiline -n "$pattern" "$repo_root" --glob '*.rs'; then
  echo "error: public API taking &[u8] found; source text should use &str/Arc<str> (fuzz_* are allowed)" >&2
  exit 1
else
  status=$?
  if [[ $status -ne 1 ]]; then
    exit "$status"
  fi
fi
