#!/usr/bin/env bash
set -euo pipefail

# Guard against new public APIs that accept raw &[u8] or Vec<u8> as source text.
# UTF-8 validation should happen at IO boundaries, and fuzz entrypoints are the
# only allowed byte-oriented public functions. Output buffers like &mut Vec<u8>
# are allowed.

repo_root="$(cd -- "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pattern_bytes='pub(?:\s*\([^)]*\))?(?:\s+(?:async|const|unsafe))*\s+fn\s+(?!fuzz_)[^(]+\([^)]*&\[u8\]'
pattern_vec='pub(?:\s*\([^)]*\))?(?:\s+(?:async|const|unsafe))*\s+fn\s+(?!fuzz_)[^(]+\((?![^)]*&mut\s*Vec<u8>)[^)]*Vec<u8>'

search_rs() {
  local pattern="$1"

  if command -v rg >/dev/null 2>&1; then
    rg --pcre2 --multiline -n "$pattern" "$repo_root" --glob '*.rs'
    return $?
  fi

  if command -v python3 >/dev/null 2>&1; then
    python3 - "$repo_root" "$pattern" <<'PY'
import os
import re
import sys

repo_root = sys.argv[1]
pattern = sys.argv[2]

rx = re.compile(pattern, re.MULTILINE)
found = False

skip_dirs = {".git", "target", "node_modules"}

for root, dirs, files in os.walk(repo_root):
  dirs[:] = [d for d in dirs if d not in skip_dirs]
  for file in files:
    if not file.endswith(".rs"):
      continue
    path = os.path.join(root, file)
    try:
      with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    except Exception as e:
      print(f"check_utf8_apis: failed to read {path}: {e}", file=sys.stderr)
      sys.exit(2)

    for m in rx.finditer(content):
      found = True
      before = content[: m.start()]
      line = before.count("\n") + 1
      col = m.start() - before.rfind("\n")
      rel = os.path.relpath(path, repo_root)
      print(f"{rel}:{line}:{col}:{m.group(0)}")

sys.exit(0 if found else 1)
PY
    return $?
  fi

  echo "error: need rg (ripgrep) or python3 for UTF-8 API checks" >&2
  return 2
}

if search_rs "$pattern_bytes"; then
  echo "error: public API taking &[u8] found; source text should use &str/Arc<str> (fuzz_* are allowed)" >&2
  exit 1
else
  status=$?
  if [[ $status -ne 1 ]]; then
    exit "$status"
  fi
fi

if search_rs "$pattern_vec"; then
  echo "error: public API taking Vec<u8> found; source text should use &str/Arc<str> (fuzz_* are allowed, &mut Vec<u8> outputs are fine)" >&2
  exit 1
else
  status=$?
  if [[ $status -ne 1 ]]; then
    exit "$status"
  fi
fi
