#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required to run diagnostic code checks" >&2
  exit 1
fi

tmp="$(mktemp)"
sorted_tmp="$(mktemp)"
trap 'rm -f "$tmp" "$sorted_tmp"' EXIT

collect() {
  # ripgrep exits with 1 when there are no matches; that's not an error for us.
  rg "$@" >>"$tmp" || true
}

# Common rg options:
# - multiline: most call sites put the code on a separate line
# - -o + --replace: print "file:line:CODE" for each captured code
RG_COMMON=(
  --multiline
  --multiline-dotall
  --pcre2
  -n
  --no-heading
  --with-filename
  -g
  '*.rs'
  -o
)

# Diagnostic constructors that take a code as the first argument.
collect "${RG_COMMON[@]}" 'Diagnostic::(?:error|warning|note|help)\(\s*"([^"]+)"' --replace '$1'

# Diagnostic::new(severity, code, ...)
collect "${RG_COMMON[@]}" 'Diagnostic::new\(\s*[^,]+,\s*"([^"]+)"' --replace '$1'

# Explicit DiagnosticCode conversions.
collect "${RG_COMMON[@]}" 'DiagnosticCode::from\(\s*"([^"]+)"' --replace '$1'

# typecheck-ts registry (and other crates using Code::new).
collect "${RG_COMMON[@]}" 'Code::new\(\s*"([^"]+)"' --replace '$1'

# optimize-js helpers.
collect "${RG_COMMON[@]}" 'diagnostic_with_(?:span|range)\(\s*"([^"]+)"' --replace '$1'

# hir-js lowering helpers (`ctx.warn("LOWER0003", ...)`).
collect "${RG_COMMON[@]}" '\.warn\(\s*"([A-Z0-9]+)"' --replace '$1'

# diagnostics helpers that imply a fixed code.
collect -n --no-heading --with-filename -g'*.rs' -o '\bhost_error\(' --replace 'HOST0001'
collect -n --no-heading --with-filename -g'*.rs' -o '\bdiagnostics::ice\(' --replace 'ICE0001'

# parse-js parser codes are defined in a match and referenced via `SyntaxErrorType::code()`.
collect -n --no-heading --with-filename -o '"(PS[0-9]{4})"' parse-js/src/error.rs --replace '$1'

# emit-js defines codes in a match and threads them through a helper.
collect -n --no-heading --with-filename -o '"([A-Z]{2,}[A-Z0-9]*[0-9]{4,5})"' emit-js/src/lib.rs --replace '$1'

# minify-js currently stores its TS erase code in a const.
collect -n --no-heading --with-filename -o '"([A-Z]{2,}[A-Z0-9]*[0-9]{4,5})"' minify-js/src/ts_erase.rs --replace '$1'

sort -u "$tmp" >"$sorted_tmp"

python3 - "$sorted_tmp" <<'PY'
import re
import sys
from collections import defaultdict

LINE_RE = re.compile(r"^(?P<path>.*?):(?P<line>\d+):(?P<code>.+)$")

def crate_for_path(path):
    parts = path.split("/")
    if not parts:
        return "<unknown>"
    if parts[0] == "bench" and len(parts) >= 2:
        return f"bench/{parts[1]}"
    return parts[0]

class Rule:
    def __init__(self, name, regex, allowed_crates=None, shared=False):
        self.name = name
        self.regex = re.compile(regex)
        self.allowed_crates = set(allowed_crates) if allowed_crates is not None else None
        self.shared = shared

RULES = [
    Rule("PS", r"^PS\d{4}$", allowed_crates={"parse-js"}),
    Rule("BIND", r"^BIND\d{4}$", allowed_crates={"semantic-js"}),
    Rule("LOWER", r"^LOWER\d{4}$", allowed_crates={"hir-js"}),
    Rule("TC", r"^TC\d{4}$", allowed_crates={"typecheck-ts"}),
    Rule("TS", r"^TS\d{4,5}$", shared=True),
    Rule("OPT", r"^OPT\d{4}$", allowed_crates={"optimize-js"}),
    Rule("EMIT", r"^EMIT\d{4}$", allowed_crates={"emit-js"}),
    Rule("MINIFYTS", r"^MINIFYTS\d{4}$", allowed_crates={"minify-js"}),
    Rule("MINIFY", r"^MINIFY\d{4}$", allowed_crates={"bench/minify-js"}),
    Rule("CONF", r"^CONF\d{4}$", allowed_crates={"parse-js"}),
    Rule("T262", r"^T262\d{4}$", allowed_crates={"test262"}),
    Rule("HOST", r"^HOST\d{4}$", shared=True),
    Rule("ICE", r"^ICE\d{4}$", shared=True),
    Rule("CANCEL", r"^CANCEL\d{4}$", allowed_crates={"typecheck-ts"}),
    Rule("OOM", r"^OOM\d{4}$", allowed_crates={"typecheck-ts"}),
    Rule("TEST", r"^TEST\d{4}$", shared=True),
]

def classify(code):
    for rule in RULES:
        if rule.regex.match(code):
            return rule
    return None

occurrences = []
path_input = sys.argv[1]
with open(path_input, "r", encoding="utf-8") as f:
  for raw in f:
    raw = raw.rstrip("\n")
    if not raw:
        continue
    m = LINE_RE.match(raw)
    if not m:
        print(f"error: unexpected rg output line: {raw}", file=sys.stderr)
        sys.exit(1)
    path = m.group("path")
    line = int(m.group("line"))
    code = m.group("code")
    crate = crate_for_path(path)
    occurrences.append((path, line, code, crate))

invalid = []
wrong_crate = []

code_to_rule = {}
code_to_occ = defaultdict(list)
code_to_crates = defaultdict(set)

for path, line, code, crate in occurrences:
    rule = classify(code)
    if rule is None:
        invalid.append((path, line, code))
        continue
    code_to_rule.setdefault(code, rule)
    code_to_occ[code].append((path, line, crate))
    code_to_crates[code].add(crate)
    if rule.allowed_crates is not None and crate not in rule.allowed_crates:
        wrong_crate.append((path, line, code, crate, rule.allowed_crates))

collisions = []
for code, crates in code_to_crates.items():
    rule = code_to_rule.get(code)
    if rule is None or rule.shared:
        continue
    if len(crates) > 1:
        collisions.append((code, crates, code_to_occ[code]))

if invalid or wrong_crate or collisions:
    if invalid:
        print("error: malformed diagnostic codes found:", file=sys.stderr)
        for path, line, code in sorted(invalid):
            print(f"  {path}:{line}: {code}", file=sys.stderr)
        print(file=sys.stderr)

    if wrong_crate:
        print("error: diagnostic code prefix used outside its owning crate:", file=sys.stderr)
        for path, line, code, crate, allowed in sorted(wrong_crate):
            allowed_list = ", ".join(sorted(allowed))
            print(f"  {path}:{line}: {code} (crate={crate}; allowed={allowed_list})", file=sys.stderr)
        print(file=sys.stderr)

    if collisions:
        print("error: diagnostic code collisions across crates:", file=sys.stderr)
        for code, crates, occs in sorted(collisions, key=lambda item: item[0]):
            print(f"  {code} appears in: {', '.join(sorted(crates))}", file=sys.stderr)
            for path, line, crate in sorted(occs):
                print(f"    {path}:{line} (crate={crate})", file=sys.stderr)
        print(file=sys.stderr)

    print("hint: see docs/diagnostic-codes.md for the repo-wide policy", file=sys.stderr)
    sys.exit(1)

print(f"diagnostic code check passed ({len(code_to_rule)} unique codes, {len(occurrences)} locations)")
PY
