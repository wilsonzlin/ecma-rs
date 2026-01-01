# test262 parser harness

This crate drives [`tc39/test262-parser-tests`](https://github.com/tc39/test262-parser-tests) against `parse-js`, producing stable JSON reports that are easy to archive in CI.

## Corpus setup

The parser tests live in a submodule:

```bash
git submodule update --init test262/data
```

The runner expects the following directories under `--data-dir`:

- `pass/` — programs that must parse successfully
- `pass-explicit/` — equivalent to `pass/` with explicit grouping
- `fail/` — programs that must fail to parse
- `early/` — programs that trigger early errors

Module vs. script mode is inferred from filenames containing `.module.` (e.g.
`*.module.js` → module, otherwise script).

## Running locally

```bash
cargo run -p test262 --release -- \
  --data-dir test262/data \
  --manifest test262/manifest.toml \
  --report-path reports/test262-parser.json \
  --fail-on new
```

Key flags:

- `--json` — emit the report to stdout (useful for piping)
- `--report-path` — write the JSON artifact to disk (pretty-printed)
- `--shard <index>/<total>` — run a deterministic subset of tests
- `--manifest` — apply skip/xfail/flaky expectations
- `--fail-on {all,new,none}` — control the exit code when mismatches are present (`new` only fails on unexpected results)

### Expectations manifest

The manifest mirrors `typecheck-ts-harness`:

```toml
[[expectations]]
id = "pass/bad.js"
status = "xfail"
reason = "template literal recovery gaps"

[[expectations]]
glob = "early/**/*.js"
status = "skip"
tracking_issue = "https://github.com/wilsonzlin/ecma-rs/issues/123"
```

`status` accepts `pass`, `skip`, `xfail`, or `flaky`. The matcher can be an exact `id`, a `glob`, or a `regex`; the first match wins, with exact > glob > regex.

The shipped manifest marks `fail/**`, `early/**`, and a handful of template literal edge cases as `xfail` until the parser rejects them; prune entries as coverage improves.

### Output

The JSON artifact is deterministic (schema version `1`) and includes:

- `summary` with pass/fail/skip counts and mismatch breakdown
- ordered `results` for every test (including expectation info)
- diagnostic code and byte span for any parse failures

Only unexpected mismatches are rendered to stderr; expected failures are still captured in the artifact.

## CI

`.github/workflows/ci.yaml` runs the harness when the corpus is available, uploads the JSON report artifact, and keeps shardable flags wired for future parallelization. Use the manifest to keep known gaps tracked without hiding regressions.
