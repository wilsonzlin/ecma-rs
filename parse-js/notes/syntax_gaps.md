# Parser syntax gap tracker

Updated 2026-01-02.

The `parse-js` TypeScript conformance runner (`parse-js/src/bin/conformance_runner.rs`) now
consults TypeScript `.errors.txt` baselines and treats *expected* TypeScript **parse errors**
(generally TS1xxx) as passing. This lets us run “negative syntax” conformance tests without
maintaining a manual allowlist of expected failures.

When the runner reports a failure, it should indicate a real mismatch:
- TypeScript rejects the syntax, but `parse-js` accepts it (too permissive), or
- TypeScript accepts the syntax, but `parse-js` rejects it (a real syntax gap).

No unsupported valid syntactic constructs are currently tracked here; update this file when a
conformance run identifies a real parsing mismatch.

