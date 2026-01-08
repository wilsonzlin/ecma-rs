# `test262-semantic`

`test262-semantic` is a language semantics runner for a **curated subset** of
[`tc39/test262`](https://github.com/tc39/test262).

It is intended to be wired up to the ecma-rs VM once it exists, while already
providing:

- deterministic discovery and sharding
- suite selection (curated subsets)
- expectation manifests (`skip`/`xfail`/`flaky`)
- timeouts (best-effort cooperative cancellation)
- stable, versioned JSON reports

## Corpus setup

This runner expects a `tc39/test262` checkout directory containing:

- `test/` (the tests)
- `harness/` (shared harness scripts like `assert.js`)

The full corpus is large, so it is intended to be kept as an **optional
submodule** at:

```
engines/ecma-rs/test262-semantic/data
```

From the FastRender repo root:

```bash
git -C engines/ecma-rs submodule update --init --recursive test262-semantic/data
```

When running inside the `ecma-rs` repo directly:

```bash
git submodule update --init --recursive test262-semantic/data
```

Alternatively, you can clone `test262` anywhere and pass `--test262-dir`:

```bash
git clone --depth=1 https://github.com/tc39/test262.git /path/to/test262
```

## Test IDs

Test IDs are normalized **forward-slash** paths relative to `test/` in the
test262 checkout, for example:

```
language/expressions/addition/S11.6.1_A2.1_T1.js
```

These IDs are used for suite selection, sharding, and expectation manifests.

## Suites

Suites are small TOML/JSON files that select tests by:

- explicit IDs (`tests = [...]`)
- include globs (`include = [...]`)
- exclude globs (`exclude = [...]`)

The runner ships with a built-in suite at `suites/smoke.toml`, usable via:

```bash
cargo run -p test262-semantic -- --suite smoke
```

If a suite lists an explicit test ID that does not exist in the checkout, the
runner errors with a clear message.

## Expectation manifests (skip/xfail/flaky)

`--manifest` points to a TOML/JSON file (shared format with other harnesses in
this workspace) containing entries like:

```toml
[[expectations]]
id = "language/expressions/addition/S11.6.1_A2.1_T1.js"
status = "xfail"
reason = "known VM bug"
tracking_issue = "https://github.com/…"
```

Matchers are applied in priority order:

1. exact `id`
2. `glob`
3. `regex`

## Strict-mode variants

For script tests, each file expands to up to two cases:

- `non_strict`
- `strict`

unless `flags` contains `onlyStrict` or `noStrict`.

If `flags` contains `module`, the test runs as a single `module` case.

## JSON reports

Use `--json` to write the versioned report to stdout, and `--report-path` to
write it to a file:

```bash
cargo run -p test262-semantic -- \
  --suite smoke \
  --json --report-path out/test262_semantic.json
```

## Executor

Until the ecma-rs VM exists, the crate defaults to a `stub_executor` feature
which makes the runner compile and provides a placeholder executor.

Once the VM lands, a follow-up change can implement the internal `Executor`
trait against it.

