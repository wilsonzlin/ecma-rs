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

Depending on `--harness`, it may also require:

- `harness/` (shared harness scripts like `assert.js`, `sta.js`)

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

The runner defaults `--test262-dir` to `test262-semantic/data`, so running from
the `ecma-rs` repo root requires no extra flags.

Quick sanity check (from `engines/ecma-rs/`):

```bash
cargo run -p test262-semantic -- list
# (or: cargo run -p test262-semantic -- --list)
```

Alternatively, you can clone `test262` anywhere and pass `--test262-dir`:

```bash
git clone --depth=1 https://github.com/tc39/test262.git /path/to/test262
```

## Harness modes (`--harness`)

Most test262 tests depend on harness files under `harness/` (either implicitly via the standard
`assert.js` / `sta.js` pair, or explicitly via the frontmatter `includes` list).

The runner supports multiple harness strategies:

- `--harness test262` (default): prepend `assert.js`, `sta.js`, then frontmatter `includes`.
  - Requires a `harness/` directory.
- `--harness includes`: prepend only frontmatter `includes` (no implicit `assert.js`/`sta.js`).
  - Requires a `harness/` directory.
- `--harness none`: prepend no harness files.
  - Does not require a `harness/` directory.
  - Many tests will fail due to missing harness globals; intended for early engine bring-up.

Note: strict-mode variants still begin with `'use strict';` before any included harness code so the
directive prologue isn't terminated by prepended scripts.

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

## Harness composition (`--harness`)

By default, the runner assembles each test as:

- `harness/assert.js`
- `harness/sta.js`
- any explicit `includes: [...]` from the test262 YAML frontmatter

all **deduplicated** (for example if a test explicitly lists `assert.js`).

If you are executing tests in a JS VM/host that provides the harness builtins
itself, pass:

```bash
cargo run -p test262-semantic -- --harness host
```

In `host` mode the runner does **not** automatically prepend `assert.js`/`sta.js`
(but it still inlines any explicit `includes` from YAML frontmatter). The
executor/host is expected to provide `assert`, `Test262Error`, and any other
globals normally defined by the default harness.

## JSON reports

Use `--json` to write the versioned report to stdout, and `--report-path` to
write it to a file:

```bash
cargo run -p test262-semantic -- \
  --suite smoke \
  --json --report-path out/test262_semantic.json
```

## Executor

By default, this runner uses a `vm-js`-backed executor (a small interpreter used
as early scaffolding for the eventual ecma-rs VM).

For wiring/CI experiments where you want the harness to run but always report
success, enable the `stub_executor` feature:

```bash
cargo run -p test262-semantic --features stub_executor -- --suite smoke
```
