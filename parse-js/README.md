## parse-js

`parse-js` provides the parser that powers the rest of this workspace. The
TypeScript conformance runners depend on the official TypeScript repository as a
git submodule.

For a small, copy/paste-friendly parsing example (no filesystem I/O):

```bash
cargo run -p parse-js --example parse_js_basic
```

To run the conformance suite locally you must first initialize the submodule:

```bash
git submodule update --init --recursive --depth=1 parse-js/tests/TypeScript
```

The parser conformance runner lives in `parse-js` behind the
`conformance-runner` feature:

```bash
cargo run -p parse-js --features conformance-runner --bin conformance_runner
```

The runner enforces a per-test timeout (default 10 seconds) and uses cooperative
cancellation to abort stuck inputs without spawning an OS thread per test case.
If you need similar behavior in your own harness, `parse-js` also exposes a
`parse_with_options_cancellable` API that accepts an `Arc<AtomicBool>` cancel
flag.

If the `parse-js/tests/TypeScript` directory is missing or empty, the conformance
runner exits with setup instructions.
