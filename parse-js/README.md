## parse-js

`parse-js` provides the parser that powers the rest of this workspace. The
TypeScript conformance runners depend on the official TypeScript repository as a
git submodule.

To run the conformance suite locally you must first initialize the submodule:

```bash
git submodule update --init --recursive --depth=1 parse-js/tests/TypeScript
```

The parser conformance runner lives in `parse-js` behind the
`conformance-runner` feature:

```bash
cargo run -p parse-js --features conformance-runner --bin conformance_runner
```

If the `parse-js/tests/TypeScript` directory is missing or empty, the conformance
runner exits with setup instructions.
