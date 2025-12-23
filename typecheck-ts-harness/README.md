# typecheck-ts-harness

Utilities for running TypeScript type-checker conformance tests.

## `difftsc`

The `difftsc` subcommand runs `tsc` via Node.js to produce structured diagnostics
for fixture suites and compares them to committed baselines.

```
cargo run -p typecheck-ts-harness -- difftsc --suite fixtures/difftsc --update-baselines
cargo run -p typecheck-ts-harness -- difftsc --suite fixtures/difftsc
```

- Fixtures live under `fixtures/<suite>/` and can be single files or directories
  containing multiple files. The test name matches the file stem or directory
  name.
- Baselines are stored in `baselines/<suite>/<test>.json` and contain normalized
  diagnostic codes and spans.
- Span comparison tolerance can be adjusted with `--span-tolerance`.
- Node execution lives behind the `with-node` feature (enabled by default). When
  the feature is disabled or `node` is unavailable, the command will skip
  instead of failing.

Dependencies:

- Node.js (`--node` can override the binary path)
- The `typescript` npm package available on the Node resolution path (e.g.
  `npm install typescript` in the repository root)

The Node wrapper lives at `scripts/tsc_wrapper.js` and returns JSON diagnostics
that include code, category, file, and span offsets.
