# typecheck-ts-cli

Standalone CLI for running the `typecheck-ts` engine against on-disk TypeScript
sources.

## Usage

```bash
cargo run -p typecheck-ts-cli -- typecheck fixtures/basic.ts

# Request extra output:
cargo run -p typecheck-ts-cli -- typecheck fixtures/basic.ts \
  --type-at fixtures/basic.ts:42 \
  --symbol-at fixtures/basic.ts:17 \
  --exports fixtures/basic.ts

# Emit structured JSON (diagnostics + query results)
cargo run -p typecheck-ts-cli -- typecheck fixtures/basic.ts --json
```

### Options

- `--json`: emit `{ diagnostics, queries }` as JSON with deterministic ordering.
- `--type-at <file:offset>`: inferred type at a byte offset within the file.
- `--symbol-at <file:offset>`: resolved symbol information at an offset.
- `--exports <file>`: export map for the file with symbol/type information.
- `--lib <name>`: explicit lib set (e.g. `es2020`, `dom`); overrides defaults.
- `--no-default-lib`: disable bundled libs.
- `--target`: select target lib set (`es5`, `es2015`, …).
- `--node-resolve`: enable Node/TS-style resolution (including `node_modules`).
- `--trace` / `--profile`: emit tracing spans in JSON (compatible with the
  harness profiling format).

### Encoding

Source files are read as UTF-8. Offsets passed to `--type-at`/`--symbol-at` are
byte offsets in that UTF-8 text; invalid encodings cause the CLI to exit with an
error before rendering diagnostics.

### Module resolution

By default, imports are resolved relative to the importing file, checking
`<spec>.ts`, `<spec>.d.ts`, `<spec>.tsx`, `<spec>.js`, and `<spec>.jsx` plus
`index.*` variants. `--node-resolve` additionally walks up the directory tree
looking in `node_modules/`.

### Diagnostics

Human output uses `diagnostics::render` with file context. JSON output uses
stable ordering for diagnostics and query results to ease consumption by other
tools.
