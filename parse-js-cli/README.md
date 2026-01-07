# `parse-js-cli`

`parse-js-cli` is a small, deterministic debugging tool for the `parse-js` parser.

- Reads from a file (`--input <path>` or positional `<path>`) or stdin (default).
- Supports explicit dialect selection (`--dialect`) and module/script parsing (`--source-type`).
- Emits stable, versioned JSON on stdout.
- Can emit machine-readable JSON diagnostics via `--json-errors`.

## Usage

```sh
# Parse a file (dialect inferred from extension)
cargo run -p parse-js-cli -- path/to/file.tsx

# Parse stdin (defaults to TypeScript + module)
echo 'const x: number = 1' | cargo run -p parse-js-cli

# Force parsing as a script (rejects top-level import/export)
cargo run -p parse-js-cli -- --source-type script path/to/file.js

# Force parsing as JSX
cargo run -p parse-js-cli -- --dialect jsx path/to/file.js
```

### Dialect inference

When `--dialect` is omitted and the input is a file, the dialect is inferred from the file
extension:

- `.js` → `js`
- `.jsx` → `jsx`
- `.ts` → `ts`
- `.tsx` → `tsx`
- `.d.ts` → `dts`

If the input is stdin (no file path), the dialect defaults to `ts`.

### Source type

`--source-type` defaults to `module`.

Use `--source-type script` to parse in script mode, where `import` and `export` declarations are
rejected.

## Output format

On success, stdout is always JSON with a small envelope:

```json
{
  "schema_version": 1,
  "options": { "dialect": "ts", "source_type": "module" },
  "ast": { /* parser AST */ }
}
```

On failure:

- By default, diagnostics are rendered as human-readable text to stderr and the process exits
  non-zero.
- With `--json-errors`, diagnostics are emitted to stdout as JSON:

```json
{
  "schema_version": 1,
  "diagnostics": [ /* diagnostics::Diagnostic */ ]
}
```

