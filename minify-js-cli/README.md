# minify-js-cli

`minify-js-cli` is an extremely fast JavaScript/TypeScript minifier.

## Usage

Minify from stdin:

```bash
cat input.js | minify-js --mode global
```

Minify a file:

```bash
minify-js --mode module --input src/index.ts
```

Write minified output to a file (human mode):

```bash
minify-js --mode global --input input.js --output output.js
```

## `--mode`

`--mode` controls how the input is parsed:

- `--mode global`: parse as a script (non-module).
- `--mode module`: parse as an ES module.

## `--json`

`--json` switches stdout to a versioned, machine-consumable schema.

On success:

```json
{ "schema_version": 1, "mode": "global|module", "output": "<minified code>" }
```

On failure:

```json
{ "schema_version": 1, "mode": "global|module", "diagnostics": [ ... ] }
```

The `diagnostics` array contains `diagnostics::Diagnostic` values (with stable,
deterministic ordering).

`--output` may still be used to write the minified output to a file; JSON is
always written to stdout.

## Diagnostics + color

In human mode (the default), minified output is written to stdout and any
diagnostics are written to stderr with `context_lines = 1`.

Color defaults to auto-detection (enabled when stderr is a terminal). Override
with:

- `--color`: force-enable ANSI colors
- `--no-color`: disable ANSI colors

## Exit codes + errors

- Exit code `0`: minification succeeded.
- Exit code `1`: any error diagnostics were produced.

Input must be valid UTF-8. Invalid UTF-8 is rejected early with a host
diagnostic.

