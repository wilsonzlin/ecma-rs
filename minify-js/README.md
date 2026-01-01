# minify-js

Extremely fast JavaScript minifier, written in Rust.

## Goals

- Fully written in Rust for maximum compatibility with Rust programs and derivatives (FFI, WASM, embedded, etc.).
- Maximises performance on a single CPU core for simple efficient scaling and easy compatible integration.
- Minification of individual inputs/files only; no bundling (TypeScript is handled by erasing type-only syntax).
- Prefer minimal complexity and faster performance over maximum configurability and minimal extra compression.

## Performance

Comparison with esbuild, run on [common libraries](../bench).

<img width="400" alt="Chart showing speed of JS minifiers" src="https://static.wilsonl.in/minify-js/bench/0.6.0/total-times.svg"><img width="400" alt="Chart showing compression of JS minifiers" src="https://static.wilsonl.in/minify-js/bench/0.6.0/average-sizes.svg">

## Features

- Fast parsing via `parse-js` (JS/JSX/TS/TSX).
- TypeScript/TSX inputs are accepted: type-only syntax is erased before
  minification so the output is always JavaScript.
- Builds lexical scopes and resolves identifiers via `semantic-js` (including
  hoisting/TDZ metadata and dynamic-scope hazard marking).
- Deterministic identifier renaming (module exports preserved).
- Emits minified output via `emit-js` (minimal whitespace + ASI-safe statement
  separation).
- Supports ES2022 arbitrary module namespace identifiers (string literal
  import/export names and aliases).

## Limitations

- Identifier renaming is disabled when code contains `with` statements or direct calls to the global `eval` function to avoid changing runtime name resolution semantics.
- TypeScript constructs with runtime semantics (such as non-`declare` namespaces
  or `enum`s) are currently rejected during type erasure.
- Minification currently focuses on formatting + identifier renaming; advanced
  compression passes (constant folding, DCE, etc.) are still in progress.

## Usage

### CLI

Precompiled binaries are available for Linux, macOS (Intel and Apple Silicon), and Windows.

Download URLs (replace `VERSION` with the release tag, e.g. `0.6.0`):

- Linux x64: https://static.wilsonl.in/minify-js/cli/VERSION/linux-x86_64/minify-js
- macOS x64: https://static.wilsonl.in/minify-js/cli/VERSION/macos-x86_64/minify-js
- macOS arm64: https://static.wilsonl.in/minify-js/cli/VERSION/macos-arm64/minify-js
- Windows x64: https://static.wilsonl.in/minify-js/cli/VERSION/windows-x86_64/minify-js.exe

Use the `--help` argument for more details.

```bash
minify-js --mode global --input /path/to/src.js --output /path/to/output.min.js
```

### Rust

Add the dependency:

```toml
[dependencies]
minify-js = "0.6.0"
```

Call the method:

```rust
use minify_js::{TopLevelMode, minify};

let code: &str = "const main = () => { let my_first_variable = 1; };";
let mut out = Vec::new();
minify(TopLevelMode::Global, code, &mut out).unwrap();
assert_eq!(out.as_slice(), b"const main=()=>{let a=1;};");
```

`minify` returns a `Result<(), Vec<diagnostics::Diagnostic>>`, allowing you to
inspect structured diagnostics (including parse errors) when minification fails.

### Node.js

Install the dependency:

```bash
npm i @minify-js/node
```

Call the method (signature: `minify(topLevelType: "global" | "module", src: string | Buffer): Buffer`):

```typescript
import {minify} from "@minify-js/node";

const src = Buffer.from("let x = 1;", "utf-8");
const min = minify("global", src);
```

## In progress

- Combine and reorder declarations.
- Evaluation and folding of constant expressions.
- Removal of unreachable, unused, and redundant code.
- Inlining single-use declarations.
- Replacing if statements with conditional and logical expressions.
- Returning an explicit error on illegal code e.g. multiple declarations/exports with identical names.
- Much more inline, high level, and usage documentation.
- Simplify pattern parsing and minification.
- Micro-optimisations:
  - Unwrap string literal computed members, then identifier or number string members.
  - Replace `x === null || x === undefined` with `x == null`, where `x` is side-effect free.
  - Replace `typeof x === "undefined"` with `x === undefined`.
  - Using shorthand properties.
  - Replace `void x` with `x, undefined`.
  - Replace `return undefined` with `return`.
  - Replace `const` with `let`.
  - Hoist `let` and `const`.
  - Unwrapping blocks.
  - Unwrapping parentheses, altering expressions as necessary.
  - `if (...) return a; else if (...) return b; else return c` => `return (...) ? a : (...) ? b : c`.
