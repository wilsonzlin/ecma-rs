# Diagnostic codes

This repository uses **stable diagnostic codes** so that:

- downstream tools can reliably recognize specific diagnostics
- tests can assert on diagnostics without matching on fragile message text
- codes can remain stable even if messages, spans, or wording evolve

**Policy:** once a code is published/used, **do not change or reuse it** for a
different meaning.

## Format

Most repo-owned codes follow:

```
<PREFIX><NNNN>
```

- `PREFIX` is uppercase ASCII letters (and occasionally digits for legacy
  prefixes like `T262`).
- `NNNN` is a zero-padded 4-digit number.

### TypeScript (`TS`) codes

Some diagnostics intentionally use upstream TypeScript compiler codes to make it
easy to diff against `tsc`:

```
TS<NNNN>   or   TS<NNNNN>
```

These codes are owned by TypeScript; we treat them as stable external
identifiers.

## Prefix registry (repo-wide)

This table lists the prefixes currently used in this workspace and where they
come from.

| Prefix / format | Owner / source | Notes |
| --- | --- | --- |
| `PS####` | `parse-js` | Parser syntax errors (see `parse-js/src/error.rs`). |
| `BIND####` | `semantic-js` | Binder / name-resolution diagnostics (JS + TS binding). |
| `LOWER####` | `hir-js` | AST→HIR lowering warnings. |
| `TC####` | `typecheck-ts` | Repo-owned type checker diagnostics (see `typecheck-ts/src/codes.rs`). |
| `TS####` / `TS#####` | TypeScript | Upstream `tsc` diagnostic codes used for parity. |
| `OPT####` | `optimize-js` | Optimizer diagnostics. |
| `EMIT####` | `emit-js` | Emitter/printer diagnostics. |
| `MINIFYTS####` | `minify-js` | TypeScript erasure/minification diagnostics. |
| `MINIFY####` | `minify-js` tooling | Currently used by the benchmark harness (`bench/minify-js`). |
| `CONF####` | `parse-js` tooling | Parser conformance runner diagnostics. |
| `T262####` | `test262` tooling | test262 runner diagnostics. |
| `HOST####` | `diagnostics` | Host/environment failures (`diagnostics::host_error`). Shared across crates. |
| `ICE####` | `diagnostics` | Internal compiler errors (`diagnostics::ice`). Shared across crates. |
| `CANCEL####` | `typecheck-ts` | Cancellation diagnostics (currently typechecker-specific). |
| `OOM####` | `typecheck-ts` | Out-of-memory diagnostics (currently typechecker-specific). |
| `TEST####` | tests only | Reserved for tests/examples/snapshots; do not use for user-facing diagnostics. |

## Adding a new diagnostic code

1. **Pick the right prefix**
   - Use the prefix for the crate/layer that *owns the diagnostic* (table above).
   - If you believe a new prefix is required, update:
     - this document
     - `diagnostics/README.md` (high-level policy)
     - `scripts/check_diagnostic_codes.sh` (so CI recognizes it)

2. **Allocate the next free number**
   - Prefer allocating sequentially within the prefix namespace.
   - Do not reuse deleted codes.

3. **Define the code close to the diagnostic "registry" for that crate**
   - `parse-js`: `SyntaxErrorType::code()` in `parse-js/src/error.rs`
   - `typecheck-ts`: add a new entry in `typecheck-ts/src/codes.rs`
   - Other crates: keep code usage consistent and deterministic.

4. **Run the checker**

```
just diagnostic-codes
```

CI runs the same check and will fail on malformed prefixes or cross-crate
collisions.

