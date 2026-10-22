# Diagnostics

The single diagnostics story shared by every crate: one model, stable codes, one
renderer, deterministic ordering. Owned by the `diagnostics` crate. (Absorbed from
`docs/diagnostic-codes.md` and `diagnostics/README.md`, 2026-07.)

## Model

```rust
Diagnostic {
  code: DiagnosticCode,      // stable, e.g. "TS2322", "TC0005", "PS0012"
  severity: Error | Warning | Note | Help,
  message: String,           // human summary; NOT a stable API
  primary: Span,             // Span { file: FileId, range: TextRange } — UTF-8 byte offsets
  labels: Vec<Label>,        // related spans, primary/secondary
  notes: Vec<String>,        // free-form extra context
}
```

Design points:

- `DiagnosticCode` is `Cow<'static, str>` — borrowed statics in the common case, owned
  when deserialized.
- Canonical orderings ship with the crate: `Ord` (severity, code, span, message) for
  set semantics, and `diagnostic_cmp`/`sort_diagnostics` (file, span, code, severity,
  message, labels, notes) for user-facing order. Emit sorted at every public boundary.
- Rendering (`render::render_diagnostic`) is rustc-style: caret highlighting, label
  coalescing on shared lines, multi-file output ordered primary-first, tab expansion,
  clamping of out-of-bounds/mid-UTF-8 ranges, and eliding of long spans
  (`RenderOptions { max_lines_per_label, context_lines, render_secondary_files }`).
  Any `SourceProvider` (name + text per `FileId`) can back it; `SimpleFiles` is the
  trivial provider.

## Diagnostic vs fatal error

The contract every crate follows:

- **Diagnostic**: a user-facing issue with a stable code, primary span, and message.
  Accumulate them — users should see many issues per run. User-program errors are
  `Ok(...)` + diagnostics, never `Err`.
- **Fatal error (`Result::Err`)**: the host or pipeline cannot continue (I/O failure,
  missing dependency, unexpected panic). Not a diagnostic; CLIs exit non-zero.
- **Internal compiler errors**: never panic across a public API — convert to an
  `ICE0001` diagnostic (`diagnostics::ice(span, msg)` adds the "this is a bug" note)
  with minimal reproduction context.
- **Host/environment failures** that can be attributed to an input get `HOST0001` via
  `diagnostics::host_error(span, msg)`; without a span it uses a zero-length
  placeholder plus an explanatory note.
- **Cancellation** is transported internally as a panic payload
  (`diagnostics::Cancelled`) and surfaced as a `CANCEL####` diagnostic at the
  orchestration boundary; libraries never install global hooks, they accept an
  `AtomicBool` and check it.

Severity → exit code policy for CLIs: any `Error` diagnostic ⇒ exit 1; fatal errors ⇒
non-zero even with no diagnostics; warnings/notes only ⇒ exit 0.

## Stable codes

Codes are API. Once published, a code is never changed or reused for a different
meaning; deleted codes are never recycled. Tests assert on codes, not message text —
wording may evolve freely.

Format: `<PREFIX><NNNN>` (uppercase ASCII prefix, zero-padded 4-digit number), except
upstream TypeScript codes (`TS<NNNN>`/`TS<NNNNN>`), which we use verbatim where we
intentionally mirror `tsc` behavior so difftsc can compare code-for-code.

### Prefix registry (repo-wide)

| Prefix / format | Owner / source | Notes |
| --- | --- | --- |
| `PS####` | `parse-js` | Parser syntax errors (`parse-js/src/error.rs`, `SyntaxErrorType::code()`). |
| `BIND####` | `semantic-js` | Binder / name-resolution diagnostics (JS + TS binding). |
| `LOWER####` | `hir-js` | AST→HIR lowering warnings. |
| `TC####` | `typecheck-ts` | Repo-owned checker diagnostics (registry: `typecheck-ts/src/codes.rs`). |
| `TS####` / `TS#####` | TypeScript | Upstream `tsc` codes used for parity; treated as stable external identifiers. |
| `OPT####` | `optimize-js` | Optimizer diagnostics (e.g. `OPT0001` use-before-declaration, `OPT0002` unsupported syntax). |
| `EMIT####` | `emit-js` | Emitter/printer diagnostics. |
| `MINIFYTS####` | `minify-js` | TypeScript erasure/minification diagnostics. |
| `MINIFY####` | minify tooling | Currently the benchmark harness (`bench/minify-js`). |
| `CONF####` | `parse-js` tooling | Parser conformance runner. |
| `T262####` | `test262` tooling | test262 runner. |
| `VMJS####` | `vm-js` | VM-surfaced diagnostics (e.g. module-record syntax errors). Registered 2026-07-23 when the guard caught the prefix in use unregistered. |
| `HOST####` | `diagnostics` | Host/environment failures; shared across crates. |
| `ICE####` | `diagnostics` | Internal compiler errors; shared across crates. |
| `CANCEL####` | `typecheck-ts` | Cancellation (currently checker-specific). |
| `OOM####` | `typecheck-ts` | Out-of-memory (currently checker-specific). |
| `TEST####` | tests only | Reserved for tests/examples/snapshots; never user-facing. |

### Adding a new code

1. Pick the prefix of the crate/layer that *owns* the diagnostic. A genuinely new
   prefix requires updating: this registry, `diagnostics/README.md`, and
   `scripts/check_diagnostic_codes.sh` (so CI recognizes it).
2. Allocate the next free number sequentially within the prefix; never reuse deleted
   numbers.
3. Define the code at the crate's registry site — `parse-js/src/error.rs` for `PS`,
   `typecheck-ts/src/codes.rs` for `TC` (each `Code` there documents description,
   expected primary-span anchoring, labels, and auto-attached notes).
4. Run `just diagnostic-codes`; CI runs the same and fails on malformed prefixes or
   cross-crate collisions.

## Checker-specific conventions

`typecheck-ts/src/codes.rs` is a structured registry, not a string list: each `Code`
carries its description, where the primary span should anchor, and expected
labels/notes, and provides `error(...)`/`warning(...)` constructors that attach the
registered notes automatically. This keeps span anchoring and note text consistent
across emit sites, and gives tests a single import for asserting on codes. When we
mirror a `tsc` behavior, prefer the upstream `TS` code so differential runs line up;
use `TC` codes for behaviors that are ours (engine limits, host issues, deliberate
divergences).
