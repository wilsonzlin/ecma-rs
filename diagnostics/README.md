# Diagnostics policy

The `diagnostics` crate defines a single, shared contract for user-facing
diagnostics across parsing, binding, checking, and tooling. Diagnostics are the
structured messages we deliver to users; fatal errors are for situations where
the tool cannot continue and should bubble up as `Result::Err`.

## Diagnostic vs. fatal error

- **Diagnostic**: User-facing issue with a *stable* code, a primary span, and a
  human-readable message. Diagnostics should be accumulated where possible so
  users can see multiple issues in one run.
- **Fatal error (`Result::Err`)**: The host or pipeline failed (I/O, missing
  dependency, unexpected panic) and execution cannot continue. Fatal errors are
  not diagnostics and should cause the CLI to exit with a non-zero code.

## Required diagnostic fields

- **Code**: Stable, prefixed identifier (see registry below).
- **Primary span**: `Span { file: FileId, range: TextRange }` identifying the
  main location for the diagnostic.
- **Message**: Human-readable summary.
- **Labels/notes**: Optional related spans or extra context.

## Code prefix registry

Reserved, non-exhaustive prefixes:

- `PARSE####`: `parse-js` parser
- `BIND####`: `semantic-js` binder
- `TC####`: `typecheck-ts` type checker
- `OPT####`: `optimize-js`
- `MINIFY####`: `minify-js`
- `HOST####`: Host/environment failures
- `ICE####`: Internal compiler errors

## Severity and CLI exit codes

- `Error`: Blocks successful execution. CLIs must exit with a non-zero status
  (1 recommended) if any error diagnostics are emitted.
- `Warning`: Does not block success but should still be surfaced to users.
- `Note`/`Help`: Informational context attached to other diagnostics.

Fatal errors (I/O failures, panics) should also cause a non-zero exit code even
if no diagnostics were produced. A run with only warnings/notes should exit
with code 0.

## Helper API

- `ice(primary: Span, message: impl Into<String>) -> Diagnostic`: Shortcut for
  reporting an internal compiler error with code `ICE0001`.
- `host_error(primary: Option<Span>, message: impl Into<String>) -> Diagnostic`:
  Shortcut for host/environment failures with code `HOST0001`. Provide a span
  when available; otherwise a zero-length placeholder span is used.
