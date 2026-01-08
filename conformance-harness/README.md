# conformance-harness

Reusable, deterministic utilities for JavaScript/ECMAScript conformance runners.

This crate is VM-agnostic: it does **not** depend on `parse-js`, `semantic-js`, or
any runtime/VM implementation. It only provides shared harness mechanics:

- **Expectation manifests**: parse TOML or JSON manifests with deterministic
  precedence `id` (exact) > `glob` > `regex`.
- **Deterministic sharding**: `Shard` + `apply_shard`.
- **Cooperative timeouts**: `TimeoutManager` + `TimeoutGuard` using a generic
  cancellation token (supports `Arc<AtomicBool>` out of the box).
- **JSON report helpers**: pretty JSON writing to file/stdout + `FailOn` policy.

## Deterministic report output

To keep JSON output deterministic:

1. Use a stable ordering for your result list (e.g. sort by test id/path) before
   serializing.
2. Prefer deterministic map types (`BTreeMap`) over `HashMap` for any fields
   included in the serialized report.

## Report schema versioning

Runners should define their own schema version constant and use `ReportRef`:

```rust
use conformance_harness::ReportRef;

const REPORT_SCHEMA_VERSION: u32 = 1;

// ...
let report = ReportRef::new(REPORT_SCHEMA_VERSION, &summary, &results);
```

