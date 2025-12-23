# Fuzzing and property testing

This workspace wires minimal guardrails around parsing, lowering, and type
operations using property tests and fuzz-friendly entry points.

## Running property tests

```
cargo test -p types-ts    # canon/idempotence + assignability termination
cargo test -p hir-js      # random source strings -> parse + lower, no panics
cargo test -p typecheck-ts
```

These tests are intentionally bounded (size-limited generators, recursion/step
caps) to avoid runaway cases while still catching panics.

## Fuzz entry points

Each crate exposes a `fuzzing` feature with a helper suitable for cargo-fuzz or
other fuzzers:

- `types-ts::fuzz_canon_and_assign`
- `hir-js::fuzz_lower`
- `typecheck-ts::fuzz_check`

You can wire these into a fuzz harness or call them directly under the
`fuzzing` feature. All entry points are designed to be panic-free and
self-bounding.
