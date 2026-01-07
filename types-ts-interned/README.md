# `types-ts-interned`

Interned, deterministic TypeScript type representation + evaluator/relation engine.

## Runnable example

```bash
cargo run -p types-ts-interned --example basic
```

This example shows how to create a [`TypeStore`], intern structural types, and
run assignability checks via [`RelateCtx`].

## Fuzzing

This crate exposes a fuzz entry point behind the `fuzzing` feature:
`types_ts_interned::fuzz_type_graph(&[u8])`.

The `fuzz/type_graph` harness (wired up via `cargo-fuzz`) feeds arbitrary bytes
into `fuzz_type_graph`, which:

- Deserializes a (potentially cyclic) `TypeKind` graph from JSON.
- Builds interned types in a fresh `TypeStore`.
- Runs type evaluation/normalization and assignability checks with explicit
  depth/step limits.

Invariant: for any input, evaluation/relate must terminate and must not panic.

### Run

From the repo root:

```bash
# one-time
cargo install cargo-fuzz

# run the fuzzer
cargo fuzz run type_graph
```

This repo pins a stable toolchain, but `cargo fuzz` requires nightly-only
compiler flags for sanitizer coverage. The workspace config opts into
`RUSTC_BOOTSTRAP=1` so `cargo fuzz …` works out of the box.

If you prefer to use nightly explicitly, run:

```bash
cargo +nightly fuzz run type_graph
```
