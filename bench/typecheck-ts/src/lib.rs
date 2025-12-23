//! Benchmark helpers for the TypeScript checker stack.
//!
//! This crate is focused on providing stable, deterministic micro-benchmarks
//! for parsing, lowering, binding, and a small toy type checking engine. The
//! actual checker is expected to replace the toy engine, but the harness keeps
//! the structure and data flows we want to measure.
//!
//! Run with `cargo bench -p typecheck-ts`. To emit JSON alongside the human
//! summary, set `TYPECHECK_TS_BENCH_JSON=1` (preferred over passing `--json`
//! directly to `cargo bench`, which forwards arguments to all test binaries).

pub mod fixtures;
pub mod mini_types;
pub mod pipeline;

pub use fixtures::{all_fixtures, module_graph_fixtures, Fixture, ModuleGraphFixture};
pub use mini_types::{assignability_stress, control_flow_body, generic_overload_body, union_intersection_body};
pub use mini_types::{CheckStats, Relations, TypeStore};
pub use pipeline::{bind_module_graph, bind_single_file, lower_to_hir, parse_only, HirSummary};
