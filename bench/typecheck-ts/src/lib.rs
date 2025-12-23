//! Benchmark helpers for the TypeScript checker stack.
//!
//! This crate is focused on providing stable, deterministic micro-benchmarks
//! for parsing, lowering, binding, and a small toy type checking engine. The
//! actual checker is expected to replace the toy engine, but the harness keeps
//! the structure and data flows we want to measure.
//!
//! Run with `cargo bench -p typecheck-ts-bench`. To emit JSON alongside the human
//! summary, set `TYPECHECK_TS_BENCH_JSON=1` (preferred over passing `--json`
//! directly to `cargo bench`, which forwards arguments to all test binaries).

pub mod fixtures;
pub mod mini_types;
pub mod pipeline;

pub use fixtures::all_fixtures;
pub use fixtures::module_graph_fixtures;
pub use fixtures::Fixture;
pub use fixtures::ModuleGraphFixture;
pub use mini_types::assignability_stress;
pub use mini_types::control_flow_body;
pub use mini_types::generic_overload_body;
pub use mini_types::union_intersection_body;
pub use mini_types::CheckStats;
pub use mini_types::Relations;
pub use mini_types::TypeStore;
pub use pipeline::bind_module_graph;
pub use pipeline::bind_single_file;
pub use pipeline::lower_to_hir;
pub use pipeline::parse_only;
pub use pipeline::HirSummary;
