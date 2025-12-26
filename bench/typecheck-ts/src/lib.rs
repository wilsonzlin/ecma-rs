//! Benchmark helpers for the TypeScript checker stack.
//!
//! This crate is focused on providing stable, deterministic micro-benchmarks
//! for the real parsing, lowering, binding, and type checking pipeline.
//!
//! Run with `cargo bench -p typecheck-ts-bench`. To emit JSON alongside the human
//! summary, set `TYPECHECK_TS_BENCH_JSON=1` (preferred over passing `--json`
//! directly to `cargo bench`, which forwards arguments to all test binaries).

pub mod fixtures;
pub mod pipeline;

pub use fixtures::all_fixtures;
pub use fixtures::module_graph_fixtures;
pub use fixtures::Fixture;
pub use fixtures::ModuleGraphFixture;
pub use pipeline::assignability_micro;
pub use pipeline::bind_module_graph;
pub use pipeline::check_body_named;
pub use pipeline::check_body_with_warmups;
pub use pipeline::incremental_recheck;
pub use pipeline::lower_to_hir;
pub use pipeline::parse_and_lower;
pub use pipeline::parse_only;
pub use pipeline::summarize_hir;
pub use pipeline::type_of_exported_defs;
pub use pipeline::typecheck_fixture;
pub use pipeline::typecheck_fixture_with_options;
pub use pipeline::typecheck_module_graph;
pub use pipeline::typecheck_module_graph_with_options;
pub use pipeline::BindSummary;
pub use pipeline::BodyCheckSummary;
pub use pipeline::HirSummary;
pub use pipeline::IncrementalEdit;
pub use pipeline::IncrementalTimings;
pub use pipeline::RelationStats;
pub use pipeline::TypeOfDefSummary;
pub use pipeline::TypecheckSummary;
