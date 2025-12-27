//! Incremental salsa database for type checking and associated helpers.

pub mod expander;
pub mod inputs;
mod queries;

use crate::profile::{QueryKind, QueryStatsCollector, SalsaEventAdapter};

pub use inputs::{FileOrigin, Inputs};
pub use queries::{
  all_files, global_bindings, lower_hir, parse, parse_query_count, reset_parse_query_count,
  sem_hir, ts_semantics, Database, GlobalBindingsDb, LowerResultWithDiagnostics, TsSemantics,
  TypecheckDatabase, TypecheckStorage,
};

/// Concrete database implementing the `TypecheckDatabase` query group.
#[salsa::database(TypecheckStorage)]
#[derive(Default)]
pub struct TypecheckDb {
  storage: salsa::Storage<TypecheckDb>,
}

impl salsa::Database for TypecheckDb {}

impl salsa::ParallelDatabase for TypecheckDb {
  fn snapshot(&self) -> salsa::Snapshot<Self> {
    let db = TypecheckDb {
      storage: self.storage.snapshot(),
    };
    salsa::Snapshot::new(db)
  }
}

fn kind_from_debug_name(name: &str) -> Option<QueryKind> {
  match name {
    "parse" | "parse_file" => Some(QueryKind::Parse),
    "lower_hir" | "lower" => Some(QueryKind::LowerHir),
    "bind" | "bind_file" | "semantics" => Some(QueryKind::Bind),
    "type_of_def" | "type_of" => Some(QueryKind::TypeOfDef),
    "check_body" => Some(QueryKind::CheckBody),
    _ => None,
  }
}

fn debug_name_for_key(key: salsa::DatabaseKeyIndex) -> Option<String> {
  let debug = format!("{key:?}");
  debug.split_once('(').map(|(name, _)| name.to_string())
}

/// Best-effort mapping from salsa query keys (via their debug names) to
/// [`QueryKind`]. This keeps profiling aligned with the legacy query names.
pub fn query_kind_for_key(key: salsa::DatabaseKeyIndex) -> Option<QueryKind> {
  debug_name_for_key(key)
    .as_deref()
    .and_then(kind_from_debug_name)
}

/// Create a [`SalsaEventAdapter`] that will classify salsa events using the
/// default debug-name mapping. Database implementations should call
/// [`SalsaEventAdapter::on_event`] from their `salsa_event` hook and wrap their
/// tracked queries with [`SalsaEventAdapter::start_query`] to record timings.
pub fn profiler(collector: QueryStatsCollector) -> SalsaEventAdapter {
  SalsaEventAdapter::new(collector, query_kind_for_key)
}
