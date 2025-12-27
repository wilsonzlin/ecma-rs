//! Incremental salsa database for type checking and associated helpers.

use std::sync::OnceLock;

use dashmap::DashMap;
use salsa::{Database as SalsaDatabase, RuntimeId};

pub mod expander;
pub mod inputs;
mod queries;

use crate::profile::{QueryKind, QueryStatsCollector, QueryTimer, SalsaEventAdapter};

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
  profiler: Option<SalsaEventAdapter>,
}

impl TypecheckDb {
  /// Attach a profiler to this database. Events and query timings will be
  /// recorded into the supplied collector.
  pub fn set_profiler(&mut self, collector: QueryStatsCollector) {
    let adapter = profiler(collector);
    register_profiler(self.salsa_runtime().id(), adapter.clone());
    self.profiler = Some(adapter);
  }
}

impl salsa::Database for TypecheckDb {
  fn salsa_event(&self, event_fn: salsa::Event) {
    if let Some(adapter) = lookup_profiler(event_fn.runtime_id) {
      adapter.on_event(&event_fn);
    }
  }
}

impl salsa::ParallelDatabase for TypecheckDb {
  fn snapshot(&self) -> salsa::Snapshot<Self> {
    let db = TypecheckDb {
      storage: self.storage.snapshot(),
      profiler: self.profiler.clone(),
    };
    if let Some(adapter) = db.profiler.as_ref() {
      register_profiler(db.salsa_runtime().id(), adapter.clone());
    }
    salsa::Snapshot::new(db)
  }
}

fn kind_from_debug_name(name: &str) -> Option<QueryKind> {
  match name {
    "parse" | "parse_file" => Some(QueryKind::Parse),
    "lower_hir" | "lower" => Some(QueryKind::LowerHir),
    "bind" | "bind_file" | "semantics" | "ts_semantics" => Some(QueryKind::Bind),
    "sem_hir" => Some(QueryKind::LowerHir),
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

pub(crate) fn start_timer(db: &dyn TypecheckDatabase, kind: QueryKind) -> Option<QueryTimer> {
  let runtime_id = db.salsa_runtime().id();
  lookup_profiler(runtime_id).map(|adapter| adapter.collector().timer(kind, false))
}

/// Create a [`SalsaEventAdapter`] that will classify salsa events using the
/// default debug-name mapping. Database implementations should call
/// [`SalsaEventAdapter::on_event`] from their `salsa_event` hook and wrap their
/// tracked queries with [`SalsaEventAdapter::start_query`] to record timings.
pub fn profiler(collector: QueryStatsCollector) -> SalsaEventAdapter {
  SalsaEventAdapter::new(collector, query_kind_for_key)
}

fn profilers() -> &'static DashMap<RuntimeId, SalsaEventAdapter> {
  static PROFILERS: OnceLock<DashMap<RuntimeId, SalsaEventAdapter>> = OnceLock::new();
  PROFILERS.get_or_init(DashMap::new)
}

fn register_profiler(id: RuntimeId, profiler: SalsaEventAdapter) {
  profilers().insert(id, profiler);
}

fn lookup_profiler(id: RuntimeId) -> Option<SalsaEventAdapter> {
  profilers().get(&id).map(|p| p.clone())
}
