//! Incremental salsa database for type checking and associated helpers.

pub mod expander;
pub mod inputs;
mod queries;

pub use inputs::{FileOrigin, Inputs};
pub use queries::{
  all_files, lower_hir, parse, parse_query_count, reset_parse_query_count, sem_hir, ts_semantics,
  Database, LowerResultWithDiagnostics, TsSemantics, TypecheckDatabase, TypecheckStorage,
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
