//! Incremental salsa database for type checking and associated helpers.

pub mod expander;
mod queries;

pub use queries::{
  lower_hir, parse, parse_query_count, reset_parse_query_count, sem_hir, LowerResultWithDiagnostics,
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
