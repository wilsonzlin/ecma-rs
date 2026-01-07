use std::collections::{BTreeMap, HashMap};

use crate::api::{BodyId, DefId, FileId, TextRange};
use crate::semantic_js;
use crate::SymbolBinding;
use types_ts_interned::TypeId;

/// Export entry for [`ExportMap`].
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportEntry {
  /// Symbol backing the export.
  pub symbol: semantic_js::SymbolId,
  /// Definition associated with the export, if it originates locally.
  pub def: Option<DefId>,
  /// Inferred or annotated type for the export, if available.
  pub type_id: Option<TypeId>,
}

/// Mapping from export names to entries.
pub type ExportMap = BTreeMap<String, ExportEntry>;

#[derive(Clone, Debug)]
pub(super) struct Reexport {
  pub(super) from: FileId,
  pub(super) original: String,
  pub(super) alias: String,
  pub(super) type_only: bool,
  pub(super) span: TextRange,
}

#[derive(Clone, Debug)]
pub(super) struct ExportAll {
  pub(super) from: FileId,
  pub(super) type_only: bool,
}

#[derive(Clone)]
pub(super) struct FileState {
  pub(super) defs: Vec<DefId>,
  pub(super) exports: ExportMap,
  pub(super) bindings: HashMap<String, SymbolBinding>,
  pub(super) top_body: Option<BodyId>,
  pub(super) reexports: Vec<Reexport>,
  pub(super) export_all: Vec<ExportAll>,
}

