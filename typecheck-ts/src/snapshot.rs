use serde::{Deserialize, Serialize};

use crate::api::TextRange;
use crate::lib_support::{CompilerOptions, FileKind};
use crate::program::{BodyCheckResult, BuiltinTypes, DefData, TypeStore};
use crate::symbols::{semantic_js, SymbolBinding, SymbolOccurrence};
use crate::{BodyId, DefId, Diagnostic, ExportMap, FileId, FileKey};
use types_ts_interned::{
  TypeId, TypeId as InternedTypeId, TypeParamId, TypeStoreSnapshot as InternedTypeStoreSnapshot,
};

/// Bumped whenever the on-disk snapshot schema changes in a breaking way.
pub const PROGRAM_SNAPSHOT_VERSION: u32 = 10;

/// File metadata captured in a snapshot, including an optional copy of the text
/// to allow offline reconstruction. Snapshots are hybrid: when `text` is `None`
/// the host must still be able to provide the source, but hashes are recorded
/// to allow higher-level caches to detect drift.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FileSnapshot {
  pub file: FileId,
  pub key: FileKey,
  pub kind: FileKind,
  /// Whether this file originated from bundled or host-provided libraries.
  pub is_lib: bool,
  pub hash: String,
  pub text: Option<String>,
}

/// Serialized view of a [`FileState`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FileStateSnapshot {
  pub file: FileId,
  pub defs: Vec<DefId>,
  pub exports: ExportMap,
  pub bindings: Vec<(String, SymbolBinding)>,
  pub top_body: Option<BodyId>,
  #[serde(default)]
  pub ambient_modules: Vec<AmbientModuleSnapshot>,
}

/// Serialized view of an ambient module.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AmbientModuleSnapshot {
  pub name: String,
  pub defs: Vec<DefId>,
  pub exports: ExportMap,
  pub bindings: Vec<(String, SymbolBinding)>,
  pub reexports: Vec<ReexportSnapshot>,
  pub export_all: Vec<ExportAllSnapshot>,
  pub ambient_modules: Vec<AmbientModuleSnapshot>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReexportSnapshot {
  pub from: FileId,
  pub original: String,
  pub alias: String,
  pub type_only: bool,
  pub span: TextRange,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExportAllSnapshot {
  pub from: FileId,
  pub type_only: bool,
  pub span: TextRange,
}

/// Serialized view of a single definition entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DefSnapshot {
  pub def: DefId,
  pub data: DefData,
}

/// Stable, deterministic snapshot of a checked program suitable for caching and
/// offline queries. Snapshots capture the file registry (including host-chosen
/// keys), compiler options, and cached query results so callers can restore
/// without re-parsing or re-checking.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProgramSnapshot {
  pub schema_version: u32,
  pub tool_version: String,
  pub compiler_options: CompilerOptions,
  pub roots: Vec<FileId>,
  pub files: Vec<FileSnapshot>,
  pub file_states: Vec<FileStateSnapshot>,
  pub def_data: Vec<DefSnapshot>,
  pub def_types: Vec<(DefId, TypeId)>,
  pub canonical_defs: Vec<((FileId, String), DefId)>,
  pub namespace_types: Vec<(DefId, TypeId)>,
  pub body_results: Vec<BodyCheckResult>,
  pub symbol_occurrences: Vec<(FileId, Vec<SymbolOccurrence>)>,
  pub symbol_to_def: Vec<(semantic_js::SymbolId, DefId)>,
  pub global_bindings: Vec<(String, SymbolBinding)>,
  pub diagnostics: Vec<Diagnostic>,
  pub type_store: TypeStore,
  pub interned_type_store: InternedTypeStoreSnapshot,
  pub interned_def_types: Vec<(DefId, InternedTypeId)>,
  pub enum_value_types: Vec<(DefId, InternedTypeId)>,
  pub interned_type_params: Vec<(DefId, Vec<TypeParamId>)>,
  pub value_def_map: Vec<(DefId, DefId)>,
  pub builtin: BuiltinTypes,
  pub next_def: u32,
  pub next_body: u32,
  pub next_symbol: u32,
}
