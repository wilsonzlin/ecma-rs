use serde::{Deserialize, Serialize};

use crate::lib_support::{CompilerOptions, FileKind};
use crate::program::{
  BodyCheckResult, BuiltinTypes, DefData, SymbolBinding, SymbolOccurrence, TypeStore,
};
use crate::{semantic_js, BodyId, DefId, Diagnostic, ExportMap, FileId, TextRange};
use types_ts_interned::{
  TypeId, TypeId as InternedTypeId, TypeParamId, TypeStoreSnapshot as InternedTypeStoreSnapshot,
};

/// Bumped whenever the on-disk snapshot schema changes in a breaking way.
pub const PROGRAM_SNAPSHOT_VERSION: u32 = 2;

/// File metadata captured in a snapshot, including an optional copy of the text
/// to allow offline reconstruction.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FileSnapshot {
  pub file: FileId,
  pub kind: FileKind,
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
}

/// Serialized view of a single definition entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DefSnapshot {
  pub def: DefId,
  pub data: DefData,
}

/// Minimal body metadata needed for offset and query mapping.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BodyDataSnapshot {
  pub id: BodyId,
  pub file: FileId,
  pub owner: Option<DefId>,
  pub expr_spans: Vec<TextRange>,
  pub pat_spans: Vec<TextRange>,
}

/// Stable, deterministic snapshot of a checked program suitable for caching and
/// offline queries.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProgramSnapshot {
  pub schema_version: u32,
  pub tool_version: String,
  pub compiler_options: CompilerOptions,
  pub roots: Vec<FileId>,
  pub files: Vec<FileSnapshot>,
  pub file_states: Vec<FileStateSnapshot>,
  pub def_data: Vec<DefSnapshot>,
  pub body_data: Vec<BodyDataSnapshot>,
  pub def_types: Vec<(DefId, TypeId)>,
  pub body_results: Vec<BodyCheckResult>,
  pub symbol_occurrences: Vec<(FileId, Vec<SymbolOccurrence>)>,
  pub symbol_to_def: Vec<(semantic_js::SymbolId, DefId)>,
  pub global_bindings: Vec<(String, SymbolBinding)>,
  pub diagnostics: Vec<Diagnostic>,
  pub type_store: TypeStore,
  pub interned_type_store: InternedTypeStoreSnapshot,
  pub interned_def_types: Vec<(DefId, InternedTypeId)>,
  pub interned_type_params: Vec<(DefId, Vec<TypeParamId>)>,
  pub builtin: BuiltinTypes,
  pub next_def: u32,
  pub next_body: u32,
  pub next_symbol: u32,
}
