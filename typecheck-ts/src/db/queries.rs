use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use diagnostics::{sort_diagnostics, Diagnostic, FileId};
use hir_js::{lower_file_with_diagnostics, FileKind as HirFileKind, LowerResult};
use semantic_js::ts as sem_ts;

use crate::db::inputs::{FileOrigin, Inputs};
use crate::lib_support::lib_env::{collect_libs, validate_libs};
use crate::lib_support::{FileKind, LibFile, LibManager};
use crate::queries::parse as parser;
use crate::sem_hir::sem_hir_from_lower;

#[derive(Debug, Clone)]
pub struct LowerResultWithDiagnostics {
  pub lowered: Option<Arc<LowerResult>>,
  pub diagnostics: Vec<Diagnostic>,
  pub file_kind: FileKind,
}

impl PartialEq for LowerResultWithDiagnostics {
  fn eq(&self, other: &Self) -> bool {
    let lowered_eq = match (&self.lowered, &other.lowered) {
      (Some(left), Some(right)) => Arc::ptr_eq(left, right),
      (None, None) => true,
      _ => false,
    };
    lowered_eq && self.diagnostics == other.diagnostics && self.file_kind == other.file_kind
  }
}

impl Eq for LowerResultWithDiagnostics {}

static PARSE_QUERY_CALLS: AtomicUsize = AtomicUsize::new(0);

/// Number of times the [`parse`] query has been executed (not served from cache).
pub fn parse_query_count() -> usize {
  PARSE_QUERY_CALLS.load(Ordering::Relaxed)
}

/// Reset the parse query execution counter.
pub fn reset_parse_query_count() {
  PARSE_QUERY_CALLS.store(0, Ordering::Relaxed);
}

#[derive(Clone)]
pub struct TsSemantics {
  pub semantics: Arc<sem_ts::TsProgramSemantics>,
  pub diagnostics: Arc<Vec<Diagnostic>>,
}

impl PartialEq for TsSemantics {
  fn eq(&self, other: &Self) -> bool {
    // Binder outputs are compared by identity; any dependency change rebuilds
    // semantics.
    Arc::ptr_eq(&self.semantics, &other.semantics) && self.diagnostics == other.diagnostics
  }
}

impl Eq for TsSemantics {}

impl std::fmt::Debug for TsSemantics {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TsSemantics")
      .field("semantics", &self.semantics)
      .field("diagnostics", &self.diagnostics)
      .finish()
  }
}

#[salsa::query_group(TypecheckStorage)]
pub trait TypecheckDatabase: salsa::Database {
  /// Full UTF-8 source text for a file.
  #[salsa::input]
  fn file_text(&self, file: FileId) -> Arc<str>;

  /// File kind, used to derive parsing and lowering options.
  #[salsa::input]
  fn file_kind(&self, file: FileId) -> FileKind;

  /// Root files for module graph traversal and semantics.
  #[salsa::input]
  fn roots(&self) -> Arc<Vec<FileId>>;

  /// Host-provided module resolution.
  #[salsa::input]
  fn module_resolve(&self, from: FileId, specifier: Arc<str>) -> Option<FileId>;

  /// Parse source text into a `parse-js` AST with diagnostics.
  fn parse(&self, file: FileId) -> parser::ParseResult;

  /// Lower parsed AST into HIR with any diagnostics produced during lowering.
  fn lower_hir(&self, file: FileId) -> LowerResultWithDiagnostics;

  /// Semantic HIR derived from lowered HIR, suitable for binding and checking.
  fn sem_hir(&self, file: FileId) -> sem_ts::HirFile;

  /// All reachable files starting from [`roots`], following imports and
  /// re-exports.
  fn all_files(&self) -> Arc<Vec<FileId>>;

  /// Semantic binding result across all files, including diagnostics.
  fn ts_semantics(&self) -> Arc<TsSemantics>;
}

pub fn parse(db: &dyn TypecheckDatabase, file: FileId) -> parser::ParseResult {
  PARSE_QUERY_CALLS.fetch_add(1, Ordering::Relaxed);
  let kind = db.file_kind(file);
  let source = db.file_text(file);
  parser::parse(file, kind, &source)
}

pub fn lower_hir(db: &dyn TypecheckDatabase, file: FileId) -> LowerResultWithDiagnostics {
  let parsed = db.parse(file);
  let file_kind = db.file_kind(file);
  let mut diagnostics = parsed.diagnostics.clone();
  let lowered = parsed.ast.as_ref().map(|ast| {
    let (lowered, mut lower_diags) =
      lower_file_with_diagnostics(file, map_hir_file_kind(file_kind), ast);
    diagnostics.append(&mut lower_diags);
    Arc::new(lowered)
  });

  LowerResultWithDiagnostics {
    lowered,
    diagnostics,
    file_kind,
  }
}

pub fn sem_hir(db: &dyn TypecheckDatabase, file: FileId) -> sem_ts::HirFile {
  let lowered = db.lower_hir(file);
  if let Some(lowered) = lowered.lowered.as_ref() {
    sem_hir_from_lower(lowered)
  } else {
    empty_sem_hir(file, lowered.file_kind)
  }
}

pub fn all_files(db: &dyn TypecheckDatabase) -> Arc<Vec<FileId>> {
  let mut visited = BTreeSet::new();
  let mut queue: VecDeque<FileId> = db.roots().iter().copied().collect();
  while let Some(file) = queue.pop_front() {
    if !visited.insert(file) {
      continue;
    }
    let sem_hir = db.sem_hir(file);
    for import in sem_hir.imports.iter() {
      if let Some(target) = db.module_resolve(file, Arc::<str>::from(import.specifier.as_str())) {
        queue.push_back(target);
      }
    }
    for export in sem_hir.exports.iter() {
      match export {
        sem_ts::Export::Named(named) => {
          if let Some(specifier) = named.specifier.as_ref() {
            if let Some(target) = db.module_resolve(file, Arc::<str>::from(specifier.as_str())) {
              queue.push_back(target);
            }
          }
        }
        sem_ts::Export::All(all) => {
          if let Some(target) = db.module_resolve(file, Arc::<str>::from(all.specifier.as_str())) {
            queue.push_back(target);
          }
        }
        sem_ts::Export::ExportAssignment { .. } => {}
      }
    }
  }
  Arc::new(visited.into_iter().collect())
}

pub fn ts_semantics(db: &dyn TypecheckDatabase) -> Arc<TsSemantics> {
  let files = db.all_files();
  let mut diagnostics = Vec::new();
  let mut sem_hirs: HashMap<sem_ts::FileId, Arc<sem_ts::HirFile>> = HashMap::new();
  for file in files.iter() {
    let lowered = db.lower_hir(*file);
    diagnostics.extend(lowered.diagnostics.iter().cloned());
    sem_hirs.insert(sem_ts::FileId(file.0), Arc::new(db.sem_hir(*file)));
  }

  let mut roots: Vec<_> = db.roots().iter().map(|f| sem_ts::FileId(f.0)).collect();
  roots.sort();
  roots.dedup();
  let resolver = DbResolver { db };
  let (semantics, mut bind_diags) = sem_ts::bind_ts_program(&roots, &resolver, |file| {
    sem_hirs
      .get(&file)
      .cloned()
      .unwrap_or_else(|| Arc::new(empty_sem_hir(FileId(file.0), db.file_kind(FileId(file.0)))))
  });
  diagnostics.append(&mut bind_diags);
  sort_diagnostics(&mut diagnostics);
  Arc::new(TsSemantics {
    semantics: Arc::new(semantics),
    diagnostics: Arc::new(diagnostics),
  })
}

struct DbResolver<'db> {
  db: &'db dyn TypecheckDatabase,
}

impl<'db> sem_ts::Resolver for DbResolver<'db> {
  fn resolve(&self, from: sem_ts::FileId, specifier: &str) -> Option<sem_ts::FileId> {
    self
      .db
      .module_resolve(FileId(from.0), Arc::<str>::from(specifier))
      .map(|id| sem_ts::FileId(id.0))
  }
}

fn empty_sem_hir(file: FileId, kind: FileKind) -> sem_ts::HirFile {
  sem_ts::HirFile {
    file_id: sem_ts::FileId(file.0),
    module_kind: sem_ts::ModuleKind::Script,
    file_kind: match kind {
      FileKind::Dts => sem_ts::FileKind::Dts,
      FileKind::Js | FileKind::Ts | FileKind::Tsx | FileKind::Jsx => sem_ts::FileKind::Ts,
    },
    decls: Vec::new(),
    imports: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  }
}

fn map_hir_file_kind(kind: FileKind) -> HirFileKind {
  match kind {
    FileKind::Dts => HirFileKind::Dts,
    FileKind::Js => HirFileKind::Js,
    FileKind::Ts => HirFileKind::Ts,
    FileKind::Tsx => HirFileKind::Tsx,
    FileKind::Jsx => HirFileKind::Jsx,
  }
}

#[derive(Clone, Debug, Default)]
struct Cached<T> {
  value: Option<T>,
  revision: u64,
}

#[derive(Clone, Debug, Default)]
struct LibFilesState {
  value: Option<Arc<[LibFile]>>,
  revision: u64,
  diagnostics: Vec<Diagnostic>,
  lib_ids: Vec<FileId>,
  lib_texts: HashMap<FileId, Arc<str>>,
}

/// Derived queries for lib loading and file aggregation.
#[derive(Clone, Debug)]
pub struct Database {
  pub inputs: Inputs,
  lib_manager: Arc<LibManager>,
  lib_files: LibFilesState,
  all_files: Cached<Arc<[FileId]>>,
  effective_file_text: HashMap<FileId, Cached<Arc<str>>>,
}

impl Database {
  /// Create a new database with a fresh [`LibManager`].
  pub fn new() -> Self {
    Self::with_lib_manager(Arc::new(LibManager::new()))
  }

  /// Create a database backed by a specific [`LibManager`].
  pub fn with_lib_manager(lib_manager: Arc<LibManager>) -> Self {
    Database {
      inputs: Inputs::default(),
      lib_manager,
      lib_files: LibFilesState::default(),
      all_files: Cached::default(),
      effective_file_text: HashMap::new(),
    }
  }

  /// Access the lib manager backing this database.
  pub fn lib_manager(&self) -> &LibManager {
    &self.lib_manager
  }

  /// Intern a file key with the provided origin.
  pub fn intern_file(&mut self, key: crate::FileKey, origin: FileOrigin) -> FileId {
    self.inputs.intern_file(key, origin)
  }

  fn compute_lib_files(&mut self) -> Arc<[LibFile]> {
    let dep_rev = std::cmp::max(
      self.inputs.compiler_options_revision(),
      self.inputs.host_libs_revision(),
    );
    if let Some(value) = self.lib_files.value.as_ref() {
      if self.lib_files.revision == dep_rev {
        return Arc::clone(value);
      }
    }

    let options = self.inputs.compiler_options().clone();
    let host_libs = self.inputs.host_libs().as_ref().to_vec();
    let libs = collect_libs(&options, host_libs, &self.lib_manager);
    let validated = validate_libs(libs, |lib| {
      self.inputs.intern_file(lib.key.clone(), FileOrigin::Lib)
    });

    let mut lib_ids = Vec::new();
    let mut lib_texts = HashMap::new();
    let mut dts_libs = Vec::new();
    for (lib, file_id) in validated.libs.into_iter() {
      lib_ids.push(file_id);
      lib_texts.insert(file_id, Arc::clone(&lib.text));
      self.inputs.set_file_kind(file_id, FileKind::Dts);
      dts_libs.push(lib);
    }
    let value = Arc::from(dts_libs.into_boxed_slice());

    self.lib_files = LibFilesState {
      value: Some(Arc::clone(&value)),
      revision: dep_rev,
      diagnostics: validated.diagnostics,
      lib_ids,
      lib_texts,
    };
    value
  }

  /// Libraries to include alongside reachable source files.
  pub fn lib_files(&mut self) -> Arc<[LibFile]> {
    self.compute_lib_files()
  }

  /// Diagnostics produced while loading libraries.
  pub fn lib_diagnostics(&mut self) -> &[Diagnostic] {
    self.compute_lib_files();
    &self.lib_files.diagnostics
  }

  /// IDs for all known libraries, in a deterministic order.
  pub fn lib_file_ids(&mut self) -> Vec<FileId> {
    self.compute_lib_files();
    self.lib_files.lib_ids.clone()
  }

  /// All files that may participate in checking, including libraries.
  pub fn all_files(&mut self) -> Arc<[FileId]> {
    let lib_revision = {
      self.compute_lib_files();
      self.lib_files.revision
    };
    let dep_rev = std::cmp::max(self.inputs.reachable_files_revision(), lib_revision);
    if let Some(value) = self.all_files.value.as_ref() {
      if self.all_files.revision == dep_rev {
        return Arc::clone(value);
      }
    }

    let mut seen = HashSet::new();
    let mut ordered = Vec::new();

    for file in self.inputs.reachable_files().iter().copied() {
      if seen.insert(file) {
        ordered.push(file);
      }
    }

    for file in self.lib_files.lib_ids.iter().copied() {
      if seen.insert(file) {
        ordered.push(file);
      }
    }

    let value = Arc::from(ordered.into_boxed_slice());
    self.all_files = Cached {
      value: Some(Arc::clone(&value)),
      revision: dep_rev,
    };
    value
  }

  /// Source text for a file, preferring lib contents when applicable.
  pub fn effective_file_text(&mut self, file: FileId) -> Option<Arc<str>> {
    let lib_revision = {
      self.compute_lib_files();
      self.lib_files.revision
    };
    let dep_rev = std::cmp::max(lib_revision, self.inputs.file_text_revision(file));
    if let Some(cached) = self.effective_file_text.get(&file) {
      if cached.revision == dep_rev {
        return cached.value.clone();
      }
    }

    let text = if let Some(text) = self.lib_files.lib_texts.get(&file) {
      Some(Arc::clone(text))
    } else {
      self.inputs.file_text(file).cloned()
    };

    self.effective_file_text.insert(
      file,
      Cached {
        value: text.clone(),
        revision: dep_rev,
      },
    );
    text
  }
}
