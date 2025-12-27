use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId};
use hir_js::{lower_file_with_diagnostics, FileKind as HirFileKind, LowerResult};
use semantic_js::ts as sem_ts;

use crate::lib_support::FileKind;
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

#[salsa::query_group(TypecheckStorage)]
pub trait TypecheckDatabase: salsa::Database {
  /// Full UTF-8 source text for a file.
  #[salsa::input]
  fn file_text(&self, file: FileId) -> Arc<str>;

  /// File kind, used to derive parsing and lowering options.
  #[salsa::input]
  fn file_kind(&self, file: FileId) -> FileKind;

  /// Parse source text into a `parse-js` AST with diagnostics.
  fn parse(&self, file: FileId) -> parser::ParseResult;

  /// Lower parsed AST into HIR with any diagnostics produced during lowering.
  fn lower_hir(&self, file: FileId) -> LowerResultWithDiagnostics;

  /// Semantic HIR derived from lowered HIR, suitable for binding and checking.
  fn sem_hir(&self, file: FileId) -> sem_ts::HirFile;
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
