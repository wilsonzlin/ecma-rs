extern crate semantic_js as semantic_js_crate;

use crate::api::{BodyId, DefId, Diagnostic, ExprId, FileId, FileKey, PatId, Span, TextRange};
use crate::check::overload::callable_signatures;
use crate::db::queries::VarInit;
use crate::db::spans::expr_at_from_spans;
use crate::db::{self, BodyCheckDb};
use crate::expand::ProgramTypeExpander as RefExpander;
use crate::files::FileOrigin;
use crate::lib_support::{CacheMode, CompilerOptions, FileKind, LibFile, LibManager};
use crate::profile::{CacheKind, CacheStat, QueryStats, QueryStatsCollector};
use crate::semantic_js;
use crate::type_queries::{
  IndexerInfo, PropertyInfo, PropertyKey, SignatureInfo, TypeKindSummary, TypeQueries,
};
use crate::{FatalError, HostError, Ice, SymbolBinding, SymbolInfo, SymbolOccurrence};
use hir_js::ids::MISSING_BODY;
use hir_js::{BinaryOp as HirBinaryOp, ExprKind as HirExprKind};
use semantic_js_crate::ts as sem_ts;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use types_ts_interned::{self as tti, RelateCtx, TypeId};

use super::check::caches::{CheckerCacheStats, CheckerCaches};
use super::check::relate_hooks;
use super::fatal_to_diagnostic;
use super::{
  display_type_from_state, lookup_interned_property_type, DefKind, ExplainTree, ExportMap,
  ProgramState, ProgramTypeExpander, TypeDisplay,
};

/// Environment provider for [`Program`].
pub trait Host: Send + Sync + 'static {
  /// Return the full text for a file.
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError>;
  /// Resolve a module specifier relative to `from`.
  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey>;

  /// Compiler options influencing lib selection and strictness.
  fn compiler_options(&self) -> CompilerOptions {
    CompilerOptions::default()
  }

  /// Additional library files to include alongside bundled libs.
  fn lib_files(&self) -> Vec<LibFile> {
    Vec::new()
  }

  /// Kind of the file; defaults to TypeScript.
  fn file_kind(&self, _file: &FileKey) -> FileKind {
    FileKind::Ts
  }
}

/// Per-body typing result. Expression and pattern IDs are local to the body.
#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodyCheckResult {
  pub(crate) body: BodyId,
  pub(crate) expr_types: Vec<TypeId>,
  pub(crate) expr_spans: Vec<TextRange>,
  pub(crate) pat_types: Vec<TypeId>,
  pub(crate) pat_spans: Vec<TextRange>,
  pub(crate) diagnostics: Vec<Diagnostic>,
  pub(crate) return_types: Vec<TypeId>,
}

impl BodyCheckResult {
  pub(crate) fn empty(body: BodyId) -> Arc<Self> {
    Arc::new(Self {
      body,
      expr_types: Vec::new(),
      expr_spans: Vec::new(),
      pat_types: Vec::new(),
      pat_spans: Vec::new(),
      diagnostics: Vec::new(),
      return_types: Vec::new(),
    })
  }

  /// Body identifier this result corresponds to.
  pub fn body(&self) -> BodyId {
    self.body
  }

  /// Diagnostics produced while checking this body.
  pub fn diagnostics(&self) -> &[Diagnostic] {
    &self.diagnostics
  }

  /// All expression types in evaluation order.
  pub fn expr_types(&self) -> &[TypeId] {
    &self.expr_types
  }

  /// All pattern types in evaluation order.
  pub fn pat_types(&self) -> &[TypeId] {
    &self.pat_types
  }

  /// Type for a specific expression, if known.
  pub fn expr_type(&self, expr: ExprId) -> Option<TypeId> {
    self.expr_types.get(expr.0 as usize).copied()
  }

  /// Type for a specific pattern, if known.
  pub fn pat_type(&self, pat: PatId) -> Option<TypeId> {
    self.pat_types.get(pat.0 as usize).copied()
  }

  /// Span for a specific expression.
  pub fn expr_span(&self, expr: ExprId) -> Option<TextRange> {
    self.expr_spans.get(expr.0 as usize).copied()
  }

  /// Span for a specific pattern.
  pub fn pat_span(&self, pat: PatId) -> Option<TextRange> {
    self.pat_spans.get(pat.0 as usize).copied()
  }

  /// Find the innermost expression covering the given offset.
  pub fn expr_at(&self, offset: u32) -> Option<(ExprId, TypeId)> {
    let (expr, _) = expr_at_from_spans(&self.expr_spans, offset)?;
    self.expr_type(expr).map(|ty| (expr, ty))
  }

  /// Spans for all expressions in this body.
  pub fn expr_spans(&self) -> &[TextRange] {
    &self.expr_spans
  }

  /// Spans for all patterns in this body.
  pub fn pat_spans(&self) -> &[TextRange] {
    &self.pat_spans
  }

  /// Types of all explicit return statements seen while checking the body.
  pub fn return_types(&self) -> &[TypeId] {
    &self.return_types
  }
}

pub(super) fn body_extent_from_spans(
  expr_spans: &[TextRange],
  pat_spans: &[TextRange],
) -> Option<TextRange> {
  let mut spans = expr_spans.iter().chain(pat_spans.iter());
  let first = spans.next().copied()?;
  let mut start = first.start;
  let mut end = first.end;
  for span in spans {
    start = start.min(span.start);
    end = end.max(span.end);
  }
  Some(TextRange::new(start, end))
}

/// Primary entry point for parsing and type checking.
pub struct Program {
  pub(super) host: Arc<dyn Host>,
  pub(super) roots: Vec<FileKey>,
  cancelled: Arc<AtomicBool>,
  state: std::sync::Mutex<ProgramState>,
  query_stats: QueryStatsCollector,
}

// Ensure the primary API surface is usable across threads.
const _: fn() = || {
  fn assert_send_sync<T: Send + Sync>() {}
  assert_send_sync::<Program>();
};

#[path = "api/cancellation.rs"]
mod cancellation;
#[path = "api/diagnostics.rs"]
mod diagnostics;
#[path = "api/display.rs"]
mod display;
#[path = "api/exports.rs"]
mod exports;
#[path = "api/files.rs"]
mod files;
#[path = "api/metadata.rs"]
mod metadata;
#[path = "api/symbols.rs"]
mod symbols;
#[path = "api/type_at.rs"]
mod type_at;
#[path = "api/type_queries.rs"]
mod type_queries;
#[path = "api/typing.rs"]
mod typing;

impl Program {
  fn ensure_not_cancelled(&self) -> Result<(), FatalError> {
    if self.cancelled.load(Ordering::Relaxed) {
      Err(FatalError::Cancelled)
    } else {
      Ok(())
    }
  }

  fn catch_fatal<R>(&self, f: impl FnOnce() -> Result<R, FatalError>) -> Result<R, FatalError> {
    match panic::catch_unwind(AssertUnwindSafe(f)) {
      Ok(res) => res,
      Err(payload) => match payload.downcast::<FatalError>() {
        Ok(fatal) => Err(*fatal),
        Err(payload) => match payload.downcast::<::diagnostics::Cancelled>() {
          Ok(_) => Err(FatalError::Cancelled),
          Err(payload) => {
            eprintln!("caught panic in catch_fatal");
            Err(FatalError::Ice(Ice::from_panic(payload)))
          }
        },
      },
    }
  }

  pub(super) fn lock_state(&self) -> std::sync::MutexGuard<'_, ProgramState> {
    self.state.lock().unwrap_or_else(|err| err.into_inner())
  }

  fn with_analyzed_state<R>(
    &self,
    f: impl FnOnce(&mut ProgramState) -> Result<R, FatalError>,
  ) -> Result<R, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.ensure_analyzed_result(&self.host, &self.roots)?;
      f(&mut state)
    })
  }

  fn with_interned_state<R>(
    &self,
    f: impl FnOnce(&mut ProgramState) -> Result<R, FatalError>,
  ) -> Result<R, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.ensure_interned_types(&self.host, &self.roots)?;
      f(&mut state)
    })
  }

  fn record_fatal(&self, fatal: FatalError) {
    let is_cancelled = matches!(fatal, FatalError::Cancelled);
    let diag = fatal_to_diagnostic(fatal);
    if !is_cancelled {
      let mut state = self.lock_state();
      state.diagnostics.push(diag);
    }
  }

  fn reset_state(&self) {
    let mut state = self.lock_state();
    state.reset_analysis_state();
    for key in self.roots.iter().cloned() {
      state.intern_file_key(key, FileOrigin::Source);
    }
  }

  fn fatal_to_diagnostics(&self, fatal: FatalError) -> Vec<Diagnostic> {
    let is_cancelled = matches!(fatal, FatalError::Cancelled);
    let diag = fatal_to_diagnostic(fatal);
    if !is_cancelled {
      let mut state = self.lock_state();
      state.diagnostics.push(diag.clone());
    }
    vec![diag]
  }

  fn builtin_unknown(&self) -> TypeId {
    let state = self.lock_state();
    state.interned_unknown()
  }
}
