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
use hir_js::{BinaryOp as HirBinaryOp, ExprKind as HirExprKind};
use hir_js::ids::MISSING_BODY;
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

impl Program {
  /// Create a new program from a host and root file list.
  pub fn new(host: impl Host, roots: Vec<FileKey>) -> Program {
    Program::with_lib_manager(host, roots, Arc::new(LibManager::new()))
  }

  /// Create a new program with a provided lib manager (useful for observing invalidation in tests).
  pub fn with_lib_manager(
    host: impl Host,
    mut roots: Vec<FileKey>,
    lib_manager: Arc<LibManager>,
  ) -> Program {
    let host: Arc<dyn Host> = Arc::new(host);
    let query_stats = QueryStatsCollector::default();
    let cancelled = Arc::new(AtomicBool::new(false));
    roots.sort_unstable_by(|a, b| a.as_str().cmp(b.as_str()));
    roots.dedup_by(|a, b| a.as_str() == b.as_str());
    let program = Program {
      host: Arc::clone(&host),
      roots,
      cancelled: Arc::clone(&cancelled),
      state: std::sync::Mutex::new(ProgramState::new(
        Arc::clone(&host),
        lib_manager,
        query_stats.clone(),
        Arc::clone(&cancelled),
      )),
      query_stats,
    };
    {
      let mut state = program.lock_state();
      for key in program.roots.iter().cloned() {
        state.intern_file_key(key, FileOrigin::Source);
      }
    }
    program
  }

  /// Compiler options used by this program.
  pub fn compiler_options(&self) -> CompilerOptions {
    match self.with_analyzed_state(|state| Ok(state.compiler_options.clone())) {
      Ok(opts) => opts,
      Err(fatal) => {
        self.record_fatal(fatal);
        CompilerOptions::default()
      }
    }
  }

  /// Override the compiler options for subsequent queries.
  pub fn set_compiler_options(&mut self, options: CompilerOptions) {
    {
      let mut state = self.lock_state();
      state.typecheck_db.set_compiler_options(options.clone());
      state.compiler_options = options.clone();
      state.compiler_options_override = Some(options.clone());
      state.checker_caches = CheckerCaches::new(options.cache.clone());
      state.cache_stats = CheckerCacheStats::default();
      state.interned_store = None;
    }
    self.reset_state();
  }

  /// Override the text for a specific file and invalidate cached results.
  pub fn set_file_text(&mut self, file: FileId, text: Arc<str>) {
    {
      let mut state = self.lock_state();
      let Some(key) = state.file_key_for_id(file) else {
        return;
      };
      state.file_overrides.insert(key.clone(), Arc::clone(&text));
      if db::Db::file_input(&state.typecheck_db, file).is_some() {
        state.typecheck_db.set_file_text(file, text);
      }
    }
    self.reset_state();
  }

  /// Resolve a file key to its internal [`FileId`], if loaded.
  pub fn file_id(&self, key: &FileKey) -> Option<FileId> {
    match self.with_analyzed_state(|state| Ok(state.file_id_for_key(key))) {
      Ok(id) => id,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// All [`FileId`]s associated with a [`FileKey`], preferring source-origin IDs first.
  pub fn file_ids_for_key(&self, key: &FileKey) -> Vec<FileId> {
    self
      .with_analyzed_state(|state| Ok(state.file_ids_for_key(key)))
      .unwrap_or_default()
  }

  /// Resolve a loaded [`FileId`] back to its [`FileKey`], if available.
  pub fn file_key(&self, file: FileId) -> Option<FileKey> {
    let state = self.lock_state();
    state.file_key_for_id(file)
  }

  /// Text contents for a loaded file, if available from the host.
  pub fn file_text(&self, file: FileId) -> Option<Arc<str>> {
    match self.with_analyzed_state(|state| Ok(state.load_text(file, &self.host).ok())) {
      Ok(text) => text,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// All known file IDs in this program.
  pub fn files(&self) -> Vec<FileId> {
    self
      .with_analyzed_state(|state| {
        let mut files: Vec<FileId> = state.files.keys().copied().collect();
        files.sort_by_key(|id| id.0);
        Ok(files)
      })
      .unwrap_or_default()
  }

  /// All files reachable from the configured roots.
  pub fn reachable_files(&self) -> Vec<FileId> {
    self
      .with_analyzed_state(|state| {
        let mut files: Vec<FileId> = if state.snapshot_loaded {
          use std::collections::{BTreeMap, VecDeque};

          let mut edges: BTreeMap<FileId, Vec<FileId>> = BTreeMap::new();
          for (from, _specifier, resolved) in state.typecheck_db.module_resolutions_snapshot() {
            let Some(resolved) = resolved else {
              continue;
            };
            edges.entry(from).or_default().push(resolved);
          }
          for deps in edges.values_mut() {
            deps.sort_by_key(|id| id.0);
            deps.dedup();
          }

          let mut queue: VecDeque<FileId> = state.root_ids.iter().copied().collect();
          let mut libs: Vec<FileId> = state.lib_file_ids.iter().copied().collect();
          libs.sort_by_key(|id| id.0);
          queue.extend(libs);

          let mut visited = BTreeMap::<FileId, ()>::new();
          while let Some(file) = queue.pop_front() {
            if visited.contains_key(&file) {
              continue;
            }
            visited.insert(file, ());
            if let Some(deps) = edges.get(&file) {
              for dep in deps {
                queue.push_back(*dep);
              }
            }
          }

          visited
            .keys()
            .copied()
            .filter(|file| !state.lib_file_ids.contains(file))
            .collect()
        } else {
          state
            .typecheck_db
            .reachable_files()
            .iter()
            .copied()
            .filter(|file| !state.lib_file_ids.contains(file))
            .collect()
        };
        files.sort_by_key(|id| id.0);
        Ok(files)
      })
      .unwrap_or_default()
  }

  /// Parse, bind, and type-check all known files, returning accumulated diagnostics.
  pub fn check(&self) -> Vec<Diagnostic> {
    match self.check_fallible() {
      Ok(diags) => diags,
      Err(fatal) => self.fatal_to_diagnostics(fatal),
    }
  }

  /// Fallible entry point that surfaces unrecoverable failures to the host.
  pub fn check_fallible(&self) -> Result<Vec<Diagnostic>, FatalError> {
    self
      .collect_program_diagnostics()
      .map(|diagnostics| diagnostics.to_vec())
  }

  fn collect_program_diagnostics(&self) -> Result<Arc<[Diagnostic]>, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.program_diagnostics(&self.host, &self.roots)
    })
  }

  /// Return collected query and cache statistics for this program.
  pub fn query_stats(&self) -> QueryStats {
    let (cache_stats, mut snapshot) = {
      let state = self.lock_state();
      let mut caches = state.cache_stats.clone();
      caches.merge(&state.checker_caches.stats());
      (caches, self.query_stats.snapshot())
    };

    let mut insert_cache = |kind: CacheKind, raw: &types_ts_interned::CacheStats| {
      let lookups = raw.hits + raw.misses;
      let stat = CacheStat {
        hits: raw.hits,
        misses: raw.misses,
        insertions: raw.insertions,
        evictions: raw.evictions,
        hit_rate: if lookups == 0 {
          0.0
        } else {
          raw.hits as f64 / lookups as f64
        },
      };
      snapshot.caches.insert(kind, stat);
    };

    insert_cache(CacheKind::Relation, &cache_stats.relation);
    insert_cache(CacheKind::Eval, &cache_stats.eval);
    insert_cache(CacheKind::RefExpansion, &cache_stats.ref_expansion);
    insert_cache(CacheKind::Instantiation, &cache_stats.instantiation);

    snapshot
  }

  /// Request cancellation of ongoing work.
  pub fn cancel(&self) {
    self.cancelled.store(true, Ordering::Relaxed);
  }

  /// Clear any pending cancellation request so new work can proceed.
  pub fn clear_cancellation(&self) {
    self.cancelled.store(false, Ordering::Relaxed);
  }

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
        Err(payload) => match payload.downcast::<diagnostics::Cancelled>() {
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

  /// Type for a definition.
  pub fn type_of_def(&self, def: DefId) -> TypeId {
    match self.type_of_def_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        self.builtin_unknown()
      }
    }
  }

  pub fn type_of_def_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| ProgramState::type_of_def(state, def))
  }

  /// Check a body, returning the cached result.
  pub fn check_body(&self, body: BodyId) -> Arc<BodyCheckResult> {
    match self.check_body_fallible(body) {
      Ok(res) => res,
      Err(fatal) => {
        let diagnostics = self.fatal_to_diagnostics(fatal);
        Arc::new(BodyCheckResult {
          body,
          expr_types: Vec::new(),
          expr_spans: Vec::new(),
          pat_types: Vec::new(),
          pat_spans: Vec::new(),
          diagnostics,
          return_types: Vec::new(),
        })
      }
    }
  }

  pub fn check_body_fallible(&self, body: BodyId) -> Result<Arc<BodyCheckResult>, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let parallel_guard = db::queries::body_check::parallel_guard();
      if parallel_guard.is_some() {
        std::thread::yield_now();
      }
      let context = {
        let mut state = self.lock_state();
        state.ensure_interned_types(&self.host, &self.roots)?;
        if let Some(res) = state.body_results.get(&body).cloned() {
          return Ok(res);
        }
        state.body_check_context()
      };
      let db = BodyCheckDb::from_shared_context(context);
      let res = db::queries::body_check::check_body(&db, body);
      let mut state = self.lock_state();
      state.body_results.insert(body, Arc::clone(&res));
      Ok(res)
    })
  }

  /// Type of a specific expression in a body.
  pub fn type_of_expr(&self, body: BodyId, expr: ExprId) -> TypeId {
    match self.type_of_expr_fallible(body, expr) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        self.builtin_unknown()
      }
    }
  }

  pub fn type_of_expr_fallible(&self, body: BodyId, expr: ExprId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let result = state.check_body(body)?;
      let unknown = state.interned_unknown();
      Ok(result.expr_type(expr).unwrap_or(unknown))
    })
  }

  /// Return symbol at a given file offset, if any.
  pub fn symbol_at(&self, file: FileId, offset: u32) -> Option<semantic_js::SymbolId> {
    match self.symbol_at_fallible(file, offset) {
      Ok(symbol) => symbol,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn symbol_at_fallible(
    &self,
    file: FileId,
    offset: u32,
  ) -> Result<Option<semantic_js::SymbolId>, FatalError> {
    self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(occurrences) = state.symbol_occurrences.get(&file) {
          return Ok(Self::symbol_from_occurrences(occurrences, offset));
        }
      }
      let occurrences = crate::db::symbol_occurrences(&state.typecheck_db, file);
      Ok(Self::symbol_from_occurrences(&occurrences, offset))
    })
  }

  fn symbol_from_occurrences(
    occurrences: &[SymbolOccurrence],
    offset: u32,
  ) -> Option<semantic_js::SymbolId> {
    let pivot = occurrences.partition_point(|occ| occ.range.start <= offset);
    let mut best_containing: Option<(u32, u32, u32, semantic_js::SymbolId)> = None;
    let mut best_empty: Option<(u32, u32, u32, semantic_js::SymbolId)> = None;

    for occ in occurrences[..pivot].iter().rev() {
      let range = occ.range;
      let len = range.len();
      let key = (len, range.start, range.end, occ.symbol);
      if range.start <= offset && offset < range.end {
        if best_containing
          .map(|existing| key < existing)
          .unwrap_or(true)
        {
          best_containing = Some(key);
        }
      } else if range.start == range.end && range.start == offset {
        if best_empty.map(|existing| key < existing).unwrap_or(true) {
          best_empty = Some(key);
        }
      }
    }

    best_containing
      .or(best_empty)
      .map(|(_, _, _, symbol)| symbol)
  }

  /// Symbol metadata if available (def, file, type, name).
  pub fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    match self.with_analyzed_state(|state| Ok(state.symbol_info(symbol))) {
      Ok(info) => info,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Innermost expression covering an offset within a file.
  pub fn expr_at(&self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    match self.expr_at_fallible(file, offset) {
      Ok(expr) => expr,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn expr_at_fallible(
    &self,
    file: FileId,
    offset: u32,
  ) -> Result<Option<(BodyId, ExprId)>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.expr_at(file, offset)))
  }

  /// Type of the innermost expression covering an offset within a file.
  pub fn type_at(&self, file: FileId, offset: u32) -> Option<TypeId> {
    match self.type_at_fallible(file, offset) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn type_at_fallible(&self, file: FileId, offset: u32) -> Result<Option<TypeId>, FatalError> {
    self.with_interned_state(|state| {
      const TYPE_AT_TRIVIA_LOOKAROUND: usize = 32;

      let mut offset = offset;
      let mut expr_at = state.expr_at(file, offset);
      let mut pat_at = state.pat_at(file, offset);

      if expr_at.is_none() && pat_at.is_none() {
        if let Ok(text) = state.load_text(file, &self.host) {
          let bytes = text.as_bytes();
          let start = (offset as usize).min(bytes.len());

          let mut found = None;
          for step in 1..=TYPE_AT_TRIVIA_LOOKAROUND {
            if start < step {
              break;
            }
            let cand = start - step;
            let Ok(cand_u32) = cand.try_into() else {
              break;
            };
            if state.expr_at(file, cand_u32).is_some() || state.pat_at(file, cand_u32).is_some() {
              found = Some(cand_u32);
              break;
            }
          }

          if found.is_none() {
            for step in 1..=TYPE_AT_TRIVIA_LOOKAROUND {
              let cand = start + step;
              if cand >= bytes.len() {
                break;
              }
              let Ok(cand_u32) = cand.try_into() else {
                break;
              };
              if state.expr_at(file, cand_u32).is_some() || state.pat_at(file, cand_u32).is_some() {
                found = Some(cand_u32);
                break;
              }
            }
          }

          if let Some(adj) = found {
            offset = adj;
            expr_at = state.expr_at(file, offset);
            pat_at = state.pat_at(file, offset);
          }
        }
      }

      let (body, expr) = match expr_at {
        Some(res) => res,
        None => {
          let Some((body, pat)) = pat_at else {
            return Ok(None);
          };
          let result = state.check_body(body)?;
          let unknown = state.interned_unknown();
          return Ok(Some(result.pat_type(pat).unwrap_or(unknown)));
        }
      };
      let result = state.check_body(body)?;
      let unknown = state.interned_unknown();
      let (expr, mut ty) = match result.expr_at(offset) {
        Some((expr_id, ty)) => (expr_id, ty),
        None => (expr, result.expr_type(expr).unwrap_or(unknown)),
      };
      let mut member_fallback: Option<(bool, tti::TypeId, String)> = None;
      let mut binding_def: Option<DefId> = None;
      let mut binding_ty: Option<TypeId> = None;
      let mut contextual_ty: Option<TypeId> = None;
      if let Some(meta) = state.body_map.get(&body) {
        if let Some(hir_id) = meta.hir {
          if let Some(lowered) = state.hir_lowered.get(&meta.file) {
            if let Some(hir_body) = lowered.body(hir_id) {
              if let Some(expr_data) = hir_body.exprs.get(expr.0 as usize) {
                match &expr_data.kind {
                  HirExprKind::Ident(name_id) => {
                    if let Some(name) = lowered.names.resolve(*name_id) {
                      if let Some(file_state) = state.files.get(&meta.file) {
                        if let Some(binding) = file_state.bindings.get(name) {
                          binding_def = binding.def;
                          binding_ty = binding.type_id;
                        }
                      }
                    }
                  }
                  HirExprKind::Member(mem) => {
                    let key = match &mem.property {
                      hir_js::ObjectKey::Ident(id) => {
                        lowered.names.resolve(*id).map(|s| s.to_string())
                      }
                      hir_js::ObjectKey::String(s) => Some(s.clone()),
                      hir_js::ObjectKey::Number(n) => Some(n.clone()),
                      hir_js::ObjectKey::Computed(_) => None,
                    };
                    if let Some(key) = key {
                      let base_ty = result.expr_type(mem.object).unwrap_or(unknown);
                      member_fallback = Some((mem.optional, base_ty, key));
                    }
                  }
                  _ => {}
                }
                if contextual_ty.is_none() {
                  if let Some(store) = state.interned_store.as_ref() {
                    for (_idx, candidate) in hir_body.exprs.iter().enumerate() {
                      if let HirExprKind::Call(call) = &candidate.kind {
                        if let Some(arg_idx) = call.args.iter().position(|arg| arg.expr.0 == expr.0)
                        {
                          if let Some(callee_ty) = result.expr_type(call.callee) {
                            let sigs = callable_signatures(store.as_ref(), callee_ty);
                            if let Some(sig_id) = sigs.first() {
                              let sig = store.signature(*sig_id);
                              if let Some(param) = sig.params.get(arg_idx) {
                                contextual_ty = Some(param.ty);
                                break;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if let Some(ctx) = contextual_ty {
        ty = ctx;
      }
      let is_unknown = state
        .interned_store
        .as_ref()
        .map(|store| {
          store.contains_type_id(ty) && matches!(store.type_kind(ty), tti::TypeKind::Unknown)
        })
        .unwrap_or(ty == unknown);
      let should_resolve_binding = is_unknown
        || state
          .interned_store
          .as_ref()
          .map(|store| {
            if !store.contains_type_id(ty) {
              return false;
            }
            matches!(
               store.type_kind(ty),
               tti::TypeKind::Ref { def, args }
                 if args.is_empty() && binding_def.map(|bd| bd.0 == def.0).unwrap_or(false)
            )
          })
          .unwrap_or(false);
      if should_resolve_binding {
        if let Some(def) = binding_def {
          match state.type_of_def(def) {
            Ok(def_ty) => {
              ty = state.ensure_interned_type(def_ty);
            }
            Err(FatalError::Cancelled) => return Err(FatalError::Cancelled),
            Err(_) => {}
          }
        }
        let still_unknown = state
          .interned_store
          .as_ref()
          .map(|store| {
            store.contains_type_id(ty) && matches!(store.type_kind(ty), tti::TypeKind::Unknown)
          })
          .unwrap_or(ty == unknown);
        if still_unknown {
          if let Some(binding_ty) = binding_ty {
            ty = binding_ty;
          }
        }
      }
      let member_fallback_allowed = state
        .interned_store
        .as_ref()
        .map(|store| {
          store.contains_type_id(ty) && matches!(store.type_kind(ty), tti::TypeKind::Unknown)
        })
        .unwrap_or(ty == unknown);
      if member_fallback_allowed {
        if let Some((optional, base_ty, key)) = member_fallback {
          if let Some(store) = state.interned_store.as_ref() {
            let caches = state.checker_caches.for_body();
            let expander = RefExpander::new(
              Arc::clone(store),
              &state.interned_def_types,
              &state.interned_type_params,
              &state.interned_type_param_decls,
              &state.interned_intrinsics,
              &state.interned_class_instances,
              caches.eval.clone(),
            );
            let mut prop_ty = lookup_interned_property_type(store, Some(&expander), base_ty, &key);
            if prop_ty.is_none() {
              if let tti::TypeKind::Ref { def, .. } = store.type_kind(base_ty) {
                if let Some(mapped) = state.interned_def_types.get(&DefId(def.0)).copied() {
                  prop_ty = lookup_interned_property_type(store, None, mapped, &key);
                }
              }
            }
            if let Some(prop_ty) = prop_ty {
              ty = if optional {
                store.union(vec![prop_ty, store.primitive_ids().undefined])
              } else {
                prop_ty
              };
            }
          }
        }
      }
      if std::env::var("DEBUG_TYPE_AT").is_ok() {
        if let Some(span) = result.expr_span(expr) {
          eprintln!(
            "type_at debug: body {:?} expr {:?} span {:?}",
            body, expr, span
          );
        } else {
          eprintln!("type_at debug: body {:?} expr {:?} (no span)", body, expr);
        }
        if let Some(meta) = state.body_map.get(&body) {
          eprintln!("  meta kind {:?}", meta.kind);
          if let Some(hir_id) = meta.hir {
            if let Some(lowered) = state.hir_lowered.get(&meta.file) {
              if let Some(hir_body) = lowered.body(hir_id) {
                if let Some(expr_data) = hir_body.exprs.get(expr.0 as usize) {
                  eprintln!("  hir expr kind {:?}", expr_data.kind);
                }
              }
            }
          }
        }
        eprintln!("  parent {:?}", state.body_parents.get(&body));
        if let Some(raw_ty) = result.expr_type(expr) {
          if let Some(store) = state.interned_store.as_ref() {
            eprintln!("  raw type {:?}", store.type_kind(raw_ty));
          } else {
            eprintln!("  raw type {:?}", raw_ty);
          }
        }
        if let Some(parent) = state.body_parents.get(&body).copied() {
          match state.check_body(parent) {
            Ok(parent_res) => {
              eprintln!("  parent pat types {:?}", parent_res.pat_types());
              if let Some(first) = parent_res.pat_types().first() {
                if let Some(store) = state.interned_store.as_ref() {
                  eprintln!("  parent pat kind {:?}", store.type_kind(*first));
                }
              }
            }
            Err(FatalError::Cancelled) => return Err(FatalError::Cancelled),
            Err(_) => {}
          }
        }
        if let Some(owner) = state.owner_of_body(body) {
          if let Some(def) = state.def_data.get(&owner) {
            eprintln!("  owner {:?}", def.name);
          }
        }
        if let Some(parent) = state.body_parents.get(&body).copied() {
          if let Some(owner) = state.owner_of_body(parent) {
            if let Some(def) = state.def_data.get(&owner) {
              eprintln!("  parent owner {:?}", def.name);
            }
          }
        }
      }
      let is_number_literal = state
        .interned_store
        .as_ref()
        .and_then(|store| store.contains_type_id(ty).then(|| store.type_kind(ty)))
        .map(|kind| matches!(kind, tti::TypeKind::NumberLiteral(_)))
        .unwrap_or(false);
      if is_number_literal {
        let is_literal = state
          .body_map
          .get(&body)
          .and_then(|meta| meta.hir)
          .and_then(|hir_id| {
            state
              .hir_lowered
              .get(&file)
              .and_then(|lowered| lowered.body(hir_id))
              .and_then(|hir_body| {
                hir_body
                  .exprs
                  .get(expr.0 as usize)
                  .map(|expr_data| matches!(expr_data.kind, HirExprKind::Literal(_)))
              })
          })
          .unwrap_or(false);
        if is_literal {
          if let Some(meta) = state.body_map.get(&body) {
            if let Some(hir_id) = meta.hir {
              if let Some(lowered) = state.hir_lowered.get(&meta.file) {
                if let Some(hir_body) = lowered.body(hir_id) {
                  let mut best: Option<(u32, TypeId)> = None;
                  for (idx, expr_data) in hir_body.exprs.iter().enumerate() {
                    let span = expr_data.span;
                    if !(span.start <= offset && offset < span.end) {
                      continue;
                    }
                    if let HirExprKind::Binary { op, .. } = &expr_data.kind {
                      let numeric = matches!(
                        op,
                        HirBinaryOp::Add
                          | HirBinaryOp::Subtract
                          | HirBinaryOp::Multiply
                          | HirBinaryOp::Divide
                          | HirBinaryOp::Exponent
                          | HirBinaryOp::Remainder
                          | HirBinaryOp::BitAnd
                          | HirBinaryOp::BitOr
                          | HirBinaryOp::BitXor
                          | HirBinaryOp::ShiftLeft
                          | HirBinaryOp::ShiftRight
                          | HirBinaryOp::ShiftRightUnsigned
                      );
                      if !numeric {
                        continue;
                      }
                      let len = span.len();
                      let bin_ty = result.expr_type(ExprId(idx as u32)).unwrap_or(ty);
                      let is_number = state
                        .interned_store
                        .as_ref()
                        .and_then(|store| {
                          store
                            .contains_type_id(bin_ty)
                            .then(|| store.type_kind(bin_ty))
                        })
                        .map(|kind| matches!(kind, tti::TypeKind::Number))
                        .unwrap_or(false);
                      if is_number {
                        let replace = best.map(|(l, _)| len < l).unwrap_or(true);
                        if replace {
                          best = Some((len, bin_ty));
                        }
                      }
                    }
                  }
                  if let Some((_, bin_ty)) = best {
                    ty = bin_ty;
                  }
                }
              }
            }
          }
        }
      }
      let ty = state.ensure_interned_type(ty);
      Ok(Some(ty))
    })
  }

  /// Interned type of a definition, using the `types-ts-interned` store.
  pub fn type_of_def_interned(&self, def: DefId) -> TypeId {
    match self.type_of_def_interned_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        let state = self.lock_state();
        state
          .interned_store
          .as_ref()
          .map(|s| s.primitive_ids().unknown)
          .unwrap_or(TypeId(0))
      }
    }
  }

  /// Interned, *expanded* type of a definition.
  ///
  /// For named type declarations (type aliases, interfaces, classes, enums),
  /// [`Program::type_of_def_interned`] returns a `TypeKind::Ref` pointing at the
  /// definition itself so callers can preserve the name. This helper returns
  /// the stored definition type instead (e.g. the RHS of a type alias).
  pub fn declared_type_of_def_interned(&self, def: DefId) -> TypeId {
    match self.declared_type_of_def_interned_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        let state = self.lock_state();
        state
          .interned_store
          .as_ref()
          .map(|s| s.primitive_ids().unknown)
          .unwrap_or(TypeId(0))
      }
    }
  }

  pub fn declared_type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized")
        .clone();
      let expanded = match state.interned_def_types.get(&def).copied() {
        Some(existing) if !matches!(store.type_kind(existing), tti::TypeKind::Unknown) => existing,
        _ => {
          ProgramState::type_of_def(state, def)?;
          state
            .interned_def_types
            .get(&def)
            .copied()
            .unwrap_or(store.primitive_ids().unknown)
        }
      };
      Ok(expanded)
    })
  }

  pub fn type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized")
        .clone();
      let expanded = match state.interned_def_types.get(&def).copied() {
        Some(existing) if !matches!(store.type_kind(existing), tti::TypeKind::Unknown) => existing,
        _ => {
          ProgramState::type_of_def(state, def)?;
          state
            .interned_def_types
            .get(&def)
            .copied()
            .unwrap_or(store.primitive_ids().unknown)
        }
      };
      let wants_named_ref = state
        .def_data
        .get(&def)
        .map(|data| {
          matches!(
            data.kind,
            DefKind::Interface(_) | DefKind::TypeAlias(_) | DefKind::Class(_) | DefKind::Enum(_)
          )
        })
        .unwrap_or(false);
      if wants_named_ref {
        let mut args = state
          .interned_type_params
          .get(&def)
          .cloned()
          .unwrap_or_default();
        args.sort_by_key(|param| param.0);
        let args: Vec<_> = args
          .into_iter()
          .map(|param| store.intern_type(tti::TypeKind::TypeParam(param)))
          .collect();
        return Ok(store.canon(store.intern_type(tti::TypeKind::Ref { def, args })));
      }
      Ok(expanded)
    })
  }

  /// Expanded kind summary for an interned type.
  pub fn type_kind(&self, ty: TypeId) -> TypeKindSummary {
    match self.type_kind_fallible(ty) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        TypeKindSummary::Unknown
      }
    }
  }

  pub fn type_kind_fallible(&self, ty: TypeId) -> Result<TypeKindSummary, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let result = queries.type_kind(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(result)
    })
  }

  /// Raw interned type kind without expansion.
  pub fn interned_type_kind(&self, ty: TypeId) -> tti::TypeKind {
    match self.interned_type_kind_fallible(ty) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        tti::TypeKind::Unknown
      }
    }
  }

  pub fn interned_type_kind_fallible(&self, ty: TypeId) -> Result<tti::TypeKind, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      Ok(store.type_kind(ty))
    })
  }

  /// Explain why `src` is not assignable to `dst`.
  ///
  /// Returns `None` if `src` is assignable to `dst`.
  pub fn explain_assignability(&self, src: TypeId, dst: TypeId) -> Option<ExplainTree> {
    match self.explain_assignability_fallible(src, dst) {
      Ok(tree) => tree,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn explain_assignability_fallible(
    &self,
    src: TypeId,
    dst: TypeId,
  ) -> Result<Option<ExplainTree>, FatalError> {
    self.with_interned_state(|state| {
      let src = state.ensure_interned_type(src);
      let dst = state.ensure_interned_type(dst);
      let store = Arc::clone(
        state
          .interned_store
          .as_ref()
          .expect("interned store initialized"),
      );
      let caches = state.checker_caches.for_body();
      let expander = RefExpander::new(
        Arc::clone(&store),
        &state.interned_def_types,
        &state.interned_type_params,
        &state.interned_type_param_decls,
        &state.interned_intrinsics,
        &state.interned_class_instances,
        caches.eval.clone(),
      );
      let hooks = relate_hooks();
      let hooks = tti::RelateHooks {
        expander: Some(&expander),
        is_same_origin_private_member: hooks.is_same_origin_private_member,
      };
      // Use a fresh relation cache so explanation trees contain full structure
      // instead of "cached" sentinel nodes from prior checker passes.
      let relation_cache = tti::RelationCache::new(state.compiler_options.cache.relation_config());
      let options = store.options();
      let ctx = RelateCtx::with_hooks_cache_and_normalizer_caches(
        Arc::clone(&store),
        options,
        hooks,
        relation_cache,
        caches.eval.clone(),
      );

      let result = ctx.explain_assignable(src, dst);
      if result.result {
        return Ok(None);
      }

      Ok(result.reason.or_else(|| {
        Some(tti::ReasonNode {
          src,
          dst,
          relation: tti::RelationKind::Assignable,
          outcome: false,
          note: Some("no explanation available".into()),
          children: Vec::new(),
        })
      }))
    })
  }

  /// Properties visible on a type after expansion.
  pub fn properties_of(&self, ty: TypeId) -> Vec<PropertyInfo> {
    match self.properties_of_fallible(ty) {
      Ok(props) => props,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn properties_of_fallible(&self, ty: TypeId) -> Result<Vec<PropertyInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let mut props = queries.properties_of(ty);
      for prop in props.iter_mut() {
        prop.ty = state.prefer_named_refs(prop.ty);
      }
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(props)
    })
  }

  pub fn property_type(&self, ty: TypeId, key: PropertyKey) -> Option<TypeId> {
    match self.property_type_fallible(ty, key) {
      Ok(res) => res,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn property_type_fallible(
    &self,
    ty: TypeId,
    key: PropertyKey,
  ) -> Result<Option<TypeId>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let prop = queries
        .property_type(ty, key)
        .map(|ty| state.prefer_named_refs(ty));
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(prop)
    })
  }

  pub fn call_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    match self.call_signatures_fallible(ty) {
      Ok(sigs) => sigs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn call_signatures_fallible(&self, ty: TypeId) -> Result<Vec<SignatureInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let sigs = queries.call_signatures(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(sigs)
    })
  }

  pub fn construct_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    match self.construct_signatures_fallible(ty) {
      Ok(sigs) => sigs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn construct_signatures_fallible(
    &self,
    ty: TypeId,
  ) -> Result<Vec<SignatureInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let sigs = queries.construct_signatures(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(sigs)
    })
  }

  pub fn indexers(&self, ty: TypeId) -> Vec<IndexerInfo> {
    match self.indexers_fallible(ty) {
      Ok(indexers) => indexers,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn indexers_fallible(&self, ty: TypeId) -> Result<Vec<IndexerInfo>, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let indexers = queries.indexers(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(indexers)
    })
  }

  /// Export map for a file.
  pub fn exports_of(&self, file: FileId) -> ExportMap {
    match self.exports_of_fallible(file) {
      Ok(exports) => exports,
      Err(fatal) => {
        self.record_fatal(fatal);
        ExportMap::new()
      }
    }
  }

  pub fn exports_of_fallible(&self, file: FileId) -> Result<ExportMap, FatalError> {
    self.with_interned_state(|state| {
      let mut exports = state.exports_of_file(file)?;

      // `typecheck-ts-harness` gathers export type facts via `Program::exports_of`.
      // Its TypeScript oracle uses `checker.getTypeOfSymbolAtLocation(...)`, which
      // returns `any` for type-only exports (interfaces/type aliases). Keep Rust
      // export type facts aligned with that behaviour without affecting the
      // internal export map used for type checking/import resolution.
      let any = state.builtin.any;
      if let Some(semantics) = state.semantics.as_ref() {
        if let Some(sem_exports) = semantics.exports_of_opt(sem_ts::FileId(file.0)) {
          let symbols = semantics.symbols();
          for (name, entry) in exports.iter_mut() {
            let Some(group) = sem_exports.get(name) else {
              continue;
            };
            let is_value_export = group
              .symbol_for(sem_ts::Namespace::VALUE, symbols)
              .is_some()
              || group
                .symbol_for(sem_ts::Namespace::NAMESPACE, symbols)
                .is_some();
            if !is_value_export {
              entry.type_id = Some(any);
            }
          }
        }
      } else {
        for entry in exports.values_mut() {
          let is_type_only = entry
            .def
            .and_then(|def| state.def_data.get(&def))
            .is_some_and(|data| matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)));
          if is_type_only {
            entry.type_id = Some(any);
          }
        }
      }

      Ok(exports)
    })
  }

  /// Global bindings available to all files (from libs, `.d.ts`, and builtins).
  pub fn global_bindings(&self) -> Arc<BTreeMap<String, SymbolBinding>> {
    match self.with_interned_state(|state| Ok(Arc::clone(&state.global_bindings))) {
      Ok(bindings) => bindings,
      Err(fatal) => {
        self.record_fatal(fatal);
        Arc::new(BTreeMap::new())
      }
    }
  }

  /// Helper to render a type as displayable string.
  pub fn display_type(&self, ty: TypeId) -> TypeDisplay {
    let (store, ty, resolver) = {
      let mut state = self.lock_state();
      state.ensure_analyzed(&self.host, &self.roots);
      if let Err(fatal) = state.ensure_interned_types(&self.host, &self.roots) {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
      }
      let mut resolver = state
        .def_data
        .iter()
        .map(|(id, data)| (tti::DefId(id.0), data.name.clone()))
        .collect::<HashMap<_, _>>();
      let (store, mut ty) = display_type_from_state(&state, ty);
      let can_evaluate = state
        .interned_store
        .as_ref()
        .map(|interned| Arc::ptr_eq(interned, &store))
        .unwrap_or(false);

      if can_evaluate {
        let canonical = store.canon(ty);
        if let tti::TypeKind::Intersection(members) = store.type_kind(canonical) {
          for (def, data) in state.def_data.iter() {
            if !matches!(data.kind, DefKind::Function(_)) {
              continue;
            }
            let Some(def_ty) = state.interned_def_types.get(def).copied() else {
              continue;
            };
            if store.canon(def_ty) != canonical {
              continue;
            }
            let Some((ns_ty, _)) = state
              .namespace_object_types
              .get(&(data.file, data.name.clone()))
            else {
              continue;
            };
            let ns_ty = store.canon(*ns_ty);
            if !members.iter().any(|member| store.canon(*member) == ns_ty) {
              continue;
            }
            let Some(ns_def) = state.find_namespace_def(data.file, &data.name) else {
              continue;
            };
            resolver.insert(tti::DefId(ns_def.0), format!("typeof {}", data.name));
            ty = store.canon(store.intern_type(tti::TypeKind::Ref {
              def: tti::DefId(ns_def.0),
              args: Vec::new(),
            }));
            break;
          }
        }
      }
      let ty = match store.type_kind(ty) {
        tti::TypeKind::Mapped(mapped) => {
          if !can_evaluate {
            ty
          } else {
            const MAX_DISPLAY_MAPPED_KEYS: usize = 64;
            let should_expand = match store.type_kind(mapped.source) {
              tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
                members.len() <= MAX_DISPLAY_MAPPED_KEYS
              }
              _ => true,
            };
            if !should_expand {
              ty
            } else {
              let caches = state.checker_caches.for_body();
              let expander = ProgramTypeExpander {
                def_types: &state.interned_def_types,
                type_params: &state.interned_type_params,
                intrinsics: &state.interned_intrinsics,
              };
              let queries =
                TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
              let evaluated = queries.evaluate(ty);
              let evaluated = state.prefer_named_class_refs_in_store(&store, evaluated);
              let ok = match store.type_kind(evaluated) {
                tti::TypeKind::Object(obj) => {
                  let shape = store.shape(store.object(obj).shape);
                  shape.properties.len() <= MAX_DISPLAY_MAPPED_KEYS
                }
                _ => false,
              };
              if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
                state.cache_stats.merge(&caches.stats());
              }
              if ok {
                evaluated
              } else {
                ty
              }
            }
          }
        }
        tti::TypeKind::Intrinsic { .. } if can_evaluate => {
          let caches = state.checker_caches.for_body();
          let expander = ProgramTypeExpander {
            def_types: &state.interned_def_types,
            type_params: &state.interned_type_params,
            intrinsics: &state.interned_intrinsics,
          };
          let queries =
            TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
          let evaluated = queries.evaluate(ty);
          let evaluated = state.prefer_named_refs_in_store(&store, evaluated);
          if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
            state.cache_stats.merge(&caches.stats());
          }
          evaluated
        }
        tti::TypeKind::Ref { def, .. }
          if can_evaluate && state.interned_intrinsics.contains_key(&DefId(def.0)) =>
        {
          let caches = state.checker_caches.for_body();
          let expander = ProgramTypeExpander {
            def_types: &state.interned_def_types,
            type_params: &state.interned_type_params,
            intrinsics: &state.interned_intrinsics,
          };
          let queries =
            TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
          let evaluated = queries.evaluate(ty);
          let evaluated = state.prefer_named_refs_in_store(&store, evaluated);
          if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
            state.cache_stats.merge(&caches.stats());
          }
          evaluated
        }
        tti::TypeKind::Ref { def, args }
          if can_evaluate
            && args.is_empty()
            && state
              .def_data
              .get(&DefId(def.0))
              .is_some_and(|data| matches!(data.kind, DefKind::Function(_) | DefKind::Var(_))) =>
        {
          match state.resolve_value_ref_type(ty) {
            Ok(resolved) => resolved,
            Err(fatal) => {
              state.diagnostics.push(fatal_to_diagnostic(fatal));
              ty
            }
          }
        }
        tti::TypeKind::Ref { def, .. } if can_evaluate => {
          let should_expand = state
            .def_data
            .get(&DefId(def.0))
            .is_some_and(|data| matches!(data.kind, DefKind::TypeAlias(_)));
          if !should_expand {
            ty
          } else {
            fn is_simple_display_type(store: &tti::TypeStore, ty: tti::TypeId) -> bool {
              match store.type_kind(ty) {
                tti::TypeKind::Any
                | tti::TypeKind::Unknown
                | tti::TypeKind::Never
                | tti::TypeKind::Void
                | tti::TypeKind::Null
                | tti::TypeKind::Undefined
                | tti::TypeKind::Boolean
                | tti::TypeKind::Number
                | tti::TypeKind::String
                | tti::TypeKind::BigInt
                | tti::TypeKind::Symbol
                | tti::TypeKind::UniqueSymbol
                | tti::TypeKind::BooleanLiteral(_)
                | tti::TypeKind::NumberLiteral(_)
                | tti::TypeKind::StringLiteral(_)
                | tti::TypeKind::BigIntLiteral(_)
                | tti::TypeKind::TemplateLiteral(_) => true,
                tti::TypeKind::Union(members) => {
                  const MAX_SIMPLE_UNION_MEMBERS: usize = 32;
                  members.len() <= MAX_SIMPLE_UNION_MEMBERS
                    && members
                      .iter()
                      .all(|member| is_simple_display_type(store, *member))
                }
                _ => false,
              }
            }

            let caches = state.checker_caches.for_body();
            let expander = ProgramTypeExpander {
              def_types: &state.interned_def_types,
              type_params: &state.interned_type_params,
              intrinsics: &state.interned_intrinsics,
            };
            let queries =
              TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
            let evaluated = queries.evaluate(ty);
            let evaluated = state.prefer_named_refs_in_store(&store, evaluated);
            if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
              state.cache_stats.merge(&caches.stats());
            }
            // Preserve user-defined alias names when they only expand to a
            // primitive keyword type. Those names often carry meaning (e.g.
            // they encode intent or come from a `typeof import()` query),
            // whereas printing `number`/`string` would lose that context.
            let expands_to_keyword = matches!(
              store.type_kind(evaluated),
              tti::TypeKind::Any
                | tti::TypeKind::Unknown
                | tti::TypeKind::Never
                | tti::TypeKind::Void
                | tti::TypeKind::Null
                | tti::TypeKind::Undefined
                | tti::TypeKind::Boolean
                | tti::TypeKind::Number
                | tti::TypeKind::String
                | tti::TypeKind::BigInt
                | tti::TypeKind::Symbol
                | tti::TypeKind::UniqueSymbol
            );
            if evaluated != ty && !expands_to_keyword && is_simple_display_type(&store, evaluated) {
              evaluated
            } else {
              ty
            }
          }
        }
        _ => ty,
      };
      let ty = state.prefer_named_class_refs_in_store(&store, ty);
      (store, ty, resolver)
    };
    let resolver = Arc::new(resolver);
    TypeDisplay {
      store,
      ty,
      resolver: Some(Arc::new(move |def| resolver.get(&def).cloned())),
    }
  }

  /// Definitions declared in a file.
  pub fn definitions_in_file(&self, file: FileId) -> Vec<DefId> {
    match self.definitions_in_file_fallible(file) {
      Ok(defs) => defs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn definitions_in_file_fallible(&self, file: FileId) -> Result<Vec<DefId>, FatalError> {
    self.with_analyzed_state(|state| {
      let mut defs = state
        .files
        .get(&file)
        .map(|f| f.defs.clone())
        .unwrap_or_default();
      defs.sort_by_key(|id| id.0);
      Ok(defs)
    })
  }

  /// Bodies belonging to a file.
  pub fn bodies_in_file(&self, file: FileId) -> Vec<BodyId> {
    match self.with_analyzed_state(|state| {
      let mut bodies: Vec<BodyId> = state
        .body_map
        .iter()
        .filter_map(|(id, meta)| (meta.file == file).then_some(*id))
        .collect();
      bodies.sort_by_key(|id| id.0);
      Ok(bodies)
    }) {
      Ok(bodies) => bodies,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Expression IDs in a body.
  pub fn exprs_in_body(&self, body: BodyId) -> Vec<ExprId> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(result) = state.body_results.get(&body) {
          return Ok((0..result.expr_types.len() as u32).map(ExprId).collect());
        }
      }
      let ids = state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .map(|body| (0..body.exprs.len() as u32).map(ExprId).collect())
        })
      });
      Ok(ids.unwrap_or_default())
    }) {
      Ok(exprs) => exprs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Pattern IDs in a body.
  pub fn pats_in_body(&self, body: BodyId) -> Vec<PatId> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(result) = state.body_results.get(&body) {
          return Ok((0..result.pat_types.len() as u32).map(PatId).collect());
        }
      }
      let ids = state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .map(|body| (0..body.pats.len() as u32).map(PatId).collect())
        })
      });
      Ok(ids.unwrap_or_default())
    }) {
      Ok(pats) => pats,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Span for a definition, if available.
  pub fn def_span(&self, def: DefId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).map(|data| Span {
        file: data.file,
        range: data.span,
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Locate the initializer for a variable definition, if any.
  pub fn var_initializer(&self, def: DefId) -> Option<VarInit> {
    match self.var_initializer_fallible(def) {
      Ok(init) => init,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn var_initializer_fallible(&self, def: DefId) -> Result<Option<VarInit>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.var_initializer(def)))
  }

  /// Span for an expression, if available.
  pub fn expr_span(&self, body: BodyId, expr: ExprId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        let Some(meta) = state.body_map.get(&body) else {
          return Ok(None);
        };
        if let Some(result) = state.body_results.get(&body) {
          if let Some(range) = result.expr_span(expr) {
            return Ok(Some(Span {
              file: meta.file,
              range,
            }));
          }
        }
      }

      Ok(state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .and_then(|body| {
              body.exprs.get(expr.0 as usize).map(|expr| Span {
                file: meta.file,
                range: expr.span,
              })
            })
        })
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Span for a pattern, if available.
  pub fn pat_span(&self, body: BodyId, pat: PatId) -> Option<Span> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        let Some(meta) = state.body_map.get(&body) else {
          return Ok(None);
        };
        if let Some(result) = state.body_results.get(&body) {
          if let Some(range) = result.pat_span(pat) {
            return Ok(Some(Span {
              file: meta.file,
              range,
            }));
          }
        }
      }

      Ok(state.body_map.get(&body).and_then(|meta| {
        meta.hir.and_then(|hir_id| {
          state
            .hir_lowered
            .get(&meta.file)
            .and_then(|lowered| lowered.body(hir_id))
            .and_then(|body| {
              body.pats.get(pat.0 as usize).map(|pat| Span {
                file: meta.file,
                range: pat.span,
              })
            })
        })
      }))
    }) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  /// Raw symbol occurrences for debugging.
  pub fn debug_symbol_occurrences(&self, file: FileId) -> Vec<(TextRange, semantic_js::SymbolId)> {
    match self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        if let Some(occurrences) = state.symbol_occurrences.get(&file) {
          return Ok(occurrences.clone());
        }
      }
      Ok(crate::db::symbol_occurrences(&state.typecheck_db, file).to_vec())
    }) {
      Ok(occurrences) => occurrences
        .iter()
        .map(|occ| (occ.range, occ.symbol))
        .collect(),
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  /// Friendly name for a definition.
  pub fn def_name(&self, def: DefId) -> Option<String> {
    match self.def_name_fallible(def) {
      Ok(name) => name,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn def_name_fallible(&self, def: DefId) -> Result<Option<String>, FatalError> {
    self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).and_then(|d| {
        // `hir-js` `VarDeclarator` nodes are internal containers for variable declarations and do
        // not correspond to user-visible bindings; hide them from the name lookup helper so
        // callers searching by name (tests included) find the actual `Var` binding.
        (!matches!(d.kind, DefKind::VarDeclarator(_))).then(|| d.name.clone())
      }))
    })
  }

  /// Kind of a definition, if known.
  pub fn def_kind(&self, def: DefId) -> Option<DefKind> {
    match self.def_kind_fallible(def) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn def_kind_fallible(&self, def: DefId) -> Result<Option<DefKind>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.def_data.get(&def).map(|d| d.kind.clone())))
  }

  /// Body attached to a definition, if any.
  pub fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    match self.body_of_def_fallible(def) {
      Ok(body) => body,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn body_of_def_fallible(&self, def: DefId) -> Result<Option<BodyId>, FatalError> {
    self.with_analyzed_state(|state| {
      Ok(state.def_data.get(&def).and_then(|d| match &d.kind {
        DefKind::Function(func) => func.body,
        DefKind::Var(var) => {
          if var.body != MISSING_BODY {
            Some(var.body)
          } else {
            state.var_initializer(def).map(|init| init.body)
          }
        }
        DefKind::VarDeclarator(var) => var.body,
        DefKind::Class(class) => class.body,
        DefKind::Enum(en) => en.body,
        DefKind::Namespace(ns) => ns.body,
        DefKind::Module(module) => module.body,
        DefKind::Import(_) | DefKind::ImportAlias(_) => None,
        DefKind::Interface(_) => None,
        DefKind::TypeAlias(_) => None,
      }))
    })
  }

  /// Implicit top-level body for a file, if any.
  pub fn file_body(&self, file: FileId) -> Option<BodyId> {
    match self.file_body_fallible(file) {
      Ok(body) => body,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn file_body_fallible(&self, file: FileId) -> Result<Option<BodyId>, FatalError> {
    self.with_analyzed_state(|state| Ok(state.files.get(&file).and_then(|f| f.top_body)))
  }

  /// Span of a definition, if known.
  pub fn span_of_def(&self, def: DefId) -> Option<Span> {
    match self.span_of_def_fallible(def) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn span_of_def_fallible(&self, def: DefId) -> Result<Option<Span>, FatalError> {
    self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        return Ok(
          state
            .def_data
            .get(&def)
            .map(|data| Span::new(data.file, data.span)),
        );
      }
      if let Some(span) = db::span_of_def(&state.typecheck_db, def) {
        return Ok(Some(span));
      }
      Ok(
        state
          .def_data
          .get(&def)
          .map(|data| Span::new(data.file, data.span)),
      )
    })
  }

  /// Span of an expression within a body, if available from cached results.
  pub fn span_of_expr(&self, body: BodyId, expr: ExprId) -> Option<Span> {
    match self.span_of_expr_fallible(body, expr) {
      Ok(span) => span,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn span_of_expr_fallible(
    &self,
    body: BodyId,
    expr: ExprId,
  ) -> Result<Option<Span>, FatalError> {
    self.with_analyzed_state(|state| {
      if state.snapshot_loaded {
        let Some(meta) = state.body_map.get(&body).copied() else {
          return Ok(None);
        };
        let res = state.check_body(body)?;
        return Ok(res.expr_span(expr).map(|range| Span::new(meta.file, range)));
      }
      if let Some(span) = db::span_of_expr(&state.typecheck_db, body, expr) {
        return Ok(Some(span));
      }
      let Some(meta) = state.body_map.get(&body).copied() else {
        return Ok(None);
      };
      let res = state.check_body(body)?;
      Ok(res.expr_span(expr).map(|range| Span::new(meta.file, range)))
    })
  }
}
