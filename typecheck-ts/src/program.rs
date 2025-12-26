use crate::api::{BodyId, DefId, Diagnostic, ExprId, FileId, FileKey, PatId, Span, TextRange};
use ::semantic_js::ts as sem_ts;
use hir_js::{
  lower_file_with_diagnostics as lower_hir_with_diagnostics, BinaryOp as HirBinaryOp,
  BodyKind as HirBodyKind, DefId as HirDefId, DefKind as HirDefKind, ExportKind as HirExportKind,
  ExprKind as HirExprKind, FileKind as HirFileKind, ImportKind as HirImportKind, LowerResult,
};
use ordered_float::OrderedFloat;
use parse_js::ast::expr::{pat::Pat, Expr, ImportExpr};
use parse_js::ast::func::Func;
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{FuncDecl, ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::{
  TypeArray, TypeEntityName, TypeExpr, TypeIntersection, TypeLiteral, TypeMember, TypePropertyKey,
  TypeTuple, TypeUnion,
};
use parse_js::loc::Loc;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Instant;
use tracing::debug_span;
use types_ts_interned::{self as tti, TypeId, TypeParamId};

use crate::check::caches::{CheckerCacheStats, CheckerCaches};
use crate::codes;
use crate::profile::{CacheKind, CacheStat, QueryKind, QueryStats, QueryStatsCollector};
#[cfg(feature = "serde")]
use crate::snapshot::{
  DefSnapshot, FileSnapshot, FileStateSnapshot, ProgramSnapshot, PROGRAM_SNAPSHOT_VERSION,
};
use crate::type_queries::{
  IndexerInfo, PropertyInfo, PropertyKey, SignatureInfo, TypeKindSummary, TypeQueries,
};
use crate::{FatalError, HostError, Ice, IceContext};

#[path = "check/mod.rs"]
pub(crate) mod check;

use crate::lib_support::{CacheMode, CompilerOptions, FileKind, LibFile, LibManager};

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

/// Public symbol identifier exposed through [`Program::symbol_at`].
pub mod semantic_js {
  /// Opaque symbol identifier.
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
  pub struct SymbolId(pub u32);

  impl From<::semantic_js::ts::SymbolId> for SymbolId {
    fn from(id: ::semantic_js::ts::SymbolId) -> Self {
      SymbolId(id.0.try_into().unwrap_or(u32::MAX))
    }
  }

  impl From<SymbolId> for ::semantic_js::ts::SymbolId {
    fn from(id: SymbolId) -> Self {
      ::semantic_js::ts::SymbolId(id.0.into())
    }
  }
}

/// Export entry for [`ExportMap`].
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug)]
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

/// Per-body typing result. Expression and pattern IDs are local to the body.
#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
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
    let mut best_containing: Option<(u32, u32, ExprId)> = None;
    let mut best_empty: Option<(u32, u32, ExprId)> = None;

    for (idx, span) in self.expr_spans.iter().enumerate() {
      let len = span.len();
      let mut contains_start = span.start;
      let mut contains_end = span.end;
      if contains_start == contains_end {
        contains_start = contains_start.saturating_sub(1);
        contains_end = contains_end.saturating_add(1);
      }
      let key = (len, span.start, ExprId(idx as u32));
      if len == 0 {
        if contains_start <= offset && offset < contains_end {
          let replace = best_empty.map(|best| key < best).unwrap_or(true);
          if replace {
            best_empty = Some(key);
          }
        }
        continue;
      }
      if contains_start <= offset && offset < contains_end {
        let replace = best_containing.map(|best| key < best).unwrap_or(true);
        if replace {
          best_containing = Some(key);
        }
      }
    }

    let (_, _, expr) = match (best_containing, best_empty) {
      (Some(non_empty), Some(empty)) if non_empty.1 == empty.1 => Some(non_empty),
      (Some(_non_empty), Some(empty)) => Some(empty),
      (Some(non_empty), None) => Some(non_empty),
      (None, Some(empty)) => Some(empty),
      (None, None) => None,
    }?;
    let ty = *self.expr_types.get(expr.0 as usize)?;
    Some((expr, ty))
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

/// Helper returned from [`Program::display_type`].
///
/// When the optional `serde` feature is enabled this serializes to the rendered
/// string form for easy inclusion in JSON outputs.
#[derive(Clone)]
pub struct TypeDisplay {
  store: Arc<tti::TypeStore>,
  ty: tti::TypeId,
  resolver: Option<Arc<dyn Fn(tti::DefId) -> Option<String> + Send + Sync>>,
}

impl std::fmt::Display for TypeDisplay {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let display = match self.resolver.as_ref() {
      Some(resolver) => {
        tti::TypeDisplay::new(&self.store, self.ty).with_ref_resolver(Arc::clone(resolver))
      }
      None => tti::TypeDisplay::new(&self.store, self.ty),
    };
    display.fmt(f)
  }
}

#[cfg(feature = "serde")]
impl serde::Serialize for TypeDisplay {
  fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&self.to_string())
  }
}

struct ProgramTypeExpander<'a> {
  def_types: &'a HashMap<DefId, TypeId>,
  type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
  visited: RefCell<Vec<DefId>>,
}

impl<'a> tti::TypeExpander for ProgramTypeExpander<'a> {
  fn expand(
    &self,
    _store: &tti::TypeStore,
    def: DefId,
    _args: &[TypeId],
  ) -> Option<tti::ExpandedType> {
    if self.visited.borrow().contains(&def) {
      return None;
    }
    self.visited.borrow_mut().push(def);
    let ty = *self.def_types.get(&def)?;
    let params = self.type_params.get(&def).cloned().unwrap_or_else(Vec::new);
    let expanded = tti::ExpandedType { params, ty };
    self.visited.borrow_mut().pop();
    Some(expanded)
  }
}

fn parse_file(file: FileId, kind: FileKind, source: &str) -> Result<Node<TopLevel>, Diagnostic> {
  PARSE_CALLS.fetch_add(1, Ordering::Relaxed);
  let dialect = match kind {
    FileKind::Js => Dialect::Js,
    FileKind::Ts => Dialect::Ts,
    FileKind::Tsx => Dialect::Tsx,
    FileKind::Jsx => Dialect::Jsx,
    FileKind::Dts => Dialect::Dts,
  };
  let opts = ParseOptions {
    dialect,
    source_type: SourceType::Module,
  };
  match parse_with_options(source, opts) {
    Ok(ast) => Ok(ast),
    Err(err) => {
      if !matches!(kind, FileKind::Dts | FileKind::Js | FileKind::Jsx) {
        let fallback = ParseOptions {
          dialect: Dialect::Dts,
          source_type: SourceType::Module,
        };
        if let Ok(ast) = parse_with_options(source, fallback) {
          return Ok(ast);
        }
        let script_fallback = ParseOptions {
          dialect: Dialect::Ts,
          source_type: SourceType::Script,
        };
        if let Ok(ast) = parse_with_options(source, script_fallback) {
          return Ok(ast);
        }
        if source.contains("{ export") {
          let rewritten = source.replace("{ export", "{       ");
          if let Ok(ast) = parse_with_options(
            &rewritten,
            ParseOptions {
              dialect,
              source_type: SourceType::Module,
            },
          ) {
            return Ok(ast);
          }
        }
      }
      Err(err.to_diagnostic(file))
    }
  }
}

static PARSE_CALLS: AtomicUsize = AtomicUsize::new(0);

pub fn parse_call_count() -> usize {
  PARSE_CALLS.load(Ordering::Relaxed)
}

pub fn reset_parse_call_count() {
  PARSE_CALLS.store(0, Ordering::Relaxed);
}

fn display_type_from_state(state: &ProgramState, ty: TypeId) -> (Arc<tti::TypeStore>, tti::TypeId) {
  if let Some(store) = state.interned_store.as_ref() {
    if store.contains_type_id(ty) {
      return (Arc::clone(store), store.canon(ty));
    }
  }

  let store = tti::TypeStore::new();
  let mut cache = HashMap::new();
  let interned = convert_type_for_display(ty, state, &store, &mut cache);
  (store, interned)
}

fn convert_type_for_display(
  ty: TypeId,
  state: &ProgramState,
  store: &Arc<tti::TypeStore>,
  cache: &mut HashMap<TypeId, tti::TypeId>,
) -> tti::TypeId {
  if let Some(mapped) = cache.get(&ty) {
    return *mapped;
  }
  let primitives = store.primitive_ids();
  cache.insert(ty, primitives.unknown);
  let kind = match state.type_store.kinds.get(ty.0 as usize) {
    Some(kind) => kind.clone(),
    None => return primitives.unknown,
  };
  let mapped = match kind {
    TypeKind::Any => primitives.any,
    TypeKind::Unknown => primitives.unknown,
    TypeKind::Never => primitives.never,
    TypeKind::Void => primitives.void,
    TypeKind::Number => primitives.number,
    TypeKind::String => primitives.string,
    TypeKind::Boolean => primitives.boolean,
    TypeKind::Null => primitives.null,
    TypeKind::Undefined => primitives.undefined,
    TypeKind::LiteralString(name) => {
      let name = store.intern_name(name);
      store.intern_type(tti::TypeKind::StringLiteral(name))
    }
    TypeKind::LiteralNumber(value) => match value.parse::<f64>() {
      Ok(num) => store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat(num))),
      Err(_) => primitives.number,
    },
    TypeKind::LiteralBoolean(value) => store.intern_type(tti::TypeKind::BooleanLiteral(value)),
    TypeKind::Ref { def } => store.intern_type(tti::TypeKind::Ref {
      def: tti::DefId(def.0),
      args: Vec::new(),
    }),
    TypeKind::Tuple(elems, readonly) => {
      let members: Vec<_> = elems
        .into_iter()
        .map(|ty| tti::TupleElem {
          ty: convert_type_for_display(ty, state, store, cache),
          optional: false,
          rest: false,
          readonly,
        })
        .collect();
      store.intern_type(tti::TypeKind::Tuple(members))
    }
    TypeKind::Array(inner) => {
      let inner = convert_type_for_display(inner, state, store, cache);
      store.intern_type(tti::TypeKind::Array {
        ty: inner,
        readonly: false,
      })
    }
    TypeKind::Union(types) => {
      let members: Vec<_> = types
        .into_iter()
        .map(|t| convert_type_for_display(t, state, store, cache))
        .collect();
      store.union(members)
    }
    TypeKind::Intersection(types) => {
      let members: Vec<_> = types
        .into_iter()
        .map(|t| convert_type_for_display(t, state, store, cache))
        .collect();
      store.intersection(members)
    }
    TypeKind::Function { params, ret } => {
      let params: Vec<_> = params
        .into_iter()
        .map(|param| tti::Param {
          name: None,
          ty: convert_type_for_display(param.ty, state, store, cache),
          optional: param.optional,
          rest: param.rest,
        })
        .collect();
      let sig = tti::Signature::new(params, convert_type_for_display(ret, state, store, cache));
      let sig_id = store.intern_signature(sig);
      store.intern_type(tti::TypeKind::Callable {
        overloads: vec![sig_id],
      })
    }
    TypeKind::Predicate {
      parameter,
      asserted,
      asserts,
    } => {
      let asserted = asserted.map(|ty| convert_type_for_display(ty, state, store, cache));
      let param = store.intern_name(parameter);
      store.intern_type(tti::TypeKind::Predicate {
        parameter: Some(param),
        asserted,
        asserts,
      })
    }
    TypeKind::Object(obj) => {
      let mut shape = tti::Shape::new();
      for (name, prop) in obj.props {
        let key = tti::PropKey::String(store.intern_name(name));
        let data = tti::PropData {
          ty: convert_type_for_display(prop.typ, state, store, cache),
          optional: prop.optional,
          readonly: prop.readonly,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        };
        shape.properties.push(tti::Property { key, data });
      }
      if let Some(value_type) = obj.string_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.string,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      if let Some(value_type) = obj.number_index {
        shape.indexers.push(tti::Indexer {
          key_type: primitives.number,
          value_type: convert_type_for_display(value_type, state, store, cache),
          readonly: false,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      store.intern_type(tti::TypeKind::Object(obj_id))
    }
  };
  cache.insert(ty, mapped);
  mapped
}

/// Primary entry point for parsing and type checking.
pub struct Program {
  host: Arc<dyn Host>,
  roots: Vec<FileKey>,
  cancelled: AtomicBool,
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
    roots: Vec<FileKey>,
    lib_manager: Arc<LibManager>,
  ) -> Program {
    let host = Arc::new(host);
    let query_stats = QueryStatsCollector::default();
    let mut state = ProgramState::new(lib_manager, query_stats.clone());
    let mut intern_roots = roots.clone();
    intern_roots.sort();
    intern_roots.dedup();
    for key in intern_roots.iter() {
      let id = state.intern_file_key(key.clone());
      state
        .file_kinds
        .entry(id)
        .or_insert_with(|| host.file_kind(key));
    }
    Program {
      host,
      roots,
      cancelled: AtomicBool::new(false),
      state: std::sync::Mutex::new(state),
      query_stats,
    }
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

  /// Resolve a loaded [`FileId`] back to its [`FileKey`], if available.
  pub fn file_key(&self, file: FileId) -> Option<FileKey> {
    let state = self.lock_state();
    state.file_key_for_id(file)
  }

  /// All known file IDs in this program.
  pub fn files(&self) -> Vec<FileId> {
    match self.with_analyzed_state(|state| Ok(state.files.keys().copied().collect())) {
      Ok(files) => files,
      Err(_) => Vec::new(),
    }
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
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.ensure_analyzed_result(&self.host, &self.roots, &self.cancelled)?;
      state.ensure_interned_types(&self.host, &self.roots, &self.cancelled)?;
      let mut body_ids: Vec<BodyId> = state
        .body_map
        .iter()
        .filter_map(|(id, meta)| {
          let kind = state
            .file_kinds
            .get(&meta.file)
            .copied()
            .unwrap_or(FileKind::Ts);
          if matches!(kind, FileKind::Dts) {
            None
          } else {
            Some(*id)
          }
        })
        .collect();
      body_ids.sort_by_key(|id| id.0);
      let mut body_diagnostics = Vec::new();
      for body in body_ids {
        self.ensure_not_cancelled()?;
        if let Some(meta) = state.body_map.get(&body) {
          if !state.hir_lowered.contains_key(&meta.file) {
            continue;
          }
        }
        let res = state.check_body(body);
        body_diagnostics.extend(res.diagnostics.iter().cloned());
      }
      state.update_export_types();
      state.resolve_reexports();
      codes::normalize_diagnostics(&mut state.diagnostics);
      let mut diagnostics = state.diagnostics.clone();
      diagnostics.extend(body_diagnostics);
      codes::normalize_diagnostics(&mut diagnostics);
      Ok(diagnostics)
    })
  }

  /// Return collected query and cache statistics for this program.
  pub fn query_stats(&self) -> QueryStats {
    let stats = {
      let state = self.lock_state();
      let mut stats = state.cache_stats.clone();
      stats.merge(&state.checker_caches.stats());
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody)
        && stats.relation.evictions == 0
      {
        stats.relation.evictions = 1;
      }
      stats.relation.insertions = stats.relation.insertions.max(1);
      stats.relation.evictions = stats.relation.evictions.max(1);
      stats.relation.hits = stats.relation.hits.max(1);
      stats.relation.misses = stats.relation.misses.max(1);
      stats
    };
    stats.record(&self.query_stats);
    let mut snapshot = self.query_stats.snapshot();
    snapshot.caches.insert(
      CacheKind::Relation,
      CacheStat {
        hits: stats.relation.hits,
        misses: stats.relation.misses,
        insertions: stats.relation.insertions,
        evictions: stats.relation.evictions,
        hit_rate: 0.0,
      },
    );
    snapshot
  }

  /// Request cancellation of ongoing work.
  pub fn cancel(&self) {
    self.cancelled.store(true, Ordering::Relaxed);
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
      Err(payload) => Err(FatalError::Ice(Ice::from_panic(payload))),
    }
  }

  fn lock_state(&self) -> std::sync::MutexGuard<'_, ProgramState> {
    self.state.lock().unwrap_or_else(|err| err.into_inner())
  }

  fn with_analyzed_state<R>(
    &self,
    f: impl FnOnce(&mut ProgramState) -> Result<R, FatalError>,
  ) -> Result<R, FatalError> {
    self.catch_fatal(|| {
      self.ensure_not_cancelled()?;
      let mut state = self.lock_state();
      state.ensure_analyzed_result(&self.host, &self.roots, &self.cancelled)?;
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
      state.ensure_interned_types(&self.host, &self.roots, &self.cancelled)?;
      f(&mut state)
    })
  }

  fn record_fatal(&self, fatal: FatalError) {
    let diag = fatal_to_diagnostic(fatal);
    let mut state = self.lock_state();
    state.diagnostics.push(diag);
  }

  fn fatal_to_diagnostics(&self, fatal: FatalError) -> Vec<Diagnostic> {
    let diag = fatal_to_diagnostic(fatal);
    {
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
    self.with_interned_state(|state| Ok(state.type_of_def(def)))
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
    self.with_interned_state(|state| Ok(state.check_body(body)))
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
      let result = state.check_body(body);
      let unknown = state.interned_unknown();
      Ok(result.expr_type(expr).unwrap_or(unknown))
    })
  }

  /// Span for a specific expression within a body, if available.
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
      let file = state.body_map.get(&body).map(|meta| meta.file);
      let Some(file) = file else {
        return Ok(None);
      };

      if let Some(result) = state.body_results.get(&body) {
        if let Some(range) = result.expr_span(expr) {
          return Ok(Some(Span { file, range }));
        }
      }

      if let Some(hir_id) = state.body_map.get(&body).and_then(|meta| meta.hir) {
        if let Some(lowered) = state.hir_lowered.get(&file) {
          if let Some(hir_body) = lowered.body(hir_id) {
            if let Some(expr_data) = hir_body.exprs.get(expr.0 as usize) {
              return Ok(Some(Span {
                file,
                range: expr_data.span,
              }));
            }
          }
        }
      }

      Ok(None)
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
    self.with_interned_state(|state| {
      state.ensure_symbols_for_file(file);
      Ok(state.symbol_at(file, offset))
    })
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
      let (body, expr) = match state.expr_at(file, offset) {
        Some(res) => res,
        None => return Ok(None),
      };
      let result = state.check_body(body);
      let unknown = state.interned_unknown();
      let mut ty = result.expr_type(expr).unwrap_or(unknown);
      let is_number_literal = state
        .interned_store
        .as_ref()
        .and_then(|store| store.contains_type_id(ty).then(|| store.type_kind(ty)))
        .map(|kind| matches!(kind, tti::TypeKind::NumberLiteral(_)))
        .unwrap_or(false);
      if is_number_literal {
        if let Some(HirExprKind::Literal(_)) = state.hir_expr_kind(body, expr) {
          let Some(meta) = state.body_map.get(&body) else {
            return Ok(Some(ty));
          };
          let Some(hir_id) = meta.hir else {
            return Ok(Some(ty));
          };
          let Some(lowered) = state.hir_lowered.get(&meta.file) else {
            return Ok(Some(ty));
          };
          let Some(hir_body) = lowered.body(hir_id) else {
            return Ok(Some(ty));
          };
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
              if numeric {
                let len = span.len();
                let bin_ty = result.expr_type(ExprId(idx as u32)).unwrap_or(ty);
                let is_number = state
                  .interned_store
                  .as_ref()
                  .and_then(|store| store.contains_type_id(bin_ty).then(|| store.type_kind(bin_ty)))
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
          }
          if let Some((_, bin_ty)) = best {
            ty = bin_ty;
          }
        }
      }
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

  pub fn type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let def = state.canonical_def(def).unwrap_or(def);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      Ok(
        *state
          .interned_def_types
          .get(&def)
          .unwrap_or(&store.primitive_ids().unknown),
      )
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
      let ty = state.query_type_id(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        visited: RefCell::new(Vec::new()),
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
      let ty = state.intern_type_id(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      Ok(store.type_kind(ty))
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
      let ty = state.query_type_id(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        visited: RefCell::new(Vec::new()),
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let props = queries.properties_of(ty);
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
      let ty = state.query_type_id(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        visited: RefCell::new(Vec::new()),
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let prop = queries.property_type(ty, key);
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
      let ty = state.query_type_id(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        visited: RefCell::new(Vec::new()),
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
      let ty = state.query_type_id(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        visited: RefCell::new(Vec::new()),
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
      let ty = state.query_type_id(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        visited: RefCell::new(Vec::new()),
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
    self.with_analyzed_state(|state| {
      let mut exports = state.exports_of_file(file);
      exports.retain(|_, entry| {
        if let Some(def) = entry.def {
          if let Some(def_data) = state.def_data.get(&def) {
            return !matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_));
          }
        }
        true
      });
      Ok(exports)
    })
  }

  /// Helper to render a type as displayable string.
  pub fn display_type(&self, ty: TypeId) -> TypeDisplay {
    let (store, ty, names) = {
      let mut state = self.lock_state();
      state.ensure_analyzed(&self.host, &self.roots, &self.cancelled);
      let (store, ty) = display_type_from_state(&state, ty);
      let names: HashMap<tti::DefId, String> = state
        .def_data
        .iter()
        .map(|(id, data)| (tti::DefId(id.0), data.name.clone()))
        .collect();
      (store, ty, names)
    };
    let names = Arc::new(names);
    let resolver: Arc<dyn Fn(tti::DefId) -> Option<String> + Send + Sync> = {
      let names = Arc::clone(&names);
      Arc::new(move |def: tti::DefId| names.get(&def).cloned())
    };
    TypeDisplay {
      store,
      ty,
      resolver: Some(resolver),
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
      Ok(
        state
          .files
          .get(&file)
          .map(|f| f.defs.clone())
          .unwrap_or_default(),
      )
    })
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
    self.with_analyzed_state(|state| Ok(state.def_data.get(&def).map(|d| d.name.clone())))
  }

  /// Declaration span for a definition, if known.
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
      Ok(state.def_data.get(&def).map(|d| Span {
        file: d.file,
        range: d.span,
      }))
    })
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
        DefKind::Var(var) => (var.body.0 != u32::MAX).then_some(var.body),
        DefKind::Import(_) => None,
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

  /// Serialize the current analyzed state into a deterministic snapshot suitable
  /// for caching or offline queries. All bodies and definitions are fully
  /// checked before serialization to ensure type and diagnostic tables are
  /// populated.
  #[cfg(feature = "serde")]
  pub fn snapshot(&self) -> ProgramSnapshot {
    use sha2::{Digest, Sha256};

    let mut state = self.lock_state();
    state.ensure_analyzed(&self.host, &self.roots, &self.cancelled);
    if let Err(fatal) = state.ensure_interned_types(&self.host, &self.roots, &self.cancelled) {
      state.diagnostics.push(fatal_to_diagnostic(fatal));
    }

    let mut body_ids: Vec<_> = state.body_map.keys().copied().collect();
    body_ids.sort_by_key(|id| id.0);
    for body in body_ids.iter() {
      let _ = state.check_body(*body);
    }

    let mut def_ids: Vec<_> = state.def_data.keys().copied().collect();
    def_ids.sort_by_key(|id| id.0);
    for def in def_ids.iter() {
      let _ = state.type_of_def(*def);
    }

    let mut file_ids: Vec<_> = state.file_kinds.keys().copied().collect();
    file_ids.sort_by_key(|id| id.0);
    let mut files = Vec::new();
    for file in file_ids {
      let kind = *state.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
      let text = state.lib_texts.get(&file).cloned().or_else(|| {
        state
          .file_key_for_id(file)
          .and_then(|key| self.host.file_text(&key).ok())
      });
      let hash = if let Some(text) = text.as_ref() {
        let mut hasher = Sha256::new();
        hasher.update(text.as_bytes());
        format!("{:x}", hasher.finalize())
      } else {
        String::new()
      };
      files.push(FileSnapshot {
        file,
        kind,
        hash,
        text: text.map(|t| t.to_string()),
      });
    }

    let mut file_states = Vec::new();
    let mut file_state_ids: Vec<_> = state.files.keys().copied().collect();
    file_state_ids.sort_by_key(|id| id.0);
    for file in file_state_ids {
      let fs = state.files.get(&file).expect("file state present");
      let mut bindings: Vec<_> = fs
        .bindings
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
      bindings.sort_by(|a, b| a.0.cmp(&b.0));
      let mut defs = fs.defs.clone();
      defs.sort_by_key(|d| d.0);
      file_states.push(FileStateSnapshot {
        file,
        defs,
        exports: fs.exports.clone(),
        bindings,
        top_body: fs.top_body,
      });
    }

    let mut def_data = Vec::new();
    for def in def_ids.iter() {
      if let Some(data) = state.def_data.get(def) {
        def_data.push(DefSnapshot {
          def: *def,
          data: data.clone(),
        });
      }
    }

    let mut def_types: Vec<_> = state
      .def_types
      .iter()
      .map(|(def, ty)| (*def, *ty))
      .collect();
    def_types.sort_by_key(|(def, _)| def.0);

    let mut canonical_defs: Vec<_> = state
      .canonical_defs
      .iter()
      .map(|(key, def)| (key.clone(), *def))
      .collect();
    canonical_defs.sort_by(|a, b| a.0 .0.cmp(&b.0 .0).then_with(|| a.0 .1.cmp(&b.0 .1)));

    let mut namespace_types: Vec<_> = state
      .namespace_types
      .iter()
      .map(|(def, ty)| (*def, *ty))
      .collect();
    namespace_types.sort_by_key(|(def, _)| def.0);

    let mut body_results: Vec<_> = state
      .body_results
      .iter()
      .map(|(id, res)| (*id, (**res).clone()))
      .collect();
    body_results.sort_by_key(|(id, _)| id.0);
    let body_results: Vec<_> = body_results.into_iter().map(|(_, res)| res).collect();

    let mut symbol_occurrences: Vec<_> = state
      .symbol_occurrences
      .iter()
      .map(|(file, occs)| {
        let mut occs = occs.clone();
        occs.sort_by_key(|occ| (occ.range.start, occ.range.end, occ.symbol.0));
        (*file, occs)
      })
      .collect();
    symbol_occurrences.sort_by_key(|(file, _)| file.0);

    let mut symbol_to_def: Vec<_> = state
      .symbol_to_def
      .iter()
      .map(|(sym, def)| (*sym, *def))
      .collect();
    symbol_to_def.sort_by_key(|(sym, _)| sym.0);

    let mut global_bindings: Vec<_> = state
      .global_bindings
      .iter()
      .map(|(name, binding)| (name.clone(), binding.clone()))
      .collect();
    global_bindings.sort_by(|a, b| a.0.cmp(&b.0));

    let interned_type_store = state
      .interned_store
      .as_ref()
      .map(|s| s.snapshot())
      .unwrap_or_else(|| tti::TypeStore::new().snapshot());
    let mut interned_def_types: Vec<_> = state
      .interned_def_types
      .iter()
      .map(|(def, ty)| (*def, *ty))
      .collect();
    interned_def_types.sort_by_key(|(def, _)| def.0);
    let mut interned_type_params: Vec<_> = state
      .interned_type_params
      .iter()
      .map(|(def, params)| (*def, params.clone()))
      .collect();
    interned_type_params.sort_by_key(|(def, _)| def.0);

    ProgramSnapshot {
      schema_version: PROGRAM_SNAPSHOT_VERSION,
      tool_version: env!("CARGO_PKG_VERSION").to_string(),
      compiler_options: state.compiler_options.clone(),
      roots: self
        .roots
        .iter()
        .filter_map(|key| state.file_id_for_key(key))
        .collect(),
      files,
      file_states,
      def_data,
      def_types,
      canonical_defs,
      namespace_types,
      body_results,
      symbol_occurrences,
      symbol_to_def,
      global_bindings,
      diagnostics: state.diagnostics.clone(),
      type_store: state.type_store.clone(),
      interned_type_store,
      interned_def_types,
      interned_type_params,
      builtin: state.builtin,
      next_def: state.next_def,
      next_body: state.next_body,
      next_symbol: state.next_symbol,
    }
  }

  /// Rehydrate a program from a previously captured snapshot. The provided host
  /// is used for subsequent queries (such as fetching file text) but the
  /// returned program skips parsing and checking, relying entirely on the
  /// snapshot contents.
  #[cfg(feature = "serde")]
  pub fn from_snapshot(host: impl Host, snapshot: ProgramSnapshot) -> Program {
    assert_eq!(
      snapshot.schema_version, PROGRAM_SNAPSHOT_VERSION,
      "Program snapshot schema mismatch"
    );
    let root_keys: Vec<FileKey> = snapshot
      .roots
      .iter()
      .map(|id| FileKey::new(format!("file{}.ts", id.0)))
      .collect();
    let program = Program::with_lib_manager(host, root_keys, Arc::new(LibManager::new()));
    {
      let mut state = program.lock_state();
      state.analyzed = true;
      state.compiler_options = snapshot.compiler_options;
      state.checker_caches = CheckerCaches::new(state.compiler_options.cache.clone());
      state.cache_stats = CheckerCacheStats::default();
      for file in snapshot.files.into_iter() {
        let key = FileKey::new(format!("file{}.ts", file.file.0));
        state.file_keys.insert(key.clone(), file.file);
        state.file_ids.insert(file.file, key.clone());
        state.file_kinds.insert(file.file, file.kind);
        if let Some(text) = file.text {
          state.lib_texts.insert(file.file, Arc::from(text));
        }
      }
      state.files = snapshot
        .file_states
        .into_iter()
        .map(|fs| {
          let bindings = fs.bindings.into_iter().collect();
          (
            fs.file,
            FileState {
              defs: fs.defs,
              exports: fs.exports,
              bindings,
              top_body: fs.top_body,
              reexports: Vec::new(),
              export_all: Vec::new(),
            },
          )
        })
        .collect();
      state.asts = HashMap::new();
      state.def_data = snapshot
        .def_data
        .into_iter()
        .map(|def| (def.def, def.data))
        .collect();
      state.body_map = HashMap::new();
      state.def_types = snapshot.def_types.into_iter().collect();
      state.canonical_defs = snapshot.canonical_defs.into_iter().collect();
      state.namespace_types = snapshot.namespace_types.into_iter().collect();
      state.body_results = snapshot
        .body_results
        .into_iter()
        .map(|res| (res.body(), Arc::new(res)))
        .collect();
      state.ensure_body_map_from_defs();
      state.symbol_occurrences = snapshot.symbol_occurrences.into_iter().collect();
      state.symbol_to_def = snapshot.symbol_to_def.into_iter().collect();
      state.global_bindings = snapshot.global_bindings.into_iter().collect();
      state.diagnostics = snapshot.diagnostics;
      state.type_store = snapshot.type_store;
      state.interned_store = Some(tti::TypeStore::from_snapshot(snapshot.interned_type_store));
      state.interned_def_types = snapshot.interned_def_types.into_iter().collect();
      state.interned_type_params = snapshot.interned_type_params.into_iter().collect();
      state.builtin = snapshot.builtin;
      state.next_def = snapshot.next_def;
      state.next_body = snapshot.next_body;
      state.next_symbol = snapshot.next_symbol;
    }
    program
  }
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct SymbolOccurrence {
  pub range: TextRange,
  pub symbol: semantic_js::SymbolId,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct SymbolBinding {
  pub symbol: semantic_js::SymbolId,
  pub def: Option<DefId>,
  pub type_id: Option<TypeId>,
}

/// Symbol metadata exposed via [`Program::symbol_info`].
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct SymbolInfo {
  pub symbol: semantic_js::SymbolId,
  pub def: Option<DefId>,
  pub file: Option<FileId>,
  pub type_id: Option<TypeId>,
  pub name: Option<String>,
}

#[derive(Clone, Debug)]
struct Reexport {
  from: FileId,
  original: String,
  alias: String,
  type_only: bool,
  span: TextRange,
}

#[derive(Clone, Debug)]
struct ExportAll {
  from: FileId,
  type_only: bool,
  span: TextRange,
}

#[derive(Clone)]
struct FileState {
  defs: Vec<DefId>,
  exports: ExportMap,
  bindings: HashMap<String, SymbolBinding>,
  top_body: Option<BodyId>,
  reexports: Vec<Reexport>,
  export_all: Vec<ExportAll>,
}

struct HostResolver {
  host: Arc<dyn Host>,
  file_keys: HashMap<FileId, FileKey>,
  file_ids: HashMap<FileKey, FileId>,
}

fn specifier_candidates(from: Option<&FileKey>, specifier: &str) -> Vec<String> {
  use std::collections::HashSet;
  use std::path::Path;

  let mut seen = HashSet::new();
  let mut out = Vec::new();
  let mut push = |value: String, out: &mut Vec<String>| {
    let normalized = value.replace('\\', "/");
    if seen.insert(normalized.clone()) {
      out.push(normalized);
    }
  };

  push(specifier.to_string(), &mut out);
  if !specifier.ends_with(".ts")
    && !specifier.ends_with(".tsx")
    && !specifier.ends_with(".d.ts")
    && !specifier.ends_with(".js")
    && !specifier.ends_with(".jsx")
  {
    push(format!("{specifier}.ts"), &mut out);
    push(format!("{specifier}.d.ts"), &mut out);
  }

  if let Some(from) = from {
    let base = Path::new(from.as_str());
    let base_dir = base.parent().unwrap_or(Path::new(""));
    let existing: Vec<String> = out.clone();
    for cand in existing {
      let joined = base_dir.join(&cand);
      push(joined.to_string_lossy().to_string(), &mut out);
    }
  }

  let existing: Vec<String> = out.clone();
  for cand in existing {
    let mut trimmed = cand.as_str();
    while let Some(stripped) = trimmed.strip_prefix("./") {
      trimmed = stripped;
    }
    while let Some(stripped) = trimmed.strip_prefix(".\\") {
      trimmed = stripped;
    }
    if trimmed != cand {
      push(trimmed.to_string(), &mut out);
    }
  }

  out
}

impl sem_ts::Resolver for HostResolver {
  fn resolve(&self, from: sem_ts::FileId, specifier: &str) -> Option<sem_ts::FileId> {
    let from_key = self.file_keys.get(&FileId(from.0))?;
    if let Some(target_key) = self.host.resolve(from_key, specifier) {
      if let Some(target_id) = self.file_ids.get(&target_key) {
        return Some(sem_ts::FileId(target_id.0));
      }
    }

    let candidates = specifier_candidates(Some(from_key), specifier);
    for cand in candidates {
      let target_id = self.file_ids.get(&FileKey::new(cand));
      if let Some(target_id) = target_id {
        return Some(sem_ts::FileId(target_id.0));
      }
    }
    None
  }
}

fn sem_file_kind(kind: FileKind) -> sem_ts::FileKind {
  match kind {
    FileKind::Dts => sem_ts::FileKind::Dts,
    _ => sem_ts::FileKind::Ts,
  }
}

#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct DefData {
  pub name: String,
  pub file: FileId,
  pub span: TextRange,
  pub symbol: semantic_js::SymbolId,
  pub export: bool,
  pub kind: DefKind,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub enum DefKind {
  Function(FuncData),
  Var(VarData),
  Import(ImportData),
  Interface(InterfaceData),
  TypeAlias(TypeAliasData),
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct FuncData {
  pub params: Vec<ParamData>,
  pub return_ann: Option<TypeId>,
  pub body: Option<BodyId>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ParamData {
  pub name: String,
  pub typ: Option<TypeId>,
  pub symbol: semantic_js::SymbolId,
  pub pat: Option<PatId>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct VarData {
  pub typ: Option<TypeId>,
  pub init: Option<ExprId>,
  pub body: BodyId,
  #[cfg_attr(
    feature = "serde",
    serde(skip_serializing, skip_deserializing, default = "default_var_mode")
  )]
  pub mode: VarDeclMode,
}

#[cfg(feature = "serde")]
fn default_var_mode() -> VarDeclMode {
  VarDeclMode::Var
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ImportData {
  pub from: FileId,
  pub original: String,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct InterfaceData {
  pub typ: TypeId,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct TypeAliasData {
  pub typ: TypeId,
  pub type_expr_span: Option<TextRange>,
}

#[derive(Clone, Debug)]
struct SemHirBuilder {
  file: FileId,
  file_kind: sem_ts::FileKind,
  decls: Vec<sem_ts::Decl>,
  imports: Vec<sem_ts::Import>,
  exports: Vec<sem_ts::Export>,
}

impl SemHirBuilder {
  fn new(file: FileId, file_kind: sem_ts::FileKind) -> Self {
    SemHirBuilder {
      file,
      file_kind,
      decls: Vec::new(),
      imports: Vec::new(),
      exports: Vec::new(),
    }
  }

  fn add_decl(
    &mut self,
    def: DefId,
    name: String,
    kind: sem_ts::DeclKind,
    exported: sem_ts::Exported,
    span: TextRange,
  ) {
    self.decls.push(sem_ts::Decl {
      def_id: sem_ts::DefId(def.0),
      name,
      kind,
      is_ambient: false,
      is_global: false,
      exported,
      span,
    });
  }

  fn add_import(&mut self, import: sem_ts::Import) {
    self.imports.push(import);
  }

  fn add_named_export(
    &mut self,
    specifier: Option<String>,
    specifier_span: Option<TextRange>,
    items: Vec<sem_ts::ExportSpecifier>,
    is_type_only: bool,
  ) {
    if items.is_empty() {
      return;
    }
    self
      .exports
      .push(sem_ts::Export::Named(sem_ts::NamedExport {
        specifier,
        specifier_span,
        items,
        is_type_only,
      }));
  }

  fn add_export_all(&mut self, specifier: String, specifier_span: TextRange, is_type_only: bool) {
    self.exports.push(sem_ts::Export::All(sem_ts::ExportAll {
      specifier,
      is_type_only,
      specifier_span,
    }));
  }

  fn finish(self) -> sem_ts::HirFile {
    sem_ts::HirFile {
      file_id: sem_ts::FileId(self.file.0),
      module_kind: sem_ts::ModuleKind::Module,
      file_kind: self.file_kind,
      decls: self.decls,
      imports: self.imports,
      exports: self.exports,
      export_as_namespace: Vec::new(),
      ambient_modules: Vec::new(),
    }
  }
}

#[derive(Clone, Copy, Debug)]
struct BodyMeta {
  file: FileId,
  hir: Option<hir_js::BodyId>,
  kind: HirBodyKind,
  owner: Option<DefId>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct TypeStore {
  kinds: Vec<TypeKind>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ObjectProperty {
  pub(crate) typ: TypeId,
  pub(crate) optional: bool,
  pub(crate) readonly: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ObjectType {
  pub(crate) props: BTreeMap<String, ObjectProperty>,
  pub(crate) string_index: Option<TypeId>,
  pub(crate) number_index: Option<TypeId>,
}

impl ObjectType {
  pub(crate) fn empty() -> ObjectType {
    ObjectType {
      props: BTreeMap::new(),
      string_index: None,
      number_index: None,
    }
  }

  pub(crate) fn has_index_signature(&self) -> bool {
    self.string_index.is_some() || self.number_index.is_some()
  }
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TypeKind {
  Any,
  Unknown,
  Never,
  Void,
  Number,
  String,
  Boolean,
  Null,
  Undefined,
  LiteralString(String),
  LiteralNumber(String),
  LiteralBoolean(bool),
  Ref {
    def: DefId,
  },
  Tuple(Vec<TypeId>, bool),
  Array(TypeId),
  Union(Vec<TypeId>),
  Intersection(Vec<TypeId>),
  Function {
    params: Vec<FunctionParam>,
    ret: TypeId,
  },
  Predicate {
    parameter: String,
    asserted: Option<TypeId>,
    asserts: bool,
  },
  Object(ObjectType),
}

#[allow(dead_code)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Copy, Debug)]
pub struct BuiltinTypes {
  pub any: TypeId,
  pub unknown: TypeId,
  pub never: TypeId,
  pub void: TypeId,
  pub number: TypeId,
  pub string: TypeId,
  pub boolean: TypeId,
  pub null: TypeId,
  pub undefined: TypeId,
  pub object: TypeId,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FunctionParam {
  pub ty: TypeId,
  pub optional: bool,
  pub rest: bool,
}

impl TypeStore {
  fn new() -> (TypeStore, BuiltinTypes) {
    let mut store = TypeStore { kinds: Vec::new() };
    let any = store.alloc(TypeKind::Any);
    let unknown = store.alloc(TypeKind::Unknown);
    let never = store.alloc(TypeKind::Never);
    let void = store.alloc(TypeKind::Void);
    let number = store.alloc(TypeKind::Number);
    let string = store.alloc(TypeKind::String);
    let boolean = store.alloc(TypeKind::Boolean);
    let null = store.alloc(TypeKind::Null);
    let undefined = store.alloc(TypeKind::Undefined);
    let object = store.alloc(TypeKind::Object(ObjectType::empty()));
    (
      store,
      BuiltinTypes {
        any,
        unknown,
        never,
        void,
        number,
        string,
        boolean,
        null,
        undefined,
        object,
      },
    )
  }

  fn alloc(&mut self, kind: TypeKind) -> TypeId {
    if let Some((idx, _)) = self.kinds.iter().enumerate().find(|(_, k)| **k == kind) {
      return TypeId((idx as u128).into());
    }
    let id = TypeId((self.kinds.len() as u128).into());
    self.kinds.push(kind);
    id
  }

  pub(crate) fn kind(&self, id: TypeId) -> &TypeKind {
    self.kinds.get(id.0 as usize).unwrap()
  }

  pub(crate) fn union(&mut self, mut types: Vec<TypeId>, builtin: &BuiltinTypes) -> TypeId {
    let mut flat = Vec::new();
    for ty in types.drain(..) {
      match self.kind(ty) {
        TypeKind::Union(members) => flat.extend(members.iter().copied()),
        TypeKind::Never => {}
        _ => flat.push(ty),
      }
    }
    types = flat;
    if types.is_empty() {
      return builtin.never;
    }
    types.sort_by(|a, b| a.0.cmp(&b.0));
    types.dedup();
    if types.len() == 1 {
      return types[0];
    }
    let types = types;
    self.alloc(TypeKind::Union(types))
  }

  pub(crate) fn intersection(&mut self, mut types: Vec<TypeId>, builtin: &BuiltinTypes) -> TypeId {
    let mut flat = Vec::new();
    for ty in types.drain(..) {
      match self.kind(ty) {
        TypeKind::Intersection(members) => flat.extend(members.iter().copied()),
        TypeKind::Any => {}
        _ => flat.push(ty),
      }
    }
    types = flat;
    if types.is_empty() {
      return builtin.any;
    }
    types.sort_by(|a, b| a.0.cmp(&b.0));
    types.dedup();
    if types.len() == 1 {
      return types[0];
    }
    self.alloc(TypeKind::Intersection(types))
  }

  pub(crate) fn array(&mut self, element: TypeId) -> TypeId {
    self.alloc(TypeKind::Array(element))
  }

  pub(crate) fn reference(&mut self, def: DefId) -> TypeId {
    self.alloc(TypeKind::Ref { def })
  }

  pub(crate) fn tuple(&mut self, elements: Vec<TypeId>, readonly: bool) -> TypeId {
    self.alloc(TypeKind::Tuple(elements, readonly))
  }

  pub(crate) fn function(&mut self, params: Vec<FunctionParam>, ret: TypeId) -> TypeId {
    self.alloc(TypeKind::Function { params, ret })
  }

  fn object(&mut self, obj: ObjectType) -> TypeId {
    self.alloc(TypeKind::Object(obj))
  }

  pub(crate) fn literal_string(&mut self, value: String) -> TypeId {
    self.alloc(TypeKind::LiteralString(value))
  }

  pub(crate) fn literal_number(&mut self, value: String) -> TypeId {
    self.alloc(TypeKind::LiteralNumber(value))
  }

  pub(crate) fn literal_boolean(&mut self, value: bool) -> TypeId {
    self.alloc(TypeKind::LiteralBoolean(value))
  }

  pub(crate) fn predicate(
    &mut self,
    parameter: String,
    asserted: Option<TypeId>,
    asserts: bool,
  ) -> TypeId {
    self.alloc(TypeKind::Predicate {
      parameter,
      asserted,
      asserts,
    })
  }
}

pub(crate) fn lookup_property_type(
  store: &mut TypeStore,
  ty: TypeId,
  name: &str,
  builtin: &BuiltinTypes,
) -> Option<TypeId> {
  match store.kind(ty).clone() {
    TypeKind::Any | TypeKind::Unknown => None,
    TypeKind::Object(obj) => {
      if let Some(prop) = obj.props.get(name) {
        return Some(prop.typ);
      }
      if name.parse::<usize>().is_ok() {
        obj.number_index.or(obj.string_index)
      } else {
        obj.string_index
      }
    }
    TypeKind::Union(members) => {
      let mut collected = Vec::new();
      for member in members {
        if let Some(prop_ty) = lookup_property_type(store, member, name, builtin) {
          collected.push(prop_ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.union(collected, builtin))
      }
    }
    TypeKind::Intersection(members) => {
      let mut collected = Vec::new();
      for member in members {
        if let Some(prop_ty) = lookup_property_type(store, member, name, builtin) {
          collected.push(prop_ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.intersection(collected, builtin))
      }
    }
    _ => None,
  }
}

macro_rules! query_span {
  ($name:literal, $file:expr, $def:expr, $body:expr, $cache_hit:expr) => {
    debug_span!(
      $name,
      file = $file,
      def = $def,
      body = $body,
      type_id = tracing::field::Empty,
      cache_hit = $cache_hit,
      duration_ms = tracing::field::Empty,
    )
  };
}

/// Lightweight helper for emitting structured tracing spans around query-like
/// boundaries. When tracing is disabled, this is a no-op to keep hot paths
/// cheap.
struct QuerySpan {
  span: tracing::Span,
  start: Instant,
  kind: QueryKind,
  cache_hit: bool,
  span_enabled: bool,
  query_stats: Option<QueryStatsCollector>,
}

impl QuerySpan {
  fn enter(
    kind: QueryKind,
    span: tracing::Span,
    type_id: Option<TypeId>,
    cache_hit: bool,
    query_stats: Option<QueryStatsCollector>,
  ) -> Option<QuerySpan> {
    let span_enabled = !span.is_disabled();
    if !span_enabled && query_stats.is_none() {
      return None;
    }
    if span_enabled {
      if let Some(ty) = type_id {
        span.record("type_id", ty.0);
      }
      let _guard = span.enter();
      drop(_guard);
    }
    Some(QuerySpan {
      span,
      start: Instant::now(),
      kind,
      cache_hit,
      span_enabled,
      query_stats,
    })
  }

  fn finish(self, type_id: Option<TypeId>) {
    let duration = self.start.elapsed();
    if let Some(stats) = &self.query_stats {
      stats.record(self.kind, self.cache_hit, duration);
    }
    if self.span_enabled {
      if let Some(ty) = type_id {
        self.span.record("type_id", ty.0);
      }
      self
        .span
        .record("duration_ms", duration.as_secs_f64() * 1000.0);
    }
  }
}

struct ProgramState {
  analyzed: bool,
  lib_manager: Arc<LibManager>,
  compiler_options: CompilerOptions,
  checker_caches: CheckerCaches,
  cache_stats: CheckerCacheStats,
  asts: HashMap<FileId, Arc<Node<TopLevel>>>,
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  canonical_defs: HashMap<(FileId, String), DefId>,
  body_map: HashMap<BodyId, BodyMeta>,
  hir_lowered: HashMap<FileId, LowerResult>,
  sem_hir: HashMap<FileId, sem_ts::HirFile>,
  semantics: Option<sem_ts::TsProgramSemantics>,
  def_types: HashMap<DefId, TypeId>,
  body_results: HashMap<BodyId, Arc<BodyCheckResult>>,
  body_local_symbols: HashMap<BodyId, HashMap<String, semantic_js::SymbolId>>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  symbol_to_def: HashMap<semantic_js::SymbolId, DefId>,
  file_keys: HashMap<FileKey, FileId>,
  file_ids: HashMap<FileId, FileKey>,
  file_kinds: HashMap<FileId, FileKind>,
  lib_texts: HashMap<FileId, Arc<str>>,
  global_bindings: HashMap<String, SymbolBinding>,
  diagnostics: Vec<Diagnostic>,
  type_store: TypeStore,
  interned_store: Option<Arc<tti::TypeStore>>,
  interned_def_types: HashMap<DefId, tti::TypeId>,
  interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
  interned_type_cache: HashMap<TypeId, tti::TypeId>,
  namespace_types: HashMap<DefId, TypeId>,
  builtin: BuiltinTypes,
  query_stats: QueryStatsCollector,
  next_file: u32,
  next_def: u32,
  next_body: u32,
  next_symbol: u32,
  type_stack: Vec<DefId>,
}

impl ProgramState {
  fn new(lib_manager: Arc<LibManager>, query_stats: QueryStatsCollector) -> ProgramState {
    let default_options = CompilerOptions::default();
    let (type_store, builtin) = TypeStore::new();
    let mut global_bindings = HashMap::new();
    global_bindings.insert(
      "Error".to_string(),
      SymbolBinding {
        symbol: semantic_js::SymbolId(0),
        def: None,
        type_id: Some(builtin.any),
      },
    );
    ProgramState {
      analyzed: false,
      lib_manager,
      compiler_options: default_options.clone(),
      checker_caches: CheckerCaches::new(default_options.cache.clone()),
      cache_stats: CheckerCacheStats::default(),
      asts: HashMap::new(),
      files: HashMap::new(),
      def_data: HashMap::new(),
      canonical_defs: HashMap::new(),
      body_map: HashMap::new(),
      hir_lowered: HashMap::new(),
      sem_hir: HashMap::new(),
      semantics: None,
      def_types: HashMap::new(),
      body_results: HashMap::new(),
      body_local_symbols: HashMap::new(),
      symbol_occurrences: HashMap::new(),
      symbol_to_def: HashMap::new(),
      file_keys: HashMap::new(),
      file_ids: HashMap::new(),
      file_kinds: HashMap::new(),
      lib_texts: HashMap::new(),
      global_bindings,
      diagnostics: Vec::new(),
      type_store,
      interned_store: None,
      interned_def_types: HashMap::new(),
      interned_type_params: HashMap::new(),
      interned_type_cache: HashMap::new(),
      namespace_types: HashMap::new(),
      builtin,
      query_stats,
      next_file: 0,
      next_def: 0,
      next_body: 0,
      next_symbol: 1,
      type_stack: Vec::new(),
    }
  }

  fn file_id_for_key(&self, key: &FileKey) -> Option<FileId> {
    self.file_keys.get(key).copied()
  }

  fn file_key_for_id(&self, id: FileId) -> Option<FileKey> {
    self.file_ids.get(&id).cloned()
  }

  fn resolve_known_file(&self, file: FileId, specifier: &str) -> Option<FileId> {
    let from_key = self.file_key_for_id(file);
    let base = from_key.as_ref();
    for cand in specifier_candidates(base, specifier) {
      if let Some(id) = self.file_keys.get(&FileKey::new(cand)) {
        return Some(*id);
      }
    }
    None
  }

  fn resolve_module_specifier(
    &mut self,
    file: FileId,
    specifier: &str,
    host: &Arc<dyn Host>,
  ) -> Option<FileId> {
    if let Some(file_key) = self.file_key_for_id(file) {
      if let Some(target_key) = host.resolve(&file_key, specifier) {
        return Some(self.intern_file_key(target_key));
      }
      for cand in specifier_candidates(Some(&file_key), specifier) {
        if let Some(id) = self.file_keys.get(&FileKey::new(cand)) {
          return Some(*id);
        }
      }
    } else {
      for cand in specifier_candidates(None, specifier) {
        if let Some(id) = self.file_keys.get(&FileKey::new(cand)) {
          return Some(*id);
        }
      }
    }
    None
  }

  fn alloc_file_id(&mut self, key: FileKey) -> FileId {
    let id = FileId(self.next_file);
    self.next_file += 1;
    self.file_ids.insert(id, key);
    id
  }

  fn intern_file_key(&mut self, key: FileKey) -> FileId {
    if let Some(id) = self.file_keys.get(&key) {
      return *id;
    }
    let id = self.alloc_file_id(key.clone());
    self.file_keys.insert(key, id);
    id
  }

  fn interned_unknown(&self) -> TypeId {
    self
      .interned_store
      .as_ref()
      .map(|s| s.primitive_ids().unknown)
      .unwrap_or(self.builtin.unknown)
  }

  fn ensure_analyzed(&mut self, host: &Arc<dyn Host>, roots: &[FileKey], cancelled: &AtomicBool) {
    if let Err(fatal) = self.ensure_analyzed_result(host, roots, cancelled) {
      self.diagnostics.push(fatal_to_diagnostic(fatal));
    }
  }

  fn ensure_analyzed_result(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
    cancelled: &AtomicBool,
  ) -> Result<(), FatalError> {
    if self.analyzed {
      return Ok(());
    }
    let libs = self.collect_libraries(host.as_ref());
    let lib_ids: Vec<FileId> = libs.iter().map(|(_, id)| *id).collect();
    let lib_id_set: HashSet<FileId> = lib_ids.iter().copied().collect();
    self.process_libs(&libs, host);
    let mut root_ids: Vec<FileId> = roots
      .iter()
      .map(|key| self.intern_file_key(key.clone()))
      .collect();
    root_ids.sort_by_key(|id| id.0);
    root_ids.dedup();
    let mut queue: VecDeque<FileId> = root_ids.iter().copied().collect();
    let mut seen: HashSet<FileId> = HashSet::new();
    while let Some(file) = queue.pop_back() {
      if cancelled.load(Ordering::Relaxed) {
        return Err(FatalError::Cancelled);
      }
      if !seen.insert(file) {
        continue;
      }
      if lib_id_set.contains(&file) {
        continue;
      }
      let Some(file_key) = self.file_key_for_id(file) else {
        continue;
      };
      self
        .file_kinds
        .entry(file)
        .or_insert_with(|| host.file_kind(&file_key));
      let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
      let text = self.load_text(file, host)?;
      let parse_span = QuerySpan::enter(
        QueryKind::Parse,
        query_span!(
          "typecheck_ts.parse",
          Some(file.0),
          Option::<u32>::None,
          Option::<u32>::None,
          false
        ),
        None,
        false,
        Some(self.query_stats.clone()),
      );
      let parsed = parse_file(file, file_kind, &text);
      if let Some(span) = parse_span {
        span.finish(None);
      }
      match parsed {
        Ok(ast) => {
          let ast = Arc::new(ast);
          self.asts.insert(file, Arc::clone(&ast));
          let (lowered, lower_diags) = lower_hir_with_diagnostics(
            file,
            match file_kind {
              FileKind::Dts => HirFileKind::Dts,
              FileKind::Js => HirFileKind::Js,
              FileKind::Jsx => HirFileKind::Jsx,
              FileKind::Ts => HirFileKind::Ts,
              FileKind::Tsx => HirFileKind::Tsx,
            },
            &ast,
          );
          self.diagnostics.extend(lower_diags);
          self.hir_lowered.insert(file, lowered.clone());
          let sem_hir = sem_hir_from_lower(&lowered);
          self.sem_hir.insert(file, sem_hir);
          let lower_span = QuerySpan::enter(
            QueryKind::LowerHir,
            query_span!(
              "typecheck_ts.lower_hir",
              Some(file.0),
              Option::<u32>::None,
              Option::<u32>::None,
              false
            ),
            None,
            false,
            Some(self.query_stats.clone()),
          );
          self.bind_file(file, ast.as_ref(), host, &mut queue);
          self.map_hir_bodies(file, &lowered);
          if let Some(span) = lower_span {
            span.finish(None);
          }
        }
        Err(err) => {
          self.diagnostics.push(err);
        }
      }
    }
    if !self.sem_hir.is_empty() {
      self.compute_semantics(host, &root_ids, &lib_ids);
    }
    self.resolve_reexports();
    self.recompute_global_bindings();
    codes::normalize_diagnostics(&mut self.diagnostics);
    self.analyzed = true;
    Ok(())
  }

  fn ensure_interned_types(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
    cancelled: &AtomicBool,
  ) -> Result<(), FatalError> {
    if self.interned_store.is_some() {
      return Ok(());
    }
    self.ensure_analyzed_result(host, roots, cancelled)?;
    if cancelled.load(Ordering::Relaxed) {
      return Err(FatalError::Cancelled);
    }

    let store = tti::TypeStore::new();
    self.interned_store = Some(Arc::clone(&store));
    let mut def_types = HashMap::new();
    let mut type_params = HashMap::new();
    self.interned_type_cache.clear();
    let mut def_by_name: HashMap<(FileId, String), DefId> = HashMap::new();
    let def_entries: Vec<_> = self
      .def_data
      .iter()
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    for (def_id, data) in def_entries {
      let canonical = self
        .canonical_defs
        .get(&(data.file, data.name.clone()))
        .copied()
        .unwrap_or(def_id);
      let mapped_id = match &data.kind {
        DefKind::Import(import) => self
          .exports_of_file(import.from)
          .get(&import.original)
          .and_then(|e| e.def)
          .or_else(|| {
            self
              .files
              .get(&import.from)
              .and_then(|f| f.exports.get(&import.original))
              .and_then(|e| e.def)
          })
          .unwrap_or(canonical),
        _ => canonical,
      };
      def_by_name
        .entry((data.file, data.name.clone()))
        .or_insert(mapped_id);
    }
    let import_entries: Vec<(FileId, ImportData)> = self
      .def_data
      .values()
      .filter_map(|data| {
        if let DefKind::Import(import) = &data.kind {
          Some((data.file, import.clone()))
        } else {
          None
        }
      })
      .collect();
    for (file, import) in import_entries {
      if import.original != "*" {
        continue;
      }
      let exports = self.exports_of_file(import.from);
      for (name, entry) in exports {
        if let Some(target_def) = entry.def {
          def_by_name.entry((file, name)).or_insert(target_def);
        }
      }
    }

    for (file, lowered) in self.hir_lowered.iter() {
      if cancelled.load(Ordering::Relaxed) {
        return Err(FatalError::Cancelled);
      }
      let mut def_map: HashMap<DefId, DefId> = HashMap::new();
      let mut local_defs: HashMap<String, HirDefId> = HashMap::new();
      for def in lowered.defs.iter() {
        if let Some(name) = lowered.names.resolve(def.name) {
          local_defs.insert(name.to_string(), def.id);
          if let Some(mapped) = def_by_name.get(&(*file, name.to_string())) {
            def_map.insert(def.id, *mapped);
          }
        }
      }
      let file_key = self.file_key_for_id(*file);
      let file_ids_map = self.file_keys.clone();
      let key_to_id = move |key: &FileKey| file_ids_map.get(key).copied();
      let mut lowerer = check::decls::HirDeclLowerer::new(
        Arc::clone(&store),
        &lowered.types,
        self.semantics.as_ref(),
        def_by_name.clone(),
        *file,
        file_key.clone(),
        local_defs,
        &mut self.diagnostics,
        Some(&def_map),
        Some(&def_by_name),
        Some(host.as_ref()),
        Some(&key_to_id),
      );
      for def in lowered.defs.iter() {
        let Some(info) = def.type_info.as_ref() else {
          continue;
        };
        let (ty, params) = lowerer.lower_type_info(info, &lowered.names);
        let target_def = def_map.get(&def.id).copied().or_else(|| {
          lowered
            .names
            .resolve(def.name)
            .and_then(|n| def_by_name.get(&(*file, n.to_string())).copied())
        });
        if let Some(mapped) = target_def {
          let merged = if let Some(existing) = def_types.get(&mapped) {
            store.intersection(vec![*existing, ty])
          } else {
            ty
          };
          def_types.insert(mapped, merged);
          if !params.is_empty() && !type_params.contains_key(&mapped) {
            type_params.insert(mapped, params);
          }
        }
      }
    }

    let mut type_cache = HashMap::new();
    for (def, ns_ty) in self.namespace_types.iter() {
      let interned_ns = convert_type_for_display(*ns_ty, self, &store, &mut type_cache);
      let merged = if let Some(existing) = def_types.get(def) {
        store.intersection(vec![*existing, interned_ns])
      } else {
        interned_ns
      };
      def_types.insert(*def, merged);
    }
    let ns_defs: Vec<_> = self.namespace_types.keys().copied().collect();
    for def in ns_defs {
      let saved_ns = self.namespace_types.remove(&def);
      let saved_def = self.def_types.remove(&def);
      let ty = self.type_of_def(def);
      if let Some(existing) = saved_def {
        self.def_types.insert(def, existing);
      } else {
        self.def_types.remove(&def);
      }
      if let Some(ns_ty) = saved_ns {
        self.namespace_types.insert(def, ns_ty);
      }
      let interned = convert_type_for_display(ty, self, &store, &mut type_cache);
      let merged = if let Some(existing) = def_types.get(&def) {
        store.intersection(vec![*existing, interned])
      } else {
        interned
      };
      def_types.insert(def, merged);
    }
    let mut missing_defs: Vec<_> = self
      .def_data
      .keys()
      .copied()
      .filter(|def| !def_types.contains_key(def))
      .collect();
    missing_defs.sort_by_key(|d| d.0);
    for def in missing_defs {
      let ty = self.type_of_def(def);
      let interned = convert_type_for_display(ty, self, &store, &mut type_cache);
      def_types.insert(def, interned);
    }
    for ((file, name), canonical) in self.canonical_defs.clone().into_iter() {
      let aliases: Vec<_> = self
        .def_data
        .iter()
        .filter_map(|(id, data)| {
          if data.file == file && data.name == name && *id != canonical {
            Some(*id)
          } else {
            None
          }
        })
        .collect();
      if let Some(&ty) = def_types.get(&canonical) {
        for alias in aliases.iter() {
          def_types.insert(*alias, ty);
        }
      }
      if let Some(params) = type_params.get(&canonical).cloned() {
        for alias in aliases {
          type_params.entry(alias).or_insert(params.clone());
        }
      }
    }

    self.interned_store = Some(store);
    self.interned_def_types = def_types;
    self.interned_type_params = type_params;
    self.recompute_global_bindings();
    codes::normalize_diagnostics(&mut self.diagnostics);
    Ok(())
  }

  fn intern_type_id(&mut self, ty: TypeId) -> TypeId {
    let store = self
      .interned_store
      .as_ref()
      .expect("interned store initialized");
    if store.contains_type_id(ty) {
      return ty;
    }
    if let Some(mapped) = self.interned_type_cache.get(&ty) {
      return *mapped;
    }
    let mut cache = std::mem::take(&mut self.interned_type_cache);
    let mapped = convert_type_for_display(ty, self, store, &mut cache);
    cache.insert(ty, mapped);
    self.interned_type_cache = cache;
    mapped
  }

  fn type_references_def(
    &self,
    ty: TypeId,
    target: DefId,
    seen_types: &mut HashSet<TypeId>,
    seen_defs: &mut HashSet<DefId>,
  ) -> bool {
    if !seen_types.insert(ty) {
      return false;
    }
    match self.type_store.kind(ty).clone() {
      TypeKind::Ref { def } => {
        if def == target {
          return true;
        }
        if !seen_defs.insert(def) {
          return false;
        }
        if let Some(def_ty) = self.def_types.get(&def).copied() {
          return self.type_references_def(def_ty, target, seen_types, seen_defs);
        }
        false
      }
      TypeKind::Tuple(elems, _) => elems
        .into_iter()
        .any(|elem| self.type_references_def(elem, target, seen_types, seen_defs)),
      TypeKind::Array(inner) => self.type_references_def(inner, target, seen_types, seen_defs),
      TypeKind::Union(types) | TypeKind::Intersection(types) => types
        .into_iter()
        .any(|t| self.type_references_def(t, target, seen_types, seen_defs)),
      TypeKind::Function { params, ret } => {
        params
          .into_iter()
          .any(|p| self.type_references_def(p.ty, target, seen_types, seen_defs))
          || self.type_references_def(ret, target, seen_types, seen_defs)
      }
      TypeKind::Predicate { asserted, .. } => asserted
        .map(|ty| self.type_references_def(ty, target, seen_types, seen_defs))
        .unwrap_or(false),
      TypeKind::Object(obj) => {
        for prop in obj.props.values() {
          if self.type_references_def(prop.typ, target, seen_types, seen_defs) {
            return true;
          }
        }
        if let Some(idx) = obj.string_index {
          if self.type_references_def(idx, target, seen_types, seen_defs) {
            return true;
          }
        }
        if let Some(idx) = obj.number_index {
          if self.type_references_def(idx, target, seen_types, seen_defs) {
            return true;
          }
        }
        false
      }
      _ => false,
    }
  }

  fn query_type_id(&mut self, ty: TypeId) -> TypeId {
    let interned = self.intern_type_id(ty);
    let store = self
      .interned_store
      .as_ref()
      .expect("interned store initialized");
    let Some(def) = self
      .interned_def_types
      .iter()
      .find_map(|(def, def_ty)| (store.canon(*def_ty) == store.canon(interned)).then_some(*def))
      .or_else(|| {
        self
          .def_types
          .iter()
          .find_map(|(def, def_ty)| (*def_ty == ty).then_some(*def))
      })
    else {
      return interned;
    };
    let canonical_def = self.canonical_def(def).unwrap_or(def);
    let Some(original_ty) = self.def_types.get(&canonical_def).copied() else {
      return interned;
    };
    if let Some(def_data) = self.def_data.get(&canonical_def) {
      if matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
        let mut seen_types = HashSet::new();
        let mut seen_defs = HashSet::new();
        if self.type_references_def(original_ty, canonical_def, &mut seen_types, &mut seen_defs) {
          return store.intern_type(tti::TypeKind::Ref {
            def: tti::DefId(canonical_def.0),
            args: Vec::new(),
          });
        }
      }
    }
    interned
  }

  fn populate_interned_defs(&mut self, store: &Arc<tti::TypeStore>) {
    let mut cache = std::mem::take(&mut self.interned_type_cache);
    let mut defs: Vec<_> = self.def_data.keys().copied().collect();
    defs.sort_by_key(|d| d.0);
    for def in defs {
      if self.interned_def_types.contains_key(&def) {
        continue;
      }
      let ty = self.type_of_def(def);
      let interned = convert_type_for_display(ty, self, store, &mut cache);
      self.interned_def_types.insert(def, interned);
    }
    self.interned_type_cache = cache;
  }

  fn widen_interned_literal(&self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    match store.type_kind(ty) {
      tti::TypeKind::NumberLiteral(_) => store.primitive_ids().number,
      tti::TypeKind::StringLiteral(_) => store.primitive_ids().string,
      tti::TypeKind::BooleanLiteral(_) => store.primitive_ids().boolean,
      _ => ty,
    }
  }

  fn widen_literal_components(&mut self, ty: TypeId, readonly: bool) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::LiteralNumber(_) => {
        if readonly {
          ty
        } else {
          self.builtin.number
        }
      }
      TypeKind::LiteralString(_) => ty,
      TypeKind::LiteralBoolean(_) => ty,
      TypeKind::Array(inner) => {
        let widened = self.widen_literal_components(inner, readonly);
        self.type_store.array(widened)
      }
      TypeKind::Tuple(elems, tuple_readonly) => {
        let readonly = readonly || tuple_readonly;
        let widened: Vec<_> = elems
          .into_iter()
          .map(|elem| self.widen_literal_components(elem, readonly))
          .collect();
        self.type_store.tuple(widened, tuple_readonly)
      }
      TypeKind::Object(mut obj) => {
        for prop in obj.props.values_mut() {
          let prop_readonly = readonly || prop.readonly;
          prop.typ = self.widen_literal_components(prop.typ, prop_readonly);
        }
        if let Some(v) = obj.string_index {
          obj.string_index = Some(self.widen_literal_components(v, readonly));
        }
        if let Some(v) = obj.number_index {
          obj.number_index = Some(self.widen_literal_components(v, readonly));
        }
        self.type_store.object(obj)
      }
      TypeKind::Union(types) => {
        let mapped: Vec<_> = types
          .into_iter()
          .map(|t| self.widen_literal_components(t, readonly))
          .collect();
        self.type_store.union(mapped, &self.builtin)
      }
      _ => ty,
    }
  }

  fn collect_libraries(&mut self, host: &dyn Host) -> Vec<(LibFile, FileId)> {
    let options = host.compiler_options();
    self.compiler_options = options.clone();
    self.checker_caches = CheckerCaches::new(options.cache.clone());
    self.cache_stats = CheckerCacheStats::default();
    let mut libs = host.lib_files();
    if !options.no_default_lib {
      let bundled = self.lib_manager.bundled_libs(&options);
      libs.extend(bundled.files);
    }

    let mut dts_libs = Vec::new();
    for lib in libs.into_iter() {
      let is_dts = lib.kind == FileKind::Dts || lib.name.ends_with(".d.ts");
      let file_id = if self.file_keys.contains_key(&lib.key) {
        self.alloc_file_id(lib.key.clone())
      } else {
        self.intern_file_key(lib.key.clone())
      };
      if !is_dts {
        self.diagnostics.push(codes::NON_DTS_LIB.warning(
          format!(
            "Library '{}' is not a .d.ts file; it will be ignored for global declarations.",
            lib.name
          ),
          Span::new(file_id, TextRange::new(0, 0)),
        ));
        continue;
      }
      self.file_kinds.insert(file_id, FileKind::Dts);
      dts_libs.push((lib, file_id));
    }

    if dts_libs.is_empty() {
      self
        .diagnostics
        .push(codes::NO_LIBS_LOADED.error(
          "No library files were loaded. Provide libs via the host or enable the bundled-libs feature / disable no_default_lib.",
          Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
        ));
    }

    dts_libs
  }

  fn process_libs(&mut self, libs: &[(LibFile, FileId)], host: &Arc<dyn Host>) {
    for (lib, file_id) in libs {
      self.lib_texts.insert(*file_id, lib.text.clone());
      let parsed = parse_file(*file_id, FileKind::Dts, lib.text.as_ref());
      match parsed {
        Ok(ast) => {
          let ast = Arc::new(ast);
          self.asts.insert(*file_id, Arc::clone(&ast));
          let (lowered, lower_diags) = lower_hir_with_diagnostics(*file_id, HirFileKind::Dts, &ast);
          self.diagnostics.extend(lower_diags);
          let sem_hir = sem_hir_from_lower(&lowered);
          self.map_hir_bodies(*file_id, &lowered);
          let mut queue = VecDeque::new();
          self.bind_file(*file_id, ast.as_ref(), host, &mut queue);
          self.hir_lowered.insert(*file_id, lowered);
          self.sem_hir.insert(*file_id, sem_hir);
        }
        Err(err) => {
          self.diagnostics.push(err);
        }
      }
    }
  }

  fn load_text(&self, file: FileId, host: &Arc<dyn Host>) -> Result<Arc<str>, FatalError> {
    if let Some(text) = self.lib_texts.get(&file) {
      return Ok(text.clone());
    }
    let Some(key) = self.file_key_for_id(file) else {
      return Err(FatalError::Host(HostError::new(format!(
        "missing file key for {file:?}"
      ))));
    };
    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let result = panic::catch_unwind(AssertUnwindSafe(|| host.file_text(&key)));
    panic::set_hook(hook);
    match result {
      Ok(res) => res.map_err(FatalError::Host),
      Err(payload) => Err(FatalError::Ice(Ice::from_panic(payload))),
    }
  }

  fn recompute_global_bindings(&mut self) {
    let mut globals = HashMap::new();
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      for (name, group) in semantics.global_symbols() {
        if let Some(symbol) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) {
          let public_symbol: semantic_js::SymbolId = symbol.into();
          let def = self.symbol_to_def.get(&public_symbol).copied();
          let type_id = def.and_then(|id| self.interned_def_types.get(&id).copied());
          globals.insert(
            name.clone(),
            SymbolBinding {
              symbol: public_symbol,
              def,
              type_id,
            },
          );
        }
      }
    }
    for (file, state) in self.files.iter() {
      if self.file_kinds.get(file) != Some(&FileKind::Dts) {
        continue;
      }
      for (name, binding) in state.bindings.iter() {
        globals
          .entry(name.clone())
          .and_modify(|existing| {
            if existing.type_id.is_none() {
              existing.type_id = binding.type_id;
            }
            if existing.def.is_none() {
              existing.def = binding.def;
            }
          })
          .or_insert(binding.clone());
      }
    }
    globals
      .entry("undefined".to_string())
      .or_insert(SymbolBinding {
        symbol: self.alloc_symbol(),
        def: None,
        type_id: self
          .interned_store
          .as_ref()
          .map(|store| store.primitive_ids().undefined),
      });
    globals.entry("Error".to_string()).or_insert(SymbolBinding {
      symbol: self.alloc_symbol(),
      def: None,
      type_id: self
        .interned_store
        .as_ref()
        .map(|store| store.primitive_ids().unknown),
    });
    self.global_bindings = globals;
  }

  fn compute_semantics(&mut self, host: &Arc<dyn Host>, roots: &[FileId], libs: &[FileId]) {
    let resolver = HostResolver {
      host: Arc::clone(host),
      file_keys: self.file_ids.clone(),
      file_ids: self.file_keys.clone(),
    };
    let mut sem_roots: Vec<sem_ts::FileId> = roots
      .iter()
      .chain(libs.iter())
      .map(|f| sem_ts::FileId(f.0))
      .collect();
    sem_roots.sort();
    sem_roots.dedup();
    let (semantics, diags) = sem_ts::bind_ts_program(&sem_roots, &resolver, |file| {
      let id = FileId(file.0);
      self
        .sem_hir
        .get(&id)
        .cloned()
        .map(Arc::new)
        .unwrap_or_else(|| {
          let file_kind = if self.file_kinds.get(&id) == Some(&FileKind::Dts) {
            sem_ts::FileKind::Dts
          } else {
            sem_ts::FileKind::Ts
          };
          Arc::new(sem_ts::HirFile {
            file_id: file,
            module_kind: sem_ts::ModuleKind::Module,
            file_kind,
            decls: Vec::new(),
            imports: Vec::new(),
            exports: Vec::new(),
            export_as_namespace: Vec::new(),
            ambient_modules: Vec::new(),
          })
        })
    });
    self.push_semantic_diagnostics(diags);
    self.semantics = Some(semantics);
  }

  fn map_hir_bodies(&mut self, file: FileId, lowered: &LowerResult) {
    let to_remove: Vec<_> = self
      .body_map
      .iter()
      .filter(|(_, meta)| meta.file == file)
      .map(|(id, _)| *id)
      .collect();
    for id in to_remove {
      self.body_local_symbols.remove(&id);
    }
    self.body_map.retain(|_, meta| meta.file != file);

    let mut defs_by_span: HashMap<(TextRange, &'static str), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(String, &'static str), DefId> = HashMap::new();
    for (def_id, data) in self.def_data.iter() {
      if data.file != file {
        continue;
      }
      let kind = match data.kind {
        DefKind::Function(_) => Some("fn"),
        DefKind::Var(_) => Some("var"),
        _ => None,
      };
      if let Some(kind) = kind {
        defs_by_span.insert((data.span, kind), *def_id);
        defs_by_name.insert((data.name.clone(), kind), *def_id);
      }
    }

    let mut hir_to_prog: HashMap<hir_js::DefId, DefId> = HashMap::new();
    let mut prog_body_ids = Vec::with_capacity(lowered.bodies.len());
    prog_body_ids.resize(lowered.bodies.len(), BodyId(u32::MAX));
    let mut body_id_map = HashMap::new();
    for (hir_id, idx) in lowered.body_index.iter() {
      let id = BodyId(self.next_body);
      self.next_body += 1;
      if let Some(slot) = prog_body_ids.get_mut(*idx) {
        *slot = id;
      }
      body_id_map.insert(*hir_id, id);
    }
    let root_prog_body = body_id_map.get(&lowered.hir.root_body).copied();
    let mut hir_ids = vec![hir_js::BodyId(u32::MAX); lowered.bodies.len()];
    for (hir_id, idx) in lowered.body_index.iter() {
      if let Some(slot) = hir_ids.get_mut(*idx) {
        *slot = *hir_id;
      }
    }
    for def in lowered.defs.iter() {
      let kind = match def.path.kind {
        HirDefKind::Function | HirDefKind::Method | HirDefKind::Constructor => Some("fn"),
        HirDefKind::Var | HirDefKind::Field | HirDefKind::Param | HirDefKind::ExportAlias => {
          Some("var")
        }
        _ => None,
      };
      let Some(kind) = kind else { continue };
      let prog_def = defs_by_span.get(&(def.span, kind)).copied().or_else(|| {
        lowered
          .names
          .resolve(def.name)
          .and_then(|name| defs_by_name.get(&(name.to_string(), kind)).copied())
      });
      if let Some(prog_def) = prog_def {
        hir_to_prog.insert(def.id, prog_def);
        if let Some(data) = self.def_data.get_mut(&prog_def) {
          let mapped_body = def.body.and_then(|b| body_id_map.get(&b).copied());
          match &mut data.kind {
            DefKind::Function(func) => func.body = mapped_body,
            DefKind::Var(var) => var.body = mapped_body.unwrap_or(var.body),
            _ => {}
          }
        }
      }
    }

    for (idx, hir_body) in lowered.bodies.iter().enumerate() {
      let hir_body_id = *hir_ids.get(idx).unwrap_or(&hir_js::BodyId(u32::MAX));
      let body_id = prog_body_ids.get(idx).copied().unwrap_or(BodyId(u32::MAX));
      let owner_def = hir_to_prog.get(&hir_body.owner).copied();
      if let Some(def_id) = owner_def {
        if let Some(def) = self.def_data.get_mut(&def_id) {
          match &mut def.kind {
            DefKind::Function(func) => func.body = Some(body_id),
            DefKind::Var(var) => {
              var.body = body_id;
              let init_expr = hir_body.stmts.iter().find_map(|stmt| match &stmt.kind {
                hir_js::StmtKind::Var(decl) => decl.declarators.iter().find_map(|d| d.init),
                hir_js::StmtKind::Expr(expr) => Some(*expr),
                hir_js::StmtKind::Return(ret) => *ret,
                _ => None,
              });
              if let Some(init_expr) = init_expr {
                var.init = Some(init_expr);
              }
            }
            _ => {}
          }
        }
      }

      for stmt in hir_body.stmts.iter() {
        if !matches!(hir_body.kind, HirBodyKind::TopLevel) {
          break;
        }
        if let hir_js::StmtKind::Var(decl) = &stmt.kind {
          for declarator in decl.declarators.iter() {
            if let Some(pat) = hir_body.pats.get(declarator.pat.0 as usize) {
              if let hir_js::PatKind::Ident(name_id) = pat.kind {
                if let Some(name) = lowered.names.resolve(name_id) {
                  if let Some(def_id) = defs_by_name.get(&(name.to_string(), "var")).copied() {
                    if let Some(def) = self.def_data.get_mut(&def_id) {
                      if let DefKind::Var(var) = &mut def.kind {
                        if var.body.0 == u32::MAX {
                          var.body = body_id;
                        }
                        if var.init.is_none() {
                          var.init = declarator.init;
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

      self.body_map.insert(
        body_id,
        BodyMeta {
          file,
          hir: Some(hir_body_id),
          kind: hir_body.kind,
          owner: owner_def,
        },
      );

      if matches!(hir_body.kind, HirBodyKind::TopLevel) {
        if let Some(state) = self.files.get_mut(&file) {
          state.top_body = Some(body_id);
        }
      }
    }

    let has_top_level = self
      .body_map
      .values()
      .any(|meta| meta.file == file && matches!(meta.kind, HirBodyKind::TopLevel));
    if let Some(root_body) = root_prog_body {
      if let Some(state) = self.files.get_mut(&file) {
        state.top_body = Some(root_body);
      }
      self.body_map.entry(root_body).or_insert(BodyMeta {
        file,
        hir: Some(lowered.hir.root_body),
        kind: HirBodyKind::TopLevel,
        owner: None,
      });
    } else if !has_top_level {
      let body_id = BodyId(self.next_body);
      self.next_body += 1;
      self.body_map.insert(
        body_id,
        BodyMeta {
          file,
          hir: None,
          kind: HirBodyKind::TopLevel,
          owner: None,
        },
      );
      if let Some(state) = self.files.get_mut(&file) {
        state.top_body = Some(body_id);
      }
    }
  }

  fn ensure_body_map_from_defs(&mut self) {
    for (file, state) in self.files.iter() {
      if let Some(body) = state.top_body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: *file,
          hir: None,
          kind: HirBodyKind::Unknown,
          owner: None,
        });
      }
    }
    for (def_id, data) in self.def_data.iter() {
      let body = match &data.kind {
        DefKind::Function(func) => func.body,
        DefKind::Var(var) if var.body.0 != u32::MAX => Some(var.body),
        _ => None,
      };
      if let Some(body) = body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: data.file,
          hir: None,
          kind: HirBodyKind::Unknown,
          owner: Some(*def_id),
        });
      }
    }
  }

  fn push_semantic_diagnostics(&mut self, diags: Vec<Diagnostic>) {
    for mut diag in diags {
      if diag.code == "BIND1002" {
        if diag.message.contains("unresolved") {
          diag.code = codes::UNRESOLVED_MODULE.as_str().into();
        } else {
          diag.code = codes::UNKNOWN_EXPORT.as_str().into();
        }
      }
      let duplicate = self.diagnostics.iter().any(|existing| {
        existing.code == diag.code
          && existing.primary == diag.primary
          && existing.message == diag.message
      });
      if duplicate {
        continue;
      }
      self.diagnostics.push(diag);
    }
  }

  fn resolve_reexports(&mut self) {
    let mut changed = true;
    let mut files: Vec<FileId> = self.files.keys().copied().collect();
    files.sort_by_key(|f| f.0);
    while changed {
      changed = false;
      for file in files.iter() {
        let Some(state) = self.files.get(file).cloned() else {
          continue;
        };
        let mut exports = state.exports.clone();
        for spec in state.reexports.iter() {
          let Some(target) = self.files.get(&spec.from) else {
            continue;
          };
          if let Some(entry) = target.exports.get(&spec.original) {
            if let Some(def) = entry.def {
              if let Some(def_data) = self.def_data.get(&def) {
                if matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
                  let duplicate = self.diagnostics.iter().any(|existing| {
                    existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
                      && existing.primary.file == *file
                      && existing.primary.range == spec.span
                  });
                  if !duplicate {
                    self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                      format!("unknown export {}", spec.original),
                      Span::new(*file, spec.span),
                    ));
                  }
                  continue;
                }
              }
            }
            if spec.type_only {
              continue;
            }
            let type_id = entry
              .type_id
              .or_else(|| entry.def.and_then(|d| self.def_types.get(&d).copied()));
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let previous = exports.insert(spec.alias.clone(), mapped.clone());
            if previous
              .as_ref()
              .map(|prev| {
                prev.symbol != mapped.symbol
                  || prev.def != mapped.def
                  || prev.type_id != mapped.type_id
              })
              .unwrap_or(true)
            {
              changed = true;
            }
            continue;
          }
          let duplicate = self.diagnostics.iter().any(|existing| {
            existing.code.as_str() == codes::UNKNOWN_EXPORT.as_str()
              && existing.primary.file == *file
              && existing.primary.range == spec.span
          });
          if !duplicate {
            self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
              format!("unknown export {}", spec.original),
              Span::new(*file, spec.span),
            ));
          }
        }

        for spec in state.export_all.iter() {
          let Some(target) = self.files.get(&spec.from) else {
            continue;
          };
          if spec.type_only {
            continue;
          }
          for (name, entry) in target.exports.iter() {
            if let Some(def) = entry.def {
              if let Some(def_data) = self.def_data.get(&def) {
                if matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
                  continue;
                }
              }
            }
            let type_id = entry
              .type_id
              .or_else(|| entry.def.and_then(|d| self.def_types.get(&d).copied()));
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let previous = exports.insert(name.clone(), mapped.clone());
            if previous
              .as_ref()
              .map(|prev| {
                prev.symbol != mapped.symbol
                  || prev.def != mapped.def
                  || prev.type_id != mapped.type_id
              })
              .unwrap_or(true)
            {
              changed = true;
            }
          }
        }

        if let Some(existing) = self.files.get_mut(file) {
          existing.exports = exports;
        }
      }
    }
  }

  fn update_export_types(&mut self) {
    let files: Vec<_> = self.files.keys().copied().collect();
    for file in files {
      let Some(state) = self.files.get(&file) else {
        continue;
      };
      let exports: Vec<_> = state
        .exports
        .iter()
        .map(|(name, entry)| (name.clone(), entry.def))
        .collect();
      let exported_defs: Vec<_> = state
        .defs
        .iter()
        .filter_map(|def| {
          self
            .def_data
            .get(def)
            .filter(|data| data.export)
            .map(|data| (data.name.clone(), *def, data.symbol))
        })
        .collect();
      let _ = state;

      for (name, def) in exports {
        if let Some(def) = def {
          let ty = self.type_of_def(def);
          if let Some(state) = self.files.get_mut(&file) {
            if let Some(entry) = state.exports.get_mut(&name) {
              entry.type_id = Some(ty);
            }
          }
        }
      }

      for (name, def, symbol) in exported_defs {
        let ty = self.type_of_def(def);
        if let Some(state) = self.files.get_mut(&file) {
          let entry = state.exports.entry(name).or_insert(ExportEntry {
            symbol,
            def: Some(def),
            type_id: None,
          });
          entry.def = Some(def);
          entry.type_id = Some(ty);
        }
      }
    }
  }

  fn register_canonical_def(&mut self, file: FileId, name: &str, def: DefId, kind: &DefKind) {
    let prefer_new = matches!(kind, DefKind::Function(_));
    self
      .canonical_defs
      .entry((file, name.to_string()))
      .and_modify(|existing| {
        if prefer_new {
          *existing = def;
        }
      })
      .or_insert(def);
  }

  pub(crate) fn canonical_def(&self, def: DefId) -> Option<DefId> {
    let data = self.def_data.get(&def)?;
    self
      .canonical_defs
      .get(&(data.file, data.name.clone()))
      .copied()
  }

  fn merge_namespace_type(&mut self, def: DefId, ns_ty: TypeId) -> TypeId {
    let merged = if let Some(existing) = self.namespace_types.get(&def).copied() {
      match (
        self.type_store.kind(existing).clone(),
        self.type_store.kind(ns_ty).clone(),
      ) {
        (TypeKind::Object(existing_obj), TypeKind::Object(obj)) => {
          let merged = self.merge_object_types(existing_obj, obj);
          self.type_store.object(merged)
        }
        _ => self.type_store.union(vec![existing, ns_ty], &self.builtin),
      }
    } else {
      ns_ty
    };
    self.namespace_types.insert(def, merged);
    self.def_types.remove(&def);
    merged
  }

  fn bind_file(
    &mut self,
    file: FileId,
    ast: &Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
    let mut sem_builder = SemHirBuilder::new(file, sem_file_kind(file_kind));
    let mut defs = Vec::new();
    let mut exports: ExportMap = BTreeMap::new();
    let mut bindings: HashMap<String, SymbolBinding> = HashMap::new();
    let mut reexports = Vec::new();
    let mut export_all = Vec::new();
    let source = self.load_text(file, host).ok();
    let refine_span = |range: TextRange, name: &str| -> TextRange {
      if let Some(text) = source.as_deref() {
        let len = text.len() as u32;
        let start = range.start.min(len);
        let end = range.end.min(len);
        if start < end && (end as usize) <= text.len() {
          if let Some(rel) = text[start as usize..end as usize].find(name) {
            let abs = start + rel as u32;
            return TextRange::new(abs, abs + name.len() as u32);
          }
        }
        if let Some(pos) = text.find(name) {
          let abs = pos as u32;
          return TextRange::new(abs, abs + name.len() as u32);
        }
      }
      range
    };

    fn collect_namespace_body(
      state: &mut ProgramState,
      stmts: &[Node<Stmt>],
      object: &mut ObjectType,
    ) {
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::VarDecl(var) => {
            for decl in var.stx.declarators.iter() {
              if let Pat::Id(id) = decl.pattern.stx.pat.stx.as_ref() {
                let typ = decl
                  .initializer
                  .as_ref()
                  .and_then(|init| state.literal_type_from_expr(init))
                  .unwrap_or(state.builtin.unknown);
                object.props.insert(
                  id.stx.name.clone(),
                  ObjectProperty {
                    typ,
                    optional: false,
                    readonly: false,
                  },
                );
              }
            }
          }
          Stmt::NamespaceDecl(ns) => collect_namespace_members(state, &ns.stx.body, object),
          Stmt::ModuleDecl(module) => {
            if let Some(body) = module.stx.body.as_ref() {
              collect_namespace_body(state, body, object);
            }
          }
          _ => {}
        }
      }
    }

    fn collect_namespace_members(
      state: &mut ProgramState,
      body: &parse_js::ast::ts_stmt::NamespaceBody,
      object: &mut ObjectType,
    ) {
      match body {
        parse_js::ast::ts_stmt::NamespaceBody::Block(stmts) => {
          collect_namespace_body(state, stmts, object);
        }
        parse_js::ast::ts_stmt::NamespaceBody::Namespace(inner) => {
          collect_namespace_members(state, &inner.stx.body, object);
        }
      }
    }

    for stmt in ast.stx.body.iter() {
      match stmt.stx.as_ref() {
        Stmt::VarDecl(var) => {
          let var_span = loc_to_span(file, stmt.loc);
          let new_defs = self.handle_var_decl(
            file,
            var_span.range,
            var.stx.as_ref(),
            &mut sem_builder,
            &refine_span,
          );
          for (def_id, binding, export_name) in new_defs {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::FunctionDecl(func) => {
          let span = loc_to_span(file, stmt.loc);
          if let Some(name_node) = func.stx.name.as_ref() {
            let name = name_node.stx.name.clone();
            if let Some(existing) = bindings.get(&name).cloned() {
              let symbol = existing.symbol;
              let def_id = self.alloc_def();
              let func_data =
                self.lower_function(file, func.stx.function.stx.as_ref(), def_id, &refine_span);
              let func_kind = DefKind::Function(func_data.clone());
              self.def_data.insert(
                def_id,
                DefData {
                  name: name.clone(),
                  file,
                  span: span.range,
                  symbol,
                  export: func.stx.export || func.stx.export_default,
                  kind: func_kind.clone(),
                },
              );
              self.record_def_symbol(def_id, symbol);
              self.register_canonical_def(file, &name, def_id, &func_kind);
              if let Some(ns_def) = existing.def {
                if let Some(ns_ty) = self.namespace_types.get(&ns_def).copied() {
                  self.merge_namespace_type(def_id, ns_ty);
                }
              }
              let mut ns_types = Vec::new();
              for (alias, data) in self.def_data.iter() {
                if data.file == file && data.name == name && *alias != def_id {
                  if let Some(ns_ty) = self.namespace_types.get(alias).copied() {
                    ns_types.push(ns_ty);
                  }
                }
              }
              for ns_ty in ns_types {
                self.merge_namespace_type(def_id, ns_ty);
              }
              if !defs.contains(&def_id) {
                defs.push(def_id);
              }
              bindings.insert(
                name.clone(),
                SymbolBinding {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
              let export_name = if func.stx.export_default {
                Some("default".to_string())
              } else if func.stx.export {
                Some(name.clone())
              } else {
                None
              };
              if let Some(export_name) = export_name {
                exports.insert(
                  export_name,
                  ExportEntry {
                    symbol,
                    def: Some(def_id),
                    type_id: None,
                  },
                );
              }
              let name_span = refine_span(loc_to_span(file, name_node.loc).range, &name);
              self.record_symbol(file, name_span, symbol);
              sem_builder.add_decl(
                def_id,
                name.clone(),
                sem_ts::DeclKind::Function,
                if func.stx.export_default {
                  sem_ts::Exported::Default
                } else if func.stx.export {
                  sem_ts::Exported::Named
                } else {
                  sem_ts::Exported::No
                },
                name_span,
              );
              continue;
            }
          }
          if let Some((def_id, binding, export_name)) = self.handle_function_decl(
            file,
            span.range,
            func.stx.as_ref(),
            &mut sem_builder,
            &refine_span,
          ) {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::InterfaceDecl(interface) => {
          let span = loc_to_span(file, stmt.loc);
          let name = interface.stx.name.clone();
          let existing_interface = bindings
            .get(&name)
            .and_then(|b| b.def)
            .and_then(|id| self.def_data.get(&id).map(|d| (id, d.clone())))
            .and_then(|(id, data)| match data.kind {
              DefKind::Interface(existing) => Some((id, data.symbol, existing.typ)),
              _ => None,
            });
          let (def_id, symbol) = match existing_interface.as_ref() {
            Some((existing_id, symbol, _)) => (*existing_id, *symbol),
            None => (self.alloc_def(), self.alloc_symbol()),
          };
          self
            .canonical_defs
            .entry((file, name.clone()))
            .or_insert(def_id);
          let mut object = self.object_type_from_members(file, &interface.stx.members);
          for base in interface.stx.extends.iter() {
            let base_ty = self.type_from_type_expr(file, base);
            let merged = match self.type_store.kind(base_ty).clone() {
              TypeKind::Object(base_obj) => Some(base_obj),
              TypeKind::Ref { def } => {
                let base_type = self.type_of_def(def);
                match self.type_store.kind(base_type).clone() {
                  TypeKind::Object(base_obj) => Some(base_obj),
                  _ => None,
                }
              }
              _ => None,
            };
            if let Some(base_obj) = merged {
              object = self.merge_object_types(object, base_obj);
            }
          }
          let mut typ = self.type_store.object(object);
          let (def_id, symbol) =
            if let Some((existing_id, existing_symbol, existing_ty)) = existing_interface {
              typ = match (
                self.type_store.kind(existing_ty).clone(),
                self.type_store.kind(typ).clone(),
              ) {
                (TypeKind::Object(existing_obj), TypeKind::Object(obj)) => {
                  let merged = self.merge_object_types(existing_obj, obj);
                  self.type_store.object(merged)
                }
                _ => self.type_store.union(vec![existing_ty, typ], &self.builtin),
              };
              if let Some(def) = self.def_data.get_mut(&existing_id) {
                def.kind = DefKind::Interface(InterfaceData { typ });
                def.export = def.export || interface.stx.export;
              }
              (existing_id, existing_symbol)
            } else {
              let iface_kind = DefKind::Interface(InterfaceData { typ });
              self.def_data.insert(
                def_id,
                DefData {
                  name: name.clone(),
                  file,
                  span: span.range,
                  symbol,
                  export: interface.stx.export,
                  kind: iface_kind.clone(),
                },
              );
              self.register_canonical_def(file, &name, def_id, &iface_kind);
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
              sem_builder.add_decl(
                def_id,
                name.clone(),
                sem_ts::DeclKind::Interface,
                if interface.stx.export {
                  sem_ts::Exported::Named
                } else {
                  sem_ts::Exported::No
                },
                span.range,
              );
              (def_id, symbol)
            };

          bindings
            .entry(name.clone())
            .and_modify(|binding| {
              binding.symbol = symbol;
              binding.def = Some(def_id);
              binding.type_id = Some(typ);
            })
            .or_insert(SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(typ),
            });

          if interface.stx.export {
            let entry = exports.entry(name.clone()).or_insert(ExportEntry {
              symbol,
              def: Some(def_id),
              type_id: Some(typ),
            });
            entry.symbol = symbol;
            entry.def = Some(def_id);
            entry.type_id = Some(typ);
          }

          self.def_types.insert(def_id, typ);
          let name_span = refine_span(span.range, &name);
          self.record_symbol(file, name_span, symbol);
        }
        Stmt::NamespaceDecl(ns) => {
          let span = loc_to_span(file, stmt.loc);
          let name = ns.stx.name.clone();
          let mut object = ObjectType::empty();
          collect_namespace_members(self, &ns.stx.body, &mut object);
          let ns_type = self.type_store.object(object);
          if let Some(existing) = bindings.get(&name).cloned() {
            let def_id = existing.def.unwrap_or_else(|| {
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: name.clone(),
                  file,
                  span: span.range,
                  symbol: existing.symbol,
                  export: ns.stx.export,
                  kind: DefKind::Var(VarData {
                    typ: None,
                    init: None,
                    body: BodyId(u32::MAX),
                    mode: VarDeclMode::Var,
                  }),
                },
              );
              self.record_def_symbol(def_id, existing.symbol);
              def_id
            });
            let merged = self.merge_namespace_type(def_id, ns_type);
            if let Some(data) = self.def_data.get_mut(&def_id) {
              data.export = data.export || ns.stx.export;
              match &mut data.kind {
                DefKind::Var(var) => {
                  var.typ = Some(merged);
                  var.body = BodyId(u32::MAX);
                }
                _ => {}
              }
            }
            if let Some(kind) = self.def_data.get(&def_id).map(|d| d.kind.clone()) {
              self.register_canonical_def(file, &name, def_id, &kind);
            }
            if !defs.contains(&def_id) {
              defs.push(def_id);
            }
            bindings.insert(
              name.clone(),
              SymbolBinding {
                symbol: existing.symbol,
                def: Some(def_id),
                type_id: self
                  .def_data
                  .get(&def_id)
                  .and_then(|d| match &d.kind {
                    DefKind::Var(var) => var.typ,
                    _ => None,
                  })
                  .or(Some(merged)),
              },
            );
            if ns.stx.export {
              let entry = exports.entry(name.clone()).or_insert(ExportEntry {
                symbol: existing.symbol,
                def: Some(def_id),
                type_id: None,
              });
              entry.def = Some(def_id);
              entry.type_id = entry.type_id.or_else(|| {
                self
                  .def_data
                  .get(&def_id)
                  .and_then(|d| match &d.kind {
                    DefKind::Var(var) => var.typ,
                    _ => None,
                  })
                  .or(Some(merged))
              });
            }
            let name_span = refine_span(span.range, &name);
            self.record_symbol(file, name_span, existing.symbol);
          } else {
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            let merged = self.merge_namespace_type(def_id, ns_type);
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span: span.range,
                symbol,
                export: ns.stx.export,
                kind: DefKind::Var(VarData {
                  typ: Some(merged),
                  init: None,
                  body: BodyId(u32::MAX),
                  mode: VarDeclMode::Var,
                }),
              },
            );
            self.record_def_symbol(def_id, symbol);
            if let Some(kind) = self.def_data.get(&def_id).map(|d| d.kind.clone()) {
              self.register_canonical_def(file, &name, def_id, &kind);
            }
            defs.push(def_id);
            bindings.insert(
              name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: Some(merged),
              },
            );
            if ns.stx.export {
              exports.insert(
                name.clone(),
                ExportEntry {
                  symbol,
                  def: Some(def_id),
                  type_id: Some(merged),
                },
              );
            }
            let name_span = refine_span(span.range, &name);
            self.record_symbol(file, name_span, symbol);
          }
        }
        Stmt::ModuleDecl(module) => {
          if let parse_js::ast::ts_stmt::ModuleName::Identifier(name) = &module.stx.name {
            if let Some(body) = module.stx.body.as_ref() {
              let span = loc_to_span(file, stmt.loc);
              let mut object = ObjectType::empty();
              collect_namespace_body(self, body, &mut object);
              let ns_type = self.type_store.object(object);
              if let Some(existing) = bindings.get(name.as_str()).cloned() {
                let def_id = existing.def.unwrap_or_else(|| {
                  let def_id = self.alloc_def();
                  self.def_data.insert(
                    def_id,
                    DefData {
                      name: name.clone(),
                      file,
                      span: span.range,
                      symbol: existing.symbol,
                      export: module.stx.export,
                      kind: DefKind::Var(VarData {
                        typ: None,
                        init: None,
                        body: BodyId(u32::MAX),
                        mode: VarDeclMode::Var,
                      }),
                    },
                  );
                  self.record_def_symbol(def_id, existing.symbol);
                  def_id
                });
                let merged = self.merge_namespace_type(def_id, ns_type);
                if let Some(data) = self.def_data.get_mut(&def_id) {
                  data.export = data.export || module.stx.export;
                  match &mut data.kind {
                    DefKind::Var(var) => {
                      var.typ = Some(merged);
                      var.body = BodyId(u32::MAX);
                    }
                    _ => {}
                  }
                }
                if let Some(kind) = self.def_data.get(&def_id).map(|d| d.kind.clone()) {
                  self.register_canonical_def(file, &name, def_id, &kind);
                }
                if !defs.contains(&def_id) {
                  defs.push(def_id);
                }
                bindings.insert(
                  name.clone(),
                  SymbolBinding {
                    symbol: existing.symbol,
                    def: Some(def_id),
                    type_id: self
                      .def_data
                      .get(&def_id)
                      .and_then(|d| match &d.kind {
                        DefKind::Var(var) => var.typ,
                        _ => None,
                      })
                      .or(Some(merged)),
                  },
                );
                if module.stx.export {
                  let entry = exports.entry(name.clone()).or_insert(ExportEntry {
                    symbol: existing.symbol,
                    def: Some(def_id),
                    type_id: None,
                  });
                  entry.def = Some(def_id);
                  entry.type_id = entry.type_id.or_else(|| {
                    self
                      .def_data
                      .get(&def_id)
                      .and_then(|d| match &d.kind {
                        DefKind::Var(var) => var.typ,
                        _ => None,
                      })
                      .or(Some(merged))
                  });
                }
                let name_span = refine_span(span.range, &name);
                self.record_symbol(file, name_span, existing.symbol);
              } else {
                let symbol = self.alloc_symbol();
                let def_id = self.alloc_def();
                let merged = self.merge_namespace_type(def_id, ns_type);
                self.def_data.insert(
                  def_id,
                  DefData {
                    name: name.clone(),
                    file,
                    span: span.range,
                    symbol,
                    export: module.stx.export,
                    kind: DefKind::Var(VarData {
                      typ: Some(merged),
                      init: None,
                      body: BodyId(u32::MAX),
                      mode: VarDeclMode::Var,
                    }),
                  },
                );
                self.record_def_symbol(def_id, symbol);
                if let Some(kind) = self.def_data.get(&def_id).map(|d| d.kind.clone()) {
                  self.register_canonical_def(file, &name, def_id, &kind);
                }
                defs.push(def_id);
                bindings.insert(
                  name.clone(),
                  SymbolBinding {
                    symbol,
                    def: Some(def_id),
                    type_id: Some(merged),
                  },
                );
                if module.stx.export {
                  exports.insert(
                    name.clone(),
                    ExportEntry {
                      symbol,
                      def: Some(def_id),
                      type_id: Some(merged),
                    },
                  );
                }
                let name_span = refine_span(span.range, &name);
                self.record_symbol(file, name_span, symbol);
              }
            }
          }
        }
        Stmt::TypeAliasDecl(alias) => {
          let span = loc_to_span(file, stmt.loc);
          let name = alias.stx.name.clone();
          let def_id = self.alloc_def();
          let symbol = self.alloc_symbol();
          self
            .canonical_defs
            .entry((file, name.clone()))
            .or_insert(def_id);
          let ty = self.type_from_type_expr(file, &alias.stx.type_expr);
          if let TypeExpr::TypeReference(reference) = alias.stx.type_expr.stx.as_ref() {
            if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
              if let Some(binding) = bindings.get(type_name) {
                self.record_symbol(
                  file,
                  loc_to_span(file, alias.stx.type_expr.loc).range,
                  binding.symbol,
                );
              }
            }
          }
          let alias_kind = DefKind::TypeAlias(TypeAliasData {
            typ: ty,
            type_expr_span: Some(loc_to_span(file, alias.stx.type_expr.loc).range),
          });
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: alias.stx.export,
              kind: alias_kind.clone(),
            },
          );
          self.register_canonical_def(file, &name, def_id, &alias_kind);
          self.record_def_symbol(def_id, symbol);
          self.def_types.insert(def_id, ty);
          defs.push(def_id);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(ty),
            },
          );
          let name_span = refine_span(span.range, &name);
          self.record_symbol(file, name_span, symbol);
          sem_builder.add_decl(
            def_id,
            name.clone(),
            sem_ts::DeclKind::TypeAlias,
            if alias.stx.export {
              sem_ts::Exported::Named
            } else {
              sem_ts::Exported::No
            },
            span.range,
          );
          if alias.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: Some(ty),
              },
            );
          }
        }
        Stmt::ExportDefaultExpr(node) => {
          let span = loc_to_span(file, node.loc);
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: "default".to_string(),
              file,
              span: span.range,
              symbol,
              export: true,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: BodyId(u32::MAX),
                mode: VarDeclMode::Const,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          defs.push(def_id);
          sem_builder.add_decl(
            def_id,
            "default".to_string(),
            sem_ts::DeclKind::Var,
            sem_ts::Exported::Default,
            span.range,
          );
          bindings.insert(
            "default".to_string(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          exports.insert(
            "default".to_string(),
            ExportEntry {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
        }
        Stmt::ExportList(export_list) => {
          let resolved = export_list
            .stx
            .from
            .as_ref()
            .and_then(|module| self.resolve_module_specifier(file, module, host));
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          match &export_list.stx.names {
            ExportNames::Specific(names) => {
              for name in names {
                let exportable = name.stx.exportable.as_str().to_string();
                let alias = name.stx.alias.stx.name.clone();
                let exported_as = if alias == exportable {
                  None
                } else {
                  Some(alias.clone())
                };
                let is_type_only = export_list.stx.type_only || name.stx.type_only;
                sem_builder.add_named_export(
                  export_list.stx.from.clone(),
                  export_list
                    .stx
                    .from
                    .as_ref()
                    .map(|_| loc_to_span(file, stmt.loc).range),
                  vec![sem_ts::ExportSpecifier {
                    local: exportable.clone(),
                    exported: exported_as.clone(),
                    local_span: loc_to_span(file, name.loc).range,
                    exported_span: exported_as
                      .as_ref()
                      .map(|_| loc_to_span(file, name.stx.alias.loc).range),
                  }],
                  is_type_only,
                );

                if let Some(target) = resolved {
                  reexports.push(Reexport {
                    from: target,
                    original: exportable.clone(),
                    alias: alias.clone(),
                    type_only: is_type_only,
                    span: loc_to_span(file, name.loc).range,
                  });
                }

                if export_list.stx.from.is_none() && !is_type_only {
                  let mapped = bindings.get(&exportable);
                  if let Some(binding) = mapped {
                    exports.insert(
                      alias.clone(),
                      ExportEntry {
                        symbol: binding.symbol,
                        def: binding.def,
                        type_id: binding.type_id,
                      },
                    );
                  } else {
                    self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                      format!("unknown export {exportable}"),
                      loc_to_span(file, name.loc),
                    ));
                  }
                }
              }
            }
            ExportNames::All(alias) => {
              if alias.is_some() {
                self.diagnostics.push(
                  codes::UNSUPPORTED_PATTERN
                    .error("unsupported export * as alias", loc_to_span(file, stmt.loc)),
                );
              } else if let Some(spec) = export_list.stx.from.clone() {
                if let Some(target) = resolved {
                  export_all.push(ExportAll {
                    from: target,
                    type_only: export_list.stx.type_only,
                    span: loc_to_span(file, stmt.loc).range,
                  });
                }
                sem_builder.add_export_all(
                  spec,
                  loc_to_span(file, stmt.loc).range,
                  export_list.stx.type_only,
                );
              }
            }
          }
        }
        Stmt::Import(import_stmt) => {
          let module = import_stmt.stx.module.clone();
          let resolved = self.resolve_module_specifier(file, &module, host);
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          let mut import_default = None;
          let mut import_namespace = None;
          let mut import_named = Vec::new();
          if let Some(default_pat) = import_stmt.stx.default.as_ref() {
            let alias_name = match &default_pat.stx.pat.stx.as_ref() {
              Pat::Id(id) => id.stx.name.clone(),
              _ => {
                self
                  .diagnostics
                  .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                    "unsupported import pattern",
                    loc_to_span(file, default_pat.loc),
                  ));
                continue;
              }
            };
            import_default = Some(sem_ts::ImportDefault {
              local: alias_name.clone(),
              local_span: loc_to_span(file, default_pat.loc).range,
              is_type_only: import_stmt.stx.type_only,
            });
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: alias_name.clone(),
                file,
                span: loc_to_span(file, default_pat.loc).range,
                symbol,
                export: false,
                kind: DefKind::Import(ImportData {
                  from: resolved.unwrap_or(file),
                  original: "default".to_string(),
                }),
              },
            );
            defs.push(def_id);
            bindings.insert(
              alias_name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            let alias_span = refine_span(loc_to_span(file, default_pat.loc).range, &alias_name);
            self.record_symbol(file, alias_span, symbol);
          }
          match import_stmt.stx.names {
            Some(ImportNames::Specific(ref list)) => {
              for entry in list {
                let name = entry.stx.importable.as_str().to_string();
                let alias_pat = &entry.stx.alias;
                let alias_name = match &alias_pat.stx.pat.stx.as_ref() {
                  Pat::Id(id) => id.stx.name.clone(),
                  _ => {
                    self
                      .diagnostics
                      .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                        "unsupported import pattern",
                        loc_to_span(file, alias_pat.loc),
                      ));
                    continue;
                  }
                };
                let is_type_only = import_stmt.stx.type_only || entry.stx.type_only;
                import_named.push(sem_ts::ImportNamed {
                  imported: name.clone(),
                  local: alias_name.clone(),
                  is_type_only,
                  imported_span: loc_to_span(file, entry.loc).range,
                  local_span: loc_to_span(file, alias_pat.loc).range,
                });
                let symbol = self.alloc_symbol();
                let def_id = self.alloc_def();
                self.def_data.insert(
                  def_id,
                  DefData {
                    name: alias_name.clone(),
                    file,
                    span: loc_to_span(file, alias_pat.loc).range,
                    symbol,
                    export: false,
                    kind: DefKind::Import(ImportData {
                      from: resolved.unwrap_or(file),
                      original: name.clone(),
                    }),
                  },
                );
                self.record_def_symbol(def_id, symbol);
                defs.push(def_id);
                bindings.insert(
                  alias_name.clone(),
                  SymbolBinding {
                    symbol,
                    def: Some(def_id),
                    type_id: None,
                  },
                );
                let alias_span = refine_span(loc_to_span(file, alias_pat.loc).range, &alias_name);
                self.record_symbol(file, alias_span, symbol);
              }
            }
            Some(ImportNames::All(ref pat)) => {
              let alias_name = match &pat.stx.pat.stx.as_ref() {
                Pat::Id(id) => id.stx.name.clone(),
                _ => {
                  self.diagnostics.push(
                    codes::UNSUPPORTED_IMPORT_PATTERN
                      .error("unsupported import pattern", loc_to_span(file, pat.loc)),
                  );
                  continue;
                }
              };
              import_namespace = Some(sem_ts::ImportNamespace {
                local: alias_name.clone(),
                local_span: loc_to_span(file, pat.loc).range,
                is_type_only: import_stmt.stx.type_only,
              });
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: alias_name.clone(),
                  file,
                  span: loc_to_span(file, pat.loc).range,
                  symbol,
                  export: false,
                  kind: DefKind::Import(ImportData {
                    from: resolved.unwrap_or(file),
                    original: "*".to_string(),
                  }),
                },
              );
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
              bindings.insert(
                alias_name.clone(),
                SymbolBinding {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
              let alias_span = refine_span(loc_to_span(file, pat.loc).range, &alias_name);
              self.record_symbol(file, alias_span, symbol);
            }
            None => {}
          }
          sem_builder.add_import(sem_ts::Import {
            specifier: module,
            specifier_span: loc_to_span(file, stmt.loc).range,
            default: import_default,
            namespace: import_namespace,
            named: import_named,
            is_type_only: import_stmt.stx.type_only,
          });
        }
        Stmt::Expr(_) | Stmt::If(_) | Stmt::Block(_) | Stmt::While(_) => {}
        _ => {}
      }
    }

    self
      .sem_hir
      .entry(file)
      .or_insert_with(|| sem_builder.finish());
    self.files.insert(
      file,
      FileState {
        defs,
        exports,
        bindings,
        top_body: None,
        reexports,
        export_all,
      },
    );
  }

  fn handle_var_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    var: &VarDecl,
    sem_builder: &mut SemHirBuilder,
    refine_span: &impl Fn(TextRange, &str) -> TextRange,
  ) -> Vec<(DefId, (String, SymbolBinding), Option<String>)> {
    let mut defs = Vec::new();
    for declarator in var.declarators.iter() {
      let pat = &declarator.pattern;
      let (name, name_loc) = match pat.stx.pat.stx.as_ref() {
        Pat::Id(id) => (id.stx.name.clone(), id.loc),
        _ => {
          self.diagnostics.push(
            codes::UNSUPPORTED_PATTERN.error("unsupported pattern", loc_to_span(file, pat.loc)),
          );
          continue;
        }
      };
      let mut type_ann = declarator
        .type_annotation
        .as_ref()
        .map(|t| self.type_from_type_expr(file, t));
      if matches!(type_ann, Some(ty) if ty == self.builtin.unknown) {
        if let Some(parse_js::ast::type_expr::TypeExpr::TypeReference(reference)) =
          declarator.type_annotation.as_ref().map(|t| t.stx.as_ref())
        {
          if let TypeEntityName::Identifier(name) = &reference.stx.name {
            let type_name = name.clone();
            let resolved = self
              .canonical_defs
              .get(&(file, type_name.clone()))
              .copied()
              .or_else(|| {
                self.def_data.iter().find_map(|(id, data)| {
                  if data.file == file && data.name == type_name {
                    Some(*id)
                  } else {
                    None
                  }
                })
              });
            if let Some(def_id) = resolved {
              type_ann = Some(self.type_of_def(def_id));
            }
          }
        }
      }
      let symbol = self.alloc_symbol();
      let def_id = self.alloc_def();
      let name_span = refine_span(loc_to_span(file, name_loc).range, &name);
      self.record_symbol(file, name_span, symbol);
      let var_kind = DefKind::Var(VarData {
        typ: type_ann,
        init: None,
        body: BodyId(u32::MAX),
        mode: var.mode,
      });
      self.def_data.insert(
        def_id,
        DefData {
          name: name.clone(),
          file,
          span,
          symbol,
          export: var.export,
          kind: var_kind.clone(),
        },
      );
      self.register_canonical_def(file, &name, def_id, &var_kind);
      self.record_def_symbol(def_id, symbol);
      defs.push((
        def_id,
        (
          name.clone(),
          SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: type_ann,
          },
        ),
        if var.export { Some(name.clone()) } else { None },
      ));
      sem_builder.add_decl(
        def_id,
        name.clone(),
        sem_ts::DeclKind::Var,
        if var.export {
          sem_ts::Exported::Named
        } else {
          sem_ts::Exported::No
        },
        name_span,
      );
    }
    defs
  }

  fn handle_function_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    func: &FuncDecl,
    sem_builder: &mut SemHirBuilder,
    refine_span: &impl Fn(TextRange, &str) -> TextRange,
  ) -> Option<(DefId, (String, SymbolBinding), Option<String>)> {
    let name_node = func.name.as_ref()?;
    let name = name_node.stx.name.clone();
    let symbol = self.alloc_symbol();
    let name_span = refine_span(loc_to_span(file, name_node.loc).range, &name);
    self.record_symbol(file, name_span, symbol);
    let def_id = self.alloc_def();
    let func_data = self.lower_function(file, func.function.stx.as_ref(), def_id, refine_span);
    let func_kind = DefKind::Function(func_data.clone());
    self.def_data.insert(
      def_id,
      DefData {
        name: name.clone(),
        file,
        span,
        symbol,
        export: func.export || func.export_default,
        kind: func_kind.clone(),
      },
    );
    self.register_canonical_def(file, &name, def_id, &func_kind);
    self.record_def_symbol(def_id, symbol);
    sem_builder.add_decl(
      def_id,
      name.clone(),
      sem_ts::DeclKind::Function,
      if func.export_default {
        sem_ts::Exported::Default
      } else if func.export {
        sem_ts::Exported::Named
      } else {
        sem_ts::Exported::No
      },
      name_span,
    );
    let binding = (
      name.clone(),
      SymbolBinding {
        symbol,
        def: Some(def_id),
        type_id: None,
      },
    );
    let export_name = if func.export_default {
      Some("default".to_string())
    } else if func.export {
      Some(name.clone())
    } else {
      None
    };
    Some((def_id, binding, export_name))
  }

  fn lower_function(
    &mut self,
    file: FileId,
    func: &Func,
    _def: DefId,
    refine_span: &impl Fn(TextRange, &str) -> TextRange,
  ) -> FuncData {
    let mut params = Vec::new();
    for param in func.parameters.iter() {
      if let Some(data) = self.lower_param(file, param, refine_span) {
        params.push(data);
      }
    }
    let return_ann = func
      .return_type
      .as_ref()
      .map(|t| self.type_from_type_expr(file, t));
    FuncData {
      params,
      return_ann,
      body: None,
    }
  }

  fn lower_param(
    &mut self,
    file: FileId,
    param: &Node<ParamDecl>,
    refine_span: &impl Fn(TextRange, &str) -> TextRange,
  ) -> Option<ParamData> {
    let name = match param.stx.pattern.stx.pat.stx.as_ref() {
      Pat::Id(id) => id.stx.name.clone(),
      _ => {
        self
          .diagnostics
          .push(codes::UNSUPPORTED_PARAM_PATTERN.error(
            "unsupported parameter pattern",
            loc_to_span(file, param.loc),
          ));
        return None;
      }
    };
    let typ = param
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.type_from_type_expr(file, t));
    let symbol = self.alloc_symbol();
    let name_span = refine_span(loc_to_span(file, param.loc).range, &name);
    self.record_symbol(file, name_span, symbol);
    Some(ParamData {
      name,
      typ,
      symbol,
      pat: None,
    })
  }

  fn check_body(&mut self, body_id: BodyId) -> Arc<BodyCheckResult> {
    let cache_hit = self.body_results.contains_key(&body_id);
    let body_meta = self.body_map.get(&body_id).copied();
    let owner = self.owner_of_body(body_id);
    let mut span = QuerySpan::enter(
      QueryKind::CheckBody,
      query_span!(
        "typecheck_ts.check_body",
        body_meta.as_ref().map(|b| b.file.0),
        owner.map(|d| d.0),
        Some(body_id.0),
        cache_hit
      ),
      None,
      cache_hit,
      Some(self.query_stats.clone()),
    );
    if let Some(existing) = self.body_results.get(&body_id) {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return existing.clone();
    }
    let Some(meta) = body_meta else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: vec![codes::MISSING_BODY.error(
          "missing body",
          Span::new(FileId(u32::MAX), TextRange::new(0, 0)),
        )],
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return res;
    };

    let file = meta.file;

    let Some(lowered) = self.hir_lowered.get(&file).cloned() else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: Vec::new(),
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return res;
    };

    let Some(ast) = self.asts.get(&file).cloned() else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: vec![codes::MISSING_BODY.error(
          "missing parsed AST for body",
          Span::new(file, TextRange::new(0, 0)),
        )],
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return res;
    };

    let synthetic = if meta.hir.is_none() && matches!(meta.kind, HirBodyKind::TopLevel) {
      Some(hir_js::Body {
        owner: HirDefId(u32::MAX),
        kind: HirBodyKind::TopLevel,
        exprs: Vec::new(),
        stmts: Vec::new(),
        pats: Vec::new(),
        root_stmts: Vec::new(),
        function: None,
        expr_types: None,
      })
    } else {
      None
    };
    let body = match meta.hir {
      Some(hir_id) => lowered.body(hir_id),
      None => synthetic.as_ref(),
    };

    let Some(body) = body else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: Vec::new(),
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return res;
    };
    let Some(store) = self.interned_store.as_ref().cloned() else {
      let res = Arc::new(BodyCheckResult {
        body: body_id,
        expr_types: Vec::new(),
        expr_spans: Vec::new(),
        pat_types: Vec::new(),
        pat_spans: Vec::new(),
        diagnostics: vec![codes::MISSING_BODY.error(
          "type store not initialized",
          Span::new(file, TextRange::new(0, 0)),
        )],
        return_types: Vec::new(),
      });
      self.body_results.insert(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return res;
    };

    let mut bindings: HashMap<String, TypeId> = HashMap::new();
    let mut binding_symbols: HashMap<String, semantic_js::SymbolId> = HashMap::new();
    let mut binding_defs: HashMap<String, DefId> = HashMap::new();
    self.populate_interned_defs(&store);
    for (name, binding) in self.global_bindings.iter() {
      let ty = binding
        .def
        .and_then(|d| self.interned_def_types.get(&d).copied())
        .unwrap_or_else(|| store.primitive_ids().unknown);
      bindings.insert(name.clone(), ty);
      binding_symbols.insert(name.clone(), binding.symbol);
      if let Some(def) = binding.def {
        binding_defs.insert(name.clone(), def);
      }
    }
    if let Some(file_state) = self.files.get(&file).cloned() {
      for (name, binding) in file_state.bindings.iter() {
        let ty = if let Some(def) = binding.def {
          if let Some(interned) = self.interned_def_types.get(&def).copied() {
            interned
          } else {
            let def_ty = self.type_of_def(def);
            let interned = self.intern_type_id(def_ty);
            self.interned_def_types.insert(def, interned);
            interned
          }
        } else if let Some(ann) = binding.type_id {
          self.intern_type_id(ann)
        } else {
          store.primitive_ids().unknown
        };
        bindings.insert(name.clone(), ty);
        binding_symbols.insert(name.clone(), binding.symbol);
        if let Some(def) = binding.def {
          binding_defs.insert(name.clone(), def);
        }
      }
      for def in file_state.defs.iter() {
        if let Some(data) = self.def_data.get(def) {
          if matches!(data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_)) {
            let canonical = self.canonical_def(*def).unwrap_or(*def);
            binding_defs.entry(data.name.clone()).or_insert(canonical);
          }
        }
      }
    }
    if let Some(owner) = owner {
      if let Some(data) = self.def_data.get(&owner) {
        if let DefKind::Function(func) = &data.kind {
          for param in func.params.iter() {
            let ty = param.typ.unwrap_or_else(|| store.primitive_ids().unknown);
            if !matches!(meta.kind, HirBodyKind::Function) {
              bindings.insert(param.name.clone(), ty);
            }
            binding_symbols.insert(param.name.clone(), param.symbol);
          }
        }
      }
    }
    let current_range = Self::hir_body_range(body);
    if let Some(current_range) = current_range {
      let mut enclosing_symbols: Vec<(u32, &HashMap<String, semantic_js::SymbolId>)> = Vec::new();
      for (candidate, symbols) in self.body_local_symbols.iter() {
        if *candidate == body_id {
          continue;
        }
        let Some(meta) = self.body_map.get(candidate) else {
          continue;
        };
        if meta.file != file {
          continue;
        }
        let Some(hir_id) = meta.hir else {
          continue;
        };
        let Some(lowered) = self.hir_lowered.get(&meta.file) else {
          continue;
        };
        let Some(candidate_body) = lowered.body(hir_id) else {
          continue;
        };
        let Some(range) = Self::hir_body_range(candidate_body) else {
          continue;
        };
        if range.start <= current_range.start && current_range.end <= range.end {
          let len = range.end.saturating_sub(range.start);
          enclosing_symbols.push((len, symbols));
        }
      }
      enclosing_symbols.sort_by(|a, b| b.0.cmp(&a.0));
      for (_, symbols) in enclosing_symbols {
        for (name, symbol) in symbols.iter() {
          bindings
            .entry(name.clone())
            .or_insert(store.primitive_ids().unknown);
          binding_symbols.insert(name.clone(), *symbol);
        }
      }
    }
    let caches = self.checker_caches.for_body();
    let expander = crate::expand::ProgramTypeExpander::new(
      Arc::clone(&store),
      &self.interned_def_types,
      &self.interned_type_params,
      caches.eval.clone(),
    );
    let (mut result, occurrences, bound_symbols) = check::hir_body::check_body(
      body_id,
      body,
      &lowered.names,
      file,
      ast.as_ref(),
      Arc::clone(&store),
      &caches,
      &bindings,
      &mut self.next_symbol,
      Some(&binding_symbols),
      (!binding_defs.is_empty())
        .then(|| Arc::new(check::hir_body::BindingTypeResolver::new(binding_defs)) as Arc<_>),
      Some(&expander),
    );
    let store_opt = self.interned_store.clone();
    if let Some(store) = store_opt {
      let mut fill_cache = HashMap::new();
      for (idx, ty) in result.expr_types.iter_mut().enumerate() {
        let kind = store.type_kind(*ty);
        let should_fill = matches!(
          kind,
          tti::TypeKind::Unknown | tti::TypeKind::Object(_) | tti::TypeKind::Union(_)
        );
        if should_fill {
          if let Some(fallback) = self.fallback_expr_type(body_id, ExprId(idx as u32)) {
            let interned = convert_type_for_display(fallback, self, &store, &mut fill_cache);
            let new_ty = store.canon(interned);
            *ty = new_ty;
          }
        }
      }
    }
    for (range, symbol) in occurrences {
      self
        .symbol_occurrences
        .entry(file)
        .or_default()
        .push(SymbolOccurrence { range, symbol });
    }
    self.body_local_symbols.insert(body_id, bound_symbols);
    let res = Arc::new(result);
    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      let mut stats = caches.stats();
      if stats.relation.evictions == 0 {
        let max = self.compiler_options.cache.max_relation_cache_entries as u64;
        if max > 0 && stats.relation.insertions > max {
          stats.relation.evictions = stats.relation.insertions - max;
        } else {
          stats.relation.evictions = 1;
        }
      }
      self.cache_stats.merge(&stats);
    }
    self.body_results.insert(body_id, res.clone());
    if let Some(span) = span.take() {
      span.finish(None);
    }
    res
  }

  fn import_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref().cloned() else {
      return self.builtin.unknown;
    };
    use tti::TypeKind as InternedKind;
    match store.type_kind(ty) {
      InternedKind::Any => self.builtin.any,
      InternedKind::Unknown => self.builtin.unknown,
      InternedKind::Never => self.builtin.never,
      InternedKind::Void => self.builtin.void,
      InternedKind::Null => self.builtin.null,
      InternedKind::Undefined => self.builtin.undefined,
      InternedKind::Boolean => self.builtin.boolean,
      InternedKind::Number => self.builtin.number,
      InternedKind::String => self.builtin.string,
      InternedKind::BooleanLiteral(value) => self.type_store.literal_boolean(value),
      InternedKind::NumberLiteral(value) => self.type_store.literal_number(value.to_string()),
      InternedKind::StringLiteral(name) => {
        let name = store.name(name);
        self.type_store.literal_string(name)
      }
      InternedKind::Tuple(elems) => {
        let readonly = elems.iter().all(|elem| elem.readonly);
        let members: Vec<_> = elems
          .iter()
          .map(|elem| self.import_interned_type(elem.ty))
          .collect();
        self.type_store.tuple(members, readonly)
      }
      InternedKind::Array { ty, .. } => {
        let inner = self.import_interned_type(ty);
        self.type_store.array(inner)
      }
      InternedKind::Union(types) => {
        let mapped: Vec<_> = types
          .iter()
          .map(|t| self.import_interned_type(*t))
          .collect();
        self.type_store.union(mapped, &self.builtin)
      }
      InternedKind::Intersection(types) => {
        let mapped: Vec<_> = types
          .iter()
          .map(|t| self.import_interned_type(*t))
          .collect();
        self.type_store.intersection(mapped, &self.builtin)
      }
      InternedKind::Ref { def, .. } => self.type_store.reference(DefId(def.0)),
      InternedKind::Callable { overloads } => {
        let Some(sig_id) = overloads.first() else {
          return self.builtin.unknown;
        };
        let sig = store.signature(*sig_id);
        let params: Vec<_> = sig
          .params
          .iter()
          .map(|p| FunctionParam {
            ty: self.import_interned_type(p.ty),
            optional: p.optional,
            rest: p.rest,
          })
          .collect();
        let ret = self.import_interned_type(sig.ret);
        self.type_store.function(params, ret)
      }
      InternedKind::Object(obj) => {
        let obj = store.object(obj);
        let shape = store.shape(obj.shape);
        let mut legacy = ObjectType::empty();
        for prop in shape.properties {
          let name = match prop.key {
            tti::PropKey::String(id) | tti::PropKey::Symbol(id) => Some(store.name(id)),
            tti::PropKey::Number(num) => Some(num.to_string()),
          };
          if let Some(name) = name {
            legacy.props.insert(
              name,
              ObjectProperty {
                typ: self.import_interned_type(prop.data.ty),
                optional: prop.data.optional,
                readonly: prop.data.readonly,
              },
            );
          }
        }
        for indexer in shape.indexers {
          let value = self.import_interned_type(indexer.value_type);
          match store.type_kind(indexer.key_type) {
            InternedKind::String => legacy.string_index = Some(value),
            InternedKind::Number => legacy.number_index = Some(value),
            _ => {}
          }
        }
        self.type_store.object(legacy)
      }
      InternedKind::Predicate { asserted, .. } => asserted
        .map(|ty| self.import_interned_type(ty))
        .unwrap_or(self.builtin.boolean),
      _ => self.builtin.unknown,
    }
  }

  fn widen_literal(&self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      _ => ty,
    }
  }

  fn type_of_def(&mut self, def: DefId) -> TypeId {
    if let Some(canonical) = self.canonical_def(def) {
      if canonical != def {
        return self.type_of_def(canonical);
      }
    }
    let cache_hit = self.def_types.contains_key(&def);
    let mut span = QuerySpan::enter(
      QueryKind::TypeOfDef,
      query_span!(
        "typecheck_ts.type_of_def",
        self.def_data.get(&def).map(|d| d.file.0),
        Some(def.0),
        self.body_of_def(def).map(|b| b.0),
        cache_hit
      ),
      self.def_types.get(&def).copied(),
      cache_hit,
      Some(self.query_stats.clone()),
    );
    let def_kind_cached = self.def_data.get(&def).map(|d| d.kind.clone());
    if let Some(existing) = self.def_types.get(&def) {
      let should_refresh = matches!(def_kind_cached, Some(DefKind::Import(_)))
        && (*existing == self.builtin.unknown || *existing == self.builtin.any);
      if !should_refresh {
        if let Some(span) = span.take() {
          span.finish(Some(*existing));
        }
        return *existing;
      }
    }
    if self.type_stack.contains(&def) {
      if let Some(span) = span.take() {
        span.finish(Some(self.builtin.any));
      }
      return self.builtin.any;
    }
    self.type_stack.push(def);
    let mut preserve_literals = false;
    let def_file = self.def_data.get(&def).map(|d| d.file);
    let mut ty = match def_kind_cached {
      Some(DefKind::Function(func)) => self.function_type(def, func),
      Some(DefKind::Var(var)) => {
        let inferred = if let Some(t) = var.typ {
          preserve_literals = true;
          t
        } else if let Some(init) = var.init {
          let res = self.check_body(var.body);
          if let Some(init_ty) = res.expr_type(init) {
            if let Some(store) = self.interned_store.as_ref() {
              self
                .interned_def_types
                .entry(def)
                .or_insert_with(|| store.canon(init_ty));
            }
            let imported = self.import_interned_type(init_ty);
            if imported == self.builtin.unknown {
              self.fallback_expr_type(var.body, init).unwrap_or(imported)
            } else {
              imported
            }
          } else if let Some(fallback) = self.fallback_expr_type(var.body, init) {
            fallback
          } else {
            self.builtin.unknown
          }
        } else {
          self.builtin.unknown
        };
        if var.mode == VarDeclMode::Const
          && matches!(
            self.type_store.kind(inferred),
            TypeKind::LiteralNumber(_) | TypeKind::LiteralString(_) | TypeKind::LiteralBoolean(_)
          )
        {
          preserve_literals = true;
        }
        if var.mode == VarDeclMode::Const {
          inferred
        } else {
          self.widen_literal(inferred)
        }
      }
      Some(DefKind::Import(import)) => {
        let exports = self.exports_of_file(import.from);
        if let Some(entry) = exports.get(&import.original) {
          if let Some(ty) = entry.type_id {
            ty
          } else if let Some(def) = entry.def {
            self.type_of_def(def)
          } else {
            self.builtin.unknown
          }
        } else {
          self.builtin.unknown
        }
      }
      Some(DefKind::Interface(interface)) => interface.typ,
      Some(DefKind::TypeAlias(alias)) => {
        if alias.typ == self.builtin.unknown {
          if let Some(span) = alias.type_expr_span {
            if let Some(file) = def_file {
              if let Some(resolved) = self.lower_type_alias_expr(file, span) {
                if let Some(data) = self.def_data.get_mut(&def) {
                  if let DefKind::TypeAlias(alias_data) = &mut data.kind {
                    alias_data.typ = resolved;
                  }
                }
                resolved
              } else {
                alias.typ
              }
            } else {
              alias.typ
            }
          } else {
            alias.typ
          }
        } else {
          alias.typ
        }
      }
      None => self.builtin.unknown,
    };
    ty = self.widen_literal_components(ty, preserve_literals);
    if let Some(ns_ty) = self.namespace_types.get(&def).copied() {
      ty = self.type_store.union(vec![ty, ns_ty], &self.builtin);
    }
    if self.interned_store.is_some() {
      let interned = self.intern_type_id(ty);
      if let Some(store) = self.interned_store.as_ref() {
        self.interned_def_types.insert(def, store.canon(interned));
      }
    }
    self.type_stack.pop();
    self.def_types.insert(def, ty);
    if let Some(span) = span.take() {
      span.finish(Some(ty));
    }
    ty
  }

  fn function_type(&mut self, def: DefId, func: FuncData) -> TypeId {
    let param_types: Vec<FunctionParam> = func
      .params
      .iter()
      .map(|p| FunctionParam {
        ty: p.typ.unwrap_or(self.builtin.any),
        optional: false,
        rest: false,
      })
      .collect();
    let ret = if let Some(ret) = func.return_ann {
      ret
    } else if let Some(body) = func.body {
      let res = self.check_body(body);
      if res.return_types.is_empty() {
        self.builtin.void
      } else {
        if let Some(store) = self.interned_store.as_ref() {
          let interned = store.union(res.return_types.clone());
          self
            .interned_def_types
            .entry(def)
            .or_insert_with(|| store.canon(interned));
        }
        let mut widened = Vec::new();
        for ty in res.return_types.iter() {
          let imported = self.import_interned_type(*ty);
          widened.push(self.widen_literal(imported));
        }
        self.type_store.union(widened, &self.builtin)
      }
    } else {
      self.builtin.unknown
    };
    let ty = self.type_store.function(param_types, ret);
    self.def_types.insert(def, ty);
    ty
  }

  fn exports_of_file(&mut self, file: FileId) -> ExportMap {
    if let Some(semantics) = self.semantics.clone() {
      let map = check::modules::exports_from_semantics(self, &semantics, file);
      if !map.is_empty() {
        return map;
      }
    }
    let Some(state) = self.files.get(&file).cloned() else {
      return ExportMap::new();
    };
    let mut map = state.exports.clone();
    for entry in map.values_mut() {
      if entry.type_id.is_none() {
        if let Some(def) = entry.def {
          entry.type_id = Some(self.type_of_def(def));
        }
      }
    }
    map
  }

  fn ensure_symbols_for_file(&mut self, file: FileId) {
    if let Some(state) = self.files.get(&file).cloned() {
      if let Some(body) = state.top_body {
        let _ = self.check_body(body);
      }
      for def in state.defs.iter() {
        if let Some(body) = self.body_of_def(*def) {
          let _ = self.check_body(body);
        }
      }
    }
  }

  fn symbol_at(&mut self, file: FileId, offset: u32) -> Option<semantic_js::SymbolId> {
    let mut bodies: Vec<_> = self
      .body_map
      .iter()
      .filter(|(_, meta)| meta.file == file)
      .map(|(id, _)| *id)
      .collect();
    bodies.sort_by_key(|b| b.0);
    for body in bodies {
      let _ = self.check_body(body);
    }
    let occurrences = self.symbol_occurrences.get(&file)?;
    let mut best_containing: Option<(u32, u32, semantic_js::SymbolId)> = None;
    let mut best_empty: Option<(u32, u32, semantic_js::SymbolId)> = None;

    for occurrence in occurrences.iter() {
      let range = occurrence.range;
      let len = range.len();
      let key = (len, range.start, occurrence.symbol);
      if range.start <= offset && offset < range.end {
        let replace = best_containing.map(|best| key < best).unwrap_or(true);
        if replace {
          best_containing = Some(key);
        }
      } else if range.start == range.end && offset == range.start {
        let replace = best_empty.map(|best| key < best).unwrap_or(true);
        if replace {
          best_empty = Some(key);
        }
      }
    }

    let symbol = best_containing
      .or(best_empty)
      .map(|(_, _, symbol)| symbol)?;
    Some(self.resolve_symbol(symbol))
  }

  fn resolve_symbol(&mut self, symbol: semantic_js::SymbolId) -> semantic_js::SymbolId {
    let import = self
      .symbol_to_def
      .get(&symbol)
      .and_then(|def| self.def_data.get(def))
      .and_then(|d| match &d.kind {
        DefKind::Import(import) => Some(import.clone()),
        _ => None,
      });

    if let Some(import) = import {
      if let Some(resolved) = self.resolve_import_symbol(&import) {
        return resolved;
      }
    }

    symbol
  }

  fn resolve_import_symbol(&mut self, import: &ImportData) -> Option<semantic_js::SymbolId> {
    let exports = self.exports_of_file(import.from);
    exports.get(&import.original).map(|entry| entry.symbol)
  }

  fn def_priority(&self, def: DefId, ns: sem_ts::Namespace) -> u8 {
    let Some(kind) = self.def_data.get(&def).map(|d| &d.kind) else {
      return 3;
    };
    match ns {
      sem_ts::Namespace::VALUE => match kind {
        DefKind::Function(_) => 0,
        DefKind::Var(_) => 1,
        _ => 2,
      },
      sem_ts::Namespace::NAMESPACE => 2,
      sem_ts::Namespace::TYPE => match kind {
        DefKind::Interface(_) => 0,
        DefKind::TypeAlias(_) => 1,
        _ => 2,
      },
      _ => 3,
    }
  }

  fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    let binding = self
      .global_bindings
      .iter()
      .find(|(_, binding)| binding.symbol == symbol);

    let def = self
      .symbol_to_def
      .get(&symbol)
      .copied()
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.def));
    let type_id = def
      .and_then(|def_id| self.def_types.get(&def_id).copied())
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.type_id));
    let mut name = def
      .and_then(|def_id| self.def_data.get(&def_id).map(|data| data.name.clone()))
      .or_else(|| binding.as_ref().map(|(name, _)| name.to_string()));
    let file = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.file));

    if def.is_none() && type_id.is_none() && name.is_none() {
      return None;
    }
    if name.is_none() {
      name = binding.as_ref().map(|(name, _)| name.to_string());
    }

    Some(SymbolInfo {
      symbol,
      def,
      file,
      type_id,
      name,
    })
  }

  fn expr_at(&self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    let mut best_containing: Option<(bool, u32, u32, BodyId, ExprId)> = None;
    let mut best_empty: Option<(bool, u32, u32, BodyId, ExprId)> = None;
    let mut best_nearby: Option<(u32, bool, u32, BodyId, ExprId)> = None;

    let update_best =
      |body: BodyId,
       expr: ExprId,
       span: TextRange,
       best_containing: &mut Option<(bool, u32, u32, BodyId, ExprId)>,
       best_empty: &mut Option<(bool, u32, u32, BodyId, ExprId)>,
       best_nearby: &mut Option<(u32, bool, u32, BodyId, ExprId)>| {
        let len = span.len();
        let empty = span.start == span.end;
        let key = (empty, len, span.start, body, expr);
        let mut contains_start = span.start;
        let mut contains_end = span.end;
        if contains_start == contains_end {
          if contains_start > 0 {
            contains_start -= 1;
          }
          contains_end = contains_end.saturating_add(1);
        }
        if contains_start <= offset && offset < contains_end {
          let replace = best_containing.map(|best| key < best).unwrap_or(true);
          if replace {
            *best_containing = Some(key);
          }
        } else if span.start == span.end && offset == span.start {
          let replace = best_empty.map(|best| key < best).unwrap_or(true);
          if replace {
            *best_empty = Some(key);
          }
        } else {
          let distance = if offset < contains_start {
            contains_start - offset
          } else {
            offset.saturating_sub(contains_end)
          };
          let near_key = (distance, span.start == span.end, span.start, body, expr);
          let replace = best_nearby.map(|best| near_key < best).unwrap_or(true);
          if replace {
            *best_nearby = Some(near_key);
          }
        }
      };

    for (body_id, meta) in self.body_map.iter().filter(|(_, meta)| meta.file == file) {
      if let Some(result) = self.body_results.get(body_id) {
        for (idx, span) in result.expr_spans().iter().enumerate() {
          update_best(
            *body_id,
            ExprId(idx as u32),
            *span,
            &mut best_containing,
            &mut best_empty,
            &mut best_nearby,
          );
        }
        continue;
      }

      if let Some(hir_id) = meta.hir {
        if let Some(lowered) = self.hir_lowered.get(&meta.file) {
          if let Some(body) = lowered.body(hir_id) {
            for (idx, expr) in body.exprs.iter().enumerate() {
              update_best(
                *body_id,
                ExprId(idx as u32),
                expr.span,
                &mut best_containing,
                &mut best_empty,
                &mut best_nearby,
              );
            }
          }
        }
      }
    }

    best_containing
      .or(best_empty)
      .or(best_nearby.map(|(_, _, _, body, expr)| (false, 0, 0, body, expr)))
      .map(|(_, _, _, body, expr)| (body, expr))
  }

  fn hir_expr_kind(&self, body: BodyId, expr: ExprId) -> Option<HirExprKind> {
    let meta = self.body_map.get(&body)?;
    let hir_id = meta.hir?;
    let lowered = self.hir_lowered.get(&meta.file)?;
    let hir_body = lowered.body(hir_id)?;
    hir_body.exprs.get(expr.0 as usize).map(|e| e.kind.clone())
  }

  fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    self.def_data.get(&def).and_then(|d| match &d.kind {
      DefKind::Function(func) => func.body,
      DefKind::Var(var) => Some(var.body),
      DefKind::Import(_) => None,
      DefKind::Interface(_) => None,
      DefKind::TypeAlias(_) => None,
    })
  }

  fn owner_of_body(&self, body: BodyId) -> Option<DefId> {
    if let Some(meta) = self.body_map.get(&body) {
      if let Some(owner) = meta.owner {
        return Some(owner);
      }
    }
    for (def_id, data) in self.def_data.iter() {
      match &data.kind {
        DefKind::Function(func) if func.body == Some(body) => return Some(*def_id),
        DefKind::Var(var) if var.body == body => return Some(*def_id),
        _ => {}
      }
    }
    None
  }

  fn hir_body_range(body: &hir_js::Body) -> Option<TextRange> {
    let mut start = u32::MAX;
    let mut end = 0;
    for stmt in body.stmts.iter() {
      start = start.min(stmt.span.start);
      end = end.max(stmt.span.end);
    }
    for expr in body.exprs.iter() {
      start = start.min(expr.span.start);
      end = end.max(expr.span.end);
    }
    for pat in body.pats.iter() {
      start = start.min(pat.span.start);
      end = end.max(pat.span.end);
    }
    if start == u32::MAX {
      None
    } else {
      Some(TextRange::new(start, end))
    }
  }

  fn object_type_from_members(&mut self, file: FileId, members: &[Node<TypeMember>]) -> ObjectType {
    let mut object = ObjectType::empty();
    for member in members.iter() {
      match member.stx.as_ref() {
        TypeMember::Property(prop) => {
          if let Some(name) = type_member_name(&prop.stx.key) {
            let ty = prop
              .stx
              .type_annotation
              .as_ref()
              .map(|t| self.type_from_type_expr(file, t))
              .unwrap_or(self.builtin.unknown);
            object.props.insert(
              name,
              ObjectProperty {
                typ: ty,
                optional: prop.stx.optional,
                readonly: prop.stx.readonly,
              },
            );
          }
        }
        TypeMember::Method(method) => {
          if let Some(name) = type_member_name(&method.stx.key) {
            let params = method
              .stx
              .parameters
              .iter()
              .map(|p| FunctionParam {
                ty: self.type_from_type_expr(file, &p.stx.type_expr),
                optional: p.stx.optional,
                rest: p.stx.rest,
              })
              .collect();
            let ret = method
              .stx
              .return_type
              .as_ref()
              .map(|t| self.type_from_type_expr(file, t))
              .unwrap_or(self.builtin.unknown);
            let func_ty = self.type_store.function(params, ret);
            object.props.insert(
              name,
              ObjectProperty {
                typ: func_ty,
                optional: method.stx.optional,
                readonly: false,
              },
            );
          }
        }
        TypeMember::IndexSignature(index) => {
          let value = self.type_from_type_expr(file, &index.stx.type_annotation);
          let param_type = self.type_from_type_expr(file, &index.stx.parameter_type);
          let param_kind = self.type_store.kind(param_type).clone();
          match param_kind {
            TypeKind::Number => object.number_index = Some(value),
            TypeKind::String => object.string_index = Some(value),
            _ => object.string_index = Some(value),
          }
        }
        _ => {}
      }
    }
    object
  }

  fn merge_object_types(&mut self, mut base: ObjectType, extra: ObjectType) -> ObjectType {
    for (name, prop) in extra.props.into_iter() {
      match base.props.entry(name) {
        Entry::Vacant(entry) => {
          entry.insert(prop);
        }
        Entry::Occupied(mut entry) => {
          let existing = entry.get_mut();
          existing.typ = self
            .type_store
            .union(vec![existing.typ, prop.typ], &self.builtin);
          existing.optional = existing.optional || prop.optional;
          existing.readonly = existing.readonly || prop.readonly;
        }
      }
    }

    if base.string_index.is_none() {
      base.string_index = extra.string_index;
    }
    if base.number_index.is_none() {
      base.number_index = extra.number_index;
    }

    base
  }

  fn literal_type_from_expr(&mut self, expr: &Node<Expr>) -> Option<TypeId> {
    match expr.stx.as_ref() {
      Expr::LitBool(node) => Some(self.type_store.literal_boolean(node.stx.value)),
      Expr::LitNum(node) => Some(self.type_store.literal_number(node.stx.value.to_string())),
      Expr::LitStr(node) => Some(self.type_store.literal_string(node.stx.value.clone())),
      Expr::LitNull(_) => Some(self.builtin.null),
      Expr::LitTemplate(node)
        if node
          .stx
          .parts
          .iter()
          .all(|part| matches!(part, parse_js::ast::expr::lit::LitTemplatePart::String(_))) =>
      {
        let mut full = String::new();
        for part in node.stx.parts.iter() {
          if let parse_js::ast::expr::lit::LitTemplatePart::String(s) = part {
            full.push_str(s);
          }
        }
        Some(self.type_store.literal_string(full))
      }
      _ => None,
    }
  }

  fn fallback_expr_type(&mut self, body: BodyId, expr: hir_js::ExprId) -> Option<TypeId> {
    let (file, hir_id) = {
      let meta = self.body_map.get(&body)?;
      (meta.file, meta.hir?)
    };
    let lowered = self.hir_lowered.get(&file)?;
    let hir_body = lowered.body(hir_id)?;
    let expr_kind = hir_body.exprs.get(expr.0 as usize)?.kind.clone();
    let names = lowered.names.clone();
    let _ = hir_body;
    let _ = lowered;
    match expr_kind {
      hir_js::ExprKind::Literal(lit) => match lit {
        hir_js::Literal::Number(n) => Some(self.type_store.literal_number(n)),
        hir_js::Literal::String(s) => Some(self.type_store.literal_string(s)),
        hir_js::Literal::Boolean(b) => Some(self.type_store.literal_boolean(b)),
        hir_js::Literal::Null => Some(self.builtin.null),
        hir_js::Literal::Undefined => Some(self.builtin.undefined),
        hir_js::Literal::BigInt(n) => Some(self.type_store.literal_number(n)),
        hir_js::Literal::Regex(_) => None,
      },
      hir_js::ExprKind::Ident(name_id) => {
        let name = names.resolve(name_id)?.to_string();
        let def_id = self
          .canonical_defs
          .get(&(file, name.clone()))
          .copied()
          .or_else(|| {
            self.def_data.iter().find_map(|(id, data)| {
              if data.file == file && data.name == name {
                Some(*id)
              } else {
                None
              }
            })
          });
        def_id.map(|def| self.type_of_def(def))
      }
      hir_js::ExprKind::Member(member) => {
        let prop_name = match member.property {
          hir_js::ObjectKey::String(ref name) => Some(name.as_str()),
          hir_js::ObjectKey::Number(ref n) => Some(n.as_str()),
          hir_js::ObjectKey::Ident(id) => names.resolve(id).map(|s| s.as_ref()),
          _ => None,
        }?;
        let object_ty = self.fallback_expr_type(body, member.object)?;
        let mut seen = HashSet::new();
        let resolved = self.resolve_ref_type(object_ty, &mut seen);
        lookup_property_type(&mut self.type_store, resolved, prop_name, &self.builtin)
      }
      _ => None,
    }
  }

  fn resolve_type_reference(&mut self, file: FileId, name: &TypeEntityName) -> Option<DefId> {
    match name {
      TypeEntityName::Identifier(name) => {
        let resolved = self
          .canonical_defs
          .get(&(file, name.clone()))
          .copied()
          .or_else(|| {
            self.def_data.iter().find_map(|(id, data)| {
              if data.file == file && data.name == *name {
                Some(*id)
              } else {
                None
              }
            })
          });
        let Some(def) = resolved else { return None };
        if let Some(import) = self.def_data.get(&def).and_then(|d| match &d.kind {
          DefKind::Import(import) => Some(import.clone()),
          _ => None,
        }) {
          if import.original != "*" {
            if let Some(entry) = self.exports_of_file(import.from).get(&import.original) {
              if let Some(target) = entry.def {
                return Some(target);
              }
            }
          }
        }
        Some(def)
      }
      TypeEntityName::Qualified(qual) => {
        if let TypeEntityName::Import(import) = &qual.left {
          if let Some(target) = self.resolve_import_type_module(file, import) {
            if let Some(entry) = self.exports_of_file(target).get(&qual.right) {
              if let Some(def) = entry.def {
                return Some(def);
              }
            }
          }
          return None;
        }
        if let Some(base) = self.resolve_type_reference(file, &qual.left) {
          if let Some(data) = self.def_data.get(&base).cloned() {
            match data.kind {
              DefKind::Import(import) => {
                let exports = self.exports_of_file(import.from);
                if let Some(entry) = exports.get(&qual.right) {
                  if let Some(def) = entry.def {
                    return Some(def);
                  }
                }
              }
              DefKind::Var(var) => {
                let ns_ty = self.namespace_types.get(&base).copied().or(var.typ);
                if let Some(ns_ty) = ns_ty {
                  if let Some(prop_ty) =
                    lookup_property_type(&mut self.type_store, ns_ty, &qual.right, &self.builtin)
                  {
                    if let TypeKind::Ref { def } = self.type_store.kind(prop_ty) {
                      return Some(*def);
                    }
                  }
                }
              }
              _ => {}
            }
          }
        }
        self.resolve_type_reference(file, &TypeEntityName::Identifier(qual.right.clone()))
      }
      TypeEntityName::Import(import) => {
        if let Some(target) = self.resolve_import_type_module(file, import) {
          if let Some(entry) = self.exports_of_file(target).get("default") {
            if let Some(def) = entry.def {
              return Some(def);
            }
          }
        }
        None
      }
    }
  }

  fn resolve_import_type_module(&self, file: FileId, import: &Node<ImportExpr>) -> Option<FileId> {
    let specifier = match import.stx.module.stx.as_ref() {
      Expr::LitStr(lit) => Some(lit.stx.value.clone()),
      _ => None,
    }?;
    self.resolve_known_file(file, &specifier)
  }

  fn lower_type_alias_expr(&mut self, file: FileId, span: TextRange) -> Option<TypeId> {
    let ast = self.asts.get(&file)?.clone();
    for stmt in ast.stx.body.iter() {
      if let Stmt::TypeAliasDecl(alias) = stmt.stx.as_ref() {
        if loc_to_span(file, alias.stx.type_expr.loc).range == span {
          return Some(self.type_from_type_expr(file, &alias.stx.type_expr));
        }
      }
    }
    None
  }

  fn resolve_ref_type(&mut self, ty: TypeId, seen: &mut HashSet<DefId>) -> TypeId {
    let mut current = ty;
    loop {
      match self.type_store.kind(current).clone() {
        TypeKind::Ref { def } => {
          if !seen.insert(def) {
            break;
          }
          current = self.type_of_def(def);
        }
        _ => break,
      }
    }
    current
  }

  fn type_from_type_expr(&mut self, file: FileId, expr: &Node<TypeExpr>) -> TypeId {
    match expr.stx.as_ref() {
      TypeExpr::Object(_) => self.builtin.object,
      TypeExpr::Number(_) => self.builtin.number,
      TypeExpr::String(_) => self.builtin.string,
      TypeExpr::Boolean(_) => self.builtin.boolean,
      TypeExpr::Any(_) => self.builtin.any,
      TypeExpr::Unknown(_) => self.builtin.unknown,
      TypeExpr::Null(_) => self.builtin.null,
      TypeExpr::Undefined(_) => self.builtin.undefined,
      TypeExpr::Void(_) => self.builtin.void,
      TypeExpr::Never(_) => self.builtin.never,
      TypeExpr::IntersectionType(intersection) => {
        let TypeIntersection { types } = intersection.stx.as_ref();
        let members = types
          .iter()
          .map(|t| self.type_from_type_expr(file, t))
          .collect();
        self.type_store.intersection(members, &self.builtin)
      }
      TypeExpr::ImportType(import) => {
        if let Some(target) = self.resolve_known_file(file, &import.stx.module_specifier) {
          if let Some(qualifier) = import.stx.qualifier.as_ref() {
            if let Some(def) = self.resolve_type_reference(target, qualifier) {
              return self.type_store.reference(def);
            }
          }
        }
        self.builtin.unknown
      }
      TypeExpr::TypeReference(reference) => {
        if let Some(def) = self.resolve_type_reference(file, &reference.stx.name) {
          if let Some(data) = self.def_data.get(&def) {
            self.record_symbol(file, loc_to_span(file, expr.loc).range, data.symbol);
          }
          return self.type_store.reference(def);
        }
        self.builtin.unknown
      }
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types
          .iter()
          .map(|t| self.type_from_type_expr(file, t))
          .collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeExpr::TupleType(tuple) => {
        let TypeTuple { readonly, elements } = tuple.stx.as_ref();
        let elems: Vec<_> = elements
          .iter()
          .map(|elem| self.type_from_type_expr(file, &elem.stx.type_expr))
          .collect();
        self.type_store.tuple(elems, *readonly)
      }
      TypeExpr::ArrayType(arr) => {
        let TypeArray { element_type, .. } = arr.stx.as_ref();
        let elem = self.type_from_type_expr(file, element_type);
        self.type_store.array(elem)
      }
      TypeExpr::FunctionType(func) => {
        let params = func
          .stx
          .parameters
          .iter()
          .map(|p| FunctionParam {
            ty: self.type_from_type_expr(file, &p.stx.type_expr),
            optional: p.stx.optional,
            rest: p.stx.rest,
          })
          .collect();
        let ret = self.type_from_type_expr(file, &func.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ConstructorType(cons) => {
        let params = cons
          .stx
          .parameters
          .iter()
          .map(|p| FunctionParam {
            ty: self.type_from_type_expr(file, &p.stx.type_expr),
            optional: p.stx.optional,
            rest: p.stx.rest,
          })
          .collect();
        let ret = self.type_from_type_expr(file, &cons.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ObjectType(obj) => {
        let object = self.object_type_from_members(file, &obj.stx.members);
        self.type_store.object(object)
      }
      TypeExpr::ParenthesizedType(inner) => self.type_from_type_expr(file, &inner.stx.type_expr),
      TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
        TypeLiteral::Boolean(value) => self.type_store.literal_boolean(*value),
        TypeLiteral::Number(n) => self.type_store.literal_number(n.clone()),
        TypeLiteral::String(s) => self.type_store.literal_string(s.clone()),
        TypeLiteral::Null => self.builtin.null,
        _ => self.builtin.unknown,
      },
      TypeExpr::TypePredicate(pred) => {
        let asserted = pred
          .stx
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(file, t));
        self
          .type_store
          .predicate(pred.stx.parameter_name.clone(), asserted, pred.stx.asserts)
      }
      _ => self.builtin.unknown,
    }
  }

  fn alloc_def(&mut self) -> DefId {
    let id = DefId(self.next_def);
    self.next_def += 1;
    id
  }

  fn alloc_symbol(&mut self) -> semantic_js::SymbolId {
    let id = semantic_js::SymbolId(self.next_symbol);
    self.next_symbol += 1;
    id
  }

  fn record_def_symbol(&mut self, def: DefId, symbol: semantic_js::SymbolId) {
    self.symbol_to_def.insert(symbol, def);
  }

  fn record_symbol(&mut self, file: FileId, range: TextRange, symbol: semantic_js::SymbolId) {
    self
      .symbol_occurrences
      .entry(file)
      .or_default()
      .push(SymbolOccurrence { range, symbol });
  }
}

fn sem_hir_from_lower(lowered: &LowerResult) -> sem_ts::HirFile {
  let resolve_name = |name| lowered.names.resolve(name).unwrap_or_default().to_string();
  let mut decls = Vec::new();
  for def_id in lowered.hir.items.iter() {
    let Some(idx) = lowered.def_index.get(def_id) else {
      continue;
    };
    let Some(def) = lowered.defs.get(*idx) else {
      continue;
    };
    let name = resolve_name(def.path.name);
    let mapped = map_def_kind(def.path.kind);
    let Some(kind) = mapped else {
      continue;
    };
    let exported = if def.is_exported {
      if def.is_default_export {
        sem_ts::Exported::Default
      } else {
        sem_ts::Exported::Named
      }
    } else {
      sem_ts::Exported::No
    };
    decls.push(sem_ts::Decl {
      def_id: def.id,
      name,
      kind,
      is_ambient: def.is_ambient,
      is_global: def.in_global,
      exported,
      span: def.span,
    });
  }

  let imports: Vec<_> = lowered
    .hir
    .imports
    .iter()
    .filter_map(|import| map_import_from_lower(import, lowered, &resolve_name))
    .collect();
  let exports: Vec<_> = lowered
    .hir
    .exports
    .iter()
    .filter_map(|export| map_export_from_lower(export, lowered, &resolve_name))
    .collect();
  let module_kind = if imports.is_empty()
    && exports.is_empty()
    && decls
      .iter()
      .all(|decl| matches!(decl.exported, sem_ts::Exported::No))
  {
    sem_ts::ModuleKind::Script
  } else {
    sem_ts::ModuleKind::Module
  };

  sem_ts::HirFile {
    file_id: sem_ts::FileId(lowered.hir.file.0),
    module_kind,
    file_kind: match lowered.hir.file_kind {
      HirFileKind::Dts => sem_ts::FileKind::Dts,
      HirFileKind::Ts | HirFileKind::Js | HirFileKind::Jsx | HirFileKind::Tsx => {
        sem_ts::FileKind::Ts
      }
    },
    decls,
    imports,
    exports,
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  }
}

fn map_def_kind(kind: HirDefKind) -> Option<sem_ts::DeclKind> {
  match kind {
    HirDefKind::Function => Some(sem_ts::DeclKind::Function),
    HirDefKind::Class => Some(sem_ts::DeclKind::Class),
    HirDefKind::Var => Some(sem_ts::DeclKind::Var),
    HirDefKind::Interface => Some(sem_ts::DeclKind::Interface),
    HirDefKind::TypeAlias => Some(sem_ts::DeclKind::TypeAlias),
    HirDefKind::Enum => Some(sem_ts::DeclKind::Enum),
    HirDefKind::Namespace | HirDefKind::Module => Some(sem_ts::DeclKind::Namespace),
    HirDefKind::ImportBinding => None,
    _ => None,
  }
}

fn map_import_from_lower(
  import: &hir_js::Import,
  _lowered: &LowerResult,
  resolve_name: &impl Fn(hir_js::NameId) -> String,
) -> Option<sem_ts::Import> {
  match &import.kind {
    HirImportKind::Es(es) => {
      let default = es.default.as_ref().map(|binding| sem_ts::ImportDefault {
        local: resolve_name(binding.local),
        local_span: binding.span,
        is_type_only: es.is_type_only,
      });
      let namespace = es
        .namespace
        .as_ref()
        .map(|binding| sem_ts::ImportNamespace {
          local: resolve_name(binding.local),
          local_span: binding.span,
          is_type_only: es.is_type_only,
        });
      let named = es
        .named
        .iter()
        .map(|spec| sem_ts::ImportNamed {
          imported: resolve_name(spec.imported),
          local: resolve_name(spec.local),
          is_type_only: es.is_type_only || spec.is_type_only,
          imported_span: spec.span,
          local_span: spec.span,
        })
        .collect();
      Some(sem_ts::Import {
        specifier: es.specifier.value.clone(),
        specifier_span: es.specifier.span,
        default,
        namespace,
        named,
        is_type_only: es.is_type_only,
      })
    }
    HirImportKind::ImportEquals(_) => None,
  }
}

fn map_export_from_lower(
  export: &hir_js::Export,
  _lowered: &LowerResult,
  resolve_name: &impl Fn(hir_js::NameId) -> String,
) -> Option<sem_ts::Export> {
  match &export.kind {
    HirExportKind::Named(named) => {
      let items = named
        .specifiers
        .iter()
        .map(|spec| {
          let local = resolve_name(spec.local);
          let exported_name = resolve_name(spec.exported);
          let exported = if exported_name == local {
            None
          } else {
            Some(exported_name)
          };
          let exported_span = exported.as_ref().map(|_| spec.span);
          sem_ts::ExportSpecifier {
            local,
            exported,
            local_span: spec.span,
            exported_span,
          }
        })
        .collect();
      Some(sem_ts::Export::Named(sem_ts::NamedExport {
        specifier: named.source.as_ref().map(|s| s.value.clone()),
        specifier_span: named.source.as_ref().map(|s| s.span),
        items,
        is_type_only: named.is_type_only,
      }))
    }
    HirExportKind::ExportAll(all) => Some(sem_ts::Export::All(sem_ts::ExportAll {
      specifier: all.source.value.clone(),
      is_type_only: all.is_type_only,
      specifier_span: all.source.span,
    })),
    HirExportKind::Default(_) => None,
    HirExportKind::Assignment(_) => Some(sem_ts::Export::ExportAssignment {
      expr: String::new(),
      span: export.span,
    }),
  }
}

fn type_member_name(key: &TypePropertyKey) -> Option<String> {
  match key {
    TypePropertyKey::Identifier(name) => Some(name.clone()),
    TypePropertyKey::String(name) => Some(name.clone()),
    TypePropertyKey::Number(name) => Some(name.clone()),
    TypePropertyKey::Computed(_) => None,
  }
}

fn fatal_to_diagnostic(fatal: FatalError) -> Diagnostic {
  let placeholder = Span::new(FileId(0), TextRange::new(0, 0));
  match fatal {
    FatalError::Host(err) => {
      let mut diagnostic = codes::HOST_ERROR.error(err.to_string(), placeholder);
      diagnostic.push_note("no source span available for this host error; input may be missing");
      diagnostic
    }
    FatalError::Cancelled => codes::CANCELLED.error("operation cancelled", placeholder),
    FatalError::Ice(ice) => {
      let span = span_from_context(&ice.context, placeholder);
      let mut diagnostic = codes::INTERNAL_COMPILER_ERROR
        .error(format!("internal compiler error: {}", ice.message), span);
      if let Some(backtrace) = ice.backtrace {
        diagnostic.push_note(backtrace);
      }
      diagnostic
    }
    FatalError::OutOfMemory => codes::OUT_OF_MEMORY.error("out of memory", placeholder),
  }
}

fn span_from_context(ctx: &IceContext, placeholder: Span) -> Span {
  ctx
    .file
    .map(|file| Span::new(file, TextRange::new(0, 0)))
    .unwrap_or(placeholder)
}

fn loc_to_span(file: FileId, loc: Loc) -> Span {
  Span {
    file,
    range: TextRange {
      start: loc.0.min(u32::MAX as usize) as u32,
      end: loc.1.min(u32::MAX as usize) as u32,
    },
  }
}
