use crate::api::{BodyId, DefId, Diagnostic, ExprId, FileId, FileKey, PatId, Span, TextRange};
use crate::db::spans::expr_at_from_spans;
use crate::semantic_js;
use crate::{SymbolBinding, SymbolInfo, SymbolOccurrence};
use ::semantic_js::ts as sem_ts;
use hir_js::{
  lower_file_with_diagnostics as lower_hir_with_diagnostics, BinaryOp as HirBinaryOp,
  BodyKind as HirBodyKind, DefId as HirDefId, DefKind as HirDefKind, ExportKind as HirExportKind,
  ExprKind as HirExprKind, FileKind as HirFileKind, LowerResult, NameId, PatId as HirPatId,
  PatKind as HirPatKind, VarDeclKind as HirVarDeclKind,
};
use ordered_float::OrderedFloat;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::func::Func;
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{FuncDecl, ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{ImportEqualsRhs, NamespaceBody};
use parse_js::ast::type_expr::{
  TypeArray, TypeEntityName, TypeExpr, TypeLiteral, TypeMember, TypePropertyKey, TypeUnion,
};
use parse_js::loc::Loc;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::cmp::Reverse;
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;
use tracing::debug_span;
use types_ts_interned::{self as tti, PropData, PropKey, Property, RelateCtx, TypeId, TypeParamId};

use self::check::caches::{CheckerCacheStats, CheckerCaches};
use self::check::flow_bindings::FlowBindings;
use self::check::relate_hooks;
use crate::check::type_expr::{TypeLowerer, TypeResolver};
use crate::codes;
use crate::db::queries::{var_initializer_in_file, VarInit};
use crate::db::{self, BodyCheckContext, BodyCheckDb, BodyInfo, GlobalBindingsDb};
use crate::expand::ProgramTypeExpander as RefExpander;
use crate::files::{FileOrigin, FileRegistry};
use crate::profile::{
  CacheKind, CacheStat, QueryKind, QueryStats, QueryStatsCollector, QueryTimer,
};
use crate::sem_hir::sem_hir_from_lower;
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

use crate::lib_support::lib_env::{collect_libs, validate_libs};
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
    let display = if let Some(resolver) = self.resolver.as_ref() {
      tti::TypeDisplay::new(&self.store, self.ty).with_ref_resolver(Arc::clone(resolver))
    } else {
      tti::TypeDisplay::new(&self.store, self.ty)
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

#[derive(Clone, Copy)]
struct ProgramTypeExpander<'a> {
  def_types: &'a HashMap<DefId, TypeId>,
  type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
}

impl<'a> tti::TypeExpander for ProgramTypeExpander<'a> {
  fn expand(
    &self,
    _store: &tti::TypeStore,
    def: DefId,
    _args: &[TypeId],
  ) -> Option<tti::ExpandedType> {
    let ty = *self.def_types.get(&def)?;
    let params = self.type_params.get(&def).cloned().unwrap_or_else(Vec::new);
    Some(tti::ExpandedType { params, ty })
  }
}

fn display_type_from_state(state: &ProgramState, ty: TypeId) -> (Arc<tti::TypeStore>, tti::TypeId) {
  if let Some(store) = state.interned_store.as_ref() {
    if store.contains_type_id(ty) {
      return (Arc::clone(store), store.canon(ty));
    }
    if let Some(mapped) = state.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        state.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return (Arc::clone(store), store.canon(mapped));
    }
  }

  let store = tti::TypeStore::with_options((&state.compiler_options).into());
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
    TypeKind::Function { params, ret } => {
      let params: Vec<_> = params
        .into_iter()
        .map(|param| tti::Param {
          name: None,
          ty: convert_type_for_display(param, state, store, cache),
          optional: false,
          rest: false,
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
      let param = if parameter.is_empty() {
        None
      } else {
        Some(store.intern_name(parameter))
      };
      let asserted = asserted.map(|ty| convert_type_for_display(ty, state, store, cache));
      store.intern_type(tti::TypeKind::Predicate {
        parameter: param,
        asserted,
        asserts,
      })
    }
    TypeKind::Mapped { source, value } => {
      let param = tti::TypeParamId(0);
      let source = convert_type_for_display(source, state, store, cache);
      let value = convert_type_for_display(value, state, store, cache);
      let mapped = tti::MappedType {
        param,
        source,
        value,
        readonly: tti::MappedModifier::Preserve,
        optional: tti::MappedModifier::Preserve,
        name_type: None,
        as_type: None,
      };
      store.intern_type(tti::TypeKind::Mapped(mapped))
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
    roots: Vec<FileKey>,
    lib_manager: Arc<LibManager>,
  ) -> Program {
    let host: Arc<dyn Host> = Arc::new(host);
    let query_stats = QueryStatsCollector::default();
    let cancelled = Arc::new(AtomicBool::new(false));
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
      let mut roots = program.roots.clone();
      roots.sort_by(|a, b| a.as_str().cmp(b.as_str()));
      for key in roots.into_iter() {
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
    let overrides = {
      let state = self.lock_state();
      state.file_overrides.clone()
    };
    self.reset_state(overrides, options);
  }

  /// Override the text for a specific file and invalidate cached results.
  pub fn set_file_text(&mut self, file: FileId, text: Arc<str>) {
    let Some(key) = ({
      let state = self.lock_state();
      state.file_key_for_id(file)
    }) else {
      return;
    };
    let (overrides, options) = {
      let mut state = self.lock_state();
      state.file_overrides.insert(key.clone(), text);
      (state.file_overrides.clone(), state.compiler_options.clone())
    };
    self.reset_state(overrides, options);
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
    match self.with_analyzed_state(|state| Ok(state.file_ids_for_key(key))) {
      Ok(ids) => ids,
      Err(_) => Vec::new(),
    }
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
    match self.with_analyzed_state(|state| Ok(state.files.keys().copied().collect())) {
      Ok(files) => files,
      Err(_) => Vec::new(),
    }
  }

  /// All files reachable from the configured roots.
  pub fn reachable_files(&self) -> Vec<FileId> {
    match self.with_analyzed_state(|state| {
      let mut files: Vec<FileId> = state
        .typecheck_db
        .reachable_files()
        .iter()
        .copied()
        .filter(|file| !state.lib_file_ids.contains(file))
        .collect();
      files.sort_by_key(|id| id.0);
      Ok(files)
    }) {
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
      Err(payload) => {
        eprintln!("caught panic in catch_fatal");
        Err(FatalError::Ice(Ice::from_panic(payload)))
      }
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

  fn reset_state(&self, overrides: HashMap<FileKey, Arc<str>>, compiler_options: CompilerOptions) {
    let lib_manager = {
      let state = self.lock_state();
      state.lib_manager.clone()
    };
    let mut new_state = ProgramState::new(
      Arc::clone(&self.host),
      lib_manager,
      self.query_stats.clone(),
      Arc::clone(&self.cancelled),
    );
    new_state.file_overrides = overrides;
    new_state.compiler_options = compiler_options;
    let mut roots = self.roots.clone();
    roots.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    for key in roots.into_iter() {
      new_state.intern_file_key(key, FileOrigin::Source);
    }
    let mut state = self.lock_state();
    *state = new_state;
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
      let context = {
        let mut state = self.lock_state();
        state.ensure_interned_types(&self.host, &self.roots)?;
        if let Some(res) = state.body_results.get(&body).cloned() {
          return Ok(res);
        }
        state.body_check_context()
      };
      let db = BodyCheckDb::new(context);
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
      let (body, expr) = match state.expr_at(file, offset) {
        Some(res) => res,
        None => return Ok(None),
      };
      let result = state.check_body(body)?;
      let unknown = state.interned_unknown();
      let (expr, mut ty) = match result.expr_at(offset) {
        Some((expr_id, ty)) => (expr_id, ty),
        None => (expr, result.expr_type(expr).unwrap_or(unknown)),
      };
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
          if let Ok(parent_res) = state.check_body(parent) {
            eprintln!("  parent pat types {:?}", parent_res.pat_types());
            if let Some(first) = parent_res.pat_types().first() {
              if let Some(store) = state.interned_store.as_ref() {
                eprintln!("  parent pat kind {:?}", store.type_kind(*first));
              }
            }
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

  pub fn type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized")
        .clone();
      let ty = match state.interned_def_types.get(&def).copied() {
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
      Ok(ty)
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
      let resolver = state
        .def_data
        .iter()
        .map(|(id, data)| (tti::DefId(id.0), data.name.clone()))
        .collect::<HashMap<_, _>>();
      let (store, ty) = display_type_from_state(&state, ty);
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
      Ok(
        state
          .files
          .get(&file)
          .map(|f| f.defs.clone())
          .unwrap_or_default(),
      )
    })
  }

  /// Bodies belonging to a file.
  pub fn bodies_in_file(&self, file: FileId) -> Vec<BodyId> {
    match self.with_analyzed_state(|state| {
      Ok(
        state
          .body_map
          .iter()
          .filter_map(|(id, meta)| (meta.file == file).then_some(*id))
          .collect(),
      )
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
    match self
      .with_analyzed_state(|state| Ok(crate::db::symbol_occurrences(&state.typecheck_db, file)))
    {
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
    self.with_analyzed_state(|state| Ok(state.def_data.get(&def).map(|d| d.name.clone())))
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
          if var.body.0 != u32::MAX {
            Some(var.body)
          } else {
            state.var_initializer(def).map(|init| init.body)
          }
        }
        DefKind::Class(class) => class.body,
        DefKind::Enum(en) => en.body,
        DefKind::Namespace(ns) => ns.body,
        DefKind::Module(module) => module.body,
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

  /// Serialize the current analyzed state into a deterministic snapshot suitable
  /// for caching or offline queries. All bodies and definitions are fully
  /// checked before serialization to ensure type and diagnostic tables are
  /// populated.
  #[cfg(feature = "serde")]
  pub fn snapshot(&self) -> ProgramSnapshot {
    use sha2::{Digest, Sha256};

    let mut state = self.lock_state();
    state.ensure_analyzed(&self.host, &self.roots);
    if let Err(fatal) = state.ensure_interned_types(&self.host, &self.roots) {
      state.diagnostics.push(fatal_to_diagnostic(fatal));
    }

    let mut body_ids: Vec<_> = state.body_map.keys().copied().collect();
    body_ids.sort_by_key(|id| id.0);
    for body in body_ids.iter() {
      if let Err(fatal) = state.check_body(*body) {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        break;
      }
    }

    let mut def_ids: Vec<_> = state.def_data.keys().copied().collect();
    def_ids.sort_by_key(|id| id.0);
    for def in def_ids.iter() {
      if let Err(fatal) = ProgramState::type_of_def(&mut state, *def) {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        break;
      }
    }

    let mut file_ids: Vec<_> = state.file_kinds.keys().copied().collect();
    file_ids.sort_by_key(|id| id.0);
    let mut files = Vec::new();
    for file in file_ids {
      let kind = *state.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
      let key = state
        .file_key_for_id(file)
        .unwrap_or_else(|| FileKey::new(format!("file{}.ts", file.0)));
      let is_lib = state.lib_file_ids.contains(&file);
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
        key,
        kind,
        is_lib,
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

    let mut body_results: Vec<_> = state
      .body_results
      .iter()
      .map(|(id, res)| (*id, (**res).clone()))
      .collect();
    body_results.sort_by_key(|(id, _)| id.0);
    let body_results: Vec<_> = body_results.into_iter().map(|(_, res)| res).collect();

    let mut symbol_occurrences = Vec::new();
    let mut symbol_files: Vec<_> = state.file_kinds.keys().copied().collect();
    symbol_files.sort_by_key(|file| file.0);
    for file in symbol_files {
      let occs = crate::db::symbol_occurrences(&state.typecheck_db, file);
      symbol_occurrences.push((file, occs.iter().cloned().collect()));
    }

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
      .unwrap_or_else(|| {
        let store = tti::TypeStore::with_options((&state.compiler_options).into());
        store.snapshot()
      });
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

    let canonical_defs_map = match state.canonical_defs() {
      Ok(map) => map,
      Err(fatal) => {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        HashMap::new()
      }
    };
    let mut canonical_defs: Vec<_> = canonical_defs_map
      .into_iter()
      .map(|((file, name, ns), def)| ((file, name, ns.bits()), def))
      .collect();
    canonical_defs.sort_by(|a, b| (a.0 .0, &a.0 .1, a.0 .2).cmp(&(b.0 .0, &b.0 .1, b.0 .2)));

    let mut namespace_types: Vec<_> = state
      .namespace_object_types
      .iter()
      .filter_map(|((file, name), (_, store_ty))| {
        state
          .find_namespace_def(*file, name)
          .map(|def| (def, *store_ty))
      })
      .collect();
    namespace_types.sort_by_key(|(def, _)| def.0);

    let diagnostics = match state.program_diagnostics(&self.host, &self.roots) {
      Ok(diags) => diags.to_vec(),
      Err(fatal) => {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
        state.diagnostics.clone()
      }
    };

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
      diagnostics,
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
    let file_key_map: HashMap<_, _> = snapshot
      .files
      .iter()
      .map(|file| (file.file, file.key.clone()))
      .collect();
    let root_keys: Vec<FileKey> = snapshot
      .roots
      .iter()
      .map(|id| {
        file_key_map
          .get(id)
          .cloned()
          .unwrap_or_else(|| FileKey::new(format!("file{}.ts", id.0)))
      })
      .collect();
    let program = Program::with_lib_manager(host, root_keys, Arc::new(LibManager::new()));
    {
      let mut state = program.lock_state();
      state.analyzed = true;
      state.compiler_options = snapshot.compiler_options;
      state.checker_caches = CheckerCaches::new(state.compiler_options.cache.clone());
      state.cache_stats = CheckerCacheStats::default();
      for file in snapshot.files.into_iter() {
        let key = file.key.clone();
        let origin = if file.is_lib {
          FileOrigin::Lib
        } else {
          FileOrigin::Source
        };
        let id = state.file_registry.intern(&key, origin);
        debug_assert_eq!(id, file.file, "snapshot file id mismatch");
        state.file_kinds.insert(file.file, file.kind);
        if file.is_lib {
          state.lib_file_ids.insert(file.file);
        }
        if let Some(text) = file.text {
          let arc = Arc::from(text);
          state.lib_texts.insert(file.file, Arc::clone(&arc));
          state.set_salsa_inputs(file.file, file.kind, arc);
        } else {
          state.typecheck_db.set_file_kind(file.file, file.kind);
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
      state.body_parents = HashMap::new();
      state.def_types = snapshot.def_types.into_iter().collect();
      state.body_results = snapshot
        .body_results
        .into_iter()
        .map(|res| (res.body(), Arc::new(res)))
        .collect();
      state.ensure_body_map_from_defs();
      state.symbol_to_def = snapshot.symbol_to_def.into_iter().collect();
      state.global_bindings = Arc::new(snapshot.global_bindings.into_iter().collect());
      state.diagnostics = snapshot.diagnostics;
      state.type_store = snapshot.type_store;
      state.interned_store = Some(tti::TypeStore::from_snapshot(snapshot.interned_type_store));
      state.interned_def_types = snapshot.interned_def_types.into_iter().collect();
      state.interned_type_params = snapshot.interned_type_params.into_iter().collect();
      state.root_ids = snapshot.roots.clone();
      state.lib_diagnostics.clear();
      if let Some(store) = state.interned_store.clone() {
        for (def, store_ty) in snapshot.namespace_types.into_iter() {
          state.def_types.entry(def).or_insert(store_ty);
          let def_data = state.def_data.get(&def).cloned();
          let interned = state
            .interned_def_types
            .get(&def)
            .copied()
            .unwrap_or_else(|| {
              let mut cache = HashMap::new();
              store.canon(convert_type_for_display(
                store_ty, &state, &store, &mut cache,
              ))
            });
          if let Some(data) = def_data {
            state
              .namespace_object_types
              .insert((data.file, data.name.clone()), (interned, store_ty));
          }
          state.interned_def_types.entry(def).or_insert(interned);
        }
      }
      state.builtin = snapshot.builtin;
      state.next_def = snapshot.next_def;
      state.next_body = snapshot.next_body;
      state.next_symbol = snapshot.next_symbol;
      state.sync_typecheck_roots();
      state.rebuild_callable_overloads();
      state.merge_callable_overload_types();
    }
    program
  }
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
  registry: FileRegistry,
}

impl sem_ts::Resolver for HostResolver {
  fn resolve(&self, from: sem_ts::FileId, specifier: &str) -> Option<sem_ts::FileId> {
    let from_key = self.registry.lookup_key(FileId(from.0))?;
    let target_key = self.host.resolve(&from_key, specifier)?;
    let target_id = self.registry.lookup_id(&target_key)?;
    Some(sem_ts::FileId(target_id.0))
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
  Class(ClassData),
  Enum(EnumData),
  Namespace(NamespaceData),
  Module(ModuleData),
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
  pub target: ImportTarget,
  pub original: String,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub enum ImportTarget {
  File(FileId),
  Unresolved { specifier: String },
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
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ClassData {
  pub body: Option<BodyId>,
  pub instance_type: Option<TypeId>,
  pub static_type: Option<TypeId>,
  pub declare: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct EnumData {
  pub body: Option<BodyId>,
  pub is_const: bool,
  pub value_type: Option<TypeId>,
  pub type_type: Option<TypeId>,
  pub declare: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct NamespaceData {
  pub body: Option<BodyId>,
  pub value_type: Option<TypeId>,
  pub type_type: Option<TypeId>,
  pub declare: bool,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub struct ModuleData {
  pub body: Option<BodyId>,
  pub value_type: Option<TypeId>,
  pub type_type: Option<TypeId>,
  pub declare: bool,
}

#[derive(Clone)]
struct ProgramTypeResolver {
  semantics: Arc<sem_ts::TsProgramSemantics>,
  def_kinds: HashMap<DefId, DefKind>,
  registry: FileRegistry,
  host: Arc<dyn Host>,
  current_file: FileId,
  local_defs: HashMap<String, DefId>,
}

impl ProgramTypeResolver {
  fn new(
    host: Arc<dyn Host>,
    semantics: Arc<sem_ts::TsProgramSemantics>,
    def_kinds: HashMap<DefId, DefKind>,
    registry: FileRegistry,
    current_file: FileId,
    local_defs: HashMap<String, DefId>,
  ) -> Self {
    ProgramTypeResolver {
      semantics,
      def_kinds,
      registry,
      host,
      current_file,
      local_defs,
    }
  }

  fn matches_namespace(kind: &DefKind, ns: sem_ts::Namespace) -> bool {
    ProgramState::def_namespaces(kind).contains(ns)
  }

  fn resolve_local(&self, name: &str, ns: sem_ts::Namespace) -> Option<DefId> {
    let def = self.local_defs.get(name).copied()?;
    let kind = self.def_kinds.get(&def)?;
    Self::matches_namespace(kind, ns).then_some(def)
  }

  fn global_symbol(&self, name: &str, ns: sem_ts::Namespace) -> Option<sem_ts::SymbolId> {
    self
      .semantics
      .global_symbols()
      .get(name)
      .and_then(|group| group.symbol_for(ns, self.semantics.symbols()))
  }

  fn symbol_owner_file(&self, symbol: sem_ts::SymbolId) -> Option<sem_ts::FileId> {
    let sym = self.semantics.symbols().symbol(symbol);
    match &sym.origin {
      sem_ts::SymbolOrigin::Import { from, .. } => match from {
        sem_ts::ModuleRef::File(file) => Some(*file),
        _ => None,
      },
      _ => match &sym.owner {
        sem_ts::SymbolOwner::Module(file) => Some(*file),
        _ => None,
      },
    }
  }

  fn resolve_symbol_in_module(&self, name: &str, ns: sem_ts::Namespace) -> Option<DefId> {
    let resolved = self
      .semantics
      .resolve_in_module(sem_ts::FileId(self.current_file.0), name, ns)
      .and_then(|symbol| self.pick_decl(symbol, ns))
      .or_else(|| {
        self
          .global_symbol(name, ns)
          .and_then(|symbol| self.pick_decl(symbol, ns))
      });
    resolved.or_else(|| self.resolve_local(name, ns))
  }

  fn resolve_namespace_import_path(
    &self,
    path: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if path.len() < 2 {
      return None;
    }
    let symbol = self
      .semantics
      .resolve_in_module(
        sem_ts::FileId(self.current_file.0),
        &path[0],
        sem_ts::Namespace::NAMESPACE,
      )
      .or_else(|| self.global_symbol(&path[0], sem_ts::Namespace::NAMESPACE))
      .or_else(|| self.global_symbol(&path[0], final_ns))?;
    let Some(mut module) = self
      .import_origin_file(symbol)
      .or_else(|| self.symbol_owner_file(symbol))
    else {
      return None;
    };
    self.resolve_export_path(&path[1..], &mut module, final_ns)
  }

  fn resolve_export_path(
    &self,
    segments: &[String],
    module: &mut sem_ts::FileId,
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    for (idx, segment) in segments.iter().enumerate() {
      let is_last = idx + 1 == segments.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      let symbol = self.semantics.resolve_export(*module, segment, ns)?;
      if is_last {
        return self.pick_decl(symbol, final_ns);
      }
      *module = self.import_origin_file(symbol)?;
    }
    None
  }

  fn pick_decl(&self, symbol: sem_ts::SymbolId, ns: sem_ts::Namespace) -> Option<DefId> {
    let symbols = self.semantics.symbols();
    let mut best: Option<(u8, usize, DefId)> = None;
    for (idx, decl_id) in self.semantics.symbol_decls(symbol, ns).iter().enumerate() {
      let decl = symbols.decl(*decl_id);
      let def = decl.def_id;
      let Some(kind) = self.def_kinds.get(&def) else {
        continue;
      };
      if !Self::matches_namespace(kind, ns) {
        continue;
      }
      let pri = self.def_priority(def, ns);
      best = match best {
        Some((best_pri, best_idx, best_def))
          if best_pri < pri || (best_pri == pri && best_idx <= idx) =>
        {
          Some((best_pri, best_idx, best_def))
        }
        _ => Some((pri, idx, def)),
      };
    }
    best.map(|(_, _, def)| def)
  }

  fn def_priority(&self, def: DefId, ns: sem_ts::Namespace) -> u8 {
    let Some(kind) = self.def_kinds.get(&def) else {
      return u8::MAX;
    };
    if !Self::matches_namespace(kind, ns) {
      return u8::MAX;
    }
    if ns.contains(sem_ts::Namespace::VALUE) {
      return match kind {
        DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_) => 0,
        DefKind::Var(var) if var.body.0 != u32::MAX => 1,
        DefKind::Namespace(_) | DefKind::Module(_) => 2,
        DefKind::Import(_) => 3,
        DefKind::Var(_) => 4,
        DefKind::Interface(_) | DefKind::TypeAlias(_) => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::TYPE) {
      return match kind {
        DefKind::Interface(_) => 0,
        DefKind::TypeAlias(_) => 1,
        DefKind::Class(_) => 2,
        DefKind::Enum(_) => 3,
        DefKind::Import(_) => 4,
        _ => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::NAMESPACE) {
      return match kind {
        DefKind::Namespace(_) | DefKind::Module(_) => 0,
        DefKind::Import(_) => 1,
        _ => 2,
      };
    }
    u8::MAX
  }

  fn import_origin_file(&self, symbol: sem_ts::SymbolId) -> Option<sem_ts::FileId> {
    match &self.semantics.symbols().symbol(symbol).origin {
      sem_ts::SymbolOrigin::Import { from, .. } => match from {
        sem_ts::ModuleRef::File(file) => Some(*file),
        _ => None,
      },
      _ => None,
    }
  }
}

impl TypeResolver for ProgramTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, sem_ts::Namespace::TYPE),
      _ => self.resolve_namespace_import_path(path, sem_ts::Namespace::TYPE),
    }
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, sem_ts::Namespace::VALUE),
      _ => self.resolve_namespace_import_path(path, sem_ts::Namespace::VALUE),
    }
  }

  fn resolve_import_type(&self, module: &str, qualifier: Option<&[String]>) -> Option<DefId> {
    let Some(from_key) = self.registry.lookup_key(self.current_file) else {
      return None;
    };
    let target_key = self.host.resolve(&from_key, module)?;
    let target_file = self.registry.lookup_id(&target_key)?;
    let mut module = sem_ts::FileId(target_file.0);
    let Some(path) = qualifier else {
      return None;
    };
    if path.is_empty() {
      return None;
    }
    self.resolve_export_path(path, &mut module, sem_ts::Namespace::TYPE)
  }
}

#[derive(Clone, Debug)]
struct SemHirBuilder {
  file: FileId,
  file_kind: sem_ts::FileKind,
  is_ambient: bool,
  decls: Vec<sem_ts::Decl>,
  imports: Vec<sem_ts::Import>,
  exports: Vec<sem_ts::Export>,
  ambient_modules: Vec<sem_ts::AmbientModule>,
}

impl SemHirBuilder {
  fn new(file: FileId, file_kind: sem_ts::FileKind) -> Self {
    SemHirBuilder {
      file,
      file_kind,
      is_ambient: false,
      decls: Vec::new(),
      imports: Vec::new(),
      exports: Vec::new(),
      ambient_modules: Vec::new(),
    }
  }

  fn new_ambient(file: FileId, file_kind: sem_ts::FileKind) -> Self {
    SemHirBuilder {
      is_ambient: true,
      ..SemHirBuilder::new(file, file_kind)
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
      is_ambient: self.is_ambient,
      is_global: false,
      exported,
      span,
    });
  }

  fn add_import(&mut self, import: sem_ts::Import) {
    self.imports.push(import);
  }

  fn add_ambient_module(&mut self, module: sem_ts::AmbientModule) {
    self.ambient_modules.push(module);
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
      alias: None,
      alias_span: None,
    }));
  }

  fn finish(self) -> sem_ts::HirFile {
    sem_ts::HirFile {
      file_id: sem_ts::FileId(self.file.0),
      module_kind: sem_ts::ModuleKind::Module,
      file_kind: self.file_kind,
      decls: self.decls,
      imports: self.imports,
      import_equals: Vec::new(),
      exports: self.exports,
      export_as_namespace: Vec::new(),
      ambient_modules: self.ambient_modules,
    }
  }

  fn into_ambient(self, name: String, name_span: TextRange) -> sem_ts::AmbientModule {
    sem_ts::AmbientModule {
      name,
      name_span,
      decls: self.decls,
      imports: self.imports,
      import_equals: Vec::new(),
      exports: self.exports,
      export_as_namespace: Vec::new(),
      ambient_modules: self.ambient_modules,
    }
  }
}

#[derive(Clone, Copy, Debug)]
struct BodyMeta {
  file: FileId,
  hir: Option<hir_js::BodyId>,
  kind: HirBodyKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DefMatchKind {
  Function,
  Var,
  Class,
  Enum,
  Namespace,
  Module,
  Interface,
  TypeAlias,
  Import,
  Other,
}

fn match_kind_from_def(kind: &DefKind) -> DefMatchKind {
  match kind {
    DefKind::Function(_) => DefMatchKind::Function,
    DefKind::Var(_) => DefMatchKind::Var,
    DefKind::Class(_) => DefMatchKind::Class,
    DefKind::Enum(_) => DefMatchKind::Enum,
    DefKind::Namespace(_) => DefMatchKind::Namespace,
    DefKind::Module(_) => DefMatchKind::Module,
    DefKind::Import(_) => DefMatchKind::Import,
    DefKind::Interface(_) => DefMatchKind::Interface,
    DefKind::TypeAlias(_) => DefMatchKind::TypeAlias,
  }
}

fn match_kind_from_hir(kind: HirDefKind) -> DefMatchKind {
  match kind {
    HirDefKind::Function | HirDefKind::Method | HirDefKind::Constructor => DefMatchKind::Function,
    HirDefKind::ImportBinding => DefMatchKind::Import,
    HirDefKind::Class => DefMatchKind::Class,
    HirDefKind::Enum => DefMatchKind::Enum,
    HirDefKind::Namespace => DefMatchKind::Namespace,
    HirDefKind::Module => DefMatchKind::Module,
    HirDefKind::Var | HirDefKind::Field | HirDefKind::Param | HirDefKind::ExportAlias => {
      DefMatchKind::Var
    }
    HirDefKind::Interface => DefMatchKind::Interface,
    HirDefKind::TypeAlias => DefMatchKind::TypeAlias,
    _ => DefMatchKind::Other,
  }
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
  Tuple(Vec<TypeId>, bool),
  Array(TypeId),
  Union(Vec<TypeId>),
  Function {
    params: Vec<TypeId>,
    ret: TypeId,
  },
  Predicate {
    parameter: String,
    asserted: Option<TypeId>,
    asserts: bool,
  },
  Mapped {
    source: TypeId,
    value: TypeId,
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

impl TypeStore {
  const UNKNOWN_IDX: usize = 1;

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
    self.kinds.get(id.0 as usize).unwrap_or_else(|| {
      // Gracefully degrade to `unknown` when encountering an out-of-range
      // identifier instead of panicking; upstream code will treat this as a
      // cache miss and recompute.
      let fallback = Self::UNKNOWN_IDX.min(self.kinds.len().saturating_sub(1));
      &self.kinds[fallback]
    })
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

  pub(crate) fn array(&mut self, element: TypeId) -> TypeId {
    self.alloc(TypeKind::Array(element))
  }

  pub(crate) fn mapped(&mut self, source: TypeId, value: TypeId) -> TypeId {
    self.alloc(TypeKind::Mapped { source, value })
  }

  pub(crate) fn tuple(&mut self, elements: Vec<TypeId>, readonly: bool) -> TypeId {
    self.alloc(TypeKind::Tuple(elements, readonly))
  }

  pub(crate) fn function(&mut self, params: Vec<TypeId>, ret: TypeId) -> TypeId {
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
  span_enabled: bool,
  timer: Option<QueryTimer>,
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
    let start = Instant::now();
    let timer = query_stats.map(|stats| stats.timer_with_start(kind, cache_hit, start));
    if span_enabled {
      if let Some(ty) = type_id {
        span.record("type_id", ty.0);
      }
      let _guard = span.enter();
      drop(_guard);
    }
    Some(QuerySpan {
      span,
      start,
      span_enabled,
      timer,
    })
  }

  fn finish(self, type_id: Option<TypeId>) {
    let duration = self.start.elapsed();
    if let Some(timer) = self.timer {
      timer.finish_with_duration(duration);
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

#[derive(Clone)]
struct DeclTypeResolver {
  file: FileId,
  defs: Arc<HashMap<(FileId, String), DefId>>,
  by_name: HashMap<String, DefId>,
}

impl DeclTypeResolver {
  fn new(file: FileId, defs: Arc<HashMap<(FileId, String), DefId>>) -> Self {
    let mut by_name = HashMap::new();
    for ((_, name), def) in defs.iter() {
      by_name.entry(name.clone()).or_insert(*def);
    }
    DeclTypeResolver {
      file,
      defs,
      by_name,
    }
  }

  fn resolve_name(&self, name: &str) -> Option<DefId> {
    self
      .defs
      .get(&(self.file, name.to_string()))
      .copied()
      .or_else(|| self.by_name.get(name).copied())
  }
}

impl TypeResolver for DeclTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<tti::DefId> {
    path.last().and_then(|name| self.resolve_name(name))
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<tti::DefId> {
    self.resolve_type_name(path)
  }
}

struct ProgramState {
  analyzed: bool,
  cancelled: Arc<AtomicBool>,
  host: Arc<dyn Host>,
  lib_manager: Arc<LibManager>,
  compiler_options: CompilerOptions,
  file_overrides: HashMap<FileKey, Arc<str>>,
  typecheck_db: db::TypecheckDb,
  checker_caches: CheckerCaches,
  cache_stats: CheckerCacheStats,
  asts: HashMap<FileId, Arc<Node<TopLevel>>>,
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  body_map: HashMap<BodyId, BodyMeta>,
  body_parents: HashMap<BodyId, BodyId>,
  hir_lowered: HashMap<FileId, LowerResult>,
  sem_hir: HashMap<FileId, sem_ts::HirFile>,
  local_semantics: HashMap<FileId, sem_ts::locals::TsLocalSemantics>,
  semantics: Option<Arc<sem_ts::TsProgramSemantics>>,
  def_types: HashMap<DefId, TypeId>,
  body_results: HashMap<BodyId, Arc<BodyCheckResult>>,
  symbol_to_def: HashMap<semantic_js::SymbolId, DefId>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  file_registry: FileRegistry,
  file_kinds: HashMap<FileId, FileKind>,
  lib_file_ids: HashSet<FileId>,
  lib_texts: HashMap<FileId, Arc<str>>,
  lib_diagnostics: Vec<Diagnostic>,
  root_ids: Vec<FileId>,
  global_bindings: Arc<BTreeMap<String, SymbolBinding>>,
  namespace_object_types: HashMap<(FileId, String), (tti::TypeId, TypeId)>,
  callable_overloads: HashMap<(FileId, String), Vec<DefId>>,
  diagnostics: Vec<Diagnostic>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  type_store: TypeStore,
  interned_store: Option<Arc<tti::TypeStore>>,
  interned_def_types: HashMap<DefId, tti::TypeId>,
  interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
  builtin: BuiltinTypes,
  query_stats: QueryStatsCollector,
  current_file: Option<FileId>,
  next_def: u32,
  next_body: u32,
  next_symbol: u32,
  type_stack: Vec<DefId>,
}

impl GlobalBindingsDb for ProgramState {
  fn ts_semantics(&self) -> Option<Arc<sem_ts::TsProgramSemantics>> {
    self.semantics.clone()
  }

  fn dts_value_bindings(&self) -> Vec<(String, SymbolBinding)> {
    let mut bindings = Vec::new();
    let semantics = self.semantics.as_deref();
    for (file, state) in self.files.iter() {
      if self.file_kinds.get(file) != Some(&FileKind::Dts) {
        continue;
      }
      for (name, binding) in state.bindings.iter() {
        let mut binding = binding.clone();
        if let Some(def) = binding.def {
          if let Some(ty) = self.interned_def_types.get(&def).copied() {
            binding.type_id = Some(ty);
          }
          if let Some(sem) = semantics {
            if let Some(symbol) = sem.symbol_for_def(def, sem_ts::Namespace::VALUE) {
              binding.symbol = symbol.into();
            }
          }
        }
        bindings.push((name.clone(), binding));
      }
    }
    bindings
  }

  fn type_of_def(&self, def: DefId) -> Option<TypeId> {
    self.interned_def_types.get(&def).copied()
  }

  fn primitive_ids(&self) -> Option<tti::PrimitiveIds> {
    self
      .interned_store
      .as_ref()
      .map(|store| store.primitive_ids())
  }
}

impl ProgramState {
  fn new(
    host: Arc<dyn Host>,
    lib_manager: Arc<LibManager>,
    query_stats: QueryStatsCollector,
    cancelled: Arc<AtomicBool>,
  ) -> ProgramState {
    let default_options = CompilerOptions::default();
    let (type_store, builtin) = TypeStore::new();
    ProgramState {
      analyzed: false,
      cancelled,
      host,
      lib_manager,
      compiler_options: default_options.clone(),
      file_overrides: HashMap::new(),
      typecheck_db: db::TypecheckDb::default(),
      checker_caches: CheckerCaches::new(default_options.cache.clone()),
      cache_stats: CheckerCacheStats::default(),
      asts: HashMap::new(),
      files: HashMap::new(),
      def_data: HashMap::new(),
      body_map: HashMap::new(),
      body_parents: HashMap::new(),
      hir_lowered: HashMap::new(),
      sem_hir: HashMap::new(),
      local_semantics: HashMap::new(),
      semantics: None,
      def_types: HashMap::new(),
      body_results: HashMap::new(),
      symbol_to_def: HashMap::new(),
      symbol_occurrences: HashMap::new(),
      file_registry: FileRegistry::new(),
      file_kinds: HashMap::new(),
      lib_file_ids: HashSet::new(),
      lib_texts: HashMap::new(),
      lib_diagnostics: Vec::new(),
      root_ids: Vec::new(),
      global_bindings: Arc::new(BTreeMap::new()),
      namespace_object_types: HashMap::new(),
      callable_overloads: HashMap::new(),
      diagnostics: Vec::new(),
      symbol_occurrences: HashMap::new(),
      type_store,
      interned_store: None,
      interned_def_types: HashMap::new(),
      interned_type_params: HashMap::new(),
      builtin,
      query_stats,
      current_file: None,
      next_def: 0,
      next_body: 0,
      next_symbol: 0,
      type_stack: Vec::new(),
    }
  }

  fn check_cancelled(&self) -> Result<(), FatalError> {
    if self.cancelled.load(Ordering::Relaxed) {
      Err(FatalError::Cancelled)
    } else {
      Ok(())
    }
  }

  fn set_extra_diagnostics_input(&mut self) {
    let arc: Arc<[Diagnostic]> = Arc::from(self.lib_diagnostics.clone().into_boxed_slice());
    self.typecheck_db.set_extra_diagnostics(arc);
  }

  fn file_id_for_key(&self, key: &FileKey) -> Option<FileId> {
    self.file_registry.lookup_id(key)
  }

  fn file_ids_for_key(&self, key: &FileKey) -> Vec<FileId> {
    self.file_registry.lookup_ids(key)
  }

  fn body_check_context(&self) -> BodyCheckContext {
    let store = self
      .interned_store
      .as_ref()
      .expect("interned store initialized");
    let mut body_info = HashMap::new();
    for (id, meta) in self.body_map.iter() {
      body_info.insert(
        *id,
        BodyInfo {
          file: meta.file,
          hir: meta.hir,
          kind: meta.kind,
        },
      );
    }
    let mut file_bindings = HashMap::new();
    for (file, state) in self.files.iter() {
      file_bindings.insert(*file, state.bindings.clone());
    }
    let mut def_spans = HashMap::new();
    for (def, data) in self.def_data.iter() {
      def_spans.insert((data.file, data.span), *def);
    }
    BodyCheckContext {
      store: Arc::clone(store),
      interned_def_types: self.interned_def_types.clone(),
      interned_type_params: self.interned_type_params.clone(),
      asts: self.asts.clone(),
      lowered: self
        .hir_lowered
        .iter()
        .map(|(file, lowered)| (*file, Arc::new(lowered.clone())))
        .collect(),
      body_info,
      body_parents: self.body_parents.clone(),
      global_bindings: self
        .global_bindings
        .iter()
        .map(|(name, binding)| (name.clone(), binding.clone()))
        .collect(),
      file_bindings,
      def_spans,
      checker_caches: self.checker_caches.clone(),
      cache_mode: self.compiler_options.cache.mode,
      cache_options: self.compiler_options.cache.clone(),
      query_stats: self.query_stats.clone(),
    }
  }

  fn file_key_for_id(&self, id: FileId) -> Option<FileKey> {
    self.file_registry.lookup_key(id)
  }

  fn intern_file_key(&mut self, key: FileKey, origin: FileOrigin) -> FileId {
    let id = self.file_registry.intern(&key, origin);
    if matches!(origin, FileOrigin::Lib) {
      self.lib_file_ids.insert(id);
    } else {
      self.lib_file_ids.remove(&id);
    }
    id
  }

  fn merge_sem_hir(mut base: sem_ts::HirFile, extras: sem_ts::HirFile) -> sem_ts::HirFile {
    debug_assert_eq!(base.file_id, extras.file_id);
    debug_assert_eq!(base.file_kind, extras.file_kind);

    let mut existing_defs: HashSet<sem_ts::DefId> =
      base.decls.iter().map(|decl| decl.def_id).collect();
    let mut existing_decl_keys: HashSet<(String, sem_ts::DeclKind)> = base
      .decls
      .iter()
      .map(|decl| (decl.name.clone(), decl.kind.clone()))
      .collect();

    for decl in extras.decls {
      if existing_defs.contains(&decl.def_id)
        || existing_decl_keys.contains(&(decl.name.clone(), decl.kind.clone()))
      {
        continue;
      }
      existing_defs.insert(decl.def_id);
      existing_decl_keys.insert((decl.name.clone(), decl.kind.clone()));
      base.decls.push(decl);
    }

    for import in extras.imports {
      if !base.imports.contains(&import) {
        base.imports.push(import);
      }
    }
    for import_equals in extras.import_equals {
      if !base.import_equals.contains(&import_equals) {
        base.import_equals.push(import_equals);
      }
    }
    for export in extras.exports {
      if !base.exports.contains(&export) {
        base.exports.push(export);
      }
    }
    for export in extras.export_as_namespace {
      if !base.export_as_namespace.contains(&export) {
        base.export_as_namespace.push(export);
      }
    }
    base.ambient_modules.extend(extras.ambient_modules);

    base.module_kind = ProgramState::module_kind_from_sem_hir(&base);
    base
  }

  fn module_kind_from_sem_hir(file: &sem_ts::HirFile) -> sem_ts::ModuleKind {
    if file.imports.is_empty()
      && file.import_equals.is_empty()
      && file.exports.is_empty()
      && file.export_as_namespace.is_empty()
      && file.ambient_modules.is_empty()
      && file
        .decls
        .iter()
        .all(|decl| matches!(decl.exported, sem_ts::Exported::No))
    {
      sem_ts::ModuleKind::Script
    } else {
      sem_ts::ModuleKind::Module
    }
  }

  fn def_namespaces(kind: &DefKind) -> sem_ts::Namespace {
    match kind {
      DefKind::Function(_) | DefKind::Var(_) => sem_ts::Namespace::VALUE,
      DefKind::Class(_) | DefKind::Enum(_) => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
      DefKind::Interface(_) => sem_ts::Namespace::TYPE,
      DefKind::TypeAlias(_) => sem_ts::Namespace::TYPE,
      DefKind::Namespace(_) | DefKind::Module(_) => {
        sem_ts::Namespace::VALUE | sem_ts::Namespace::NAMESPACE
      }
      DefKind::Import(_) => {
        sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
      }
    }
  }

  fn def_priority(&self, def: DefId, ns: sem_ts::Namespace) -> u8 {
    let Some(data) = self.def_data.get(&def) else {
      return u8::MAX;
    };
    if !Self::def_namespaces(&data.kind).contains(ns) {
      return u8::MAX;
    }
    if ns.contains(sem_ts::Namespace::VALUE) {
      return match &data.kind {
        DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_) => 0,
        DefKind::Var(var) if var.body.0 != u32::MAX => 1,
        DefKind::Namespace(_) | DefKind::Module(_) => 2,
        DefKind::Import(_) => 3,
        DefKind::Var(_) => 4,
        DefKind::Interface(_) | DefKind::TypeAlias(_) => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::TYPE) {
      return match &data.kind {
        DefKind::Interface(_) => 0,
        DefKind::TypeAlias(_) => 1,
        DefKind::Class(_) => 2,
        DefKind::Enum(_) => 3,
        DefKind::Import(_) => 4,
        _ => 5,
      };
    }
    if ns.contains(sem_ts::Namespace::NAMESPACE) {
      return match &data.kind {
        DefKind::Namespace(_) | DefKind::Module(_) => 0,
        DefKind::Import(_) => 1,
        _ => 2,
      };
    }
    u8::MAX
  }

  pub(crate) fn map_decl_to_program_def(
    &self,
    decl: &sem_ts::DeclData,
    ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    let direct = DefId(decl.def_id.0);
    if self.def_data.contains_key(&direct) {
      return Some(direct);
    }

    let mut best: Option<(u8, DefId)> = None;
    for (id, data) in self.def_data.iter() {
      if data.file == FileId(decl.file.0) && data.name == decl.name {
        let pri = self.def_priority(*id, ns);
        best = best
          .map(|(best_pri, best_id)| {
            if pri < best_pri || (pri == best_pri && id < &best_id) {
              (pri, *id)
            } else {
              (best_pri, best_id)
            }
          })
          .or(Some((pri, *id)));
      }
    }
    best.map(|(_, id)| id)
  }

  fn canonical_defs(
    &mut self,
  ) -> Result<HashMap<(FileId, String, sem_ts::Namespace), DefId>, FatalError> {
    let mut def_entries: Vec<_> = self
      .def_data
      .iter()
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    def_entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
    let mut def_by_name: HashMap<(FileId, String, sem_ts::Namespace), DefId> = HashMap::new();
    for (def_id, data) in def_entries {
      let namespaces = Self::def_namespaces(&data.kind);
      for ns in [
        sem_ts::Namespace::VALUE,
        sem_ts::Namespace::TYPE,
        sem_ts::Namespace::NAMESPACE,
      ] {
        if !namespaces.contains(ns) {
          continue;
        }
        let key = (data.file, data.name.clone(), ns);
        let mut mapped_def = def_id;
        if let DefKind::Import(import) = &data.kind {
          if let Some(target) = self
            .exports_for_import(import)?
            .get(&import.original)
            .and_then(|entry| entry.def)
          {
            mapped_def = target;
          }
        }
        def_by_name
          .entry(key)
          .and_modify(|existing| {
            let current = self.def_priority(*existing, ns);
            let new_pri = self.def_priority(mapped_def, ns);
            if new_pri < current || (new_pri == current && mapped_def < *existing) {
              *existing = mapped_def;
            }
          })
          .or_insert(mapped_def);
      }
    }
    Ok(def_by_name)
  }

  fn rebuild_callable_overloads(&mut self) {
    self.callable_overloads.clear();
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      let mut seen_symbols = HashSet::new();
      for def_id in self
        .def_data
        .iter()
        .filter_map(|(def_id, data)| matches!(data.kind, DefKind::Function(_)).then_some(def_id))
      {
        let Some(symbol) =
          semantics.symbol_for_def(sem_ts::DefId(def_id.0), sem_ts::Namespace::VALUE)
        else {
          continue;
        };
        if !seen_symbols.insert(symbol) {
          continue;
        }
        let mut defs = Vec::new();
        let mut seen_defs = HashSet::new();
        for decl_id in semantics.symbol_decls(symbol, sem_ts::Namespace::VALUE) {
          let decl = symbols.decl(*decl_id);
          if !matches!(decl.kind, sem_ts::DeclKind::Function) {
            continue;
          }
          if let Some(mapped) = self.map_decl_to_program_def(decl, sem_ts::Namespace::VALUE) {
            if seen_defs.insert(mapped) {
              defs.push(mapped);
            }
          }
        }
        if !defs.is_empty() {
          for def in defs.iter().copied() {
            if let Some(def_data) = self.def_data.get(&def) {
              self
                .callable_overloads
                .entry((def_data.file, def_data.name.clone()))
                .or_insert_with(|| defs.clone());
            }
          }
        }
      }
      return;
    }

    let mut grouped: BTreeMap<(FileId, String), Vec<(DefId, TextRange)>> = BTreeMap::new();
    for (id, data) in self
      .def_data
      .iter()
      .filter(|(_, data)| matches!(data.kind, DefKind::Function(_)))
    {
      grouped
        .entry((data.file, data.name.clone()))
        .or_default()
        .push((*id, data.span));
    }
    for ((file, name), mut defs) in grouped.into_iter() {
      defs.sort_by_key(|(id, span)| (span.start, span.end, id.0));
      let ordered: Vec<_> = defs.into_iter().map(|(id, _)| id).collect();
      self.callable_overloads.insert((file, name), ordered);
    }
  }

  fn callable_overload_defs(&mut self, def: DefId) -> Option<Vec<DefId>> {
    let (file, name) = {
      let data = self.def_data.get(&def)?;
      if !matches!(data.kind, DefKind::Function(_)) {
        return None;
      }
      (data.file, data.name.clone())
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let key = (file, name);
    Some(
      self
        .callable_overloads
        .get(&key)
        .cloned()
        .unwrap_or_else(|| vec![def]),
    )
  }

  fn merged_overload_callable_type(
    &mut self,
    defs: &[DefId],
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    if defs.is_empty() {
      return None;
    }
    let mut overloads = Vec::new();
    let mut seen_sigs = HashSet::new();
    for def in defs.iter().copied() {
      if !self.interned_def_types.contains_key(&def) {
        let _ = self.type_of_def(def);
      }
      let ty = self.interned_def_types.get(&def).copied().or_else(|| {
        self.def_types.get(&def).copied().map(|store_ty| {
          let mapped = store.canon(convert_type_for_display(store_ty, self, store, cache));
          self.interned_def_types.insert(def, mapped);
          mapped
        })
      });
      let Some(ty) = ty else {
        continue;
      };
      if let tti::TypeKind::Callable { overloads: sigs } = store.type_kind(ty) {
        let mut sigs: Vec<_> = sigs.iter().copied().collect();
        sigs.sort();
        for sig in sigs.into_iter() {
          if seen_sigs.insert(sig) {
            overloads.push(sig);
          }
        }
      }
    }
    if overloads.is_empty() {
      return None;
    }
    Some(store.canon(store.intern_type(tti::TypeKind::Callable { overloads })))
  }

  fn callable_overload_type_for_def(
    &mut self,
    def: DefId,
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    let defs = self.callable_overload_defs(def)?;
    if defs.len() < 2 {
      return None;
    }
    let merged = self.merged_overload_callable_type(&defs, store, cache)?;
    for member in defs {
      self.interned_def_types.insert(member, merged);
    }
    Some(merged)
  }

  fn merge_callable_overload_types(&mut self) {
    let Some(store) = self.interned_store.clone() else {
      return;
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let mut cache = HashMap::new();
    let mut keys: Vec<_> = self.callable_overloads.keys().cloned().collect();
    keys.sort_by(|a, b| (a.0 .0, &a.1).cmp(&(b.0 .0, &b.1)));
    for key in keys.into_iter() {
      let Some(defs) = self.callable_overloads.get(&key).cloned() else {
        continue;
      };
      if defs.len() < 2 {
        continue;
      }
      if let Some(merged) = self.merged_overload_callable_type(&defs, &store, &mut cache) {
        for def in defs.into_iter() {
          self.interned_def_types.insert(def, merged);
        }
      }
    }
  }

  fn interned_unknown(&self) -> TypeId {
    self
      .interned_store
      .as_ref()
      .map(|s| s.primitive_ids().unknown)
      .unwrap_or(self.builtin.unknown)
  }

  fn find_namespace_def(&self, file: FileId, name: &str) -> Option<DefId> {
    self
      .def_data
      .iter()
      .find_map(|(id, data)| match &data.kind {
        DefKind::Namespace(_) | DefKind::Module(_) if data.file == file && data.name == name => {
          Some(*id)
        }
        _ => None,
      })
  }

  fn merge_namespace_value_types(&mut self) -> Result<(), FatalError> {
    let Some(store) = self.interned_store.clone() else {
      return Ok(());
    };
    let mut entries: Vec<_> = self
      .namespace_object_types
      .iter()
      .map(|(k, v)| (k.clone(), *v))
      .collect();
    entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
    for ((file, name), (ns_interned, ns_store)) in entries.into_iter() {
      let ns_def = self.find_namespace_def(file, &name);
      let value_def = self
        .def_data
        .iter()
        .find_map(|(id, data)| match &data.kind {
          DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_)
            if data.file == file && data.name == name =>
          {
            Some(*id)
          }
          DefKind::Var(var) if data.file == file && data.name == name && var.body.0 != u32::MAX => {
            Some(*id)
          }
          _ => None,
        });
      if let (Some(ns_def), Some(val_def)) = (ns_def, value_def) {
        let mut val_interned = self
          .def_types
          .get(&val_def)
          .copied()
          .and_then(|val_store_ty| {
            let mut cache = HashMap::new();
            Some(store.canon(convert_type_for_display(
              val_store_ty,
              self,
              &store,
              &mut cache,
            )))
          })
          .or_else(|| self.interned_def_types.get(&val_def).copied());
        if val_interned
          .map(|ty| {
            matches!(
              store.type_kind(ty),
              tti::TypeKind::Any | tti::TypeKind::Unknown
            )
          })
          .unwrap_or(false)
        {
          val_interned = self.interned_def_types.get(&val_def).copied();
        }
        if let Some(val_ty_interned) = val_interned {
          let merged = store.intersection(vec![val_ty_interned, ns_interned]);
          self.interned_def_types.insert(ns_def, merged);
          self.interned_def_types.insert(val_def, merged);
        }
        if let Some(val_ty) = self.def_types.get(&val_def).copied() {
          self.def_types.insert(ns_def, ns_store);
          self.def_types.insert(val_def, val_ty);
        }
      }
    }
    Ok(())
  }

  fn ensure_analyzed(&mut self, host: &Arc<dyn Host>, roots: &[FileKey]) {
    if let Err(fatal) = self.ensure_analyzed_result(host, roots) {
      self.diagnostics.push(fatal_to_diagnostic(fatal));
    }
  }

  fn ensure_analyzed_result(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<(), FatalError> {
    if self.analyzed {
      self.sync_typecheck_roots();
      return Ok(());
    }
    let mut sorted_roots = roots.to_vec();
    sorted_roots.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    self
      .typecheck_db
      .set_roots(Arc::<[FileKey]>::from(sorted_roots));
    self
      .typecheck_db
      .set_compiler_options(self.compiler_options.clone());
    self
      .typecheck_db
      .set_cancellation_flag(Arc::clone(&self.cancelled));
    let libs = self.collect_libraries(host.as_ref());
    let lib_ids: Vec<FileId> = libs
      .iter()
      .map(|l| self.intern_file_key(l.key.clone(), FileOrigin::Lib))
      .collect();
    self.process_libs(&libs, host);
    let mut root_ids: Vec<FileId> = roots
      .iter()
      .map(|key| self.intern_file_key(key.clone(), FileOrigin::Source))
      .collect();
    root_ids.sort_by_key(|id| id.0);
    self.root_ids = root_ids.clone();
    self.sync_typecheck_roots();
    let mut queue: VecDeque<FileId> = root_ids.iter().copied().collect();
    let mut seen: HashSet<FileId> = HashSet::new();
    while let Some(file) = queue.pop_front() {
      self.check_cancelled()?;
      let prev_file = self.current_file;
      self.current_file = Some(file);
      if !seen.insert(file) || self.lib_file_ids.contains(&file) {
        self.current_file = prev_file;
        continue;
      }
      let Some(file_key) = self.file_key_for_id(file) else {
        self.current_file = prev_file;
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
      let parsed = self.parse_via_salsa(file, file_kind, Arc::clone(&text));
      if let Some(span) = parse_span {
        span.finish(None);
      }
      match parsed {
        Ok(mut ast) => {
          let is_module = !matches!(file_kind, FileKind::Js | FileKind::Jsx);
          if let Some(locals_ast) = Arc::get_mut(&mut ast) {
            let locals = sem_ts::locals::bind_ts_locals(locals_ast, file, is_module);
            self.local_semantics.insert(file, locals);
          }
          self.asts.insert(file, Arc::clone(&ast));
          let (lowered, _lower_diags) = lower_hir_with_diagnostics(
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
          self.hir_lowered.insert(file, lowered.clone());
          let sem_hir = sem_hir_from_lower(ast.as_ref(), &lowered);
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
          let bound_sem_hir = self.bind_file(file, ast.as_ref(), host, &mut queue);
          self.align_definitions_with_hir(file, &lowered);
          self.map_hir_bodies(file, &lowered);
          if let Some(span) = lower_span {
            span.finish(None);
          }
          let merged_sem_hir = ProgramState::merge_sem_hir(sem_hir, bound_sem_hir);
          self.sem_hir.insert(file, merged_sem_hir);
        }
        Err(err) => {
          let _ = err;
        }
      }
      self.current_file = prev_file;
    }
    if !self.sem_hir.is_empty() {
      self.compute_semantics(host, &root_ids, &lib_ids)?;
    }
    self.resolve_reexports();
    self.rebuild_callable_overloads();
    self.recompute_global_bindings();
    self.analyzed = true;
    Ok(())
  }

  fn ensure_interned_types(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<(), FatalError> {
    if self.interned_store.is_some() && self.interned_def_types.len() >= self.def_data.len() {
      self.rebuild_callable_overloads();
      self.merge_callable_overload_types();
      return Ok(());
    }
    self.ensure_analyzed_result(host, roots)?;
    self.check_cancelled()?;
    self.rebuild_callable_overloads();

    let store = self.interned_store.clone().unwrap_or_else(|| {
      let store = tti::TypeStore::with_options((&self.compiler_options).into());
      self.interned_store = Some(Arc::clone(&store));
      store
    });
    self.interned_def_types.clear();
    self.interned_type_params.clear();
    let mut def_types = HashMap::new();
    let mut type_params = HashMap::new();
    let mut namespace_types: HashMap<(FileId, String), (tti::TypeId, TypeId)> = HashMap::new();
    let def_by_name = self.canonical_defs()?;
    let mut hir_def_maps: HashMap<FileId, HashMap<HirDefId, DefId>> = HashMap::new();
    let hir_namespaces = |kind: HirDefKind| -> sem_ts::Namespace {
      match kind {
        HirDefKind::Class => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
        HirDefKind::Enum => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
        HirDefKind::Interface | HirDefKind::TypeAlias => sem_ts::Namespace::TYPE,
        HirDefKind::Namespace | HirDefKind::Module => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::NAMESPACE
        }
        HirDefKind::ImportBinding => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
        }
        _ => sem_ts::Namespace::VALUE,
      }
    };
    let ns_priority = |ns: &sem_ts::Namespace| {
      if ns.contains(sem_ts::Namespace::TYPE) {
        0
      } else if ns.contains(sem_ts::Namespace::VALUE) {
        1
      } else {
        2
      }
    };
    let mut ordered_defs: Vec<_> = def_by_name.iter().collect();
    ordered_defs.sort_by(|a, b| {
      let ((file_a, name_a, ns_a), _) = a;
      let ((file_b, name_b, ns_b), _) = b;
      (file_a.0, name_a, ns_priority(ns_a), ns_a.bits()).cmp(&(
        file_b.0,
        name_b,
        ns_priority(ns_b),
        ns_b.bits(),
      ))
    });
    let mut flat_defs: HashMap<(FileId, String), DefId> = HashMap::new();
    for ((file, name, _), def_id) in ordered_defs.into_iter() {
      flat_defs.entry((*file, name.clone())).or_insert(*def_id);
    }

    let mut lowered_entries: Vec<_> = self
      .hir_lowered
      .iter()
      .map(|(file, lowered)| (*file, lowered.clone()))
      .collect();
    lowered_entries.sort_by_key(|(file, _)| file.0);
    for (file, lowered) in lowered_entries.iter() {
      self.check_cancelled()?;
      let mut def_map: HashMap<DefId, DefId> = HashMap::new();
      let mut local_defs: HashMap<String, HirDefId> = HashMap::new();
      for def in lowered.defs.iter() {
        if let Some(name) = lowered.names.resolve(def.name) {
          local_defs.insert(name.to_string(), def.id);
          let namespaces = hir_namespaces(def.path.kind);
          let mapped = namespaces
            .iter_bits()
            .find_map(|ns| def_by_name.get(&(*file, name.to_string(), ns)).copied());
          if let Some(mapped) = mapped {
            def_map.insert(def.id, mapped);
          }
        }
      }
      hir_def_maps.insert(*file, def_map.clone());
      let file_key = self.file_key_for_id(*file);
      let registry = self.file_registry.clone();
      let key_to_id = move |key: &FileKey| registry.lookup_id(key);
      let mut lowerer = check::decls::HirDeclLowerer::new(
        Arc::clone(&store),
        &lowered.types,
        self.semantics.as_deref(),
        flat_defs.clone(),
        *file,
        file_key.clone(),
        local_defs,
        &mut self.diagnostics,
        Some(&def_map),
        Some(&flat_defs),
        Some(host.as_ref()),
        Some(&key_to_id),
      );
      for def in lowered.defs.iter() {
        let Some(info) = def.type_info.as_ref() else {
          continue;
        };
        let (ty, params) = lowerer.lower_type_info(def.id, info, &lowered.names);
        let target_def = def_map.get(&def.id).copied().or_else(|| {
          lowered.names.resolve(def.name).and_then(|n| {
            let name = n.to_string();
            let namespaces = hir_namespaces(def.path.kind);
            namespaces
              .iter_bits()
              .find_map(|ns| def_by_name.get(&(*file, name.clone(), ns)).copied())
          })
        });
        if let Some(mapped) = target_def {
          let ty = if let Some(existing) = def_types.get(&mapped) {
            ProgramState::merge_interned_decl_types(&store, *existing, ty)
          } else {
            ty
          };
          def_types.insert(mapped, ty);
          if !params.is_empty() {
            type_params.insert(mapped, params);
          }
        }
      }
    }

    self.collect_function_decl_types(&store, &flat_defs, &mut def_types, &mut type_params);

    let value_ns_priority = |ns: &sem_ts::Namespace| {
      if ns.contains(sem_ts::Namespace::VALUE) {
        0
      } else if ns.contains(sem_ts::Namespace::NAMESPACE) {
        1
      } else {
        2
      }
    };
    let mut value_defs_by_name: HashMap<(FileId, String), DefId> = HashMap::new();
    let mut ordered_value_defs: Vec<_> = def_by_name.iter().collect();
    ordered_value_defs.sort_by(|a, b| {
      let ((file_a, name_a, ns_a), _) = a;
      let ((file_b, name_b, ns_b), _) = b;
      (
        file_a.0,
        name_a,
        value_ns_priority(ns_a),
        ns_a.bits(),
      )
        .cmp(&(file_b.0, name_b, value_ns_priority(ns_b), ns_b.bits()))
    });
    for ((file, name, ns), def_id) in ordered_value_defs.into_iter() {
      if ns.contains(sem_ts::Namespace::VALUE) || ns.contains(sem_ts::Namespace::NAMESPACE) {
        value_defs_by_name.entry((*file, name.clone())).or_insert(*def_id);
      }
    }

    #[derive(Clone)]
    struct NamespaceInfo {
      def: DefId,
      hir_def: HirDefId,
      file: FileId,
      name: String,
      members: Vec<(String, DefId, HirDefKind)>,
    }

    let mut hir_lookup_by_file: HashMap<FileId, HashMap<HirDefId, hir_js::DefData>> =
      HashMap::new();
    for (file, lowered) in lowered_entries.iter() {
      let mut map = HashMap::new();
      for def in lowered.defs.iter() {
        map.insert(def.id, def.clone());
      }
      hir_lookup_by_file.insert(*file, map);
    }

    let mut namespace_infos: Vec<NamespaceInfo> = Vec::new();
    let mut hir_namespace_map: HashMap<HirDefId, DefId> = HashMap::new();

    for (file, lowered) in lowered_entries.iter() {
      let def_map = hir_def_maps.get(file);
      for ns_def in lowered
        .defs
        .iter()
        .filter(|d| matches!(d.path.kind, HirDefKind::Namespace | HirDefKind::Module))
      {
        let Some(ns_name) = lowered.names.resolve(ns_def.name) else {
          continue;
        };
        let mapped = def_by_name
          .get(&(*file, ns_name.to_string(), sem_ts::Namespace::NAMESPACE))
          .copied()
          .or_else(|| def_map.and_then(|map| map.get(&ns_def.id).copied()))
          .or_else(|| self.def_data.contains_key(&ns_def.id).then_some(ns_def.id))
          .or_else(|| value_defs_by_name.get(&(*file, ns_name.to_string())).copied());
        let Some(def_id) = mapped else {
          continue;
        };
        hir_namespace_map.insert(ns_def.id, def_id);
        namespace_infos.push(NamespaceInfo {
          def: def_id,
          hir_def: ns_def.id,
          file: *file,
          name: ns_name.to_string(),
          members: Vec::new(),
        });
      }
    }

    let namespace_hirs: HashSet<HirDefId> = hir_namespace_map.keys().copied().collect();

    fn namespace_ancestor(
      mut current: Option<HirDefId>,
      lookup: &HashMap<HirDefId, hir_js::DefData>,
      namespaces: &HashSet<HirDefId>,
    ) -> Option<HirDefId> {
      while let Some(def) = current {
        if namespaces.contains(&def) {
          return Some(def);
        }
        current = lookup.get(&def).and_then(|data| data.parent);
      }
      None
    }

    let mut namespace_parents: HashMap<DefId, DefId> = HashMap::new();
    for info in namespace_infos.iter() {
      let Some(lookup) = hir_lookup_by_file.get(&info.file) else {
        continue;
      };
      let parent = lookup
        .get(&info.hir_def)
        .and_then(|def| namespace_ancestor(def.parent, lookup, &namespace_hirs))
        .and_then(|hir_parent| hir_namespace_map.get(&hir_parent).copied());
      if let Some(parent) = parent {
        namespace_parents.insert(info.def, parent);
      }
    }

    let mut namespace_members: HashMap<DefId, Vec<(String, DefId, HirDefKind)>> = HashMap::new();
    for (file, lowered) in lowered_entries.iter() {
      let Some(lookup) = hir_lookup_by_file.get(file) else {
        continue;
      };
      let def_map = hir_def_maps.get(file);
      for member in lowered.defs.iter() {
        let member_kind = member.path.kind;
        if !matches!(
          member_kind,
          HirDefKind::Var
            | HirDefKind::Function
            | HirDefKind::Class
            | HirDefKind::Enum
            | HirDefKind::Namespace
            | HirDefKind::Module
        ) {
          continue;
        }
        let Some(owner_hir) = namespace_ancestor(member.parent, lookup, &namespace_hirs) else {
          continue;
        };
        let Some(owner_def) = hir_namespace_map.get(&owner_hir).copied() else {
          continue;
        };
        let Some(member_name) = lowered.names.resolve(member.name) else {
          continue;
        };
        let target_ns = match member_kind {
          HirDefKind::Namespace | HirDefKind::Module => sem_ts::Namespace::NAMESPACE,
          _ => sem_ts::Namespace::VALUE,
        };
        let member_def = def_by_name
          .get(&(*file, member_name.to_string(), target_ns))
          .copied()
          .or_else(|| {
            if target_ns.contains(sem_ts::Namespace::VALUE) {
              value_defs_by_name
                .get(&(*file, member_name.to_string()))
                .copied()
            } else {
              None
            }
          })
          .or_else(|| def_map.and_then(|map| map.get(&member.id).copied()))
          .or_else(|| self.def_data.contains_key(&member.id).then_some(member.id));
        let Some(member_def) = member_def else {
          continue;
        };
        namespace_members
          .entry(owner_def)
          .or_default()
          .push((member_name.to_string(), member_def, member_kind));
      }
    }

    fn namespace_depth_for(
      def: DefId,
      parents: &HashMap<DefId, DefId>,
      cache: &mut HashMap<DefId, usize>,
    ) -> usize {
      if let Some(depth) = cache.get(&def) {
        return *depth;
      }
      let depth = parents
        .get(&def)
        .map(|parent| 1 + namespace_depth_for(*parent, parents, cache))
        .unwrap_or(0);
      cache.insert(def, depth);
      depth
    }

    let mut depth_cache = HashMap::new();

    let mut namespace_infos: Vec<NamespaceInfo> = namespace_infos
      .into_iter()
      .map(|mut info| {
        let mut members = namespace_members.remove(&info.def).unwrap_or_default();
        members.sort_by(|a, b| {
          let ord = a.0.cmp(&b.0);
          if ord == std::cmp::Ordering::Equal {
            a.1.cmp(&b.1)
          } else {
            ord
          }
        });
        members.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1 && a.2 == b.2);
        info.members = members;
        info
      })
      .collect();

    namespace_infos.sort_by(|a, b| {
      let depth_a = namespace_depth_for(a.def, &namespace_parents, &mut depth_cache);
      let depth_b = namespace_depth_for(b.def, &namespace_parents, &mut depth_cache);
      (
        Reverse(depth_a),
        a.file.0,
        &a.name,
        a.def.0,
      )
        .cmp(&(Reverse(depth_b), b.file.0, &b.name, b.def.0))
    });

    let mut namespace_cache: HashMap<DefId, (tti::TypeId, TypeId)> = HashMap::new();
    for info in namespace_infos.iter() {
      let mut props: BTreeMap<String, (tti::TypeId, TypeId)> = BTreeMap::new();
      for (name, member_def, member_kind) in info.members.iter() {
        let (prop_interned, prop_store) = match member_kind {
          HirDefKind::Namespace | HirDefKind::Module => namespace_cache
            .get(member_def)
            .copied()
            .or_else(|| namespace_types.get(&(info.file, name.clone())).copied())
            .unwrap_or((store.primitive_ids().any, self.builtin.any)),
          HirDefKind::Var
          | HirDefKind::Function
          | HirDefKind::Class
          | HirDefKind::Enum => {
            let interned = if let Some(existing) = def_types.get(member_def).copied() {
              existing
            } else {
              if !self.def_types.contains_key(member_def) {
                self.type_of_def(*member_def)?;
              }
              let store_ty = self
                .def_types
                .get(member_def)
                .copied()
                .unwrap_or(self.builtin.unknown);
              let interned = self.ensure_interned_type(store_ty);
              def_types.insert(*member_def, interned);
              interned
            };
            let kind = store.type_kind(interned);
            let (interned, store_ty) = if matches!(member_kind, HirDefKind::Class | HirDefKind::Enum)
              && matches!(kind, tti::TypeKind::Unknown)
            {
              (store.primitive_ids().any, self.builtin.any)
            } else {
              let store_ty = self
                .def_types
                .get(member_def)
                .copied()
                .unwrap_or_else(|| self.import_interned_type(interned));
              (interned, store_ty)
            };
            (interned, store_ty)
          }
          _ => continue,
        };
        props
          .entry(name.clone())
          .and_modify(|(existing_interned, existing_store)| {
            *existing_interned =
              ProgramState::merge_interned_decl_types(&store, *existing_interned, prop_interned);
            *existing_store = self.merge_namespace_store_types(*existing_store, prop_store);
          })
          .or_insert((prop_interned, prop_store));
      }

      let mut shape = tti::Shape::new();
      let mut obj = ObjectType::empty();
      for (name, (prop_interned, prop_store)) in props.into_iter() {
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty: prop_interned,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
        obj.props.entry(name).or_insert(ObjectProperty {
          typ: prop_store,
          optional: false,
          readonly: true,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      let interned = store.intern_type(tti::TypeKind::Object(obj_id));
      let store_ty = self.type_store.object(obj);
      namespace_cache.insert(info.def, (interned, store_ty));
      namespace_types
        .entry((info.file, info.name.clone()))
        .and_modify(|(existing_interned, existing_store)| {
          *existing_interned =
            ProgramState::merge_interned_object_types(&store, *existing_interned, interned);
          *existing_store = self.merge_namespace_store_types(*existing_store, store_ty);
        })
        .or_insert((interned, store_ty));
    }

    if !namespace_types.is_empty() {
      let mut ns_entries: Vec<_> = namespace_types.into_iter().collect();
      ns_entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
      self.namespace_object_types = ns_entries.iter().cloned().collect();
      for ((file, name), (interned, store_ty)) in ns_entries.into_iter() {
        let mapped = [sem_ts::Namespace::NAMESPACE, sem_ts::Namespace::VALUE]
          .into_iter()
          .find_map(|ns| def_by_name.get(&(file, name.clone(), ns)).copied());
        if let Some(def) = mapped {
          self
            .interned_def_types
            .entry(def)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(&store, *existing, interned);
            })
            .or_insert(interned);
          self.def_types.entry(def).or_insert(store_ty);
        }
      }
    }

    let mut missing_defs: Vec<_> = self
      .def_data
      .keys()
      .copied()
      .filter(|def_id| {
        def_types.get(def_id).map_or(true, |ty| {
          matches!(store.type_kind(*ty), tti::TypeKind::Unknown)
        })
      })
      .collect();
    missing_defs.sort_by_key(|d| d.0);
    for def_id in missing_defs {
      let store_ty = match self.def_types.get(&def_id).copied() {
        Some(ty) => ty,
        None => {
          self.type_of_def(def_id)?;
          self
            .def_types
            .get(&def_id)
            .copied()
            .unwrap_or(self.builtin.unknown)
        }
      };
      let mut cache = HashMap::new();
      let interned = convert_type_for_display(store_ty, self, &store, &mut cache);
      def_types.insert(def_id, store.canon(interned));
    }

    self.interned_store = Some(store);
    self.interned_def_types = def_types;
    self.interned_type_params = type_params;
    self.merge_callable_overload_types();
    self.merge_namespace_value_types()?;
    self.recompute_global_bindings();
    codes::normalize_diagnostics(&mut self.diagnostics);
    Ok(())
  }

  fn collect_function_decl_types(
    &mut self,
    store: &Arc<tti::TypeStore>,
    def_by_name: &HashMap<(FileId, String), DefId>,
    def_types: &mut HashMap<DefId, tti::TypeId>,
    type_params: &mut HashMap<DefId, Vec<TypeParamId>>,
  ) {
    if self.asts.is_empty() {
      return;
    }
    let resolver_defs = Arc::new(def_by_name.clone());
    let mut def_by_span: HashMap<(FileId, TextRange), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(FileId, String), Vec<DefId>> = HashMap::new();
    for (def_id, data) in self.def_data.iter() {
      if !matches!(data.kind, DefKind::Function(_)) {
        continue;
      }
      def_by_span.insert((data.file, data.span), *def_id);
      defs_by_name
        .entry((data.file, data.name.clone()))
        .or_default()
        .push(*def_id);
    }

    let mut ast_entries: Vec<_> = self
      .asts
      .iter()
      .map(|(file, ast)| (*file, Arc::clone(ast)))
      .collect();
    ast_entries.sort_by_key(|(file, _)| file.0);
    let mut sigs_by_name: HashMap<(FileId, String), Vec<tti::SignatureId>> = HashMap::new();
    let mut def_type_params: HashMap<DefId, Vec<TypeParamId>> = HashMap::new();
    for (file, ast) in ast_entries.into_iter() {
      let resolver = Arc::new(DeclTypeResolver::new(file, Arc::clone(&resolver_defs)));
      for stmt in ast.stx.body.iter() {
        let Stmt::FunctionDecl(func) = stmt.stx.as_ref() else {
          continue;
        };
        let span = loc_to_span(file, stmt.loc).range;
        let Some(def_id) = def_by_span.get(&(file, span)).copied() else {
          continue;
        };
        let Some(name) = func.stx.name.as_ref() else {
          continue;
        };
        let (sig_id, params, diags) =
          Self::lower_function_signature(store, file, func.stx.as_ref(), Some(resolver.clone()));
        if !diags.is_empty() {
          self.diagnostics.extend(diags);
        }
        sigs_by_name
          .entry((file, name.stx.name.clone()))
          .or_default()
          .push(sig_id);
        if !params.is_empty() {
          def_type_params.entry(def_id).or_insert(params);
        }
      }
    }

    for ((file, name), mut sigs) in sigs_by_name.into_iter() {
      sigs.sort();
      sigs.dedup();
      let callable = store.intern_type(tti::TypeKind::Callable { overloads: sigs });
      if let Some(def_ids) = defs_by_name.get(&(file, name)) {
        let shared_params = def_ids
          .iter()
          .find_map(|id| def_type_params.get(id).cloned());
        for def_id in def_ids {
          def_types
            .entry(*def_id)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(store, *existing, callable);
            })
            .or_insert(callable);
          if let Some(params) = def_type_params
            .get(def_id)
            .cloned()
            .or_else(|| shared_params.clone())
          {
            type_params.entry(*def_id).or_insert(params);
          }
        }
      }
    }
  }

  fn lower_function_signature(
    store: &Arc<tti::TypeStore>,
    file: FileId,
    func: &FuncDecl,
    resolver: Option<Arc<dyn TypeResolver>>,
  ) -> (tti::SignatureId, Vec<TypeParamId>, Vec<Diagnostic>) {
    let mut lowerer = match resolver {
      Some(resolver) => TypeLowerer::with_resolver(Arc::clone(store), resolver),
      None => TypeLowerer::new(Arc::clone(store)),
    };
    lowerer.set_file(file);
    let mut type_param_decls = Vec::new();
    if let Some(params) = func.function.stx.type_parameters.as_ref() {
      type_param_decls = lowerer.register_type_params(params);
    }
    let type_param_ids: Vec<_> = type_param_decls.iter().map(|d| d.id).collect();
    let mut params = Vec::new();
    let mut this_param = None;
    for (idx, param) in func.function.stx.parameters.iter().enumerate() {
      let name = match param.stx.pattern.stx.pat.stx.as_ref() {
        Pat::Id(id) => Some(id.stx.name.clone()),
        _ => None,
      };
      let ty = param
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| lowerer.lower_type_expr(ann))
        .unwrap_or(store.primitive_ids().unknown);
      if idx == 0 && matches!(name.as_deref(), Some("this")) {
        this_param = Some(ty);
        continue;
      }
      params.push(tti::Param {
        name: name.map(|n| store.intern_name(n)),
        ty,
        optional: param.stx.optional,
        rest: param.stx.rest,
      });
    }
    let ret = func
      .function
      .stx
      .return_type
      .as_ref()
      .map(|r| lowerer.lower_type_expr(r))
      .unwrap_or(store.primitive_ids().unknown);
    let sig = tti::Signature {
      params,
      ret,
      type_params: type_param_decls,
      this_param,
    };
    let sig_id = store.intern_signature(sig);
    let diags = lowerer.take_diagnostics();
    (sig_id, type_param_ids, diags)
  }

  fn merge_namespace_store_types(&mut self, existing: TypeId, incoming: TypeId) -> TypeId {
    match (
      self.type_store.kind(existing).clone(),
      self.type_store.kind(incoming).clone(),
    ) {
      (TypeKind::Object(mut a), TypeKind::Object(b)) => {
        for (name, prop) in b.props.into_iter() {
          a.props.insert(name, prop);
        }
        if a.string_index.is_none() {
          a.string_index = b.string_index;
        }
        if a.number_index.is_none() {
          a.number_index = b.number_index;
        }
        self.type_store.object(a)
      }
      _ => self.type_store.union(vec![existing, incoming], &self.builtin),
    }
  }

  fn merge_interned_object_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Object(obj_a), tti::TypeKind::Object(obj_b)) => {
        let mut shape = store.shape(store.object(obj_a).shape);
        let other = store.shape(store.object(obj_b).shape);
        let mut merged = Vec::new();
        for prop in shape
          .properties
          .into_iter()
          .chain(other.properties.into_iter())
        {
          if let Some(existing) = merged
            .iter_mut()
            .find(|p: &&mut Property| p.key == prop.key)
          {
            *existing = prop;
          } else {
            merged.push(prop);
          }
        }
        shape.properties = merged;
        shape.call_signatures.extend(other.call_signatures);
        shape
          .construct_signatures
          .extend(other.construct_signatures);
        shape.indexers.extend(other.indexers);
        let shape_id = store.intern_shape(shape);
        let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
        store.intern_type(tti::TypeKind::Object(obj_id))
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn merge_callable_with_object(
    store: &Arc<tti::TypeStore>,
    overloads: &[tti::SignatureId],
    object: tti::ObjectId,
    object_ty: tti::TypeId,
  ) -> tti::TypeId {
    let shape = store.shape(store.object(object).shape);
    let mut merged = overloads.to_vec();
    merged.extend(shape.call_signatures.iter().copied());
    merged.sort();
    merged.dedup();
    let callable = store.intern_type(tti::TypeKind::Callable { overloads: merged });
    let has_extras = !shape.properties.is_empty()
      || !shape.construct_signatures.is_empty()
      || !shape.indexers.is_empty();
    if has_extras {
      store.intersection(vec![callable, object_ty])
    } else {
      callable
    }
  }

  fn merge_interned_decl_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Callable { overloads: a }, tti::TypeKind::Callable { overloads: b }) => {
        let mut merged = a;
        merged.extend(b.into_iter());
        merged.sort();
        merged.dedup();
        store.intern_type(tti::TypeKind::Callable { overloads: merged })
      }
      (tti::TypeKind::Callable { overloads }, tti::TypeKind::Object(obj)) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, incoming)
      }
      (tti::TypeKind::Object(obj), tti::TypeKind::Callable { overloads }) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, existing)
      }
      (tti::TypeKind::Object(_), tti::TypeKind::Object(_)) => {
        ProgramState::merge_interned_object_types(store, existing, incoming)
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn collect_libraries(&mut self, host: &dyn Host) -> Vec<LibFile> {
    let options = host.compiler_options();
    self.compiler_options = options.clone();
    self.checker_caches = CheckerCaches::new(options.cache.clone());
    self.cache_stats = CheckerCacheStats::default();
    self.typecheck_db.set_compiler_options(options.clone());
    self
      .typecheck_db
      .set_cancellation_flag(self.cancelled.clone());
    let libs = collect_libs(&options, host.lib_files(), &self.lib_manager);
    let validated = validate_libs(libs, |lib| {
      self.intern_file_key(lib.key.clone(), FileOrigin::Lib)
    });
    self.lib_diagnostics = validated.diagnostics.clone();

    let mut dts_libs = Vec::new();
    for (lib, file_id) in validated.libs.into_iter() {
      self.file_kinds.insert(file_id, FileKind::Dts);
      dts_libs.push(lib);
    }

    dts_libs
  }

  fn process_libs(&mut self, libs: &[LibFile], host: &Arc<dyn Host>) {
    for lib in libs {
      let file_id = self.intern_file_key(lib.key.clone(), FileOrigin::Lib);
      self.lib_texts.insert(file_id, lib.text.clone());
      let parsed = self.parse_via_salsa(file_id, FileKind::Dts, Arc::clone(&lib.text));
      match parsed {
        Ok(mut ast) => {
          if let Some(locals_ast) = Arc::get_mut(&mut ast) {
            let locals = sem_ts::locals::bind_ts_locals(locals_ast, file_id, true);
            self.local_semantics.insert(file_id, locals);
          }
          self.asts.insert(file_id, Arc::clone(&ast));
          let (lowered, lower_diags) = lower_hir_with_diagnostics(file_id, HirFileKind::Dts, &ast);
          let _ = lower_diags;
          let mut queue = VecDeque::new();
          let bound_sem_hir = self.bind_file(file_id, ast.as_ref(), host, &mut queue);
          let sem_hir = sem_hir_from_lower(ast.as_ref(), &lowered);
          self.hir_lowered.insert(file_id, lowered.clone());
          let merged_sem_hir = ProgramState::merge_sem_hir(sem_hir, bound_sem_hir);
          self.sem_hir.insert(file_id, merged_sem_hir);
          self.align_definitions_with_hir(file_id, &lowered);
          self.map_hir_bodies(file_id, &lowered);
        }
        Err(err) => {
          let _ = err;
        }
      }
    }
  }

  fn update_typecheck_roots(&mut self, roots: &[FileId]) {
    let mut keys: Vec<FileKey> = roots
      .iter()
      .copied()
      .chain(self.lib_file_ids.iter().copied())
      .filter_map(|id| self.file_registry.lookup_key(id))
      .collect();
    keys.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    keys.dedup();
    self
      .typecheck_db
      .set_roots(Arc::from(keys.into_boxed_slice()));
  }

  fn sync_typecheck_roots(&mut self) {
    let roots = self.root_ids.clone();
    self.update_typecheck_roots(&roots);
  }

  fn prime_module_resolve_inputs(&mut self) {
    let mut seen = HashSet::new();
    for (file, sem_hir) in self.sem_hir.iter() {
      let Some(file_key) = self.file_key_for_id(*file) else {
        continue;
      };
      let mut record = |spec: &str| {
        if !seen.insert((*file, spec.to_string())) {
          return;
        }
        let target = self
          .host
          .resolve(&file_key, spec)
          .and_then(|key| self.file_registry.lookup_id(&key));
        self
          .typecheck_db
          .set_module_resolution(*file, Arc::<str>::from(spec), target);
      };
      for import in sem_hir.imports.iter() {
        record(&import.specifier);
      }
      for export in sem_hir.exports.iter() {
        match export {
          sem_ts::Export::Named(named) => {
            if let Some(specifier) = named.specifier.as_ref() {
              record(specifier);
            }
          }
          sem_ts::Export::All(all) => record(&all.specifier),
          sem_ts::Export::ExportAssignment { .. } => {}
        }
      }
    }
  }

  fn program_diagnostics(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<Arc<[Diagnostic]>, FatalError> {
    self.check_cancelled()?;
    self.ensure_analyzed_result(host, roots)?;
    self.ensure_interned_types(host, roots)?;
    self.sync_typecheck_roots();
    self.prime_module_resolve_inputs();
    self.set_extra_diagnostics_input();

    let body_ids: Vec<_> = {
      let db = self.typecheck_db.clone();
      let mut body_ids: Vec<_> = db::body_to_file(&db)
        .iter()
        .filter_map(|(body, file)| {
          let kind = db::file_kind(&db, *file);
          (!matches!(kind, FileKind::Dts)).then_some(*body)
        })
        .collect();
      body_ids.sort_by_key(|id| id.0);
      body_ids
    };

    for body in body_ids {
      self.check_cancelled()?;
      let _ = self.check_body(body)?;
    }

    let db = self.typecheck_db.clone();
    Ok(db::program_diagnostics(&db))
  }

  fn load_text(&self, file: FileId, host: &Arc<dyn Host>) -> Result<Arc<str>, HostError> {
    let Some(key) = self.file_key_for_id(file) else {
      return Err(HostError::new(format!("missing file key for {file:?}")));
    };
    let origin = self
      .file_registry
      .origin(file)
      .unwrap_or(FileOrigin::Source);
    if matches!(origin, FileOrigin::Lib) {
      if let Some(text) = self.lib_texts.get(&file) {
        return Ok(text.clone());
      }
    }
    if let Some(text) = self.file_overrides.get(&key) {
      return Ok(text.clone());
    }
    if let Some(text) = self.lib_texts.get(&file) {
      return Ok(text.clone());
    }
    host.file_text(&key)
  }

  fn record_module_resolution(
    &mut self,
    from: FileId,
    specifier: &str,
    host: &Arc<dyn Host>,
  ) -> Option<FileId> {
    let spec: Arc<str> = Arc::from(specifier.to_string());
    let resolved = self
      .file_key_for_id(from)
      .and_then(|from_key| host.resolve(&from_key, specifier))
      .map(|target_key| self.intern_file_key(target_key, FileOrigin::Source));
    self
      .typecheck_db
      .set_module_resolution(from, spec, resolved);
    resolved
  }

  fn set_salsa_inputs(&mut self, file: FileId, kind: FileKind, text: Arc<str>) {
    let key = self
      .file_registry
      .lookup_key(file)
      .unwrap_or_else(|| panic!("file {:?} must be interned before setting inputs", file));
    let origin = self
      .file_registry
      .origin(file)
      .unwrap_or(FileOrigin::Source);
    self.typecheck_db.set_file(file, key, kind, text, origin);
  }

  fn parse_via_salsa(
    &mut self,
    file: FileId,
    kind: FileKind,
    text: Arc<str>,
  ) -> Result<Arc<Node<TopLevel>>, Diagnostic> {
    self.set_salsa_inputs(file, kind, Arc::clone(&text));
    let result = db::parse(&self.typecheck_db, file);
    match result.ast {
      Some(ast) => Ok(ast),
      None => Err(result.diagnostics.into_iter().next().unwrap_or_else(|| {
        codes::MISSING_BODY.error("missing parsed AST", Span::new(file, TextRange::new(0, 0)))
      })),
    }
  }

  fn recompute_global_bindings(&mut self) {
    self.global_bindings = crate::db::global_bindings(self);
  }

  fn compute_semantics(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileId],
    libs: &[FileId],
  ) -> Result<(), FatalError> {
    self.check_cancelled()?;
    let resolver = HostResolver {
      host: Arc::clone(host),
      registry: self.file_registry.clone(),
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
            import_equals: Vec::new(),
            exports: Vec::new(),
            export_as_namespace: Vec::new(),
            ambient_modules: Vec::new(),
          })
        })
    });
    self.semantics = Some(Arc::new(semantics));
    self.push_semantic_diagnostics(diags);
    Ok(())
  }

  /// Remap bound definitions to the stable IDs produced by HIR lowering while
  /// preserving existing symbols and cached types.
  ///
  /// The binder allocates definitions sequentially, but HIR uses content-derived
  /// identifiers that stay stable across edits. Re-aligning keeps
  /// `definitions_in_file`, `expr_at`, and `type_of_def` working across repeated
  /// checks and avoids dropping cached type information when files are
  /// re-lowered.
  fn align_definitions_with_hir(&mut self, file: FileId, lowered: &LowerResult) {
    let file_def_ids: HashSet<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .map(|(id, _)| *id)
      .collect();
    let mut by_name_kind: HashMap<(String, DefMatchKind), Vec<(DefId, DefData)>> = HashMap::new();
    for (id, data) in self.def_data.iter() {
      if data.file != file {
        continue;
      }
      by_name_kind
        .entry((data.name.clone(), match_kind_from_def(&data.kind)))
        .or_default()
        .push((*id, data.clone()));
    }
    for defs in by_name_kind.values_mut() {
      defs.sort_by_key(|(_, data)| (data.span.start, data.span.end));
    }

    let mut new_def_data: HashMap<DefId, DefData> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file != file)
      .map(|(id, data)| (*id, data.clone()))
      .collect();
    let mut new_def_types: HashMap<DefId, TypeId> = self
      .def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_def_types: HashMap<DefId, tti::TypeId> = self
      .interned_def_types
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, ty)| (*id, *ty))
      .collect();
    let mut new_interned_type_params: HashMap<DefId, Vec<TypeParamId>> = self
      .interned_type_params
      .iter()
      .filter(|(id, _)| !file_def_ids.contains(id))
      .map(|(id, params)| (*id, params.clone()))
      .collect();
    let mut id_mapping: HashMap<DefId, DefId> = HashMap::new();

    let Some(file_state) = self.files.get(&file).cloned() else {
      return;
    };
    let mut resolved_defs = Vec::new();
    let mut bindings = file_state.bindings.clone();
    let mut exports = file_state.exports.clone();
    let reexports = file_state.reexports.clone();
    let export_all = file_state.export_all.clone();

    for def in lowered.defs.iter() {
      let name = lowered
        .names
        .resolve(def.name)
        .unwrap_or_default()
        .to_string();
      let match_kind = match_kind_from_hir(def.path.kind);
      let matched = by_name_kind
        .get_mut(&(name.clone(), match_kind))
        .and_then(|list| {
          if list.is_empty() {
            None
          } else {
            Some(list.remove(0))
          }
        });
      let (def_id, data) = if let Some((old_id, mut data)) = matched {
        id_mapping.insert(old_id, def.id);
        data.span = def.span;
        data.export = data.export || def.is_exported || def.is_default_export;
        match &mut data.kind {
          DefKind::Function(func) => func.body = def.body,
          DefKind::Var(var) => {
            if let Some(body) = def.body {
              var.body = body;
            }
          }
          DefKind::Class(class) => {
            class.body = def.body;
            class.declare |= def.is_ambient;
          }
          DefKind::Enum(en) => {
            en.body = def.body;
            en.declare |= def.is_ambient;
          }
          DefKind::Namespace(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          DefKind::Module(ns) => {
            if def.body.is_some() {
              ns.body = def.body;
            }
            ns.declare |= def.is_ambient;
          }
          _ => {}
        }
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(def.id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(def.id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(def.id, params);
        }
        (def.id, data)
      } else {
        let symbol = self.alloc_symbol();
        let kind = match match_kind {
          DefMatchKind::Function => DefKind::Function(FuncData {
            params: Vec::new(),
            return_ann: None,
            body: def.body,
          }),
          DefMatchKind::Class => DefKind::Class(ClassData {
            body: def.body,
            instance_type: None,
            static_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Enum => DefKind::Enum(EnumData {
            body: def.body,
            is_const: false,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Namespace => DefKind::Namespace(NamespaceData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Module => DefKind::Module(ModuleData {
            body: def.body,
            value_type: None,
            type_type: None,
            declare: def.is_ambient,
          }),
          DefMatchKind::Interface => DefKind::Interface(InterfaceData {
            typ: self.builtin.unknown,
          }),
          DefMatchKind::TypeAlias => DefKind::TypeAlias(TypeAliasData {
            typ: self.builtin.unknown,
          }),
          _ => DefKind::Var(VarData {
            typ: None,
            init: None,
            body: def.body.unwrap_or(BodyId(u32::MAX)),
            mode: VarDeclMode::Var,
          }),
        };
        let data = DefData {
          name: name.clone(),
          file,
          span: def.span,
          symbol,
          export: def.is_exported || def.is_default_export,
          kind,
        };
        self.record_def_symbol(def.id, symbol);
        self.record_symbol(file, def.span, symbol);
        (def.id, data)
      };

      bindings
        .entry(name.clone())
        .and_modify(|binding| {
          binding.symbol = data.symbol;
          binding.def = Some(def_id);
        })
        .or_insert(SymbolBinding {
          symbol: data.symbol,
          def: Some(def_id),
          type_id: None,
        });

      if data.export {
        let export_name = if def.is_default_export {
          "default".to_string()
        } else {
          name.clone()
        };
        exports.insert(
          export_name,
          ExportEntry {
            symbol: data.symbol,
            def: Some(def_id),
            type_id: new_def_types.get(&def_id).copied(),
          },
        );
      }

      new_def_data.insert(def_id, data);
      resolved_defs.push(def_id);
    }

    for leftovers in by_name_kind.values_mut() {
      for (old_id, data) in leftovers.drain(..) {
        new_def_data.insert(old_id, data.clone());
        if let Some(ty) = self.def_types.get(&old_id).copied() {
          new_def_types.insert(old_id, ty);
        }
        if let Some(ty) = self.interned_def_types.get(&old_id).copied() {
          new_interned_def_types.insert(old_id, ty);
        }
        if let Some(params) = self.interned_type_params.get(&old_id).cloned() {
          new_interned_type_params.insert(old_id, params);
        }
      }
    }

    for binding in bindings.values_mut() {
      if let Some(def) = binding.def {
        if let Some(mapped) = id_mapping.get(&def) {
          binding.def = Some(*mapped);
        }
      }
    }
    for entry in exports.values_mut() {
      if let Some(def) = entry.def {
        if let Some(mapped) = id_mapping.get(&def) {
          entry.def = Some(*mapped);
        }
      }
    }

    self.files.insert(
      file,
      FileState {
        defs: resolved_defs,
        exports,
        bindings,
        top_body: file_state.top_body,
        reexports,
        export_all,
      },
    );

    self.def_data = new_def_data;
    self.def_types = new_def_types;
    self.interned_def_types = new_interned_def_types;
    self.interned_type_params = new_interned_type_params;

    self.symbol_to_def.clear();
    for (def, data) in self.def_data.iter() {
      self.symbol_to_def.insert(data.symbol, *def);
    }
    self.next_def = self
      .def_data
      .keys()
      .map(|d| d.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);
  }

  fn map_hir_bodies(&mut self, file: FileId, lowered: &LowerResult) {
    let stale: HashSet<_> = self
      .body_map
      .iter()
      .filter(|(_, meta)| meta.file == file)
      .map(|(id, _)| *id)
      .collect();
    self.body_map.retain(|_, meta| meta.file != file);
    self.body_parents.retain(|child, _| !stale.contains(child));

    if let Some(state) = self.files.get_mut(&file) {
      state.top_body = Some(lowered.root_body());
    }

    let mut defs_by_span: HashMap<(TextRange, &'static str), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(String, &'static str), DefId> = HashMap::new();
    let mut file_defs: Vec<_> = self
      .def_data
      .iter()
      .filter(|(_, data)| data.file == file)
      .collect();
    file_defs.sort_by_key(|(id, data)| (data.span.start, data.span.end, id.0));
    for (def_id, data) in file_defs {
      let kind = match data.kind {
        DefKind::Function(_) => Some("fn"),
        DefKind::Var(_) => Some("var"),
        _ => None,
      };
      if let Some(kind) = kind {
        defs_by_span.entry((data.span, kind)).or_insert(*def_id);
        defs_by_name
          .entry((data.name.clone(), kind))
          .or_insert(*def_id);
      }
    }

    for (hir_body_id, idx) in lowered.body_index.iter() {
      let hir_body = lowered
        .bodies
        .get(*idx)
        .map(Arc::as_ref)
        .unwrap_or_else(|| panic!("missing lowered body for id {:?}", hir_body_id));

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Var(decl) = &stmt.kind {
          for declarator in decl.declarators.iter() {
            let pat_span = hir_body.pats.get(declarator.pat.0 as usize).map(|p| p.span);
            let def_id = pat_span
              .and_then(|span| defs_by_span.get(&(span, "var")).copied())
              .or_else(|| {
                hir_body
                  .pats
                  .get(declarator.pat.0 as usize)
                  .and_then(|pat| match &pat.kind {
                    hir_js::PatKind::Ident(name_id) => lowered
                      .names
                      .resolve(*name_id)
                      .and_then(|name| defs_by_name.get(&(name.to_string(), "var")).copied()),
                    _ => None,
                  })
              });
            if let Some(def_id) = def_id {
              if let Some(def) = self.def_data.get_mut(&def_id) {
                if let DefKind::Var(var) = &mut def.kind {
                  var.mode = match decl.kind {
                    hir_js::VarDeclKind::Var => VarDeclMode::Var,
                    hir_js::VarDeclKind::Let => VarDeclMode::Let,
                    hir_js::VarDeclKind::Const => VarDeclMode::Const,
                  };
                  let prefer = matches!(hir_body.kind, HirBodyKind::Initializer);
                  if var.body.0 == u32::MAX || prefer {
                    var.body = *hir_body_id;
                  }
                  if let Some(init) = declarator.init {
                    if var.init.is_none() || prefer {
                      var.init = Some(init);
                    }
                  }
                }
              }
            }
          }
        }
      }

      for stmt in hir_body.stmts.iter() {
        if let hir_js::StmtKind::Decl(def) = &stmt.kind {
          if let Some(hir_def) = lowered.def(*def) {
            if let Some(child) = hir_def.body {
              self.body_parents.insert(child, *hir_body_id);
            }
          }
        }
      }

      for expr in hir_body.exprs.iter() {
        match &expr.kind {
          HirExprKind::FunctionExpr { body, .. } | HirExprKind::ClassExpr { body, .. } => {
            self.body_parents.insert(*body, *hir_body_id);
          }
          _ => {}
        }
      }

      self.body_map.insert(
        *hir_body_id,
        BodyMeta {
          file,
          hir: Some(*hir_body_id),
          kind: hir_body.kind,
        },
      );
    }

    for export in lowered.hir.exports.iter() {
      if let HirExportKind::Default(default) = &export.kind {
        match &default.value {
          hir_js::ExportDefaultValue::Expr { expr, body } => {
            if let Some((_def_id, def)) = self
              .def_data
              .iter_mut()
              .find(|(_, data)| data.file == file && data.name == "default")
            {
              if let DefKind::Var(var) = &mut def.kind {
                var.body = *body;
                var.init = Some(*expr);
                var.mode = VarDeclMode::Const;
              }
              self.body_parents.insert(*body, lowered.root_body());
            }
          }
          hir_js::ExportDefaultValue::Class { def, body, .. }
          | hir_js::ExportDefaultValue::Function { def, body, .. } => {
            if let Some(data) = self.def_data.get_mut(def) {
              match &mut data.kind {
                DefKind::Function(func) => func.body = Some(*body),
                DefKind::Class(class) => class.body = Some(*body),
                _ => {}
              }
            }
            self.body_parents.insert(*body, lowered.root_body());
          }
        }
      }
    }

    self.next_body = self
      .body_map
      .keys()
      .map(|b| b.0)
      .max()
      .unwrap_or(0)
      .saturating_add(1);
  }

  fn ensure_body_map_from_defs(&mut self) {
    for (file, state) in self.files.iter() {
      if let Some(body) = state.top_body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: *file,
          hir: None,
          kind: HirBodyKind::Unknown,
        });
      }
    }
    for data in self.def_data.values() {
      let body = match &data.kind {
        DefKind::Function(func) => func.body,
        DefKind::Var(var) if var.body.0 != u32::MAX => Some(var.body),
        DefKind::Class(class) => class.body,
        DefKind::Enum(en) => en.body,
        DefKind::Namespace(ns) => ns.body,
        DefKind::Module(ns) => ns.body,
        _ => None,
      };
      if let Some(body) = body {
        self.body_map.entry(body).or_insert(BodyMeta {
          file: data.file,
          hir: None,
          kind: HirBodyKind::Unknown,
        });
      }
    }
  }

  fn push_semantic_diagnostics(&mut self, diags: Vec<Diagnostic>) {
    for mut diag in diags {
      if diag.code == "BIND1002" && diag.message.contains("unresolved import:") {
        if let Some(spec) = diag.message.split(':').nth(1).map(|s| s.trim()) {
          let has_ambient = self
            .semantics
            .as_ref()
            .and_then(|semantics| semantics.exports_of_ambient_module(spec))
            .map(|exports| !exports.is_empty())
            .unwrap_or(false);
          if has_ambient {
            continue;
          }
        }
      }
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
            if !spec.type_only {
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
            }
            let type_id = entry
              .type_id
              .or_else(|| entry.def.and_then(|d| self.def_types.get(&d).copied()));
            let mapped = ExportEntry {
              symbol: entry.symbol,
              def: None,
              type_id,
            };
            let mut update = true;
            if let Some(existing) = exports.get(&spec.alias) {
              if existing.symbol == mapped.symbol && existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
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
          for (name, entry) in target.exports.iter() {
            let mut is_type = false;
            if let Some(def) = entry.def {
              if let Some(def_data) = self.def_data.get(&def) {
                is_type = matches!(def_data.kind, DefKind::TypeAlias(_) | DefKind::Interface(_));
                if !spec.type_only && is_type {
                  continue;
                }
              }
            }
            if spec.type_only && !is_type {
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
            let mut update = true;
            if let Some(existing) = exports.get(name) {
              if existing.symbol == mapped.symbol && existing.def == mapped.def {
                update = mapped.type_id.is_some()
                  && (existing.type_id.is_none() || existing.type_id != mapped.type_id);
              } else {
                update = false;
              }
            }
            if update {
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
        }

        if let Some(existing) = self.files.get_mut(file) {
          existing.exports = exports;
        }
      }
    }
  }

  fn update_export_types(&mut self) -> Result<(), FatalError> {
    let mut updates: Vec<(FileId, String, DefId)> = Vec::new();
    for (file_id, state) in self.files.iter() {
      for (name, entry) in state.exports.iter() {
        if let Some(def) = entry.def {
          updates.push((*file_id, name.clone(), def));
        }
      }
    }
    for (file_id, name, def) in updates.into_iter() {
      if let Some(ty) = self.export_type_for_def(def)? {
        if let Some(state) = self.files.get_mut(&file_id) {
          if let Some(entry) = state.exports.get_mut(&name) {
            entry.type_id = Some(ty);
          }
        }
      }
    }
    Ok(())
  }

  fn export_type_for_def(&mut self, def: DefId) -> Result<Option<TypeId>, FatalError> {
    if let Some(store) = self.interned_store.clone() {
      let mut cache = HashMap::new();
      if let Some(merged) = self.callable_overload_type_for_def(def, &store, &mut cache) {
        return Ok(Some(merged));
      }
      if !self.def_types.contains_key(&def) {
        self.type_of_def(def)?;
      }
      if let Some(ty) = self.interned_def_types.get(&def).copied() {
        return Ok(Some(ty));
      }
      let Some(store_ty) = self.def_types.get(&def).copied() else {
        return Ok(None);
      };
      let interned = convert_type_for_display(store_ty, self, &store, &mut cache);
      let interned = store.canon(interned);
      self.interned_def_types.insert(def, interned);
      Ok(Some(interned))
    } else {
      Ok(self.def_types.get(&def).copied())
    }
  }

  fn queue_type_imports_in_stmt(
    &mut self,
    file: FileId,
    stmt: &Node<Stmt>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::TypeAliasDecl(alias) => {
        self.queue_type_imports_in_type_expr(file, &alias.stx.type_expr, host, queue);
      }
      Stmt::FunctionDecl(func) => {
        for param in func.stx.function.stx.parameters.iter() {
          if let Some(ann) = param.stx.type_annotation.as_ref() {
            self.queue_type_imports_in_type_expr(file, ann, host, queue);
          }
        }
        if let Some(ret) = func.stx.function.stx.return_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, ret, host, queue);
        }
        if let Some(body) = func.stx.function.stx.body.as_ref() {
          if let parse_js::ast::func::FuncBody::Block(block) = body {
            for stmt in block.iter() {
              self.queue_type_imports_in_stmt(file, stmt, host, queue);
            }
          }
        }
      }
      Stmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter() {
          if let Some(ann) = decl.type_annotation.as_ref() {
            self.queue_type_imports_in_type_expr(file, ann, host, queue);
          }
        }
      }
      Stmt::Block(block) => {
        for stmt in block.stx.body.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      Stmt::NamespaceDecl(ns) => {
        self.queue_type_imports_in_namespace_body(file, &ns.stx.body, host, queue);
      }
      Stmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          for stmt in body.iter() {
            self.queue_type_imports_in_stmt(file, stmt, host, queue);
          }
        }
      }
      Stmt::GlobalDecl(global) => {
        for stmt in global.stx.body.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      _ => {}
    }
  }

  fn queue_type_imports_in_namespace_body(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match body {
      NamespaceBody::Block(stmts) => {
        for stmt in stmts.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      NamespaceBody::Namespace(inner) => {
        self.queue_type_imports_in_namespace_body(file, &inner.stx.body, host, queue)
      }
    }
  }

  fn queue_type_imports_in_type_expr(
    &mut self,
    file: FileId,
    expr: &Node<TypeExpr>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match expr.stx.as_ref() {
      TypeExpr::ImportType(import) => {
        if let Some(target) =
          self.record_module_resolution(file, &import.stx.module_specifier, host)
        {
          queue.push_back(target);
        }
        if let Some(args) = import.stx.type_arguments.as_ref() {
          for arg in args {
            self.queue_type_imports_in_type_expr(file, arg, host, queue);
          }
        }
        if let Some(qualifier) = import.stx.qualifier.as_ref() {
          self.queue_type_imports_in_entity_name(file, qualifier, host, queue);
        }
      }
      TypeExpr::ArrayType(arr) => {
        self.queue_type_imports_in_type_expr(file, &arr.stx.element_type, host, queue);
      }
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter() {
          self.queue_type_imports_in_type_expr(file, &elem.stx.type_expr, host, queue);
        }
      }
      TypeExpr::UnionType(union) => {
        for ty in union.stx.types.iter() {
          self.queue_type_imports_in_type_expr(file, ty, host, queue);
        }
      }
      TypeExpr::IntersectionType(intersection) => {
        for ty in intersection.stx.types.iter() {
          self.queue_type_imports_in_type_expr(file, ty, host, queue);
        }
      }
      TypeExpr::FunctionType(func) => {
        for param in func.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        self.queue_type_imports_in_type_expr(file, &func.stx.return_type, host, queue);
        if let Some(params) = func.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
      }
      TypeExpr::ConstructorType(cons) => {
        for param in cons.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        self.queue_type_imports_in_type_expr(file, &cons.stx.return_type, host, queue);
        if let Some(params) = cons.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
      }
      TypeExpr::ObjectType(obj) => {
        for member in obj.stx.members.iter() {
          match member.stx.as_ref() {
            TypeMember::Property(prop) => {
              if let Some(ann) = prop.stx.type_annotation.as_ref() {
                self.queue_type_imports_in_type_expr(file, ann, host, queue);
              }
            }
            TypeMember::Method(method) => {
              for param in method.stx.parameters.iter() {
                self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
              }
              if let Some(ret) = method.stx.return_type.as_ref() {
                self.queue_type_imports_in_type_expr(file, ret, host, queue);
              }
              if let Some(params) = method.stx.type_parameters.as_ref() {
                for tp in params.iter() {
                  if let Some(constraint) = tp.stx.constraint.as_ref() {
                    self.queue_type_imports_in_type_expr(file, constraint, host, queue);
                  }
                  if let Some(default) = tp.stx.default.as_ref() {
                    self.queue_type_imports_in_type_expr(file, default, host, queue);
                  }
                }
              }
            }
            TypeMember::Constructor(cons) => {
              for param in cons.stx.parameters.iter() {
                self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
              }
              if let Some(ret) = cons.stx.return_type.as_ref() {
                self.queue_type_imports_in_type_expr(file, ret, host, queue);
              }
            }
            TypeMember::CallSignature(call) => {
              for param in call.stx.parameters.iter() {
                self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
              }
              if let Some(ret) = call.stx.return_type.as_ref() {
                self.queue_type_imports_in_type_expr(file, ret, host, queue);
              }
              if let Some(params) = call.stx.type_parameters.as_ref() {
                for tp in params.iter() {
                  if let Some(constraint) = tp.stx.constraint.as_ref() {
                    self.queue_type_imports_in_type_expr(file, constraint, host, queue);
                  }
                  if let Some(default) = tp.stx.default.as_ref() {
                    self.queue_type_imports_in_type_expr(file, default, host, queue);
                  }
                }
              }
            }
            TypeMember::IndexSignature(idx) => {
              self.queue_type_imports_in_type_expr(file, &idx.stx.parameter_type, host, queue);
              self.queue_type_imports_in_type_expr(file, &idx.stx.type_annotation, host, queue);
            }
            _ => {}
          }
        }
      }
      TypeExpr::ParenthesizedType(inner) => {
        self.queue_type_imports_in_type_expr(file, &inner.stx.type_expr, host, queue);
      }
      TypeExpr::KeyOfType(keyof) => {
        self.queue_type_imports_in_type_expr(file, &keyof.stx.type_expr, host, queue);
      }
      TypeExpr::IndexedAccessType(indexed) => {
        self.queue_type_imports_in_type_expr(file, &indexed.stx.object_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &indexed.stx.index_type, host, queue);
      }
      TypeExpr::ConditionalType(cond) => {
        self.queue_type_imports_in_type_expr(file, &cond.stx.check_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.extends_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.true_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.false_type, host, queue);
      }
      TypeExpr::MappedType(mapped) => {
        self.queue_type_imports_in_type_expr(file, &mapped.stx.constraint, host, queue);
        self.queue_type_imports_in_type_expr(file, &mapped.stx.type_expr, host, queue);
        if let Some(name_type) = mapped.stx.name_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, name_type, host, queue);
        }
      }
      TypeExpr::TemplateLiteralType(tpl) => {
        for span in tpl.stx.spans.iter() {
          self.queue_type_imports_in_type_expr(file, &span.stx.type_expr, host, queue);
        }
      }
      TypeExpr::TypePredicate(pred) => {
        if let Some(ann) = pred.stx.type_annotation.as_ref() {
          self.queue_type_imports_in_type_expr(file, ann, host, queue);
        }
      }
      TypeExpr::InferType(infer) => {
        if let Some(constraint) = infer.stx.constraint.as_ref() {
          self.queue_type_imports_in_type_expr(file, constraint, host, queue);
        }
      }
      TypeExpr::TypeReference(reference) => {
        if let Some(args) = reference.stx.type_arguments.as_ref() {
          for arg in args {
            self.queue_type_imports_in_type_expr(file, arg, host, queue);
          }
        }
      }
      TypeExpr::TypeQuery(query) => {
        self.queue_type_imports_in_entity_name(file, &query.stx.expr_name, host, queue);
      }
      _ => {}
    }
  }

  fn queue_type_imports_in_entity_name(
    &mut self,
    file: FileId,
    name: &TypeEntityName,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match name {
      TypeEntityName::Qualified(qualified) => {
        self.queue_type_imports_in_entity_name(file, &qualified.left, host, queue);
      }
      TypeEntityName::Import(_) => {}
      _ => {}
    }
  }

  fn bind_file(
    &mut self,
    file: FileId,
    ast: &Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) -> sem_ts::HirFile {
    let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
    let mut sem_builder = SemHirBuilder::new(file, sem_file_kind(file_kind));
    let mut defs = Vec::new();
    let mut exports: ExportMap = BTreeMap::new();
    let mut bindings: HashMap<String, SymbolBinding> = HashMap::new();
    let mut reexports = Vec::new();
    let mut export_all = Vec::new();

    for stmt in ast.stx.body.iter() {
      self.queue_type_imports_in_stmt(file, stmt, host, queue);
      match stmt.stx.as_ref() {
        Stmt::VarDecl(var) => {
          let var_span = loc_to_span(file, stmt.loc);
          let new_defs =
            self.handle_var_decl(file, var_span.range, var.stx.as_ref(), &mut sem_builder);
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
          if let Some((def_id, binding, export_name)) =
            self.handle_function_decl(file, span.range, func.stx.as_ref(), &mut sem_builder)
          {
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
          let mut object = self.object_type_from_members(&interface.stx.members);
          for base in interface.stx.extends.iter() {
            let base_ty = self.type_from_type_expr(base);
            if let TypeKind::Object(base_obj) = self.type_store.kind(base_ty).clone() {
              object = self.merge_object_types(object, base_obj);
            }
          }
          let mut typ = self.type_store.object(object);
          let existing_interface = bindings
            .get(&name)
            .and_then(|b| b.def)
            .and_then(|id| self.def_data.get(&id).map(|d| (id, d.clone())))
            .and_then(|(id, data)| match data.kind {
              DefKind::Interface(existing) => Some((id, data.symbol, existing.typ)),
              _ => None,
            });
          let (def_id, symbol) =
            if let Some((existing_id, symbol, existing_ty)) = existing_interface {
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
              (existing_id, symbol)
            } else {
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: name.clone(),
                  file,
                  span: span.range,
                  symbol,
                  export: interface.stx.export,
                  kind: DefKind::Interface(InterfaceData { typ }),
                },
              );
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
          self.record_symbol(file, span.range, symbol);
        }
        Stmt::TypeAliasDecl(alias) => {
          let span = loc_to_span(file, stmt.loc);
          let name = alias.stx.name.clone();
          let mut ty = self.type_from_type_expr(&alias.stx.type_expr);
          if ty == self.builtin.unknown {
            ty = self.type_store.literal_string(name.clone());
          }
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
          let def_id = self.alloc_def();
          let symbol = self.alloc_symbol();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: alias.stx.export,
              kind: DefKind::TypeAlias(TypeAliasData { typ: ty }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.def_types.insert(def_id, ty);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(ty),
            },
          );
          defs.push(def_id);
          self.record_symbol(file, span.range, symbol);
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
        Stmt::NamespaceDecl(ns) => {
          let span = loc_to_span(file, stmt.loc);
          let name = ns.stx.name.clone();
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: ns.stx.export,
              kind: DefKind::Namespace(NamespaceData {
                body: None,
                value_type: None,
                type_type: None,
                declare: ns.stx.declare,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if ns.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
          }
        }
        Stmt::ModuleDecl(module) => {
          if matches!(
            module.stx.name,
            parse_js::ast::ts_stmt::ModuleName::String(_)
          ) {
            self.bind_ambient_module(file, module, &mut sem_builder, &mut defs);
          }
          let span = loc_to_span(file, stmt.loc);
          let name = match &module.stx.name {
            parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.clone(),
            parse_js::ast::ts_stmt::ModuleName::String(s) => s.clone(),
          };
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: module.stx.export,
              kind: DefKind::Module(ModuleData {
                body: None,
                value_type: None,
                type_type: None,
                declare: module.stx.declare,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if module.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
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
            .and_then(|module| self.record_module_resolution(file, module, host));
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
          let resolved = self.record_module_resolution(file, &module, host);
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          let import_target =
            resolved
              .map(ImportTarget::File)
              .unwrap_or_else(|| ImportTarget::Unresolved {
                specifier: module.clone(),
              });
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
                  target: import_target.clone(),
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
            self.record_symbol(file, loc_to_span(file, default_pat.loc).range, symbol);
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
                      target: import_target.clone(),
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
                self.record_symbol(file, loc_to_span(file, alias_pat.loc).range, symbol);
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
                    target: import_target.clone(),
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
              self.record_symbol(file, loc_to_span(file, pat.loc).range, symbol);
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
        Stmt::ImportEqualsDecl(import_equals) => match &import_equals.stx.rhs {
          ImportEqualsRhs::Require { module } => {
            let resolved = self
              .file_key_for_id(file)
              .and_then(|file_key| host.resolve(&file_key, module))
              .map(|target| self.intern_file_key(target, FileOrigin::Source));
            if let Some(target) = resolved {
              queue.push_back(target);
            }
            let import_target =
              resolved
                .map(ImportTarget::File)
                .unwrap_or_else(|| ImportTarget::Unresolved {
                  specifier: module.clone(),
                });
            let span = loc_to_span(file, stmt.loc).range;
            let name = import_equals.stx.name.clone();
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span,
                symbol,
                export: import_equals.stx.export,
                kind: DefKind::Import(ImportData {
                  target: import_target.clone(),
                  original: "*".to_string(),
                }),
              },
            );
            self.record_def_symbol(def_id, symbol);
            defs.push(def_id);
            bindings.insert(
              name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            self.record_symbol(file, span, symbol);
            if import_equals.stx.export {
              exports.insert(
                name.clone(),
                ExportEntry {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
            }
            sem_builder.add_import(sem_ts::Import {
              specifier: module.clone(),
              specifier_span: span,
              default: None,
              namespace: Some(sem_ts::ImportNamespace {
                local: name,
                local_span: span,
                is_type_only: false,
              }),
              named: Vec::new(),
              is_type_only: false,
            });
          }
          ImportEqualsRhs::EntityName { .. } => {
            self
              .diagnostics
              .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                "import = aliasing non-module targets is not supported yet",
                loc_to_span(file, stmt.loc),
              ));
          }
        },
        Stmt::Expr(_) | Stmt::If(_) | Stmt::Block(_) | Stmt::While(_) => {}
        _ => {}
      }
    }

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
    sem_builder.finish()
  }

  fn bind_ambient_module(
    &mut self,
    file: FileId,
    module: &Node<parse_js::ast::ts_stmt::ModuleDecl>,
    builder: &mut SemHirBuilder,
    defs: &mut Vec<DefId>,
  ) {
    let Some(body) = module.stx.body.as_ref() else {
      return;
    };
    let name_span = loc_to_span(file, module.loc).range;
    let name = match &module.stx.name {
      parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.clone(),
      parse_js::ast::ts_stmt::ModuleName::String(specifier) => specifier.clone(),
    };
    let mut module_builder = SemHirBuilder::new_ambient(file, builder.file_kind);
    let mut bindings = HashMap::new();
    for stmt in body.iter() {
      self.bind_ambient_stmt(file, stmt, &mut module_builder, &mut bindings, defs);
    }
    builder.add_ambient_module(module_builder.into_ambient(name, name_span));
  }

  fn bind_ambient_stmt(
    &mut self,
    file: FileId,
    stmt: &Node<Stmt>,
    builder: &mut SemHirBuilder,
    bindings: &mut HashMap<String, SymbolBinding>,
    defs: &mut Vec<DefId>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::VarDecl(var) => {
        let var_span = loc_to_span(file, stmt.loc);
        let new_defs = self.handle_var_decl(file, var_span.range, var.stx.as_ref(), builder);
        for (def_id, binding, _export_name) in new_defs {
          defs.push(def_id);
          let (name, value) = binding;
          bindings.insert(name, value);
        }
      }
      Stmt::FunctionDecl(func) => {
        let span = loc_to_span(file, stmt.loc);
        if let Some((def_id, binding, _export_name)) =
          self.handle_function_decl(file, span.range, func.stx.as_ref(), builder)
        {
          defs.push(def_id);
          let (name, value) = binding;
          bindings.insert(name, value);
        }
      }
      Stmt::InterfaceDecl(interface) => {
        let span = loc_to_span(file, stmt.loc);
        let name = interface.stx.name.clone();
        let mut object = self.object_type_from_members(&interface.stx.members);
        for base in interface.stx.extends.iter() {
          let base_ty = self.type_from_type_expr(base);
          if let TypeKind::Object(base_obj) = self.type_store.kind(base_ty).clone() {
            object = self.merge_object_types(object, base_obj);
          }
        }
        let mut typ = self.type_store.object(object);
        let existing_interface = bindings
          .get(&name)
          .and_then(|b| b.def)
          .and_then(|id| self.def_data.get(&id).map(|d| (id, d.clone())))
          .and_then(|(id, data)| match data.kind {
            DefKind::Interface(existing) => Some((id, data.symbol, existing.typ)),
            _ => None,
          });
        let (def_id, symbol) = if let Some((existing_id, symbol, existing_ty)) = existing_interface
        {
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
          (existing_id, symbol)
        } else {
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: interface.stx.export,
              kind: DefKind::Interface(InterfaceData { typ }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          defs.push(def_id);
          builder.add_decl(
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

        self.def_types.insert(def_id, typ);
        self.record_symbol(file, span.range, symbol);
      }
      Stmt::TypeAliasDecl(alias) => {
        let span = loc_to_span(file, stmt.loc);
        let name = alias.stx.name.clone();
        let mut ty = self.type_from_type_expr(&alias.stx.type_expr);
        if ty == self.builtin.unknown {
          ty = self.type_store.literal_string(name.clone());
        }
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
        let def_id = self.alloc_def();
        let symbol = self.alloc_symbol();
        self.def_data.insert(
          def_id,
          DefData {
            name: name.clone(),
            file,
            span: span.range,
            symbol,
            export: alias.stx.export,
            kind: DefKind::TypeAlias(TypeAliasData { typ: ty }),
          },
        );
        self.record_def_symbol(def_id, symbol);
        self.def_types.insert(def_id, ty);
        bindings.insert(
          name.clone(),
          SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: Some(ty),
          },
        );
        defs.push(def_id);
        self.record_symbol(file, span.range, symbol);
        builder.add_decl(
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
      }
      Stmt::NamespaceDecl(ns) => {
        self.bind_ambient_namespace_body(file, &ns.stx.body, builder, bindings, defs);
      }
      Stmt::ModuleDecl(module) => {
        if matches!(
          module.stx.name,
          parse_js::ast::ts_stmt::ModuleName::String(_)
        ) {
          self.bind_ambient_module(file, module, builder, defs);
        }
      }
      _ => {}
    }
  }

  fn bind_ambient_namespace_body(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    builder: &mut SemHirBuilder,
    bindings: &mut HashMap<String, SymbolBinding>,
    defs: &mut Vec<DefId>,
  ) {
    match body {
      NamespaceBody::Block(stmts) => {
        for stmt in stmts.iter() {
          self.bind_ambient_stmt(file, stmt, builder, bindings, defs);
        }
      }
      NamespaceBody::Namespace(inner) => {
        self.bind_ambient_namespace_body(file, &inner.stx.body, builder, bindings, defs)
      }
    }
  }

  fn handle_var_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    var: &VarDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Vec<(DefId, (String, SymbolBinding), Option<String>)> {
    let mut defs = Vec::new();
    for declarator in var.declarators.iter() {
      let pat = &declarator.pattern;
      let name = match pat.stx.pat.stx.as_ref() {
        Pat::Id(id) => id.stx.name.clone(),
        _ => {
          self.diagnostics.push(
            codes::UNSUPPORTED_PATTERN.error("unsupported pattern", loc_to_span(file, pat.loc)),
          );
          continue;
        }
      };
      let type_ann = declarator
        .type_annotation
        .as_ref()
        .map(|t| self.type_from_type_expr(t));
      let symbol = self.alloc_symbol();
      let def_id = self.alloc_def();
      self.record_symbol(file, loc_to_span(file, pat.loc).range, symbol);
      self.def_data.insert(
        def_id,
        DefData {
          name: name.clone(),
          file,
          span,
          symbol,
          export: var.export,
          kind: DefKind::Var(VarData {
            typ: type_ann,
            init: None,
            body: BodyId(u32::MAX),
            mode: var.mode,
          }),
        },
      );
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
        loc_to_span(file, pat.loc).range,
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
  ) -> Option<(DefId, (String, SymbolBinding), Option<String>)> {
    let name_node = func.name.as_ref()?;
    let name = name_node.stx.name.clone();
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, name_node.loc).range, symbol);
    let def_id = self.alloc_def();
    let func_data = self.lower_function(file, func.function.stx.as_ref(), def_id);
    self.def_data.insert(
      def_id,
      DefData {
        name: name.clone(),
        file,
        span,
        symbol,
        export: func.export || func.export_default,
        kind: DefKind::Function(func_data),
      },
    );
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
      loc_to_span(file, name_node.loc).range,
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

  fn lower_function(&mut self, file: FileId, func: &Func, _def: DefId) -> FuncData {
    let mut params = Vec::new();
    for param in func.parameters.iter() {
      if let Some(data) = self.lower_param(file, param) {
        params.push(data);
      }
    }
    let return_ann = func
      .return_type
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    FuncData {
      params,
      return_ann,
      body: None,
    }
  }

  fn lower_param(&mut self, file: FileId, param: &Node<ParamDecl>) -> Option<ParamData> {
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
      .map(|t| self.type_from_type_expr(t));
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, param.stx.pattern.loc).range, symbol);
    Some(ParamData {
      name,
      typ,
      symbol,
      pat: None,
    })
  }

  fn collect_parent_bindings(
    &mut self,
    body_id: BodyId,
    bindings: &mut HashMap<String, TypeId>,
    binding_defs: &mut HashMap<String, DefId>,
  ) -> Result<(), FatalError> {
    self.check_cancelled()?;
    fn record_pat(
      state: &ProgramState,
      pat_id: HirPatId,
      body: &hir_js::Body,
      names: &hir_js::NameInterner,
      result: &BodyCheckResult,
      bindings: &mut HashMap<String, TypeId>,
      binding_defs: &mut HashMap<String, DefId>,
      file: FileId,
    ) {
      let Some(pat) = body.pats.get(pat_id.0 as usize) else {
        return;
      };
      let ty = result
        .pat_type(PatId(pat_id.0))
        .unwrap_or(state.builtin.unknown);
      match &pat.kind {
        HirPatKind::Ident(name_id) => {
          if let Some(name) = names.resolve(*name_id) {
            if ty != state.builtin.unknown {
              bindings
                .entry(name.to_string())
                .and_modify(|existing| {
                  if let Some(store) = state.interned_store.as_ref() {
                    if matches!(store.type_kind(*existing), tti::TypeKind::Unknown) {
                      *existing = ty;
                    }
                  }
                })
                .or_insert(ty);
            }
            if let Some(def_id) = state
              .def_data
              .iter()
              .find_map(|(id, data)| (data.file == file && data.span == pat.span).then_some(*id))
            {
              binding_defs.entry(name.to_string()).or_insert(def_id);
            }
          }
        }
        HirPatKind::Array(arr) => {
          for elem in arr.elements.iter().flatten() {
            record_pat(
              state,
              elem.pat,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
          if let Some(rest) = arr.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
        }
        HirPatKind::Object(obj) => {
          for prop in obj.props.iter() {
            record_pat(
              state,
              prop.value,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
          if let Some(rest) = obj.rest {
            record_pat(
              state,
              rest,
              body,
              names,
              result,
              bindings,
              binding_defs,
              file,
            );
          }
        }
        HirPatKind::Rest(inner) => {
          record_pat(
            state,
            **inner,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
          );
        }
        HirPatKind::Assign { target, .. } => {
          record_pat(
            state,
            *target,
            body,
            names,
            result,
            bindings,
            binding_defs,
            file,
          );
        }
        HirPatKind::AssignTarget(_) => {}
      }
    }

    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      self.check_cancelled()?;
      if !visited.insert(parent) {
        break;
      }
      let parent_result = self.check_body(parent)?;
      let Some(meta) = self.body_map.get(&parent).copied() else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(hir_body_id) = meta.hir else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(body) = lowered.body(hir_body_id) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      for pat in body.pats.iter().enumerate() {
        record_pat(
          self,
          HirPatId(pat.0 as u32),
          body,
          &lowered.names,
          &parent_result,
          bindings,
          binding_defs,
          meta.file,
        );
      }
      current = self.body_parents.get(&parent).copied();
    }
    Ok(())
  }

  fn build_type_resolver(
    &self,
    binding_defs: &HashMap<String, DefId>,
  ) -> Option<Arc<dyn TypeResolver>> {
    if binding_defs.is_empty() {
      return None;
    }
    if let Some(semantics) = self.semantics.as_ref() {
      let def_kinds = self
        .def_data
        .iter()
        .map(|(id, data)| (*id, data.kind.clone()))
        .collect();
      return Some(Arc::new(ProgramTypeResolver::new(
        Arc::clone(&self.host),
        Arc::clone(semantics),
        def_kinds,
        self.file_registry.clone(),
        self.current_file.unwrap_or(FileId(u32::MAX)),
        binding_defs.clone(),
      )) as Arc<_>);
    }
    Some(Arc::new(check::hir_body::BindingTypeResolver::new(
      binding_defs.clone(),
    )) as Arc<_>)
  }

  fn function_expr_span(&self, body_id: BodyId) -> Option<TextRange> {
    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let Some(meta) = self.body_map.get(&parent) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(hir_body_id) = meta.hir else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(lowered) = self.hir_lowered.get(&meta.file) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      let Some(parent_body) = lowered.body(hir_body_id) else {
        current = self.body_parents.get(&parent).copied();
        continue;
      };
      for expr in parent_body.exprs.iter() {
        if let HirExprKind::FunctionExpr { body, .. } = expr.kind {
          if body == body_id {
            return Some(expr.span);
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    None
  }

  fn contextual_callable_for_body(
    &mut self,
    body_id: BodyId,
    func_span: TextRange,
    store: &Arc<tti::TypeStore>,
  ) -> Result<Option<TypeId>, FatalError> {
    let mut visited = HashSet::new();
    let mut current = self.body_parents.get(&body_id).copied();
    while let Some(parent) = current {
      if !visited.insert(parent) {
        break;
      }
      let parent_result = self.check_body(parent)?;
      for (idx, span) in parent_result.expr_spans.iter().enumerate() {
        if *span != func_span {
          continue;
        }
        if let Some(ty) = parent_result.expr_types.get(idx).copied() {
          if store.contains_type_id(ty)
            && matches!(store.type_kind(ty), tti::TypeKind::Callable { .. })
          {
            return Ok(Some(ty));
          }
        }
      }
      current = self.body_parents.get(&parent).copied();
    }
    Ok(None)
  }

  fn check_body(&mut self, body_id: BodyId) -> Result<Arc<BodyCheckResult>, FatalError> {
    self.check_cancelled()?;
    let _parallel_guard = db::queries::body_check::parallel_guard();
    let cache_hit = self.body_results.contains_key(&body_id);
    let body_meta = self.body_map.get(&body_id).copied();
    let owner = self.owner_of_body(body_id);
    let prev_file = self.current_file;
    if let Some(meta) = body_meta.as_ref() {
      self.current_file = Some(meta.file);
    }
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
    if let Some(existing) = self.body_results.get(&body_id).cloned() {
      self
        .typecheck_db
        .set_body_result(body_id, Arc::clone(&existing));
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Ok(existing);
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
      self.typecheck_db.set_body_result(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Ok(res);
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
      self.typecheck_db.set_body_result(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Ok(res);
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
      self.typecheck_db.set_body_result(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return Ok(res);
    };

    let mut _synthetic = None;
    let body = if let Some(hir_id) = meta.hir {
      lowered.body(hir_id)
    } else if matches!(meta.kind, HirBodyKind::TopLevel) {
      _synthetic = Some(hir_js::Body {
        owner: HirDefId(u32::MAX),
        kind: HirBodyKind::TopLevel,
        exprs: Vec::new(),
        stmts: Vec::new(),
        pats: Vec::new(),
        root_stmts: Vec::new(),
        function: None,
        expr_types: None,
      });
      _synthetic.as_ref()
    } else {
      None
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
      self.typecheck_db.set_body_result(body_id, res.clone());
      if let Some(span) = span.take() {
        span.finish(None);
      }
      return Ok(res);
    };

    if let Err(err) = self.check_cancelled() {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Err(err);
    }

    let store = match self.interned_store.as_ref() {
      Some(store) => Arc::clone(store),
      None => {
        let store = tti::TypeStore::with_options((&self.compiler_options).into());
        self.interned_store = Some(Arc::clone(&store));
        store
      }
    };

    let mut bindings: HashMap<String, TypeId> = HashMap::new();
    let mut binding_defs: HashMap<String, DefId> = HashMap::new();
    let mut convert_cache = HashMap::new();
    let map_def_ty = |state: &ProgramState,
                      store: &Arc<tti::TypeStore>,
                      cache: &mut HashMap<TypeId, tti::TypeId>,
                      def: DefId| {
      state.interned_def_types.get(&def).copied().or_else(|| {
        state
          .def_types
          .get(&def)
          .copied()
          .map(|ty| store.canon(convert_type_for_display(ty, state, store, cache)))
      })
    };
    let global_binding_entries: Vec<_> = self
      .global_bindings
      .iter()
      .map(|(name, binding)| (name.clone(), binding.clone()))
      .collect();
    let file_binding_entries: Option<Vec<_>> = self.files.get(&file).map(|state| {
      state
        .bindings
        .iter()
        .map(|(name, binding)| (name.clone(), binding.clone()))
        .collect()
    });
    let mut bind = |name: &str, binding: &SymbolBinding| {
      let mut def_for_resolver = binding.def;
      let mut ty = None;
      if let Some(def) = binding.def {
        if let Some(defs) = self.callable_overload_defs(def) {
          if let Some(first) = defs.first().copied() {
            def_for_resolver = Some(first);
          }
          if defs.len() > 1 {
            if let Some(merged) =
              self.callable_overload_type_for_def(def, &store, &mut convert_cache)
            {
              ty = Some(merged);
            }
          }
        }
        if ty.is_none() {
          ty = map_def_ty(self, &store, &mut convert_cache, def);
        }
      }
      let ty = ty.unwrap_or_else(|| store.primitive_ids().unknown);
      bindings.insert(name.to_string(), ty);
      if let Some(def) = def_for_resolver {
        binding_defs.insert(name.to_string(), def);
      }
    };
    for (name, binding) in global_binding_entries.into_iter() {
      bind(&name, &binding);
    }
    if let Some(bindings) = file_binding_entries {
      for (name, binding) in bindings.into_iter() {
        bind(&name, &binding);
      }
    }

    if let Err(err) = self.collect_parent_bindings(body_id, &mut bindings, &mut binding_defs) {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Err(err);
    }

    if let Err(err) = self.check_cancelled() {
      if let Some(span) = span.take() {
        span.finish(None);
      }
      self.current_file = prev_file;
      return Err(err);
    }

    let contextual_fn_ty = if matches!(meta.kind, HirBodyKind::Function) {
      if let Some(func_span) = self.function_expr_span(body_id) {
        self.contextual_callable_for_body(body_id, func_span, &store)?
      } else {
        None
      }
    } else {
      None
    };

    let caches = self.checker_caches.for_body();
    let expander = RefExpander::new(
      Arc::clone(&store),
      &self.interned_def_types,
      &self.interned_type_params,
      caches.eval.clone(),
    );
    let prim = store.primitive_ids();
    let semantic_resolver = self.build_type_resolver(&binding_defs);
    let resolver = if let Some(semantics) = self.semantics.as_ref() {
      let def_kinds = self
        .def_data
        .iter()
        .map(|(id, data)| (*id, data.kind.clone()))
        .collect();
      Some(Arc::new(ProgramTypeResolver::new(
        Arc::clone(&self.host),
        Arc::clone(semantics),
        def_kinds,
        self.file_registry.clone(),
        file,
        binding_defs.clone(),
      )) as Arc<_>)
    } else if !binding_defs.is_empty() {
      Some(Arc::new(check::hir_body::BindingTypeResolver::new(
        binding_defs.clone(),
      )) as Arc<_>)
    } else {
      None
    };
    let resolver = semantic_resolver.or(resolver);
    let mut result = check::hir_body::check_body_with_expander(
      body_id,
      body,
      &lowered.names,
      file,
      ast.as_ref(),
      Arc::clone(&store),
      &caches,
      &bindings,
      resolver,
      Some(&expander),
      contextual_fn_ty,
    );
    if !body.exprs.is_empty() {
      let mut initial_env: HashMap<NameId, TypeId> = HashMap::new();
      if matches!(meta.kind, HirBodyKind::Function) {
        if let Some(function) = body.function.as_ref() {
          for param in function.params.iter() {
            if let Some(ty) = result.pat_types.get(param.pat.0 as usize).copied() {
              if ty != prim.unknown {
                if let Some(pat) = body.pats.get(param.pat.0 as usize) {
                  if let hir_js::PatKind::Ident(name) = pat.kind {
                    initial_env.insert(name, ty);
                  }
                }
              }
            }
          }
        }
      }
      let local_semantics = self.local_semantics.get(&file);
      let flow_bindings = local_semantics.map(|locals| FlowBindings::new(body, locals));
      for (idx, expr) in body.exprs.iter().enumerate() {
        if let hir_js::ExprKind::Ident(name_id) = expr.kind {
          if initial_env.contains_key(&name_id) {
            continue;
          }
          let Some(locals) = local_semantics else {
            continue;
          };
          let Some(binding_id) = locals.resolve_expr(body, hir_js::ExprId(idx as u32)) else {
            continue;
          };
          let symbol = locals.symbol(binding_id);
          if symbol.decl_scope != locals.root_scope() {
            continue;
          }
          if let Some(name) = lowered.names.resolve(name_id) {
            if let Some(ty) = bindings.get(name) {
              initial_env.insert(name_id, *ty);
            }
          }
        }
      }
      let mut flow_hooks = relate_hooks();
      flow_hooks.expander = Some(&expander);
      let flow_relate = RelateCtx::with_hooks_and_cache(
        Arc::clone(&store),
        store.options(),
        flow_hooks,
        caches.relation.clone(),
      );
      let flow_result = check::hir_body::check_body_with_env_with_bindings(
        body_id,
        body,
        &lowered.names,
        file,
        "",
        Arc::clone(&store),
        &initial_env,
        flow_bindings.as_ref(),
        flow_relate,
        Some(&expander),
      );
      let mut relate_hooks = relate_hooks();
      relate_hooks.expander = Some(&expander);
      let relate = RelateCtx::with_hooks_and_cache(
        Arc::clone(&store),
        store.options(),
        relate_hooks,
        caches.relation.clone(),
      );
      let widen_literal = |ty: TypeId| match store.type_kind(ty) {
        tti::TypeKind::NumberLiteral(_) => prim.number,
        tti::TypeKind::StringLiteral(_) => prim.string,
        tti::TypeKind::BooleanLiteral(_) => prim.boolean,
        _ => ty,
      };
      if flow_result.expr_types.len() == result.expr_types.len() {
        for (idx, ty) in flow_result.expr_types.iter().enumerate() {
          if *ty != prim.unknown {
            let existing = result.expr_types[idx];
            let narrower =
              relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
            if existing == prim.unknown || narrower {
              result.expr_types[idx] = *ty;
            }
          }
        }
      }
      if flow_result.pat_types.len() == result.pat_types.len() {
        for (idx, ty) in flow_result.pat_types.iter().enumerate() {
          if *ty != prim.unknown {
            let existing = result.pat_types[idx];
            let narrower =
              relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
            if existing == prim.unknown || narrower {
              result.pat_types[idx] = *ty;
            }
          }
        }
      }
      let flow_return_types: Vec<_> = flow_result
        .return_types
        .into_iter()
        .map(widen_literal)
        .collect();
      if result.return_types.is_empty() && !flow_return_types.is_empty() {
        result.return_types = flow_return_types;
      } else if flow_return_types.len() == result.return_types.len() {
        for (idx, ty) in flow_return_types.iter().enumerate() {
          if *ty != prim.unknown {
            let existing = result.return_types[idx];
            let narrower =
              relate.is_assignable(*ty, existing) && !relate.is_assignable(existing, *ty);
            if existing == prim.unknown || narrower {
              result.return_types[idx] = *ty;
            }
          }
        }
      }
      if !result.return_types.is_empty() {
        result.return_types = result
          .return_types
          .iter()
          .map(|ty| widen_literal(*ty))
          .collect();
      }
      let mut flow_diagnostics = flow_result.diagnostics;
      if !flow_diagnostics.is_empty() {
        let mut seen: HashSet<(String, FileId, TextRange, String)> = HashSet::new();
        let diag_key = |diag: &Diagnostic| -> (String, FileId, TextRange, String) {
          (
            diag.code.as_str().to_string(),
            diag.primary.file,
            diag.primary.range,
            diag.message.clone(),
          )
        };
        for diag in result.diagnostics.iter() {
          seen.insert(diag_key(diag));
        }
        flow_diagnostics.sort_by(|a, b| {
          a.primary
            .file
            .cmp(&b.primary.file)
            .then(a.primary.range.start.cmp(&b.primary.range.start))
            .then(a.primary.range.end.cmp(&b.primary.range.end))
            .then(a.code.cmp(&b.code))
            .then(a.message.cmp(&b.message))
        });
        for diag in flow_diagnostics.into_iter() {
          if seen.insert(diag_key(&diag)) {
            result.diagnostics.push(diag);
          }
        }
      }
    }
    for (idx, expr) in body.exprs.iter().enumerate() {
      if result.expr_types.get(idx) == Some(&prim.unknown) {
        if let hir_js::ExprKind::Ident(name_id) = expr.kind {
          if let Some(name) = lowered.names.resolve(name_id) {
            if let Some(mut ty) = bindings.get(name).copied() {
              if ty == prim.unknown {
                if let Some(def) = binding_defs.get(name) {
                  if let Some(mapped) = map_def_ty(self, &store, &mut convert_cache, *def) {
                    ty = mapped;
                  }
                }
              }
              result.expr_types[idx] = ty;
            }
          }
        }
      }
      if let Err(err) = self.check_cancelled() {
        if let Some(span) = span.take() {
          span.finish(None);
        }
        self.current_file = prev_file;
        return Err(err);
      }
    }
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
    self.typecheck_db.set_body_result(body_id, res.clone());
    if let Some(span) = span.take() {
      span.finish(None);
    }
    self.current_file = prev_file;
    Ok(res)
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
      InternedKind::Predicate {
        parameter,
        asserted,
        asserts,
      } => {
        let param = parameter.map(|id| store.name(id)).unwrap_or_default();
        let asserted = asserted.map(|ty| self.import_interned_type(ty));
        self.type_store.predicate(param, asserted, asserts)
      }
      _ => self.builtin.unknown,
    }
  }

  fn ensure_interned_type(&mut self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    if store.contains_type_id(ty) {
      return store.canon(ty);
    }
    if let Some(mapped) = self.def_types.iter().find_map(|(def, stored_ty)| {
      if *stored_ty == ty {
        self.interned_def_types.get(def).copied()
      } else {
        None
      }
    }) {
      return store.canon(mapped);
    }
    let mut cache = HashMap::new();
    let interned = convert_type_for_display(ty, self, store, &mut cache);
    store.canon(interned)
  }

  fn prefer_named_refs(&self, ty: TypeId) -> TypeId {
    let Some(store) = self.interned_store.as_ref() else {
      return ty;
    };
    self.prefer_named_refs_in_store(store, ty)
  }

  fn prefer_named_refs_in_store(&self, store: &Arc<tti::TypeStore>, ty: TypeId) -> TypeId {
    let canonical = store.canon(ty);
    if let Some(def) = self
      .interned_def_types
      .iter()
      .find_map(|(def, def_ty)| (store.canon(*def_ty) == canonical).then_some(*def))
    {
      return store.intern_type(tti::TypeKind::Ref {
        def,
        args: Vec::new(),
      });
    }
    match store.type_kind(canonical) {
      tti::TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.union(mapped);
      }
      tti::TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|member| self.prefer_named_refs_in_store(store, member))
          .collect();
        return store.intersection(mapped);
      }
      tti::TypeKind::Array { ty, readonly } => {
        let mapped = self.prefer_named_refs_in_store(store, ty);
        if mapped != ty {
          return store.intern_type(tti::TypeKind::Array {
            ty: mapped,
            readonly,
          });
        }
      }
      tti::TypeKind::Tuple(elems) => {
        let mut changed = false;
        let mapped: Vec<_> = elems
          .into_iter()
          .map(|elem| {
            let mapped = self.prefer_named_refs_in_store(store, elem.ty);
            changed |= mapped != elem.ty;
            tti::TupleElem {
              ty: mapped,
              optional: elem.optional,
              rest: elem.rest,
              readonly: elem.readonly,
            }
          })
          .collect();
        if changed {
          return store.intern_type(tti::TypeKind::Tuple(mapped));
        }
      }
      _ => {}
    }
    canonical
  }

  fn widen_literal(&self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      _ => ty,
    }
  }

  fn widen_literal_any(&self, ty: TypeId) -> TypeId {
    let widened = self.widen_literal(ty);
    if widened != ty {
      return widened;
    }
    if let Some(store) = self.interned_store.as_ref() {
      if store.contains_type_id(ty) {
        return match store.type_kind(ty) {
          tti::TypeKind::NumberLiteral(_) => self.builtin.number,
          tti::TypeKind::StringLiteral(_) => self.builtin.string,
          tti::TypeKind::BooleanLiteral(_) => self.builtin.boolean,
          _ => ty,
        };
      }
    }
    ty
  }

  fn widen_union_literals(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      TypeKind::Union(types) => {
        let members: Vec<_> = types
          .into_iter()
          .map(|t| self.widen_union_literals(t))
          .collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(inner);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  fn widen_array_elements(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::Array(inner) => {
        let widened = self.widen_union_literals(*inner);
        self.type_store.array(widened)
      }
      _ => ty,
    }
  }

  fn widen_object_literal(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::Object(mut obj) => {
        let mut changed = false;
        for prop in obj.props.values_mut() {
          if prop.readonly {
            continue;
          }
          let widened = self.widen_union_literals(prop.typ);
          if widened != prop.typ {
            prop.typ = widened;
            changed = true;
          }
        }
        if let Some(value) = obj.string_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.string_index = Some(widened);
            changed = true;
          }
        }
        if let Some(value) = obj.number_index {
          let widened = self.widen_union_literals(value);
          if widened != value {
            obj.number_index = Some(widened);
            changed = true;
          }
        }
        if changed {
          self.type_store.object(obj)
        } else {
          ty
        }
      }
      _ => ty,
    }
  }

  fn init_is_satisfies(&self, body: BodyId, expr: ExprId) -> bool {
    let meta = match self.body_map.get(&body) {
      Some(meta) => meta,
      None => return false,
    };
    let hir_id = match meta.hir {
      Some(id) => id,
      None => return false,
    };
    let lowered = match self.hir_lowered.get(&meta.file) {
      Some(lowered) => lowered,
      None => return false,
    };
    let hir_body = match lowered.body(hir_id) {
      Some(body) => body,
      None => return false,
    };
    hir_body
      .exprs
      .get(expr.0 as usize)
      .map(|e| matches!(e.kind, HirExprKind::Satisfies { .. }))
      .unwrap_or(false)
  }

  fn var_initializer(&self, def: DefId) -> Option<VarInit> {
    if let Some(init) = crate::db::var_initializer(&self.typecheck_db, def) {
      return Some(init);
    }

    let def_data = self.def_data.get(&def)?;
    let lowered = self.hir_lowered.get(&def_data.file)?;
    let hir_def = lowered.def(def)?;
    let def_name = lowered.names.resolve(hir_def.path.name);
    if !matches!(hir_def.path.kind, HirDefKind::Var) && def_name != Some("default") {
      return None;
    }
    let def_name = def_name.or_else(|| Some(def_data.name.as_str()));
    var_initializer_in_file(lowered, def, hir_def.span, def_name)
  }

  fn type_of_def(&mut self, def: DefId) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
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
    if let Some(existing) = self.def_types.get(&def).copied() {
      let in_bounds = (existing.0 as usize) < self.type_store.kinds.len();
      if in_bounds && !matches!(self.type_store.kind(existing), TypeKind::Unknown) {
        if let Some(span) = span.take() {
          span.finish(Some(existing));
        }
        return Ok(existing);
      }
      self.def_types.remove(&def);
      self.interned_def_types.remove(&def);
    }
    let def_data = match self.def_data.get(&def).cloned() {
      Some(data) => data,
      None => {
        if let Some(span) = span.take() {
          span.finish(Some(self.builtin.unknown));
        }
        return Ok(self.builtin.unknown);
      }
    };
    let prev_file = self.current_file;
    self.current_file = Some(def_data.file);
    if self.type_stack.contains(&def) {
      if let Some(span) = span.take() {
        span.finish(Some(self.builtin.any));
      }
      self.current_file = prev_file;
      return Ok(self.builtin.any);
    }
    let ns_entry = self
      .namespace_object_types
      .get(&(def_data.file, def_data.name.clone()))
      .copied();
    self.type_stack.push(def);
    let result = (|| -> Result<TypeId, FatalError> {
      self.check_cancelled()?;
      let ty = match def_data.kind.clone() {
        DefKind::Function(func) => self.function_type(def, func)?,
        DefKind::Var(var) => {
          let init = self.var_initializer(def);
          let decl_kind =
            init
              .as_ref()
              .map(|init| init.decl_kind)
              .unwrap_or_else(|| match var.mode {
                VarDeclMode::Var => HirVarDeclKind::Var,
                VarDeclMode::Let => HirVarDeclKind::Let,
                VarDeclMode::Const => HirVarDeclKind::Const,
                VarDeclMode::Using | VarDeclMode::AwaitUsing => HirVarDeclKind::Var,
              });
          let mut init_span_for_const = None;
          let mut inferred = if let Some(t) = var.typ {
            t
          } else if let Some(init) = init {
            self.body_results.remove(&init.body);
            let res = self.check_body(init.body)?;
            init_span_for_const = res.expr_span(init.expr);
            if let Some(init_ty) = res.expr_type(init.expr) {
              if let Some(store) = self.interned_store.as_ref() {
                let init_ty = store.canon(init_ty);
                self
                  .interned_def_types
                  .entry(def)
                  .and_modify(|existing| {
                    *existing = ProgramState::merge_interned_decl_types(store, *existing, init_ty);
                  })
                  .or_insert(init_ty);
              }
              self.import_interned_type(init_ty)
            } else {
              self.builtin.unknown
            }
          } else if let Some((_, store_ty)) = ns_entry {
            store_ty
          } else {
            self.builtin.unknown
          };
          if matches!(decl_kind, HirVarDeclKind::Const) {
            if let Some(init_span) = init_span_for_const {
              if let Some(file_body) = self.files.get(&def_data.file).and_then(|f| f.top_body) {
                let res = self.check_body(file_body)?;
                let top_ty = res
                  .expr_spans()
                  .iter()
                  .enumerate()
                  .find(|(_, span)| **span == init_span)
                  .and_then(|(idx, _)| res.expr_type(ExprId(idx as u32)));
                if let (Some(top_ty), Some(store)) = (top_ty, self.interned_store.as_ref()) {
                  let top_kind = store.type_kind(top_ty);
                  let has_readonly = match top_kind {
                    tti::TypeKind::Object(obj) => {
                      let shape = store.shape(store.object(obj).shape);
                      shape.properties.iter().any(|p| p.data.readonly)
                    }
                    tti::TypeKind::Tuple(elems) => elems.iter().any(|e| e.readonly),
                    _ => false,
                  };
                  if has_readonly {
                    let top_ty = store.canon(top_ty);
                    self.interned_def_types.insert(def, top_ty);
                    inferred = self.import_interned_type(top_ty);
                  }
                }
              }
            }
          }
          let init_is_satisfies = init
            .map(|init| self.init_is_satisfies(init.body, init.expr))
            .unwrap_or(false);
          if var.typ.is_none() && !init_is_satisfies {
            inferred = self.widen_array_elements(inferred);
          }
          if var.typ.is_none() {
            if !init_is_satisfies {
              inferred = self.widen_object_literal(inferred);
            }
          }
          let ty = if matches!(decl_kind, HirVarDeclKind::Const) {
            inferred
          } else {
            self.widen_literal(inferred)
          };
          if let Some(store) = self.interned_store.as_ref() {
            let mut cache = HashMap::new();
            let interned = store.canon(convert_type_for_display(ty, self, store, &mut cache));
            if var.typ.is_some() {
              self
                .interned_def_types
                .entry(def)
                .and_modify(|existing| {
                  *existing = ProgramState::merge_interned_decl_types(store, *existing, interned);
                })
                .or_insert(interned);
            } else {
              self.interned_def_types.insert(def, interned);
            }
          }
          ty
        }
        DefKind::Class(class) => {
          if let Some(store) = self.interned_store.as_ref() {
            if let Some(instance_type) = class.instance_type {
              let mut cache = HashMap::new();
              let interned = store.canon(convert_type_for_display(
                instance_type,
                self,
                store,
                &mut cache,
              ));
              self.interned_def_types.entry(def).or_insert(interned);
            }
          }
          class.static_type.unwrap_or(self.builtin.unknown)
        }
        DefKind::Enum(en) => {
          if let Some(store) = self.interned_store.as_ref() {
            if let Some(enum_type) = en.type_type {
              let mut cache = HashMap::new();
              let interned =
                store.canon(convert_type_for_display(enum_type, self, store, &mut cache));
              self.interned_def_types.entry(def).or_insert(interned);
            }
          }
          en.value_type.unwrap_or(self.builtin.unknown)
        }
        DefKind::Namespace(ns) => {
          if let Some((ns_interned, ns_store)) = ns_entry {
            self.def_types.insert(def, ns_store);
            self.interned_def_types.entry(def).or_insert(ns_interned);
            if let Some(data) = self.def_data.get_mut(&def) {
              if let DefKind::Namespace(ns_data) = &mut data.kind {
                ns_data.value_type = Some(ns_store);
                ns_data.type_type = Some(ns_store);
              }
            }
            ns_store
          } else {
            ns.value_type.unwrap_or(self.builtin.unknown)
          }
        }
        DefKind::Module(ns) => {
          if let Some((ns_interned, ns_store)) = ns_entry {
            self.def_types.insert(def, ns_store);
            self.interned_def_types.entry(def).or_insert(ns_interned);
            if let Some(data) = self.def_data.get_mut(&def) {
              if let DefKind::Module(ns_data) = &mut data.kind {
                ns_data.value_type = Some(ns_store);
                ns_data.type_type = Some(ns_store);
              }
            }
            ns_store
          } else {
            ns.value_type.unwrap_or(self.builtin.unknown)
          }
        }
        DefKind::Import(import) => {
          let exports = self.exports_for_import(&import)?;
          if let Some(entry) = exports.get(&import.original) {
            if let Some(ty) = entry.type_id {
              ty
            } else if let Some(def) = entry.def {
              self.type_of_def(def)?
            } else {
              self.builtin.unknown
            }
          } else {
            self.builtin.unknown
          }
        }
        DefKind::Interface(interface) => {
          if let Some(store) = self.interned_store.as_ref() {
            if !self.interned_def_types.contains_key(&def) {
              let mut cache = HashMap::new();
              let interned = convert_type_for_display(interface.typ, self, store, &mut cache);
              self.interned_def_types.insert(def, store.canon(interned));
            }
          }
          interface.typ
        }
        DefKind::TypeAlias(alias) => {
          if let Some(store) = self.interned_store.as_ref() {
            if !self.interned_def_types.contains_key(&def) {
              let mut cache = HashMap::new();
              let interned = convert_type_for_display(alias.typ, self, store, &mut cache);
              self.interned_def_types.insert(def, store.canon(interned));
            }
          }
          alias.typ
        }
      };
      self.check_cancelled()?;
      Ok(ty)
    })();
    self.type_stack.pop();
    self.current_file = prev_file;
    match result {
      Ok(mut ty) => {
        if let Some(store) = self.interned_store.as_ref() {
          if store.contains_type_id(ty) {
            let interned = store.canon(ty);
            self.interned_def_types.entry(def).or_insert(interned);
            ty = self.import_interned_type(interned);
          } else if !self.interned_def_types.contains_key(&def) {
            let mut cache = HashMap::new();
            let interned = store.canon(convert_type_for_display(ty, self, store, &mut cache));
            self.interned_def_types.insert(def, interned);
          }
        }
        if let Some((ns_interned, _ns_store)) = ns_entry {
          match def_data.kind {
            DefKind::Function(_) | DefKind::Var(_) | DefKind::Class(_) | DefKind::Enum(_) => {
              if let Some(store) = self.interned_store.as_ref() {
                let merged = if let Some(existing) = self.interned_def_types.get(&def).copied() {
                  store.intersection(vec![existing, ns_interned])
                } else {
                  ns_interned
                };
                self.interned_def_types.insert(def, merged);
              }
            }
            _ => {}
          }
        }
        self.def_types.insert(def, ty);
        let ret_ty = if let Some(_store) = self.interned_store.as_ref() {
          self.interned_def_types.get(&def).copied().unwrap_or(ty)
        } else {
          ty
        };
        if let Some(span) = span.take() {
          span.finish(Some(ret_ty));
        }
        Ok(ret_ty)
      }
      Err(err) => {
        if let Some(span) = span.take() {
          span.finish(None);
        }
        Err(err)
      }
    }
  }

  fn function_type(&mut self, def: DefId, func: FuncData) -> Result<TypeId, FatalError> {
    let param_types: Vec<TypeId> = func
      .params
      .iter()
      .map(|p| p.typ.unwrap_or(self.builtin.any))
      .collect();
    let ret = if let Some(ret) = func.return_ann {
      ret
    } else if let Some(body) = func.body {
      let res = self.check_body(body)?;
      if res.return_types.is_empty() {
        self.builtin.void
      } else {
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
    if let Some(store) = self.interned_store.as_ref() {
      let mut cache = HashMap::new();
      let interned = convert_type_for_display(ty, self, store, &mut cache);
      let interned = store.canon(interned);
      self
        .interned_def_types
        .entry(def)
        .and_modify(|existing| {
          *existing = ProgramState::merge_interned_decl_types(store, *existing, interned);
        })
        .or_insert(interned);
    }
    self.def_types.insert(def, ty);
    Ok(ty)
  }

  fn exports_of_file(&mut self, file: FileId) -> Result<ExportMap, FatalError> {
    if let Some(semantics) = self.semantics.clone() {
      return check::modules::exports_from_semantics(self, semantics.as_ref(), file);
    }
    let Some(state) = self.files.get(&file).cloned() else {
      return Ok(ExportMap::new());
    };
    let mut map = state.exports.clone();
    for entry in map.values_mut() {
      if entry.type_id.is_none() {
        entry.type_id = match entry.def {
          Some(def) => self.export_type_for_def(def)?,
          None => None,
        };
      }
    }
    Ok(map)
  }

  fn exports_of_ambient_module(&mut self, specifier: &str) -> Result<ExportMap, FatalError> {
    let Some(semantics) = self.semantics.clone() else {
      return Ok(ExportMap::new());
    };
    check::modules::exports_of_ambient_module(self, &semantics, specifier)
  }

  fn exports_for_import(&mut self, import: &ImportData) -> Result<ExportMap, FatalError> {
    match &import.target {
      ImportTarget::File(file) => self.exports_of_file(*file),
      ImportTarget::Unresolved { specifier } => self.exports_of_ambient_module(specifier),
    }
  }

  fn symbol_info(&self, symbol: semantic_js::SymbolId) -> Option<SymbolInfo> {
    let mut files: Vec<_> = self.file_kinds.keys().copied().collect();
    files.sort_by_key(|file| file.0);
    for file in files {
      let locals = crate::db::local_symbol_info(&self.typecheck_db, file);
      if let Some(local) = locals.get(&symbol) {
        return Some(SymbolInfo {
          symbol,
          def: None,
          file: Some(local.file),
          type_id: None,
          name: Some(local.name.clone()),
          span: local.span,
        });
      }
    }

    let binding = self
      .global_bindings
      .iter()
      .find(|(_, binding)| binding.symbol == symbol);

    let mut def = self
      .symbol_to_def
      .get(&symbol)
      .copied()
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.def));
    let mut file = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.file));
    let mut span = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.span));
    let mut name = def
      .and_then(|def_id| self.def_data.get(&def_id).map(|data| data.name.clone()))
      .or_else(|| binding.as_ref().map(|(name, _)| name.to_string()));
    let mut type_id = def
      .and_then(|def_id| self.def_types.get(&def_id).copied())
      .or_else(|| binding.as_ref().and_then(|(_, b)| b.type_id));

    if def.is_none() {
      if let Some(semantics) = self.semantics.as_ref() {
        let sem_symbol: sem_ts::SymbolId = symbol.into();
        let sym_data = semantics.symbols().symbol(sem_symbol);
        for ns in [
          sem_ts::Namespace::VALUE,
          sem_ts::Namespace::TYPE,
          sem_ts::Namespace::NAMESPACE,
        ] {
          if !sym_data.namespaces.contains(ns) {
            continue;
          }
          if let Some(decl_id) = semantics.symbol_decls(sem_symbol, ns).first() {
            let decl = semantics.symbols().decl(*decl_id);
            def = Some(decl.def_id);
            file = Some(decl.file);
            if name.is_none() {
              name = Some(sym_data.name.clone());
            }
            if type_id.is_none() {
              type_id = self.def_types.get(&decl.def_id).copied();
            }
            break;
          }
        }
      }
    }

    if span.is_none() {
      span = def.and_then(|def_id| self.def_data.get(&def_id).map(|data| data.span));
    }

    if def.is_none() && type_id.is_none() && name.is_none() && file.is_none() {
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
      span,
    })
  }

  fn expr_at(&mut self, file: FileId, offset: u32) -> Option<(BodyId, ExprId)> {
    db::expr_at(&self.typecheck_db, file, offset)
  }

  fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    self.def_data.get(&def).and_then(|d| match &d.kind {
      DefKind::Function(func) => func.body,
      DefKind::Var(var) => {
        if var.body.0 != u32::MAX {
          Some(var.body)
        } else {
          self.var_initializer(def).map(|init| init.body)
        }
      }
      DefKind::Class(class) => class.body,
      DefKind::Enum(en) => en.body,
      DefKind::Namespace(ns) => ns.body,
      DefKind::Module(ns) => ns.body,
      DefKind::Import(_) => None,
      DefKind::Interface(_) => None,
      DefKind::TypeAlias(_) => None,
    })
  }

  fn owner_of_body(&self, body: BodyId) -> Option<DefId> {
    for (def_id, data) in self.def_data.iter() {
      match &data.kind {
        DefKind::Function(func) if func.body == Some(body) => return Some(*def_id),
        DefKind::Var(var) => {
          if var.body == body {
            return Some(*def_id);
          }
          if var.body.0 == u32::MAX {
            if let Some(init) = self.var_initializer(*def_id) {
              if init.body == body {
                return Some(*def_id);
              }
            }
          }
        }
        DefKind::Class(class) if class.body == Some(body) => return Some(*def_id),
        DefKind::Enum(en) if en.body == Some(body) => return Some(*def_id),
        DefKind::Namespace(ns) if ns.body == Some(body) => return Some(*def_id),
        DefKind::Module(ns) if ns.body == Some(body) => return Some(*def_id),
        _ => {}
      }
    }
    None
  }

  fn object_type_from_members(&mut self, members: &[Node<TypeMember>]) -> ObjectType {
    let mut object = ObjectType::empty();
    for member in members.iter() {
      match member.stx.as_ref() {
        TypeMember::Property(prop) => {
          if let Some(name) = type_member_name(&prop.stx.key) {
            let ty = prop
              .stx
              .type_annotation
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
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
              .map(|p| self.type_from_type_expr(&p.stx.type_expr))
              .collect();
            let ret = method
              .stx
              .return_type
              .as_ref()
              .map(|t| self.type_from_type_expr(t))
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
          let value = self.type_from_type_expr(&index.stx.type_annotation);
          let param_type = self.type_from_type_expr(&index.stx.parameter_type);
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

  fn type_from_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    match expr.stx.as_ref() {
      TypeExpr::TypeReference(reference) => {
        if let Some(file) = self.current_file {
          let span = loc_to_span(file, reference.loc).range;
          if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
            if let Some(binding) = self
              .files
              .get(&file)
              .and_then(|f| f.bindings.get(type_name))
            {
              let symbol = binding.symbol;
              let ty_id = binding.type_id;
              let def = binding.def;
              self.record_symbol(file, span, symbol);
              if let Some(ty) = ty_id {
                return ty;
              }
              if let Some(def) = def {
                return match self.type_of_def(def) {
                  Ok(ty) => ty,
                  Err(fatal) => {
                    if !matches!(fatal, FatalError::Cancelled) {
                      self.diagnostics.push(fatal_to_diagnostic(fatal));
                    }
                    self.builtin.unknown
                  }
                };
              }
            }
            let mut entries: Vec<_> = self.def_data.iter().collect();
            entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
            let mut best: Option<(DefId, u8)> = None;
            for (id, data) in entries.into_iter() {
              if data.name != *type_name {
                continue;
              }
              let pri = self.def_priority(*id, sem_ts::Namespace::TYPE);
              match best {
                Some((_, existing)) if existing <= pri => {}
                _ => best = Some((*id, pri)),
              }
            }
            if let Some((id, _)) = best {
              return match self.type_of_def(id) {
                Ok(ty) => ty,
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  self.builtin.unknown
                }
              };
            }
          }
        }
        self.builtin.unknown
      }
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
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types.iter().map(|t| self.type_from_type_expr(t)).collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeExpr::TupleType(tuple) => {
        let readonly = tuple.stx.readonly;
        let elements = tuple
          .stx
          .elements
          .iter()
          .map(|elem| self.type_from_type_expr(&elem.stx.type_expr))
          .collect();
        self.type_store.tuple(elements, readonly)
      }
      TypeExpr::ArrayType(arr) => {
        let TypeArray { element_type, .. } = arr.stx.as_ref();
        let elem = self.type_from_type_expr(element_type);
        self.type_store.array(elem)
      }
      TypeExpr::FunctionType(func) => {
        let params = func
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&func.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ConstructorType(cons) => {
        let params = cons
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&cons.stx.return_type);
        self.type_store.function(params, ret)
      }
      TypeExpr::ObjectType(obj) => {
        let object = self.object_type_from_members(&obj.stx.members);
        self.type_store.object(object)
      }
      TypeExpr::MappedType(mapped) => {
        let source = self.type_from_type_expr(&mapped.stx.constraint);
        let value = self.type_from_type_expr(&mapped.stx.type_expr);
        self.type_store.mapped(source, value)
      }
      TypeExpr::ParenthesizedType(inner) => self.type_from_type_expr(&inner.stx.type_expr),
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
          .map(|t| self.type_from_type_expr(t));
        self
          .type_store
          .predicate(pred.stx.parameter_name.clone(), asserted, pred.stx.asserts)
      }
      TypeExpr::TypeQuery(query) => {
        fn entity_name_segments(name: &TypeEntityName) -> Option<Vec<String>> {
          match name {
            TypeEntityName::Identifier(id) => Some(vec![id.clone()]),
            TypeEntityName::Qualified(qualified) => {
              let mut parts = entity_name_segments(&qualified.left)?;
              parts.push(qualified.right.clone());
              Some(parts)
            }
            TypeEntityName::Import(_) => None,
          }
        }

        if let Some(path) = entity_name_segments(&query.stx.expr_name) {
          if path.len() == 1 {
            let mut entries: Vec<_> = self.def_data.iter().collect();
            entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
            let mut best: Option<(DefId, u8)> = None;
            for (id, data) in entries.into_iter() {
              if data.name != path[0] {
                continue;
              }
              let pri = self.def_priority(*id, sem_ts::Namespace::VALUE);
              match best {
                Some((_, existing)) if existing <= pri => {}
                _ => best = Some((*id, pri)),
              }
            }
            if let Some((id, _)) = best {
              return match self.type_of_def(id) {
                Ok(ty) => ty,
                Err(fatal) => {
                  if !matches!(fatal, FatalError::Cancelled) {
                    self.diagnostics.push(fatal_to_diagnostic(fatal));
                  }
                  self.builtin.unknown
                }
              };
            }
          }
        }

        self.builtin.unknown
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
