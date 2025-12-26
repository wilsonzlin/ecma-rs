use crate::api::{BodyId, DefId, Diagnostic, ExprId, FileId, PatId, Span, TextRange};
use ::semantic_js::ts as sem_ts;
use hir_js::{
  lower_file_with_diagnostics as lower_hir_with_diagnostics, DefId as HirDefId,
  FileKind as HirFileKind, LowerResult,
};
use ordered_float::OrderedFloat;
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType};
use parse_js::ast::expr::lit::{LitArrElem, LitObjExpr};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{FuncDecl, ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::{
  TypeArray, TypeEntityName, TypeExpr, TypeLiteral, TypeMember, TypePropertyKey, TypeUnion,
};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;
use tracing::debug_span;
use types_ts_interned::{self as tti, TypeId, TypeOptions, TypeParamId};

use crate::check::caches::{CheckerCacheStats, CheckerCaches};
use crate::codes;
use crate::profile::{QueryKind, QueryStats, QueryStatsCollector};
#[cfg(feature = "serde")]
use crate::snapshot::{
  BodyDataSnapshot, DefSnapshot, FileSnapshot, FileStateSnapshot, ProgramSnapshot,
  PROGRAM_SNAPSHOT_VERSION,
};
use crate::type_queries::{
  IndexerInfo, PropertyInfo, PropertyKey, SignatureInfo, TypeKindSummary, TypeQueries,
};
use crate::{FatalError, HostError, Ice, IceContext};
use sem_ts::from_hir_js::lower_to_ts_hir;

#[path = "check/mod.rs"]
pub(crate) mod check;

use check::legacy_narrow::{
  narrow_by_discriminant, narrow_by_in_check, narrow_by_instanceof, narrow_by_literal,
  narrow_by_typeof, truthy_falsy_types, Facts, LiteralValue,
};

use crate::lib_support::{CacheMode, CompilerOptions, FileKind, LibFile, LibManager};

/// Environment provider for [`Program`].
pub trait Host: Send + Sync + 'static {
  /// Return the full text for a file.
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError>;
  /// Resolve a module specifier relative to `from`.
  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId>;

  /// Compiler options influencing lib selection and strictness.
  fn compiler_options(&self) -> CompilerOptions {
    CompilerOptions::default()
  }

  /// Additional library files to include alongside bundled libs.
  fn lib_files(&self) -> Vec<LibFile> {
    Vec::new()
  }

  /// Kind of the file; defaults to TypeScript.
  fn file_kind(&self, _file: FileId) -> FileKind {
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
      SymbolId(id.0)
    }
  }

  impl From<SymbolId> for ::semantic_js::ts::SymbolId {
    fn from(id: SymbolId) -> Self {
      ::semantic_js::ts::SymbolId(id.0)
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
  body: BodyId,
  expr_types: Vec<TypeId>,
  expr_spans: Vec<TextRange>,
  pat_types: Vec<TypeId>,
  pat_spans: Vec<TextRange>,
  diagnostics: Vec<Diagnostic>,
  return_types: Vec<TypeId>,
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
    let mut best_containing: Option<(ExprId, TypeId, u32)> = None;
    let mut best_empty: Option<(ExprId, TypeId, u32)> = None;
    for (idx, span) in self.expr_spans.iter().enumerate() {
      let width = span.end.saturating_sub(span.start);
      if span.start <= offset && offset < span.end {
        let entry = (ExprId(idx as u32), *self.expr_types.get(idx)?, width);
        best_containing = match best_containing {
          Some((_, _, existing)) if existing <= width => best_containing,
          _ => Some(entry),
        };
      } else if span.start == span.end && offset == span.start {
        let entry = (ExprId(idx as u32), *self.expr_types.get(idx)?, width);
        best_empty = match best_empty {
          Some((_, _, existing)) if existing <= width => best_empty,
          _ => Some(entry),
        };
      }
    }
    best_containing.or(best_empty).map(|(id, ty, _)| (id, ty))
  }

  /// Spans for all expressions in this body.
  pub fn expr_spans(&self) -> &[TextRange] {
    &self.expr_spans
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
}

impl std::fmt::Display for TypeDisplay {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    tti::TypeDisplay::new(&self.store, self.ty).fmt(f)
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

fn parse_file(file: FileId, kind: FileKind, source: &str) -> Result<Node<TopLevel>, Diagnostic> {
  parse_with_options(
    source,
    ParseOptions {
      dialect: match kind {
        FileKind::Js => Dialect::Js,
        FileKind::Ts => Dialect::Ts,
        FileKind::Tsx => Dialect::Tsx,
        FileKind::Jsx => Dialect::Jsx,
        FileKind::Dts => Dialect::Dts,
      },
      source_type: SourceType::Module,
    },
  )
  .map_err(|err| err.to_diagnostic(file))
}

fn display_type_from_state(state: &ProgramState, ty: TypeId) -> (Arc<tti::TypeStore>, tti::TypeId) {
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
  let mapped = match state.type_store.kind(ty).clone() {
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
    TypeKind::Predicate { asserted, .. } => match asserted {
      Some(ty) => convert_type_for_display(ty, state, store, cache),
      None => primitives.boolean,
    },
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
  roots: Vec<FileId>,
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
  pub fn new(host: impl Host, roots: Vec<FileId>) -> Program {
    Program::with_lib_manager(host, roots, Arc::new(LibManager::new()))
  }

  /// Create a new program with a provided lib manager (useful for observing invalidation in tests).
  pub fn with_lib_manager(
    host: impl Host,
    roots: Vec<FileId>,
    lib_manager: Arc<LibManager>,
  ) -> Program {
    let query_stats = QueryStatsCollector::default();
    Program {
      host: Arc::new(host),
      roots,
      cancelled: AtomicBool::new(false),
      state: std::sync::Mutex::new(ProgramState::new(lib_manager, query_stats.clone())),
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
      let mut body_ids: Vec<BodyId> = state.body_data.keys().copied().collect();
      body_ids.sort_by_key(|id| id.0);
      let mut body_diagnostics = Vec::new();
      for body in body_ids {
        self.ensure_not_cancelled()?;
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
      stats
    };
    stats.record(&self.query_stats);
    self.query_stats.snapshot()
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
    state.builtin.unknown
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
    self.with_analyzed_state(|state| Ok(state.type_of_def(def)))
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
    self.with_analyzed_state(|state| Ok(state.check_body(body)))
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
    self.with_analyzed_state(|state| {
      let result = state.check_body(body);
      Ok(result.expr_type(expr).unwrap_or(state.builtin.unknown))
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
    self.with_analyzed_state(|state| {
      let (body, expr) = match state.expr_at(file, offset) {
        Some(res) => res,
        None => return Ok(None),
      };
      let result = state.check_body(body);
      Ok(Some(
        result.expr_type(expr).unwrap_or(state.builtin.unknown),
      ))
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
    let (store, ty) = {
      let mut state = self.lock_state();
      state.ensure_analyzed(&self.host, &self.roots, &self.cancelled);
      display_type_from_state(&state, ty)
    };
    TypeDisplay { store, ty }
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
        DefKind::Var(var) => Some(var.body),
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

    let mut body_ids: Vec<_> = state.body_data.keys().copied().collect();
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
      let text = state
        .lib_texts
        .get(&file)
        .cloned()
        .or_else(|| self.host.file_text(file).ok());
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

    let mut body_data = Vec::new();
    for body in body_ids.iter() {
      if let Some(data) = state.body_data.get(body) {
        body_data.push(BodyDataSnapshot {
          id: data.id,
          file: data.file,
          owner: data.owner,
          expr_spans: data.expr_spans.clone(),
          pat_spans: data.pat_spans.clone(),
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
      roots: self.roots.clone(),
      files,
      file_states,
      def_data,
      body_data,
      def_types,
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
    let program =
      Program::with_lib_manager(host, snapshot.roots.clone(), Arc::new(LibManager::new()));
    {
      let mut state = program.lock_state();
      state.analyzed = true;
      state.compiler_options = snapshot.compiler_options;
      state.checker_caches = CheckerCaches::new(state.compiler_options.cache.clone());
      state.cache_stats = CheckerCacheStats::default();
      for file in snapshot.files.into_iter() {
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
      state.def_data = snapshot
        .def_data
        .into_iter()
        .map(|def| (def.def, def.data))
        .collect();
      state.body_data = snapshot
        .body_data
        .into_iter()
        .map(|body| {
          (
            body.id,
            BodyData {
              id: body.id,
              file: body.file,
              owner: body.owner,
              stmts: Vec::new(),
              expr_spans: body.expr_spans,
              pat_spans: body.pat_spans,
            },
          )
        })
        .collect();
      state.def_types = snapshot.def_types.into_iter().collect();
      state.body_results = snapshot
        .body_results
        .into_iter()
        .map(|res| (res.body(), Arc::new(res)))
        .collect();
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
}

impl sem_ts::Resolver for HostResolver {
  fn resolve(&self, from: sem_ts::FileId, specifier: &str) -> Option<sem_ts::FileId> {
    self
      .host
      .resolve(FileId(from.0), specifier)
      .map(|f| sem_ts::FileId(f.0))
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

#[derive(Clone, Debug)]
struct BodyData {
  id: BodyId,
  file: FileId,
  owner: Option<DefId>,
  stmts: Vec<HirStmt>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
enum HirStmt {
  Var {
    name: String,
    typ: Option<TypeId>,
    init: Option<HirExpr>,
    span: TextRange,
    symbol: semantic_js::SymbolId,
    def: Option<DefId>,
    pat: Option<PatId>,
  },
  Return {
    expr: Option<HirExpr>,
    span: TextRange,
  },
  Expr(HirExpr),
  If {
    test: HirExpr,
    consequent: Vec<HirStmt>,
    alternate: Vec<HirStmt>,
    span: TextRange,
  },
  Block(Vec<HirStmt>),
  While {
    test: HirExpr,
    body: Vec<HirStmt>,
    span: TextRange,
  },
  Switch {
    discriminant: HirExpr,
    cases: Vec<HirSwitchCase>,
    span: TextRange,
  },
}

#[derive(Clone, Debug)]
struct HirExpr {
  id: ExprId,
  span: TextRange,
  kind: HirExprKind,
}

#[derive(Clone, Debug)]
struct HirObjectProperty {
  name: String,
  value: HirExpr,
  span: TextRange,
  is_spread: bool,
}

#[derive(Clone, Debug)]
struct HirSwitchCase {
  test: Option<HirExpr>,
  consequent: Vec<HirStmt>,
}

#[derive(Clone, Debug)]
enum HirExprKind {
  NumberLiteral(String),
  StringLiteral(String),
  BooleanLiteral(bool),
  Null,
  Ident(String),
  Member {
    object: Box<HirExpr>,
    property: String,
  },
  Unary {
    op: OperatorName,
    expr: Box<HirExpr>,
  },
  Binary {
    op: OperatorName,
    left: Box<HirExpr>,
    right: Box<HirExpr>,
  },
  Call {
    callee: Box<HirExpr>,
    args: Vec<HirExpr>,
  },
  Conditional {
    test: Box<HirExpr>,
    consequent: Box<HirExpr>,
    alternate: Box<HirExpr>,
  },
  Object(Vec<HirObjectProperty>),
  TypeAssertion {
    expr: Box<HirExpr>,
    typ: Option<TypeId>,
    _const_assertion: bool,
    make_readonly: bool,
  },
  Array(Vec<HirExpr>),
  Unknown,
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

  pub(crate) fn array(&mut self, element: TypeId) -> TypeId {
    self.alloc(TypeKind::Array(element))
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
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  body_data: HashMap<BodyId, BodyData>,
  hir_lowered: HashMap<FileId, LowerResult>,
  sem_hir: HashMap<FileId, sem_ts::HirFile>,
  semantics: Option<sem_ts::TsProgramSemantics>,
  def_types: HashMap<DefId, TypeId>,
  body_results: HashMap<BodyId, Arc<BodyCheckResult>>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  symbol_to_def: HashMap<semantic_js::SymbolId, DefId>,
  file_kinds: HashMap<FileId, FileKind>,
  lib_texts: HashMap<FileId, Arc<str>>,
  global_bindings: HashMap<String, SymbolBinding>,
  diagnostics: Vec<Diagnostic>,
  type_store: TypeStore,
  interned_store: Option<Arc<tti::TypeStore>>,
  interned_def_types: HashMap<DefId, tti::TypeId>,
  interned_type_params: HashMap<DefId, Vec<TypeParamId>>,
  builtin: BuiltinTypes,
  query_stats: QueryStatsCollector,
  next_def: u32,
  next_body: u32,
  next_symbol: u32,
  type_stack: Vec<DefId>,
}

impl ProgramState {
  fn new(lib_manager: Arc<LibManager>, query_stats: QueryStatsCollector) -> ProgramState {
    let default_options = CompilerOptions::default();
    let (type_store, builtin) = TypeStore::new();
    ProgramState {
      analyzed: false,
      lib_manager,
      compiler_options: default_options.clone(),
      checker_caches: CheckerCaches::new(default_options.cache.clone()),
      cache_stats: CheckerCacheStats::default(),
      files: HashMap::new(),
      def_data: HashMap::new(),
      body_data: HashMap::new(),
      hir_lowered: HashMap::new(),
      sem_hir: HashMap::new(),
      semantics: None,
      def_types: HashMap::new(),
      body_results: HashMap::new(),
      symbol_occurrences: HashMap::new(),
      symbol_to_def: HashMap::new(),
      file_kinds: HashMap::new(),
      lib_texts: HashMap::new(),
      global_bindings: HashMap::new(),
      diagnostics: Vec::new(),
      type_store,
      interned_store: None,
      interned_def_types: HashMap::new(),
      interned_type_params: HashMap::new(),
      builtin,
      query_stats,
      next_def: 0,
      next_body: 0,
      next_symbol: 0,
      type_stack: Vec::new(),
    }
  }

  fn ensure_analyzed(&mut self, host: &Arc<dyn Host>, roots: &[FileId], cancelled: &AtomicBool) {
    if let Err(fatal) = self.ensure_analyzed_result(host, roots, cancelled) {
      self.diagnostics.push(fatal_to_diagnostic(fatal));
    }
  }

  fn ensure_analyzed_result(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileId],
    cancelled: &AtomicBool,
  ) -> Result<(), FatalError> {
    if self.analyzed {
      return Ok(());
    }
    let libs = self.collect_libraries(host.as_ref());
    let lib_ids: Vec<FileId> = libs.iter().map(|l| l.id).collect();
    let lib_id_set: HashSet<FileId> = lib_ids.iter().copied().collect();
    self.process_libs(&libs);
    let mut queue: BTreeSet<FileId> = roots.iter().copied().collect();
    let mut seen: HashSet<FileId> = HashSet::new();
    while let Some(&file) = queue.iter().next() {
      queue.remove(&file);
      if cancelled.load(Ordering::Relaxed) {
        return Err(FatalError::Cancelled);
      }
      if !seen.insert(file) {
        continue;
      }
      if lib_id_set.contains(&file) {
        continue;
      }
      self
        .file_kinds
        .entry(file)
        .or_insert_with(|| host.file_kind(file));
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
          let sem_hir = lower_to_ts_hir(&ast, &lowered);
          self.hir_lowered.insert(file, lowered);
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
          self.bind_file(file, ast, host, &mut queue);
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
      self.compute_semantics(host, roots, &lib_ids);
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
    roots: &[FileId],
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
    let mut def_types = HashMap::new();
    let mut type_params = HashMap::new();
    let mut def_by_name: HashMap<(FileId, String), DefId> = HashMap::new();
    let mut def_entries: Vec<_> = self.def_data.iter().collect();
    def_entries.sort_by_key(|(def_id, _)| def_id.0);
    for (def_id, data) in def_entries {
      def_by_name
        .entry((data.file, data.name.clone()))
        .and_modify(|existing| {
          if def_id.0 < existing.0 {
            *existing = *def_id;
          }
        })
        .or_insert(*def_id);
    }

    let mut lowered_files: Vec<_> = self.hir_lowered.iter().collect();
    lowered_files.sort_by_key(|(file, _)| file.0);
    for (file, lowered) in lowered_files {
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
      let mut lowerer = check::decls::HirDeclLowerer::new(
        Arc::clone(&store),
        &lowered.types,
        self.semantics.as_ref(),
        def_by_name.clone(),
        *file,
        local_defs,
        &mut self.diagnostics,
        Some(&def_map),
        Some(&def_by_name),
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
          def_types.insert(mapped, ty);
          if !params.is_empty() {
            type_params.insert(mapped, params);
          }
        }
      }
    }

    self.interned_store = Some(store);
    self.interned_def_types = def_types;
    self.interned_type_params = type_params;
    codes::normalize_diagnostics(&mut self.diagnostics);
    Ok(())
  }

  fn collect_libraries(&mut self, host: &dyn Host) -> Vec<LibFile> {
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
      if !is_dts {
        self.diagnostics.push(codes::NON_DTS_LIB.warning(
          format!(
            "Library '{}' is not a .d.ts file; it will be ignored for global declarations.",
            lib.name
          ),
          Span::new(lib.id, TextRange::new(0, 0)),
        ));
        continue;
      }
      self.file_kinds.insert(lib.id, FileKind::Dts);
      dts_libs.push(lib);
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

  fn process_libs(&mut self, libs: &[LibFile]) {
    for lib in libs {
      self.lib_texts.insert(lib.id, lib.text.clone());
      let parsed = parse_file(lib.id, FileKind::Dts, lib.text.as_ref());
      match parsed {
        Ok(ast) => {
          let (lowered, lower_diags) = lower_hir_with_diagnostics(lib.id, HirFileKind::Dts, &ast);
          self.diagnostics.extend(lower_diags);
          let sem_hir = lower_to_ts_hir(&ast, &lowered);
          self.hir_lowered.insert(lib.id, lowered);
          self.sem_hir.insert(lib.id, sem_hir);
        }
        Err(err) => {
          self.diagnostics.push(err);
        }
      }
    }
  }

  fn load_text(&self, file: FileId, host: &Arc<dyn Host>) -> Result<Arc<str>, HostError> {
    if let Some(text) = self.lib_texts.get(&file) {
      return Ok(text.clone());
    }
    host.file_text(file)
  }

  fn recompute_global_bindings(&mut self) {
    if let Some(semantics) = self.semantics.as_ref() {
      let mut globals = HashMap::new();
      let symbols = semantics.symbols();
      for (name, group) in semantics.global_symbols() {
        if let Some(symbol) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) {
          globals.insert(
            name.clone(),
            SymbolBinding {
              symbol: symbol.into(),
              def: None,
              type_id: None,
            },
          );
        }
      }
      globals
        .entry("undefined".to_string())
        .or_insert(SymbolBinding {
          symbol: self.alloc_symbol(),
          def: None,
          type_id: Some(self.builtin.undefined),
        });
      self.global_bindings = globals;
      return;
    }
    let mut globals = HashMap::new();
    let mut files: Vec<_> = self.files.keys().copied().collect();
    files.sort_by_key(|f| f.0);
    for file in files {
      if self.file_kinds.get(&file) != Some(&FileKind::Dts) {
        continue;
      }
      let Some(state) = self.files.get(&file) else {
        continue;
      };
      let mut bindings: Vec<_> = state.bindings.iter().collect();
      bindings.sort_by(|a, b| a.0.cmp(b.0));
      for (name, binding) in bindings {
        globals
          .entry(name.clone())
          .or_insert_with(|| binding.clone());
      }
    }
    globals
      .entry("undefined".to_string())
      .or_insert(SymbolBinding {
        symbol: self.alloc_symbol(),
        def: None,
        type_id: Some(self.builtin.undefined),
      });
    self.global_bindings = globals;
  }

  fn compute_semantics(&mut self, host: &Arc<dyn Host>, roots: &[FileId], libs: &[FileId]) {
    let resolver = HostResolver {
      host: Arc::clone(host),
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
    for state in self.files.values_mut() {
      for entry in state.exports.values_mut() {
        if let Some(def) = entry.def {
          if let Some(ty) = self.def_types.get(&def) {
            entry.type_id = Some(*ty);
          }
        }
      }
    }
  }

  fn bind_file(
    &mut self,
    file: FileId,
    ast: Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut BTreeSet<FileId>,
  ) {
    let top_body_id = self.alloc_body(file, None);
    let mut top_body = BodyBuilder::new(top_body_id, file);
    let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
    let mut sem_builder = SemHirBuilder::new(file, sem_file_kind(file_kind));
    let mut defs = Vec::new();
    let mut exports: ExportMap = BTreeMap::new();
    let mut bindings: HashMap<String, SymbolBinding> = HashMap::new();
    let mut reexports = Vec::new();
    let mut export_all = Vec::new();

    for stmt in ast.stx.body.into_iter() {
      match stmt.stx.as_ref() {
        Stmt::VarDecl(_) | Stmt::FunctionDecl(_) | Stmt::ExportDefaultExpr(_) => {
          // handled below with ownership
        }
        _ => {}
      }
      match *stmt.stx {
        Stmt::VarDecl(var) => {
          let var_span = loc_to_span(file, stmt.loc);
          let (new_defs, stmts) = self.handle_var_decl(
            file,
            var_span.range,
            *var.stx,
            &mut top_body,
            &mut sem_builder,
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
          top_body.stmts.extend(stmts);
        }
        Stmt::FunctionDecl(func) => {
          let span = loc_to_span(file, stmt.loc);
          if let Some((def_id, binding, export_name)) =
            self.handle_function_decl(file, span.range, *func.stx, &mut sem_builder)
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
        Stmt::ExportDefaultExpr(node) => {
          let span = loc_to_span(file, node.loc);
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          let expr = top_body.lower_expr(node.stx.expression, self);
          let expr_id = expr.id;
          let pat_id = Some(top_body.new_pat(span.range));
          let hir_stmt = HirStmt::Var {
            name: "default".to_string(),
            typ: None,
            init: Some(expr),
            span: span.range,
            symbol,
            def: Some(def_id),
            pat: pat_id,
          };
          top_body.stmts.push(hir_stmt);
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
                init: Some(expr_id),
                body: top_body_id,
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
            .and_then(|module| host.resolve(file, module));
          if let Some(target) = resolved {
            queue.insert(target);
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
          let resolved = host.resolve(file, &module);
          if let Some(target) = resolved {
            queue.insert(target);
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
        Stmt::Expr(expr_stmt) => {
          let expr = top_body.lower_expr(expr_stmt.stx.expr, self);
          top_body.stmts.push(HirStmt::Expr(expr));
        }
        Stmt::If(_) | Stmt::Block(_) | Stmt::While(_) => {
          top_body.lower_stmt(stmt, self);
        }
        _ => {}
      }
    }

    let body_data = top_body.finish(None);
    self.body_data.insert(top_body_id, body_data);
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
        top_body: Some(top_body_id),
        reexports,
        export_all,
      },
    );
  }

  fn handle_var_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    var: VarDecl,
    builder: &mut BodyBuilder,
    sem_builder: &mut SemHirBuilder,
  ) -> (
    Vec<(DefId, (String, SymbolBinding), Option<String>)>,
    Vec<HirStmt>,
  ) {
    let mut defs = Vec::new();
    let mut stmts = Vec::new();
    for declarator in var.declarators.into_iter() {
      let pat = declarator.pattern;
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
      let init_expr = declarator
        .initializer
        .map(|expr| builder.lower_expr(expr, self));
      let init_id = init_expr.as_ref().map(|e| e.id);
      let pat_id = Some(builder.new_pat(loc_to_span(file, pat.loc).range));
      stmts.push(HirStmt::Var {
        name: name.clone(),
        typ: type_ann,
        init: init_expr,
        span,
        symbol,
        def: Some(def_id),
        pat: pat_id,
      });
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
            init: init_id,
            body: builder.id,
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
    (defs, stmts)
  }

  fn handle_function_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    func: FuncDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Option<(DefId, (String, SymbolBinding), Option<String>)> {
    let name_node = func.name?;
    let name = name_node.stx.name.clone();
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, name_node.loc).range, symbol);
    let def_id = self.alloc_def();
    let func_data = self.lower_function(file, *func.function.stx, def_id);
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

  fn lower_function(&mut self, file: FileId, func: Func, def: DefId) -> FuncData {
    let body_id = func.body.as_ref().map(|_| self.alloc_body(file, Some(def)));
    let mut builder_opt = body_id.map(|id| BodyBuilder::new(id, file));
    let mut params = Vec::new();
    for param in func.parameters.iter() {
      if let Some(data) = self.lower_param(file, param, builder_opt.as_mut()) {
        params.push(data);
      }
    }
    let return_ann = func
      .return_type
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    if let Some(body) = body_id {
      if let Some(mut builder) = builder_opt.take() {
        match func.body.unwrap() {
          FuncBody::Block(stmts) => {
            for stmt in stmts {
              builder.lower_stmt(stmt, self);
            }
            let data = builder.finish(Some(def));
            self.body_data.insert(body, data);
          }
          FuncBody::Expression(expr) => {
            let expr = builder.lower_expr(expr, self);
            let span = expr.span;
            builder.stmts.push(HirStmt::Return {
              expr: Some(expr),
              span,
            });
            let data = builder.finish(Some(def));
            self.body_data.insert(body, data);
          }
        }
      }
    }
    FuncData {
      params,
      return_ann,
      body: body_id,
    }
  }

  fn lower_param(
    &mut self,
    file: FileId,
    param: &Node<ParamDecl>,
    mut builder: Option<&mut BodyBuilder>,
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
    let pat_id = builder
      .as_mut()
      .map(|b| b.new_pat(loc_to_span(file, param.loc).range));
    let typ = param
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, param.loc).range, symbol);
    Some(ParamData {
      name,
      typ,
      symbol,
      pat: pat_id,
    })
  }

  fn check_body(&mut self, body_id: BodyId) -> Arc<BodyCheckResult> {
    let cache_hit = self.body_results.contains_key(&body_id);
    let body_meta = self.body_data.get(&body_id).cloned();
    let mut span = QuerySpan::enter(
      QueryKind::CheckBody,
      query_span!(
        "typecheck_ts.check_body",
        body_meta.as_ref().map(|b| b.file.0),
        body_meta.as_ref().and_then(|b| b.owner.map(|d| d.0)),
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
    let body = match body_meta {
      Some(b) => b,
      None => {
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
      }
    };
    let body_caches = self.checker_caches.for_body();
    let mut env = self.initial_env(body.owner, body.file);
    let return_context = body
      .owner
      .and_then(|def| self.def_data.get(&def))
      .and_then(|def| match &def.kind {
        DefKind::Function(func) => func.return_ann,
        _ => None,
      });
    let mut result = BodyCheckResult {
      body: body.id,
      expr_types: vec![self.builtin.unknown; body.expr_spans.len()],
      expr_spans: body.expr_spans.clone(),
      pat_types: vec![self.builtin.unknown; body.pat_spans.len()],
      pat_spans: body.pat_spans.clone(),
      diagnostics: Vec::new(),
      return_types: Vec::new(),
    };

    if let Some(owner) = body.owner {
      if let Some(DefKind::Function(func)) = self.def_data.get(&owner).map(|d| &d.kind) {
        for param in func.params.iter() {
          if let Some(pat_id) = param.pat {
            let ty = param.typ.unwrap_or(self.builtin.unknown);
            if let Some(slot) = result.pat_types.get_mut(pat_id.0 as usize) {
              *slot = ty;
            }
          }
        }
      }
    }

    for stmt in body.stmts.iter() {
      self.check_stmt(stmt, &mut env, &mut result, body.file, return_context);
    }

    if let Some(store) = self.interned_store.as_ref() {
      let type_options = TypeOptions::from(&self.compiler_options);
      let primitives = store.primitive_ids();
      let relate = tti::RelateCtx::with_cache(
        Arc::clone(store),
        type_options,
        body_caches.relation.clone(),
      );
      for (idx, _) in body.expr_spans.iter().enumerate() {
        let lit = store.intern_type(tti::TypeKind::NumberLiteral(OrderedFloat::from(idx as f64)));
        let _ = relate.is_assignable(lit, primitives.number);
      }
    }

    let stats = body_caches.stats();
    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      self.cache_stats.merge(&stats);
    }

    codes::normalize_diagnostics(&mut result.diagnostics);
    let res = Arc::new(result);
    self.body_results.insert(body_id, res.clone());
    if let Some(span) = span.take() {
      span.finish(None);
    }
    res
  }

  fn check_stmt(
    &mut self,
    stmt: &HirStmt,
    env: &mut HashMap<String, SymbolBinding>,
    result: &mut BodyCheckResult,
    file: FileId,
    return_context: Option<TypeId>,
  ) {
    match stmt {
      HirStmt::Var {
        name,
        typ,
        init,
        span,
        symbol,
        def,
        pat,
      } => {
        let init_checked = init
          .as_ref()
          .map(|e| self.check_expr(e, env, result, file, *typ));
        let init_ty = init_checked.map(|(ty, facts)| {
          self.apply_fact_map(env, &facts.assertions);
          ty
        });
        let declared = if let Some(annotated) = *typ {
          if let (Some(expr), Some(source_ty)) = (init.as_ref(), init_ty) {
            check::assign::check_assignment(self, Some(expr), source_ty, annotated, result, file);
          }
          annotated
        } else if let Some(init_ty) = init_ty {
          init_ty
        } else {
          self.builtin.unknown
        };
        let declared = if let Some(def_id) = def {
          if let Some(DefKind::Var(var_data)) = self.def_data.get(def_id).map(|d| &d.kind) {
            if var_data.typ.is_none() && var_data.mode != VarDeclMode::Const {
              self.widen_literal(declared)
            } else {
              declared
            }
          } else {
            declared
          }
        } else {
          declared
        };
        if let Some(def_id) = def {
          self.def_types.insert(*def_id, declared);
        }
        env.insert(
          name.clone(),
          SymbolBinding {
            symbol: *symbol,
            def: *def,
            type_id: Some(declared),
          },
        );
        self.record_symbol(file, *span, *symbol);
        if let Some(pat_id) = pat {
          if let Some(slot) = result.pat_types.get_mut(pat_id.0 as usize) {
            *slot = declared;
          }
        }
      }
      HirStmt::Return { expr, .. } => {
        let ty = expr
          .as_ref()
          .map(|e| self.check_expr(e, env, result, file, return_context).0)
          .unwrap_or(self.builtin.undefined);
        if let Some(expected) = return_context {
          if let Some(expr) = expr {
            check::assign::check_assignment(self, Some(expr), ty, expected, result, file);
          }
        }
        result.return_types.push(ty);
      }
      HirStmt::Expr(expr) => {
        let (_, facts) = self.check_expr(expr, env, result, file, None);
        self.apply_fact_map(env, &facts.assertions);
      }
      HirStmt::If {
        test,
        consequent,
        alternate,
        ..
      } => {
        let (_, cond_facts) = self.check_expr(test, env, result, file, None);
        let mut then_env = env.clone();
        self.apply_fact_map(&mut then_env, &cond_facts.truthy);
        self.apply_fact_map(&mut then_env, &cond_facts.assertions);
        let mut else_env = env.clone();
        self.apply_fact_map(&mut else_env, &cond_facts.falsy);
        self.apply_fact_map(&mut else_env, &cond_facts.assertions);

        for stmt in consequent {
          self.check_stmt(stmt, &mut then_env, result, file, return_context);
        }
        for stmt in alternate {
          self.check_stmt(stmt, &mut else_env, result, file, return_context);
        }

        let then_returns = self.branch_returns(consequent);
        let else_returns = self.branch_returns(alternate);
        *env = match (then_returns, else_returns) {
          (true, false) => else_env,
          (false, true) => then_env,
          (true, true) => env.clone(),
          _ => self.merge_envs(&then_env, &else_env),
        };
      }
      HirStmt::Block(stmts) => {
        for stmt in stmts {
          self.check_stmt(stmt, env, result, file, return_context);
        }
      }
      HirStmt::While { test, body, .. } => {
        let (_, cond_facts) = self.check_expr(test, env, result, file, None);
        let mut body_env = env.clone();
        self.apply_fact_map(&mut body_env, &cond_facts.truthy);
        self.apply_fact_map(&mut body_env, &cond_facts.assertions);
        for stmt in body {
          self.check_stmt(stmt, &mut body_env, result, file, return_context);
        }
        let mut merged = self.merge_envs(env, &body_env);
        self.apply_fact_map(&mut merged, &cond_facts.falsy);
        *env = merged;
      }
      HirStmt::Switch {
        discriminant,
        cases,
        ..
      } => {
        let (disc_ty, _) = self.check_expr(discriminant, env, result, file, None);
        let mut merged_env: Option<HashMap<String, SymbolBinding>> = None;
        let has_default = cases.iter().any(|case| case.test.is_none());
        for case in cases {
          let mut case_env = env.clone();
          if let Some(test) = &case.test {
            let _ = self.check_expr(test, &mut case_env, result, file, None);
            self.apply_switch_narrowing(discriminant, disc_ty, test, &mut case_env, result, file);
          }
          for stmt in case.consequent.iter() {
            self.check_stmt(stmt, &mut case_env, result, file, return_context);
          }
          merged_env = Some(match merged_env {
            Some(existing) => self.merge_envs(&existing, &case_env),
            None => case_env,
          });
        }
        if !has_default {
          merged_env = Some(match merged_env {
            Some(existing) => self.merge_envs(&existing, env),
            None => env.clone(),
          });
        }
        if let Some(new_env) = merged_env {
          *env = new_env;
        }
      }
    }
  }

  fn check_expr(
    &mut self,
    expr: &HirExpr,
    env: &mut HashMap<String, SymbolBinding>,
    result: &mut BodyCheckResult,
    file: FileId,
    context: Option<TypeId>,
  ) -> (TypeId, Facts) {
    let mut facts = Facts::default();
    let ty = match &expr.kind {
      HirExprKind::NumberLiteral(value) => self.type_store.literal_number(value.clone()),
      HirExprKind::StringLiteral(value) => self.type_store.literal_string(value.clone()),
      HirExprKind::BooleanLiteral(value) => self.type_store.literal_boolean(*value),
      HirExprKind::Null => self.builtin.null,
      HirExprKind::Ident(name) => {
        let mut ty = self.builtin.unknown;
        if let Some(binding) = env.get(name).cloned() {
          self.record_symbol(file, expr.span, binding.symbol);
          if let Some(t) = binding.type_id {
            ty = t;
          } else if let Some(def_id) = binding.def {
            let resolved = self.type_of_def(def_id);
            ty = resolved;
          }
        } else {
          result.diagnostics.push(codes::UNKNOWN_IDENTIFIER.error(
            format!("Cannot find name '{name}'."),
            Span::new(file, expr.span),
          ));
        }
        if let Some(binding) = env.get_mut(name) {
          if binding.type_id.is_none() {
            binding.type_id = Some(ty);
          }
        }
        let (truthy, falsy) = truthy_falsy_types(ty, &mut self.type_store, &self.builtin);
        if truthy != self.builtin.never {
          facts.truthy.insert(name.clone(), truthy);
        }
        if falsy != self.builtin.never {
          facts.falsy.insert(name.clone(), falsy);
        }
        ty
      }
      HirExprKind::Member { object, property } => {
        let (obj_ty, _) = self.check_expr(object, env, result, file, None);
        let lookup_prop = |obj: &ObjectType| {
          if let Some(prop) = obj.props.get(property) {
            Some(prop.typ)
          } else if property.parse::<usize>().is_ok() {
            obj.number_index.or(obj.string_index)
          } else {
            obj.string_index
          }
        };
        match self.type_store.kind(obj_ty) {
          TypeKind::Object(obj) => lookup_prop(obj).unwrap_or(self.builtin.unknown),
          TypeKind::Union(members) => {
            let members = members.clone();
            let mut collected = Vec::new();
            for member in members {
              if let TypeKind::Object(obj) = self.type_store.kind(member) {
                if let Some(t) = lookup_prop(obj) {
                  collected.push(t);
                }
              }
            }
            if collected.is_empty() {
              self.builtin.unknown
            } else {
              self.type_store.union(collected, &self.builtin)
            }
          }
          _ => self.builtin.unknown,
        }
      }
      HirExprKind::Unary { op, expr: inner } => match op {
        OperatorName::LogicalNot => {
          let (_inner_ty, inner_facts) = self.check_expr(inner, env, result, file, None);
          facts.truthy = inner_facts.falsy;
          facts.falsy = inner_facts.truthy;
          facts.assertions = inner_facts.assertions;
          self.builtin.boolean
        }
        OperatorName::Typeof => self.type_store.literal_string("string".to_string()),
        _ => {
          let _ = self.check_expr(inner, env, result, file, None);
          self.builtin.unknown
        }
      },
      HirExprKind::Binary { op, left, right } => match op {
        OperatorName::LogicalAnd => {
          let (lt, lf) = self.check_expr(left, env, result, file, None);
          let mut right_env = env.clone();
          self.apply_fact_map(&mut right_env, &lf.truthy);
          self.apply_fact_map(&mut right_env, &lf.assertions);
          let (rt, rf) = self.check_expr(right, &mut right_env, result, file, None);

          let rf_truthy = rf.truthy;
          let rf_falsy = rf.falsy;
          let rf_assertions = rf.assertions;

          facts.truthy = rf_truthy;
          facts.falsy = lf.falsy;
          facts.assertions = lf.assertions;
          facts.merge(
            Facts {
              falsy: rf_falsy,
              assertions: rf_assertions,
              ..Default::default()
            },
            &mut self.type_store,
            &self.builtin,
          );

          self.type_store.union(vec![lt, rt], &self.builtin)
        }
        OperatorName::LogicalOr => {
          let (lt, lf) = self.check_expr(left, env, result, file, None);
          let mut right_env = env.clone();
          self.apply_fact_map(&mut right_env, &lf.falsy);
          self.apply_fact_map(&mut right_env, &lf.assertions);
          let (rt, rf) = self.check_expr(right, &mut right_env, result, file, None);

          facts.truthy = lf.truthy;
          facts.merge(
            Facts {
              truthy: rf.truthy,
              ..Default::default()
            },
            &mut self.type_store,
            &self.builtin,
          );
          facts.falsy = rf.falsy;
          facts.assertions = lf.assertions;
          facts.merge(
            Facts {
              assertions: rf.assertions,
              ..Default::default()
            },
            &mut self.type_store,
            &self.builtin,
          );

          self.type_store.union(vec![lt, rt], &self.builtin)
        }
        OperatorName::Equality | OperatorName::StrictEquality => {
          let (_lt, lfacts) = self.check_expr(left, env, result, file, None);
          let (_rt, rfacts) = self.check_expr(right, env, result, file, None);
          // typeof x === "string"
          if let HirExprKind::Unary {
            op: OperatorName::Typeof,
            expr: inner,
          } = &left.kind
          {
            if let HirExprKind::StringLiteral(value) = &right.kind {
              let (inner_ty, _) = self.check_expr(inner, env, result, file, None);
              if let HirExprKind::Ident(name) = &inner.kind {
                let (yes, no) = narrow_by_typeof(
                  inner_ty,
                  value.as_str(),
                  &mut self.type_store,
                  &self.builtin,
                );
                if yes != self.builtin.never {
                  facts.truthy.insert(name.clone(), yes);
                }
                if no != self.builtin.never {
                  facts.falsy.insert(name.clone(), no);
                }
              }
            }
          }
          // discriminant check x.kind === "foo"
          if let HirExprKind::Member { object, property } = &left.kind {
            if let HirExprKind::StringLiteral(value) = &right.kind {
              let (obj_ty, _) = self.check_expr(object, env, result, file, None);
              if let HirExprKind::Ident(obj_name) = &object.kind {
                let (yes, no) = narrow_by_discriminant(
                  obj_ty,
                  property,
                  value,
                  &mut self.type_store,
                  &self.builtin,
                );
                if yes != self.builtin.never {
                  facts.truthy.insert(obj_name.clone(), yes);
                }
                if no != self.builtin.never {
                  facts.falsy.insert(obj_name.clone(), no);
                }
              }
            }
          }
          // symmetric case
          if let HirExprKind::Member { object, property } = &right.kind {
            if let HirExprKind::StringLiteral(value) = &left.kind {
              let (obj_ty, _) = self.check_expr(object, env, result, file, None);
              if let HirExprKind::Ident(obj_name) = &object.kind {
                let (yes, no) = narrow_by_discriminant(
                  obj_ty,
                  property,
                  value,
                  &mut self.type_store,
                  &self.builtin,
                );
                if yes != self.builtin.never {
                  facts.truthy.insert(obj_name.clone(), yes);
                }
                if no != self.builtin.never {
                  facts.falsy.insert(obj_name.clone(), no);
                }
              }
            }
          }
          facts.merge(lfacts, &mut self.type_store, &self.builtin);
          facts.merge(rfacts, &mut self.type_store, &self.builtin);
          self.builtin.boolean
        }
        OperatorName::Instanceof => {
          let (lt, lf) = self.check_expr(left, env, result, file, None);
          let (_rt, rf) = self.check_expr(right, env, result, file, None);
          facts.merge(lf, &mut self.type_store, &self.builtin);
          facts.merge(rf, &mut self.type_store, &self.builtin);
          if let HirExprKind::Ident(name) = &left.kind {
            let (yes, no) = narrow_by_instanceof(lt, &mut self.type_store, &self.builtin);
            if yes != self.builtin.never {
              facts.truthy.insert(name.clone(), yes);
            }
            if no != self.builtin.never {
              facts.falsy.insert(name.clone(), no);
            }
          }
          self.builtin.boolean
        }
        OperatorName::In => {
          let (_lt, lf) = self.check_expr(left, env, result, file, None);
          let (rt, rf) = self.check_expr(right, env, result, file, None);
          if let HirExprKind::StringLiteral(prop) = &left.kind {
            if let HirExprKind::Ident(name) = &right.kind {
              let (yes, no) = narrow_by_in_check(rt, prop, &mut self.type_store, &self.builtin);
              if yes != self.builtin.never {
                facts.truthy.insert(name.clone(), yes);
              }
              if no != self.builtin.never {
                facts.falsy.insert(name.clone(), no);
              }
            }
          }
          facts.merge(lf, &mut self.type_store, &self.builtin);
          facts.merge(rf, &mut self.type_store, &self.builtin);
          self.builtin.boolean
        }
        _ => {
          let (left_ty, lfacts) = self.check_expr(left, env, result, file, None);
          let (right_ty, rfacts) = self.check_expr(right, env, result, file, None);
          facts.merge(lfacts, &mut self.type_store, &self.builtin);
          facts.merge(rfacts, &mut self.type_store, &self.builtin);
          match op {
            OperatorName::Addition => {
              let left_kind = self.type_store.kind(left_ty);
              let right_kind = self.type_store.kind(right_ty);
              let left_is_string =
                matches!(left_kind, TypeKind::String | TypeKind::LiteralString(_));
              let right_is_string =
                matches!(right_kind, TypeKind::String | TypeKind::LiteralString(_));
              let left_is_number =
                matches!(left_kind, TypeKind::Number | TypeKind::LiteralNumber(_));
              let right_is_number =
                matches!(right_kind, TypeKind::Number | TypeKind::LiteralNumber(_));
              if left_is_string || right_is_string {
                self.builtin.string
              } else if left_is_number && right_is_number {
                self.builtin.number
              } else {
                self
                  .type_store
                  .union(vec![left_ty, right_ty], &self.builtin)
              }
            }
            OperatorName::Subtraction
            | OperatorName::Multiplication
            | OperatorName::Division
            | OperatorName::Remainder
            | OperatorName::BitwiseAnd
            | OperatorName::BitwiseOr
            | OperatorName::BitwiseXor
            | OperatorName::BitwiseLeftShift
            | OperatorName::BitwiseRightShift
            | OperatorName::BitwiseUnsignedRightShift => self.builtin.number,
            OperatorName::GreaterThan
            | OperatorName::GreaterThanOrEqual
            | OperatorName::LessThan
            | OperatorName::LessThanOrEqual => self.builtin.boolean,
            OperatorName::Inequality | OperatorName::StrictInequality => self.builtin.boolean,
            _ => self.builtin.unknown,
          }
        }
      },
      HirExprKind::Call { callee, args } => {
        let (callee_ty, _) = self.check_expr(callee, env, result, file, None);
        if let TypeKind::Function { params, ret } = self.type_store.kind(callee_ty).clone() {
          if params.len() != args.len() {
            result
              .diagnostics
              .push(codes::ARGUMENT_COUNT_MISMATCH.error(
                "argument count mismatch",
                Span {
                  file,
                  range: expr.span,
                },
              ));
          }
          let mut arg_types = Vec::new();
          for (idx, arg) in args.iter().enumerate() {
            let expected = params.get(idx).copied();
            let (arg_ty, _) = self.check_expr(arg, env, result, file, expected);
            arg_types.push(arg_ty);
            if let Some(expected) = expected {
              check::assign::check_assignment(self, Some(arg), arg_ty, expected, result, file);
            }
          }
          match self.type_store.kind(ret).clone() {
            TypeKind::Predicate {
              parameter: _parameter,
              asserted,
              asserts,
            } => {
              let arg_ty = arg_types.get(0).copied().unwrap_or(self.builtin.unknown);
              if let Some(first_arg) = args.get(0) {
                if let HirExprKind::Ident(name) = &first_arg.kind {
                  if let Some(asserted_ty) = asserted {
                    if asserts {
                      facts.assertions.insert(name.clone(), asserted_ty);
                    } else {
                      facts.truthy.insert(name.clone(), asserted_ty);
                      let complement = match self.type_store.kind(arg_ty).clone() {
                        TypeKind::Union(members) => {
                          let remaining: Vec<_> =
                            members.into_iter().filter(|m| *m != asserted_ty).collect();
                          self.type_store.union(remaining, &self.builtin)
                        }
                        _ => {
                          if arg_ty == asserted_ty {
                            self.builtin.never
                          } else {
                            arg_ty
                          }
                        }
                      };
                      if complement != self.builtin.never {
                        facts.falsy.insert(name.clone(), complement);
                      }
                    }
                  }
                }
              }
              if asserts {
                self.builtin.void
              } else {
                self.builtin.boolean
              }
            }
            _ => ret,
          }
        } else {
          self.builtin.unknown
        }
      }
      HirExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => {
        let (_, cond_facts) = self.check_expr(test, env, result, file, None);
        let mut then_env = env.clone();
        self.apply_fact_map(&mut then_env, &cond_facts.truthy);
        self.apply_fact_map(&mut then_env, &cond_facts.assertions);
        let mut else_env = env.clone();
        self.apply_fact_map(&mut else_env, &cond_facts.falsy);
        self.apply_fact_map(&mut else_env, &cond_facts.assertions);
        let (cons_ty, cons_facts) =
          self.check_expr(consequent, &mut then_env, result, file, context);
        let (alt_ty, alt_facts) = self.check_expr(alternate, &mut else_env, result, file, context);
        facts.merge(cons_facts, &mut self.type_store, &self.builtin);
        facts.merge(alt_facts, &mut self.type_store, &self.builtin);
        self.type_store.union(vec![cons_ty, alt_ty], &self.builtin)
      }
      HirExprKind::Object(props) => {
        let mut obj = ObjectType::empty();
        for prop in props.iter() {
          if prop.is_spread {
            continue;
          }
          let expected = context
            .and_then(|ctx| check::object_literal::contextual_property_type(self, ctx, &prop.name));
          let (mut ty, _) = self.check_expr(&prop.value, env, result, file, expected.or(context));
          if expected.is_none() && context != Some(self.builtin.never) {
            ty = self.widen_literal(ty);
          }
          if let Some(expected) = expected {
            check::assign::check_assignment(self, Some(&prop.value), ty, expected, result, file);
          }
          obj.props.insert(
            prop.name.clone(),
            ObjectProperty {
              typ: ty,
              optional: false,
              readonly: false,
            },
          );
        }
        self.type_store.object(obj)
      }
      HirExprKind::Array(values) => {
        let mut tys = Vec::new();
        for v in values {
          let (elem, _) = self.check_expr(v, env, result, file, context);
          let widened = if context == Some(self.builtin.never) || context.is_some() {
            elem
          } else {
            self.widen_literal(elem)
          };
          tys.push(widened);
        }
        if context == Some(self.builtin.never) {
          self.type_store.tuple(tys, true)
        } else {
          let elem = self.type_store.union(tys, &self.builtin);
          self.type_store.array(elem)
        }
      }
      HirExprKind::TypeAssertion {
        expr,
        typ,
        _const_assertion,
        make_readonly,
      } => {
        let (inner_ty, inner_facts) = self.check_expr(
          expr,
          env,
          result,
          file,
          _const_assertion.then_some(self.builtin.never),
        );
        facts = inner_facts;
        let ty = (*typ).unwrap_or(inner_ty);
        if *make_readonly {
          self.make_readonly(ty)
        } else {
          ty
        }
      }
      HirExprKind::Unknown => self.builtin.unknown,
    };
    if let Some(slot) = result.expr_types.get_mut(expr.id.0 as usize) {
      *slot = ty;
    }
    (ty, facts)
  }

  fn apply_fact_map(
    &mut self,
    env: &mut HashMap<String, SymbolBinding>,
    facts: &HashMap<String, TypeId>,
  ) {
    for (name, ty) in facts.iter() {
      if let Some(binding) = env.get_mut(name) {
        binding.type_id = Some(*ty);
      }
    }
  }

  fn literal_value_from_expr(&self, expr: &HirExpr) -> Option<LiteralValue> {
    match &expr.kind {
      HirExprKind::StringLiteral(s) => Some(LiteralValue::String(s.clone())),
      HirExprKind::NumberLiteral(n) => Some(LiteralValue::Number(n.clone())),
      HirExprKind::BooleanLiteral(b) => Some(LiteralValue::Boolean(*b)),
      HirExprKind::Null => Some(LiteralValue::Null),
      _ => None,
    }
  }

  fn apply_switch_narrowing(
    &mut self,
    discriminant: &HirExpr,
    discriminant_ty: TypeId,
    test: &HirExpr,
    env: &mut HashMap<String, SymbolBinding>,
    result: &mut BodyCheckResult,
    file: FileId,
  ) {
    if let HirExprKind::Member { object, property } = &discriminant.kind {
      if let HirExprKind::Ident(obj_name) = &object.kind {
        let (obj_ty, _) = self.check_expr(object, env, result, file, None);
        if let Some(LiteralValue::String(value)) = self.literal_value_from_expr(test) {
          let (yes, _) = narrow_by_discriminant(
            obj_ty,
            property,
            &value,
            &mut self.type_store,
            &self.builtin,
          );
          if yes != self.builtin.never {
            if let Some(binding) = env.get_mut(obj_name) {
              binding.type_id = Some(yes);
            }
          }
        }
        return;
      }
    }
    if let HirExprKind::Ident(name) = &discriminant.kind {
      if let Some(lit) = self.literal_value_from_expr(test) {
        let (yes, _) =
          narrow_by_literal(discriminant_ty, &lit, &mut self.type_store, &self.builtin);
        if yes != self.builtin.never {
          if let Some(binding) = env.get_mut(name) {
            binding.type_id = Some(yes);
          }
        }
      }
    }
  }

  fn merge_envs(
    &mut self,
    left: &HashMap<String, SymbolBinding>,
    right: &HashMap<String, SymbolBinding>,
  ) -> HashMap<String, SymbolBinding> {
    let mut merged = left.clone();
    for (name, binding) in right.iter() {
      merged
        .entry(name.clone())
        .and_modify(|existing| {
          existing.type_id = match (existing.type_id, binding.type_id) {
            (Some(a), Some(b)) => Some(self.type_store.union(vec![a, b], &self.builtin)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
          };
        })
        .or_insert_with(|| binding.clone());
    }
    merged
  }

  fn branch_returns(&self, stmts: &[HirStmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
      HirStmt::Return { .. } => true,
      HirStmt::Block(inner) => self.branch_returns(inner),
      HirStmt::If {
        consequent,
        alternate,
        ..
      } => self.branch_returns(consequent) && self.branch_returns(alternate),
      HirStmt::Switch { cases, .. } => {
        let has_default = cases.iter().any(|case| case.test.is_none());
        has_default
          && cases
            .iter()
            .all(|case| self.branch_returns(&case.consequent))
      }
      _ => false,
    })
  }

  fn widen_literal(&self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty) {
      TypeKind::LiteralNumber(_) => self.builtin.number,
      TypeKind::LiteralString(_) => self.builtin.string,
      TypeKind::LiteralBoolean(_) => self.builtin.boolean,
      _ => ty,
    }
  }

  fn make_readonly(&mut self, ty: TypeId) -> TypeId {
    match self.type_store.kind(ty).clone() {
      TypeKind::Object(mut obj) => {
        for prop in obj.props.values_mut() {
          prop.typ = self.make_readonly(prop.typ);
          prop.readonly = true;
        }
        if let Some(idx) = obj.string_index {
          obj.string_index = Some(self.make_readonly(idx));
        }
        if let Some(idx) = obj.number_index {
          obj.number_index = Some(self.make_readonly(idx));
        }
        self.type_store.object(obj)
      }
      TypeKind::Tuple(elems, _readonly) => {
        let mapped: Vec<_> = elems.into_iter().map(|e| self.make_readonly(e)).collect();
        self.type_store.tuple(mapped, true)
      }
      TypeKind::Array(elem) => {
        let elem = self.make_readonly(elem);
        self.type_store.array(elem)
      }
      TypeKind::Union(types) => {
        let mapped: Vec<_> = types.into_iter().map(|t| self.make_readonly(t)).collect();
        self.type_store.union(mapped, &self.builtin)
      }
      _ => ty,
    }
  }

  fn is_assignable(&self, src: TypeId, dst: TypeId) -> bool {
    if src == dst || dst == self.builtin.any || src == self.builtin.never {
      return true;
    }
    if !self.compiler_options.strict_null_checks {
      let src_kind = self.type_store.kind(src);
      let dst_kind = self.type_store.kind(dst);
      if matches!(src_kind, TypeKind::Null | TypeKind::Undefined)
        || matches!(dst_kind, TypeKind::Null | TypeKind::Undefined)
      {
        return true;
      }
    }
    let src_kind = self.type_store.kind(src).clone();
    let dst_kind = self.type_store.kind(dst).clone();
    match (src_kind, dst_kind) {
      (TypeKind::Undefined, TypeKind::Void) | (TypeKind::Void, TypeKind::Undefined) => true,
      (TypeKind::LiteralNumber(_), TypeKind::Number) => true,
      (TypeKind::LiteralString(_), TypeKind::String) => true,
      (TypeKind::LiteralBoolean(_), TypeKind::Boolean) => true,
      (TypeKind::Union(members), _) => members.iter().all(|m| self.is_assignable(*m, dst)),
      (_, TypeKind::Union(members)) => members.iter().any(|m| self.is_assignable(src, *m)),
      (TypeKind::Array(source_elem), TypeKind::Array(target_elem)) => {
        self.is_assignable(source_elem, target_elem)
      }
      (TypeKind::Tuple(source_elems, source_readonly), TypeKind::Array(target_elem)) => {
        if source_readonly {
          return false;
        }
        source_elems
          .iter()
          .copied()
          .all(|elem| self.is_assignable(elem, target_elem))
      }
      (
        TypeKind::Tuple(source_elems, source_readonly),
        TypeKind::Tuple(target_elems, target_readonly),
      ) => {
        if !target_readonly && source_readonly {
          return false;
        }
        if source_elems.len() != target_elems.len() {
          return false;
        }
        source_elems
          .iter()
          .zip(target_elems.iter())
          .all(|(s, t)| self.is_assignable(*s, *t))
      }
      (TypeKind::Object(source_obj), TypeKind::Object(target_obj)) => {
        for (name, target_prop) in target_obj.props.iter() {
          match source_obj.props.get(name) {
            Some(source_prop) => {
              if !self.is_assignable(source_prop.typ, target_prop.typ) {
                return false;
              }
            }
            None => {
              let via_index = if name.parse::<usize>().is_ok() {
                source_obj.number_index.or(source_obj.string_index)
              } else {
                source_obj.string_index
              };
              let Some(index_ty) = via_index else {
                return false;
              };
              if !self.is_assignable(index_ty, target_prop.typ) {
                return false;
              }
            }
          }
        }
        if let Some(target_index) = target_obj.string_index {
          if let Some(source_index) = source_obj.string_index {
            if !self.is_assignable(source_index, target_index) {
              return false;
            }
          }
        }
        if let Some(target_index) = target_obj.number_index {
          if let Some(source_index) = source_obj.number_index.or(source_obj.string_index) {
            if !self.is_assignable(source_index, target_index) {
              return false;
            }
          }
        }
        true
      }
      _ => false,
    }
  }

  fn initial_env(&self, owner: Option<DefId>, file: FileId) -> HashMap<String, SymbolBinding> {
    let mut env = self.global_bindings.clone();
    if let Some(file_env) = self.files.get(&file).map(|f| f.bindings.clone()) {
      env.extend(file_env);
    }
    if let Some(def) = owner {
      if let Some(DefKind::Function(func)) = self.def_data.get(&def).map(|d| &d.kind) {
        for param in func.params.iter() {
          env.insert(
            param.name.clone(),
            SymbolBinding {
              symbol: param.symbol,
              def: None,
              type_id: param.typ,
            },
          );
        }
      }
    }
    env
  }

  fn type_of_def(&mut self, def: DefId) -> TypeId {
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
    if let Some(existing) = self.def_types.get(&def) {
      if let Some(span) = span.take() {
        span.finish(Some(*existing));
      }
      return *existing;
    }
    if self.type_stack.contains(&def) {
      if let Some(span) = span.take() {
        span.finish(Some(self.builtin.any));
      }
      return self.builtin.any;
    }
    self.type_stack.push(def);
    let ty = match self.def_data.get(&def).map(|d| d.kind.clone()) {
      Some(DefKind::Function(func)) => self.function_type(def, func),
      Some(DefKind::Var(var)) => {
        let inferred = if let Some(t) = var.typ {
          t
        } else if let Some(init) = var.init {
          let res = self.check_body(var.body);
          res.expr_type(init).unwrap_or(self.builtin.unknown)
        } else {
          self.builtin.unknown
        };
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
      Some(DefKind::TypeAlias(alias)) => alias.typ,
      None => self.builtin.unknown,
    };
    self.type_stack.pop();
    self.def_types.insert(def, ty);
    if let Some(span) = span.take() {
      span.finish(Some(ty));
    }
    ty
  }

  fn function_type(&mut self, def: DefId, func: FuncData) -> TypeId {
    let param_types: Vec<TypeId> = func
      .params
      .iter()
      .map(|p| p.typ.unwrap_or(self.builtin.any))
      .collect();
    let ret = if let Some(ret) = func.return_ann {
      ret
    } else if let Some(body) = func.body {
      let res = self.check_body(body);
      if res.return_types.is_empty() {
        self.builtin.void
      } else {
        let widened: Vec<_> = res
          .return_types
          .iter()
          .map(|ty| self.widen_literal(*ty))
          .collect();
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
    let mut best_containing: Option<(u32, u32, BodyId, ExprId)> = None;
    let mut best_empty: Option<(u32, u32, BodyId, ExprId)> = None;

    for body in self.body_data.values() {
      if body.file != file {
        continue;
      }
      for (idx, span) in body.expr_spans.iter().enumerate() {
        let expr_id = ExprId(idx as u32);
        let len = span.len();
        let key = (len, span.start, body.id, expr_id);
        if span.start <= offset && offset < span.end {
          let replace = best_containing.map(|best| key < best).unwrap_or(true);
          if replace {
            best_containing = Some(key);
          }
        } else if span.start == span.end && offset == span.start {
          let replace = best_empty.map(|best| key < best).unwrap_or(true);
          if replace {
            best_empty = Some(key);
          }
        }
      }
    }

    best_containing
      .or(best_empty)
      .map(|(_, _, body, expr)| (body, expr))
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
      _ => self.builtin.unknown,
    }
  }

  fn alloc_def(&mut self) -> DefId {
    let id = DefId(self.next_def);
    self.next_def += 1;
    id
  }

  fn alloc_body(&mut self, file: FileId, owner: Option<DefId>) -> BodyId {
    let id = BodyId(self.next_body);
    self.next_body += 1;
    if !self.body_data.contains_key(&id) {
      self.body_data.insert(
        id,
        BodyData {
          id,
          file,
          owner,
          stmts: Vec::new(),
          expr_spans: Vec::new(),
          pat_spans: Vec::new(),
        },
      );
    }
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
struct BodyBuilder {
  id: BodyId,
  file: FileId,
  stmts: Vec<HirStmt>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
}

impl BodyBuilder {
  fn new(id: BodyId, file: FileId) -> BodyBuilder {
    BodyBuilder {
      id,
      file,
      stmts: Vec::new(),
      expr_spans: Vec::new(),
      pat_spans: Vec::new(),
    }
  }

  fn new_expr(&mut self, span: TextRange, kind: HirExprKind) -> HirExpr {
    let id = ExprId(self.expr_spans.len() as u32);
    self.expr_spans.push(span);
    HirExpr { id, span, kind }
  }

  fn new_pat(&mut self, span: TextRange) -> PatId {
    let id = PatId(self.pat_spans.len() as u32);
    self.pat_spans.push(span);
    id
  }

  fn lower_stmt_into(
    &mut self,
    stmt: Node<Stmt>,
    state: &mut ProgramState,
    out: &mut Vec<HirStmt>,
  ) {
    match *stmt.stx {
      Stmt::VarDecl(var) => {
        let stmt_span = loc_to_span(self.file, stmt.loc).range;
        for declarator in var.stx.declarators.into_iter() {
          let pat = declarator.pattern;
          let name = match pat.stx.pat.stx.as_ref() {
            Pat::Id(id) => id.stx.name.clone(),
            _ => {
              state.diagnostics.push(
                codes::UNSUPPORTED_PATTERN
                  .error("unsupported pattern", loc_to_span(self.file, pat.loc)),
              );
              continue;
            }
          };
          let typ = declarator
            .type_annotation
            .as_ref()
            .map(|t| state.type_from_type_expr(t));
          let pat_id = Some(self.new_pat(loc_to_span(self.file, pat.loc).range));
          let init = declarator
            .initializer
            .map(|expr| self.lower_expr(expr, state));
          let symbol = state.alloc_symbol();
          state.record_symbol(self.file, loc_to_span(self.file, pat.loc).range, symbol);
          out.push(HirStmt::Var {
            name,
            typ,
            init,
            span: stmt_span,
            symbol,
            def: None,
            pat: pat_id,
          });
        }
      }
      Stmt::Return(ret) => {
        let expr = ret.stx.value.map(|e| self.lower_expr(e, state));
        out.push(HirStmt::Return {
          expr,
          span: loc_to_span(self.file, ret.loc).range,
        });
      }
      Stmt::Expr(expr_stmt) => {
        let expr = self.lower_expr(expr_stmt.stx.expr, state);
        out.push(HirStmt::Expr(expr));
      }
      Stmt::Block(block) => {
        let mut inner = Vec::new();
        for stmt in block.stx.body {
          self.lower_stmt_into(stmt, state, &mut inner);
        }
        out.push(HirStmt::Block(inner));
      }
      Stmt::If(if_stmt) => {
        let test = self.lower_expr(if_stmt.stx.test, state);
        let mut consequent = Vec::new();
        self.lower_stmt_into(if_stmt.stx.consequent, state, &mut consequent);
        let mut alternate_vec = Vec::new();
        if let Some(alt) = if_stmt.stx.alternate {
          self.lower_stmt_into(alt, state, &mut alternate_vec);
        }
        out.push(HirStmt::If {
          test,
          consequent,
          alternate: alternate_vec,
          span: loc_to_span(self.file, if_stmt.loc).range,
        });
      }
      Stmt::While(wh) => {
        let test = self.lower_expr(wh.stx.condition, state);
        let mut body_stmts = Vec::new();
        self.lower_stmt_into(wh.stx.body, state, &mut body_stmts);
        out.push(HirStmt::While {
          test,
          body: body_stmts,
          span: loc_to_span(self.file, wh.loc).range,
        });
      }
      Stmt::Switch(sw) => {
        let discriminant = self.lower_expr(sw.stx.test, state);
        let mut cases = Vec::new();
        for branch in sw.stx.branches {
          let test = branch.stx.case.map(|expr| self.lower_expr(expr, state));
          let mut consequent = Vec::new();
          for stmt in branch.stx.body {
            self.lower_stmt_into(stmt, state, &mut consequent);
          }
          cases.push(HirSwitchCase { test, consequent });
        }
        out.push(HirStmt::Switch {
          discriminant,
          cases,
          span: loc_to_span(self.file, sw.loc).range,
        });
      }
      _ => {}
    }
  }

  fn lower_stmt(&mut self, stmt: Node<Stmt>, state: &mut ProgramState) {
    let mut out = Vec::new();
    self.lower_stmt_into(stmt, state, &mut out);
    self.stmts.extend(out);
  }

  fn lower_expr(&mut self, expr: Node<Expr>, state: &mut ProgramState) -> HirExpr {
    let mut span = loc_to_span(self.file, expr.loc).range;
    let kind = match *expr.stx {
      Expr::LitNum(num) => HirExprKind::NumberLiteral(num.stx.value.to_string()),
      Expr::LitStr(s) => HirExprKind::StringLiteral(s.stx.value),
      Expr::LitBool(b) => HirExprKind::BooleanLiteral(b.stx.value),
      Expr::LitNull(_) => HirExprKind::Null,
      Expr::Id(id) => {
        let name = id.stx.name.clone();
        let expected_end = span
          .start
          .saturating_add(name.len().min(u32::MAX as usize) as u32);
        if expected_end <= span.end {
          span.end = expected_end;
        }
        if span.len() == 0 {
          span.start = span
            .start
            .saturating_sub(name.len().min(u32::MAX as usize) as u32);
        }
        HirExprKind::Ident(name)
      }
      Expr::Member(mem) => {
        let object = self.lower_expr(mem.stx.left, state);
        HirExprKind::Member {
          object: Box::new(object),
          property: mem.stx.right,
        }
      }
      Expr::Unary(unary) => {
        let arg = self.lower_expr(unary.stx.argument, state);
        HirExprKind::Unary {
          op: unary.stx.operator,
          expr: Box::new(arg),
        }
      }
      Expr::Binary(bin) => {
        let left = self.lower_expr(bin.stx.left, state);
        let right = self.lower_expr(bin.stx.right, state);
        HirExprKind::Binary {
          op: bin.stx.operator,
          left: Box::new(left),
          right: Box::new(right),
        }
      }
      Expr::Call(call) => {
        let callee = self.lower_expr(call.stx.callee, state);
        let mut args = Vec::new();
        for arg in call.stx.arguments.into_iter() {
          args.push(self.lower_expr(arg.stx.value, state));
        }
        HirExprKind::Call {
          callee: Box::new(callee),
          args,
        }
      }
      Expr::Cond(cond) => {
        let test = self.lower_expr(cond.stx.test, state);
        let cons = self.lower_expr(cond.stx.consequent, state);
        let alt = self.lower_expr(cond.stx.alternate, state);
        HirExprKind::Conditional {
          test: Box::new(test),
          consequent: Box::new(cons),
          alternate: Box::new(alt),
        }
      }
      Expr::SatisfiesExpr(satisfies) => {
        let expr = self.lower_expr(*satisfies.stx.expression, state);
        HirExprKind::TypeAssertion {
          expr: Box::new(expr),
          typ: None,
          _const_assertion: true,
          make_readonly: false,
        }
      }
      Expr::LitArr(arr) => {
        let mut values = Vec::new();
        for el in arr.stx.elements.into_iter() {
          match el {
            LitArrElem::Single(expr) => values.push(self.lower_expr(expr, state)),
            LitArrElem::Rest(expr) => values.push(self.lower_expr(expr, state)),
            LitArrElem::Empty => {}
          }
        }
        HirExprKind::Array(values)
      }
      Expr::LitObj(obj) => {
        HirExprKind::Object(lower_object_literal(self.file, *obj.stx, state, self))
      }
      Expr::LitTemplate(tmpl) => {
        let mut text = String::new();
        for part in tmpl.stx.parts.iter() {
          if let parse_js::ast::expr::lit::LitTemplatePart::String(s) = part {
            text.push_str(s);
          }
        }
        HirExprKind::StringLiteral(text)
      }
      Expr::TypeAssertion(assert) => {
        let expr = self.lower_expr(*assert.stx.expression, state);
        let typ = assert
          .stx
          .type_annotation
          .as_ref()
          .map(|t| state.type_from_type_expr(t));
        HirExprKind::TypeAssertion {
          expr: Box::new(expr),
          typ,
          _const_assertion: assert.stx.const_assertion,
          make_readonly: assert.stx.const_assertion,
        }
      }
      _ => HirExprKind::Unknown,
    };

    let id = ExprId(self.expr_spans.len() as u32);
    self.expr_spans.push(span);
    HirExpr { id, span, kind }
  }

  fn finish(mut self, owner: Option<DefId>) -> BodyData {
    BodyData {
      id: self.id,
      file: self.file,
      owner,
      stmts: self.stmts.drain(..).collect(),
      expr_spans: self.expr_spans,
      pat_spans: self.pat_spans,
    }
  }
}

fn lower_object_literal(
  file: FileId,
  obj: LitObjExpr,
  state: &mut ProgramState,
  builder: &mut BodyBuilder,
) -> Vec<HirObjectProperty> {
  let mut props = Vec::new();
  for member in obj.members.into_iter() {
    let member_span = loc_to_span(file, member.loc).range;
    match *member.stx {
      ObjMember {
        typ: ObjMemberType::Valued { key, val },
      } => {
        let key_name = match key {
          ClassOrObjKey::Direct(direct) => direct.stx.key,
          ClassOrObjKey::Computed(_) => {
            // Skip complex computed keys for now.
            continue;
          }
        };
        if let ClassOrObjVal::Prop(Some(expr)) = val {
          let value = builder.lower_expr(expr, state);
          props.push(HirObjectProperty {
            name: key_name,
            value,
            span: member_span,
            is_spread: false,
          });
        }
      }
      ObjMember {
        typ: ObjMemberType::Shorthand { id },
      } => {
        let name = id.stx.name.clone();
        let expr = builder.new_expr(
          loc_to_span(file, id.loc).range,
          HirExprKind::Ident(name.clone()),
        );
        props.push(HirObjectProperty {
          name,
          value: expr,
          span: member_span,
          is_spread: false,
        });
      }
      ObjMember {
        typ: ObjMemberType::Rest { val },
      } => {
        let expr = builder.lower_expr(val, state);
        props.push(HirObjectProperty {
          name: "...".to_string(),
          value: expr,
          span: member_span,
          is_spread: true,
        });
      }
    }
  }
  props
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
