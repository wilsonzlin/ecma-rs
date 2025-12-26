use ::semantic_js::ts as sem_ts;
use ::semantic_js::ts::from_hir_js::lower_to_ts_hir;
use ::semantic_js::ts::locals as sem_locals;
pub use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{lower_file, DefKind as HirDefKind, FileKind as HirFileKind, LowerResult};
pub use hir_js::{BodyId, DefId, ExprId, PatId};
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
  TypeArray, TypeEntityName, TypeExpr, TypeFunctionParameter, TypeLiteral, TypeMember,
  TypePropertyKey, TypeTupleElement, TypeUnion,
};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::parse;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;
use tracing::debug_span;
pub use types_ts_interned::TypeId;
pub use types_ts_interned::TypeKind;
pub use types_ts_interned::TypeStore;
use types_ts_interned::{
  ExpandedType, Indexer, ObjectType as InternedObjectType, Param, PropData, PropKey,
  Property as TsProperty, RelateCtx, RelateHooks, Signature, SignatureId, TupleElem,
  TypeDisplay as InternedTypeDisplay, TypeExpander,
};

use crate::type_queries::{
  IndexerInfo, PropertyInfo, PropertyKey, SignatureInfo, TypeKindSummary, TypeQueries,
};
use crate::{FatalError, HostError, Ice, IceContext};

#[path = "check/mod.rs"]
pub(crate) mod check;

use check::narrow::{
  narrow_by_discriminant, narrow_by_in_check, narrow_by_typeof, truthy_falsy_types, Facts,
};

use crate::lib_support::{CompilerOptions, FileKind, LibFile, LibManager};
pub(crate) const CODE_MISSING_LIB: &str = "TC0001";
pub(crate) const CODE_NON_DTS_LIB: &str = "TC0004";
pub(crate) const CODE_UNKNOWN_IDENTIFIER: &str = "TC0005";
pub(crate) const CODE_EXCESS_PROPERTY: &str = "TC0006";
pub(crate) const CODE_TYPE_MISMATCH: &str = "TC0007";
const CODE_UNRESOLVED_MODULE: &str = "TC1001";
const CODE_UNKNOWN_EXPORT: &str = "TC1002";
const CODE_UNSUPPORTED_IMPORT_PATTERN: &str = "TC1003";
const CODE_UNSUPPORTED_PATTERN: &str = "TC1004";
const CODE_UNSUPPORTED_PARAM_PATTERN: &str = "TC1005";
const CODE_MISSING_BODY: &str = "ICE0002";
const CODE_ARGUMENT_COUNT_MISMATCH: &str = "TC1006";
const LOCAL_SYMBOL_OFFSET: u32 = 1 << 31;

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

/// Per-body typing result. Expression IDs are local to the body.
#[allow(dead_code)]
#[derive(Debug)]
pub struct BodyCheckResult {
  body: BodyId,
  expr_types: Vec<TypeId>,
  expr_spans: Vec<TextRange>,
  pat_types: Vec<TypeId>,
  diagnostics: Vec<Diagnostic>,
  return_types: Vec<TypeId>,
}

impl BodyCheckResult {
  /// Diagnostics produced while checking this body.
  pub fn diagnostics(&self) -> &[Diagnostic] {
    &self.diagnostics
  }

  /// Type for a specific expression, if known.
  pub fn expr_type(&self, expr: ExprId) -> Option<TypeId> {
    self.expr_types.get(expr.0 as usize).copied()
  }

  /// Span for a specific expression.
  pub fn expr_span(&self, expr: ExprId) -> Option<TextRange> {
    self.expr_spans.get(expr.0 as usize).copied()
  }

  /// Type for a specific pattern, if known.
  pub fn pat_type(&self, pat: PatId) -> Option<TypeId> {
    self.pat_types.get(pat.0 as usize).copied()
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
pub struct TypeDisplay<'a> {
  store: Arc<TypeStore>,
  ty: TypeId,
  ref_resolver: Option<Arc<dyn Fn(types_ts_interned::DefId) -> Option<String> + Send + Sync + 'a>>,
  _marker: std::marker::PhantomData<&'a ()>,
}

impl<'a> std::fmt::Display for TypeDisplay<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let display = InternedTypeDisplay::new(self.store.as_ref(), self.ty);
    let display = match &self.ref_resolver {
      Some(resolver) => display.with_ref_resolver(Arc::clone(resolver)),
      None => display,
    };
    display.fmt(f)
  }
}

/// Primary entry point for parsing and type checking.
pub struct Program {
  host: Arc<dyn Host>,
  roots: Vec<FileId>,
  cancelled: AtomicBool,
  state: std::sync::Mutex<ProgramState>,
}

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
    Program {
      host: Arc::new(host),
      roots,
      cancelled: AtomicBool::new(false),
      state: std::sync::Mutex::new(ProgramState::new(lib_manager)),
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
      let mut body_ids: Vec<BodyId> = state.body_data.keys().copied().collect();
      body_ids.sort_by_key(|id| id.0);
      let mut diagnostics = state.diagnostics.clone();
      for body in body_ids {
        self.ensure_not_cancelled()?;
        let res = state.check_body(body);
        diagnostics.extend(res.diagnostics.iter().cloned());
      }
      Ok(diagnostics)
    })
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

  fn with_type_queries<R>(
    &self,
    f: impl FnOnce(TypeQueries<'_, ProgramTypeExpander<'_>>) -> R,
  ) -> Result<R, FatalError> {
    let store = self.with_analyzed_state(|state| Ok(Arc::clone(&state.type_store)))?;
    let expander = ProgramTypeExpander { program: self };
    let queries = TypeQueries::new(store, &expander);
    Ok(f(queries))
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

  /// Interned type ID for a definition (identical to [`type_of_def`] for interned types).
  pub fn type_of_def_interned(&self, def: DefId) -> TypeId {
    self.type_of_def(def)
  }

  pub fn type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.type_of_def_fallible(def)
  }

  /// Helper to render an interned type using the program's store.
  pub fn display_interned_type(&self, ty: TypeId) -> TypeDisplay<'_> {
    self.display_type(ty)
  }

  /// Interned type kind for a given ID.
  pub fn interned_type_kind(&self, ty: TypeId) -> TypeKind {
    let state = self.lock_state();
    state.type_store.type_kind(ty)
  }

  /// Coarse summary of an interned type after expanding references.
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
    self.with_type_queries(|queries| queries.type_kind(ty))
  }

  /// Deterministic list of properties on an interned type. Union and
  /// intersection semantics mirror [`TypeQueries::properties_of`].
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
    self.with_type_queries(|queries| queries.properties_of(ty))
  }

  /// Type of a specific property on an interned type, considering index
  /// signatures if present.
  pub fn property_type(&self, ty: TypeId, key: PropertyKey) -> Option<TypeId> {
    match self.property_type_fallible(ty, key) {
      Ok(prop) => prop,
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
    self.with_type_queries(|queries| queries.property_type(ty, key))
  }

  /// Call signatures available on the given type. Overload order is stable.
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
    self.with_type_queries(|queries| queries.call_signatures(ty))
  }

  /// Construct signatures available on the given type. Overload order is
  /// stable.
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
    self.with_type_queries(|queries| queries.construct_signatures(ty))
  }

  /// Index signatures available on the given type.
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
    self.with_type_queries(|queries| queries.indexers(ty))
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
    let host = Arc::clone(&self.host);
    let roots = self.roots.clone();
    self.with_analyzed_state(|state| {
      state.ensure_symbols_for_file(file);
      Ok(state.symbol_at(file, offset, &host, &roots))
    })
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
    self.with_analyzed_state(|state| Ok(state.exports_of_file(file)))
  }

  /// Helper to render a type as displayable string.
  pub fn display_type(&self, ty: TypeId) -> TypeDisplay<'_> {
    let mut state = self.lock_state();
    state.ensure_analyzed(&self.host, &self.roots, &self.cancelled);
    let store = Arc::clone(&state.type_store);
    let def_names: Arc<HashMap<_, _>> = Arc::new(
      state
        .def_data
        .iter()
        .map(|(id, data)| (*id, data.name.clone()))
        .collect(),
    );
    let resolver: Arc<dyn Fn(types_ts_interned::DefId) -> Option<String> + Send + Sync> =
      Arc::new({
        let def_names = Arc::clone(&def_names);
        move |def| def_names.get(&def).cloned()
      });
    TypeDisplay {
      store,
      ty,
      ref_resolver: Some(resolver),
      _marker: std::marker::PhantomData,
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
        DefKind::Import(_) | DefKind::Type(_) => None,
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
}

#[derive(Clone, Debug)]
struct SymbolOccurrence {
  range: TextRange,
  symbol: semantic_js::SymbolId,
}

#[derive(Clone, Debug)]
struct SymbolBinding {
  symbol: semantic_js::SymbolId,
  def: Option<DefId>,
  type_id: Option<TypeId>,
}

#[derive(Clone)]
struct FileState {
  defs: Vec<DefId>,
  exports: ExportMap,
  bindings: HashMap<String, SymbolBinding>,
  top_body: Option<BodyId>,
}

struct PendingReexport {
  source: FileId,
  target: FileId,
  name: String,
  span: TextRange,
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

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct DefData {
  name: String,
  file: FileId,
  span: TextRange,
  symbol: semantic_js::SymbolId,
  export: bool,
  kind: DefKind,
}

#[derive(Clone, Debug)]
enum DefKind {
  Function(FuncData),
  Var(VarData),
  Import(ImportData),
  Type(TypeData),
}

#[derive(Clone, Debug)]
struct FuncData {
  params: Vec<ParamData>,
  return_ann: Option<TypeId>,
  body: Option<BodyId>,
  predicate: Option<PredicateInfo>,
}

#[derive(Clone, Debug)]
struct ParamData {
  name: String,
  typ: Option<TypeId>,
  symbol: semantic_js::SymbolId,
}

#[derive(Clone, Debug)]
struct VarData {
  typ: Option<TypeId>,
  init: Option<ExprId>,
  body: BodyId,
  mode: VarDeclMode,
}

#[derive(Clone, Debug)]
struct ImportData {
  from: FileId,
  original: String,
}

#[derive(Clone, Debug)]
struct TypeData {
  ty: TypeId,
  type_expr: Option<Arc<Node<TypeExpr>>>,
}

#[derive(Clone, Debug)]
struct SemHirBuilder {
  file: FileId,
  decls: Vec<sem_ts::Decl>,
  imports: Vec<sem_ts::Import>,
  exports: Vec<sem_ts::Export>,
}

impl SemHirBuilder {
  fn new(file: FileId) -> Self {
    SemHirBuilder {
      file,
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
      file_kind: sem_ts::FileKind::Ts,
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
}

#[derive(Clone, Debug)]
struct HirExpr {
  id: ExprId,
  span: TextRange,
  kind: HirExprKind,
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
  Object(Vec<(String, HirExpr)>),
  TypeAssertion {
    expr: Box<HirExpr>,
    typ: Option<TypeId>,
    _const_assertion: bool,
  },
  Array(Vec<HirExpr>),
  Unknown,
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(crate) struct BuiltinTypes {
  pub(crate) any: TypeId,
  pub(crate) unknown: TypeId,
  pub(crate) never: TypeId,
  pub(crate) void: TypeId,
  pub(crate) number: TypeId,
  pub(crate) string: TypeId,
  pub(crate) boolean: TypeId,
  pub(crate) null: TypeId,
  pub(crate) undefined: TypeId,
  pub(crate) object: TypeId,
}

impl BuiltinTypes {
  fn from_store(store: &Arc<TypeStore>) -> Self {
    let primitives = store.primitive_ids();
    let empty_shape = store.intern_shape(types_ts_interned::Shape::new());
    let object = store.intern_type(TypeKind::Object(
      store.intern_object(types_ts_interned::ObjectType { shape: empty_shape }),
    ));
    BuiltinTypes {
      any: primitives.any,
      unknown: primitives.unknown,
      never: primitives.never,
      void: primitives.void,
      number: primitives.number,
      string: primitives.string,
      boolean: primitives.boolean,
      null: primitives.null,
      undefined: primitives.undefined,
      object,
    }
  }
}

#[derive(Clone, Debug)]
struct PredicateInfo {
  parameter: String,
  asserted: Option<TypeId>,
  asserts: bool,
}

pub(crate) fn lookup_property_type(
  store: &TypeStore,
  obj_ty: TypeId,
  name: &str,
) -> Option<TypeId> {
  let TypeKind::Object(obj_id) = store.type_kind(obj_ty) else {
    return None;
  };
  let shape = store.shape(store.object(obj_id).shape);
  for prop in shape.properties.iter() {
    if let PropKey::String(id) = prop.key {
      if store.name(id) == name {
        return Some(prop.data.ty);
      }
    }
  }
  let is_number = name.parse::<i64>().is_ok();
  for idx in shape.indexers.iter() {
    match store.type_kind(idx.key_type) {
      TypeKind::String | TypeKind::StringLiteral(_) => return Some(idx.value_type),
      TypeKind::Number | TypeKind::NumberLiteral(_) if is_number => return Some(idx.value_type),
      _ => {}
    }
  }
  None
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
}

impl QuerySpan {
  fn enter(span: tracing::Span, type_id: Option<TypeId>) -> Option<QuerySpan> {
    if span.is_disabled() {
      return None;
    }
    if let Some(ty) = type_id {
      span.record("type_id", ty.0);
    }
    let _guard = span.enter();
    drop(_guard);
    Some(QuerySpan {
      span,
      start: Instant::now(),
    })
  }

  fn finish(self, type_id: Option<TypeId>) {
    if let Some(ty) = type_id {
      self.span.record("type_id", ty.0);
    }
    self
      .span
      .record("duration_ms", self.start.elapsed().as_secs_f64() * 1000.0);
  }
}

struct ProgramTypeExpander<'a> {
  program: &'a Program,
}

impl<'a> TypeExpander for ProgramTypeExpander<'a> {
  fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
    Some(ExpandedType {
      params: Vec::new(),
      ty: self.program.type_of_def(def),
    })
  }
}

struct ProgramState {
  analyzed: bool,
  lib_manager: Arc<LibManager>,
  compiler_options: CompilerOptions,
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  body_data: HashMap<BodyId, BodyData>,
  sem_hir: HashMap<FileId, sem_ts::HirFile>,
  semantics: Option<sem_ts::TsProgramSemantics>,
  hir_lowered: HashMap<FileId, Arc<LowerResult>>,
  hir_locals: HashMap<FileId, sem_locals::TsLocalSemantics>,
  hir_semantics: Option<sem_ts::TsProgramSemantics>,
  hir_sem_hir: HashMap<FileId, Arc<sem_ts::HirFile>>,
  def_types: HashMap<DefId, TypeId>,
  body_results: HashMap<BodyId, Arc<BodyCheckResult>>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  symbol_to_def: HashMap<semantic_js::SymbolId, DefId>,
  file_kinds: HashMap<FileId, FileKind>,
  lib_texts: HashMap<FileId, Arc<str>>,
  global_bindings: HashMap<String, SymbolBinding>,
  diagnostics: Vec<Diagnostic>,
  type_store: Arc<TypeStore>,
  builtin: BuiltinTypes,
  predicates: HashMap<DefId, PredicateInfo>,
  next_def: u32,
  next_body: u32,
  next_symbol: u32,
  type_stack: Vec<DefId>,
  pending_reexports: Vec<PendingReexport>,
}

impl ProgramState {
  pub(crate) fn relate_ctx(&self) -> RelateCtx<'_> {
    RelateCtx::with_hooks(
      Arc::clone(&self.type_store),
      self.type_store.options(),
      RelateHooks::default(),
    )
  }

  fn literal_string(&self, value: &str) -> TypeId {
    let id = self.type_store.intern_name(value.to_string());
    self.type_store.intern_type(TypeKind::StringLiteral(id))
  }

  fn literal_number(&self, value: &str) -> TypeId {
    let parsed = value.parse::<f64>().unwrap_or(0.0);
    self
      .type_store
      .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(parsed)))
  }

  fn literal_boolean(&self, value: bool) -> TypeId {
    self.type_store.intern_type(TypeKind::BooleanLiteral(value))
  }

  fn array_type(&self, element: TypeId) -> TypeId {
    self.type_store.intern_type(TypeKind::Array {
      ty: element,
      readonly: false,
    })
  }

  fn callable_type(&self, params: Vec<TypeId>, ret: TypeId, this_param: Option<TypeId>) -> TypeId {
    let sig = Signature {
      params: params
        .into_iter()
        .map(|ty| Param {
          name: None,
          ty,
          optional: false,
          rest: false,
        })
        .collect(),
      ret,
      type_params: Vec::new(),
      this_param,
    };
    self.type_store.intern_type(TypeKind::Callable {
      overloads: vec![self.type_store.intern_signature(sig)],
    })
  }

  fn union_types(&self, members: Vec<TypeId>) -> TypeId {
    self.type_store.union(members)
  }

  fn widen_literal(&self, ty: TypeId) -> TypeId {
    match self.type_store.type_kind(ty) {
      TypeKind::NumberLiteral(_) => self.builtin.number,
      TypeKind::StringLiteral(_) => self.builtin.string,
      TypeKind::BooleanLiteral(_) => self.builtin.boolean,
      TypeKind::Union(members) => {
        let widened: Vec<TypeId> = members.into_iter().map(|t| self.widen_literal(t)).collect();
        self.type_store.union(widened)
      }
      _ => ty,
    }
  }

  /// Recursively widen literal primitives within composite types.
  fn widen_type(&self, ty: TypeId) -> TypeId {
    match self.type_store.type_kind(ty) {
      TypeKind::BooleanLiteral(_) | TypeKind::NumberLiteral(_) | TypeKind::StringLiteral(_) => {
        self.widen_literal(ty)
      }
      TypeKind::Union(members) => {
        let widened: Vec<TypeId> = members.into_iter().map(|m| self.widen_type(m)).collect();
        self.union_types(widened)
      }
      TypeKind::Array { ty: elem, readonly } => {
        let widened_elem = self.widen_type(elem);
        if widened_elem == elem {
          ty
        } else {
          self.type_store.intern_type(TypeKind::Array {
            ty: widened_elem,
            readonly,
          })
        }
      }
      TypeKind::Tuple(elems) => {
        let mut changed = false;
        let new_elems: Vec<_> = elems
          .into_iter()
          .map(|mut elem| {
            let widened = self.widen_type(elem.ty);
            changed |= widened != elem.ty;
            elem.ty = widened;
            elem
          })
          .collect();
        if changed {
          self.type_store.intern_type(TypeKind::Tuple(new_elems))
        } else {
          ty
        }
      }
      TypeKind::Object(obj_id) => {
        let object = self.type_store.object(obj_id);
        let shape = self.type_store.shape(object.shape);
        let mut changed = false;
        let properties: Vec<_> = shape
          .properties
          .iter()
          .map(|prop| {
            let widened = self.widen_type(prop.data.ty);
            changed |= widened != prop.data.ty;
            TsProperty {
              key: prop.key.clone(),
              data: PropData {
                ty: widened,
                optional: prop.data.optional,
                readonly: prop.data.readonly,
                accessibility: prop.data.accessibility,
                is_method: prop.data.is_method,
                origin: prop.data.origin,
                declared_on: prop.data.declared_on,
              },
            }
          })
          .collect();
        let indexers: Vec<_> = shape
          .indexers
          .iter()
          .map(|idx| {
            let widened = self.widen_type(idx.value_type);
            changed |= widened != idx.value_type;
            Indexer {
              key_type: idx.key_type,
              value_type: widened,
              readonly: idx.readonly,
            }
          })
          .collect();
        if changed {
          let shape = self.type_store.intern_shape(types_ts_interned::Shape {
            properties,
            call_signatures: shape.call_signatures.clone(),
            construct_signatures: shape.construct_signatures.clone(),
            indexers,
          });
          self.type_store.intern_type(TypeKind::Object(
            self.type_store.intern_object(InternedObjectType { shape }),
          ))
        } else {
          ty
        }
      }
      _ => ty,
    }
  }

  fn const_assertion_type(
    &self,
    expr: &HirExpr,
    result: &BodyCheckResult,
    fallback: TypeId,
  ) -> TypeId {
    match &expr.kind {
      HirExprKind::Array(values) => {
        let elems: Vec<_> = values
          .iter()
          .map(|value| TupleElem {
            ty: result
              .expr_types
              .get(value.id.0 as usize)
              .copied()
              .unwrap_or(self.builtin.unknown),
            optional: false,
            rest: false,
            readonly: true,
          })
          .collect();
        self.type_store.intern_type(TypeKind::Tuple(elems))
      }
      HirExprKind::Object(props) => {
        let mut properties = Vec::new();
        for (name, value) in props {
          if name == "..." {
            continue;
          }
          let ty = result
            .expr_types
            .get(value.id.0 as usize)
            .copied()
            .unwrap_or(self.builtin.unknown);
          properties.push(TsProperty {
            key: PropKey::String(self.type_store.intern_name(name.clone())),
            data: PropData {
              ty,
              optional: false,
              readonly: false,
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          });
        }
        self.object_type_from_parts(properties, Vec::new(), Vec::new(), Vec::new())
      }
      _ => fallback,
    }
  }

  fn object_type_from_parts(
    &self,
    properties: Vec<TsProperty>,
    call_signatures: Vec<SignatureId>,
    construct_signatures: Vec<SignatureId>,
    indexers: Vec<Indexer>,
  ) -> TypeId {
    let shape = self.type_store.intern_shape(types_ts_interned::Shape {
      properties,
      call_signatures,
      construct_signatures,
      indexers,
    });
    self.type_store.intern_type(TypeKind::Object(
      self.type_store.intern_object(InternedObjectType { shape }),
    ))
  }

  fn new(lib_manager: Arc<LibManager>) -> ProgramState {
    let type_store = TypeStore::new();
    let builtin = BuiltinTypes::from_store(&type_store);
    ProgramState {
      analyzed: false,
      lib_manager,
      compiler_options: CompilerOptions::default(),
      files: HashMap::new(),
      def_data: HashMap::new(),
      body_data: HashMap::new(),
      sem_hir: HashMap::new(),
      semantics: None,
      hir_lowered: HashMap::new(),
      hir_locals: HashMap::new(),
      hir_semantics: None,
      hir_sem_hir: HashMap::new(),
      def_types: HashMap::new(),
      body_results: HashMap::new(),
      symbol_occurrences: HashMap::new(),
      symbol_to_def: HashMap::new(),
      file_kinds: HashMap::new(),
      lib_texts: HashMap::new(),
      global_bindings: HashMap::new(),
      diagnostics: Vec::new(),
      type_store,
      builtin,
      predicates: HashMap::new(),
      next_def: 0,
      next_body: 0,
      next_symbol: 0,
      type_stack: Vec::new(),
      pending_reexports: Vec::new(),
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
    let libs = self.collect_libraries(host.as_ref(), roots);
    let mut queue: VecDeque<FileId> = libs.iter().map(|l| l.id).collect();
    for lib in libs {
      self.lib_texts.insert(lib.id, lib.text.clone());
    }
    for root in roots {
      self
        .file_kinds
        .entry(*root)
        .or_insert_with(|| host.file_kind(*root));
      queue.push_back(*root);
    }
    while let Some(file) = queue.pop_front() {
      if cancelled.load(Ordering::Relaxed) {
        return Err(FatalError::Cancelled);
      }
      if self.files.contains_key(&file) {
        continue;
      }
      self
        .file_kinds
        .entry(file)
        .or_insert_with(|| host.file_kind(file));
      let text = self.load_text(file, host)?;
      let parse_span = QuerySpan::enter(
        query_span!(
          "typecheck_ts.parse",
          Some(file.0),
          Option::<u32>::None,
          Option::<u32>::None,
          false
        ),
        None,
      );
      let parsed = parse(&text);
      if let Some(span) = parse_span {
        span.finish(None);
      }
      match parsed {
        Ok(ast) => {
          let bind_span = QuerySpan::enter(
            query_span!(
              "typecheck_ts.bind",
              Some(file.0),
              Option::<u32>::None,
              Option::<u32>::None,
              false
            ),
            None,
          );
          self.bind_file(file, ast, host, &mut queue);
          if let Some(span) = bind_span {
            span.finish(None);
          }
        }
        Err(err) => {
          self.diagnostics.push(err.to_diagnostic(file));
        }
      }
    }
    if !self.sem_hir.is_empty() {
      self.compute_semantics(host, roots);
    }
    self.process_pending_reexports();
    self.recompute_global_bindings();
    self.analyzed = true;
    Ok(())
  }

  fn collect_libraries(&mut self, host: &dyn Host, roots: &[FileId]) -> Vec<LibFile> {
    let options = host.compiler_options();
    self.compiler_options = options.clone();
    let mut libs = host.lib_files();
    if !options.no_default_lib {
      let bundled = self.lib_manager.bundled_libs(&options);
      libs.extend(bundled.files);
    }

    for lib in libs.iter() {
      self.file_kinds.insert(lib.id, lib.kind);
      if lib.kind != FileKind::Dts {
        self.diagnostics.push(Diagnostic::error(
          CODE_NON_DTS_LIB,
          format!(
            "Library '{}' is not a .d.ts file; it will be ignored for global declarations.",
            lib.name
          ),
          Span::new(lib.id, TextRange::new(0, 0)),
        ));
      }
    }

    if !libs.iter().any(|lib| lib.kind == FileKind::Dts) {
      let file = roots
        .first()
        .copied()
        .or_else(|| libs.first().map(|l| l.id))
        .unwrap_or(FileId(0));
      self.diagnostics.push(Diagnostic::error(
        CODE_MISSING_LIB,
        "No .d.ts libraries were loaded; global declarations will be missing.".to_string(),
        Span::new(file, TextRange::new(0, 0)),
      ));
    }

    libs
  }

  fn load_text(&self, file: FileId, host: &Arc<dyn Host>) -> Result<Arc<str>, HostError> {
    if let Some(text) = self.lib_texts.get(&file) {
      return Ok(text.clone());
    }
    host.file_text(file)
  }

  fn recompute_global_bindings(&mut self) {
    let mut globals = HashMap::new();
    for (file, state) in self.files.iter() {
      if self.file_kinds.get(file) != Some(&FileKind::Dts) {
        continue;
      }
      for (name, binding) in state.bindings.iter() {
        globals.entry(name.clone()).or_insert(binding.clone());
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

  fn process_pending_reexports(&mut self) {
    let pending = std::mem::take(&mut self.pending_reexports);
    for reexport in pending {
      let exports = self.exports_of_file(reexport.target);
      if !exports.contains_key(&reexport.name) {
        self.diagnostics.push(Diagnostic::error(
          CODE_UNKNOWN_EXPORT,
          format!("unknown export {}", reexport.name),
          Span {
            file: reexport.source,
            range: reexport.span,
          },
        ));
      }
    }
  }

  fn compute_semantics(&mut self, host: &Arc<dyn Host>, roots: &[FileId]) {
    let resolver = HostResolver {
      host: Arc::clone(host),
    };
    let sem_roots: Vec<sem_ts::FileId> = roots.iter().map(|f| sem_ts::FileId(f.0)).collect();
    let (semantics, _diags) = sem_ts::bind_ts_program(&sem_roots, &resolver, |file| {
      let id = FileId(file.0);
      self
        .sem_hir
        .get(&id)
        .cloned()
        .map(Arc::new)
        .unwrap_or_else(|| Arc::new(sem_ts::HirFile::module(file)))
    });
    self.semantics = Some(semantics);
  }

  fn bind_file(
    &mut self,
    file: FileId,
    ast: Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    let top_body_id = self.alloc_body(file, None);
    let mut top_body = BodyBuilder::new(top_body_id, file);
    let mut sem_builder = SemHirBuilder::new(file);
    let mut defs = Vec::new();
    let mut exports: ExportMap = BTreeMap::new();
    let mut bindings: HashMap<String, SymbolBinding> = HashMap::new();
    let mut type_defs: HashMap<String, DefId> = HashMap::new();

    let mut stmts = Vec::new();
    for stmt in ast.stx.body.into_iter() {
      match *stmt.stx {
        Stmt::GlobalDecl(global) => stmts.extend(global.stx.body.into_iter()),
        other => stmts.push(Node {
          loc: stmt.loc,
          stx: Box::new(other),
          assoc: stmt.assoc,
        }),
      }
    }

    for stmt in stmts {
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
        Stmt::TypeAliasDecl(alias) => {
          let span = loc_to_span(file, stmt.loc);
          let alias_decl = *alias.stx;
          let name = alias_decl.name.clone();
          let type_expr = Arc::new(alias_decl.type_expr);
          let def_id = *type_defs.entry(name.clone()).or_insert_with(|| {
            let def_id = self.alloc_def();
            let symbol = self.alloc_symbol();
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span: span.range,
                symbol,
                export: alias_decl.export,
                kind: DefKind::Type(TypeData {
                  ty: self.builtin.any,
                  type_expr: Some(Arc::clone(&type_expr)),
                }),
              },
            );
            defs.push(def_id);
            def_id
          });
          let ty = self.type_from_type_expr(type_expr.as_ref());
          let merged = self.def_types.get(&def_id).copied().unwrap_or(ty);
          self.def_types.insert(def_id, merged);
          if let Some(data) = self.def_data.get_mut(&def_id) {
            data.export |= alias_decl.export;
            if let DefKind::Type(type_data) = &mut data.kind {
              type_data.ty = merged;
              type_data.type_expr = Some(Arc::clone(&type_expr));
            }
          }
          if alias_decl.export {
            let symbol = self
              .def_data
              .get(&def_id)
              .map(|d| d.symbol)
              .unwrap_or_else(|| self.alloc_symbol());
            exports.insert(
              name,
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: Some(merged),
              },
            );
          }
        }
        Stmt::InterfaceDecl(decl) => {
          let span = loc_to_span(file, stmt.loc);
          let name = decl.stx.name.clone();
          let def_id = *type_defs.entry(name.clone()).or_insert_with(|| {
            let def_id = self.alloc_def();
            let symbol = self.alloc_symbol();
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span: span.range,
                symbol,
                export: decl.stx.export,
                kind: DefKind::Type(TypeData {
                  ty: self.builtin.any,
                  type_expr: None,
                }),
              },
            );
            defs.push(def_id);
            def_id
          });
          let ty = self.interface_type(&decl.stx.members, &decl.stx.extends);
          let merged = match self.def_types.get(&def_id) {
            Some(existing) => self.type_store.intersection(vec![*existing, ty]),
            None => ty,
          };
          self.def_types.insert(def_id, merged);
          if let Some(data) = self.def_data.get_mut(&def_id) {
            data.export |= decl.stx.export;
            if let DefKind::Type(type_data) = &mut data.kind {
              type_data.ty = merged;
            }
          }
          if decl.stx.export {
            let symbol = self
              .def_data
              .get(&def_id)
              .map(|d| d.symbol)
              .unwrap_or_else(|| self.alloc_symbol());
            exports.insert(
              name,
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: Some(merged),
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
          let hir_stmt = HirStmt::Var {
            name: "default".to_string(),
            typ: None,
            init: Some(expr),
            span: span.range,
            symbol,
            def: Some(def_id),
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
          if let Some(module) = export_list.stx.from.clone() {
            if let Some(target) = host.resolve(file, &module) {
              queue.push_back(target);
            } else {
              self.diagnostics.push(Diagnostic::error(
                CODE_UNRESOLVED_MODULE,
                format!("unresolved module {module}"),
                loc_to_span(file, stmt.loc),
              ));
            }
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

                if let Some(spec) = export_list.stx.from.as_ref() {
                  if let Some(target) = host.resolve(file, spec) {
                    self.pending_reexports.push(PendingReexport {
                      source: file,
                      target,
                      name: exportable.clone(),
                      span: loc_to_span(file, name.loc).range,
                    });
                  }
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
                    self.diagnostics.push(Diagnostic::error(
                      CODE_UNKNOWN_EXPORT,
                      format!("unknown export {exportable}"),
                      loc_to_span(file, name.loc),
                    ));
                  }
                }
              }
            }
            ExportNames::All(alias) => {
              if alias.is_some() {
                self.diagnostics.push(Diagnostic::error(
                  CODE_UNSUPPORTED_PATTERN,
                  "unsupported export * as alias",
                  loc_to_span(file, stmt.loc),
                ));
              } else if let Some(spec) = export_list.stx.from.clone() {
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
            queue.push_back(target);
          } else {
            self.diagnostics.push(Diagnostic::error(
              CODE_UNRESOLVED_MODULE,
              format!("unresolved module {module}"),
              loc_to_span(file, stmt.loc),
            ));
          }
          let mut import_default = None;
          let mut import_namespace = None;
          let mut import_named = Vec::new();
          if let Some(default_pat) = import_stmt.stx.default.as_ref() {
            let alias_name = match &default_pat.stx.pat.stx.as_ref() {
              Pat::Id(id) => id.stx.name.clone(),
              _ => {
                self.diagnostics.push(Diagnostic::error(
                  CODE_UNSUPPORTED_IMPORT_PATTERN,
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
                    self.diagnostics.push(Diagnostic::error(
                      CODE_UNSUPPORTED_IMPORT_PATTERN,
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
                  self.diagnostics.push(Diagnostic::error(
                    CODE_UNSUPPORTED_IMPORT_PATTERN,
                    "unsupported import pattern",
                    loc_to_span(file, pat.loc),
                  ));
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
    self.sem_hir.insert(file, sem_builder.finish());
    self.files.insert(
      file,
      FileState {
        defs,
        exports,
        bindings,
        top_body: Some(top_body_id),
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
          self.diagnostics.push(Diagnostic::error(
            CODE_UNSUPPORTED_PATTERN,
            "unsupported pattern",
            loc_to_span(file, pat.loc),
          ));
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
      stmts.push(HirStmt::Var {
        name: name.clone(),
        typ: type_ann,
        init: init_expr,
        span,
        symbol,
        def: Some(def_id),
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
    let mut params = Vec::new();
    for param in func.parameters.iter() {
      if let Some(data) = self.lower_param(file, param) {
        params.push(data);
      }
    }
    let mut predicate = None;
    let return_ann = func.return_type.as_ref().map(|t| match t.stx.as_ref() {
      TypeExpr::TypePredicate(pred) => {
        let asserted = pred
          .stx
          .type_annotation
          .as_ref()
          .map(|ta| self.type_from_type_expr(ta));
        predicate = Some(PredicateInfo {
          parameter: pred.stx.parameter_name.clone(),
          asserted,
          asserts: pred.stx.asserts,
        });
        if pred.stx.asserts {
          self.builtin.void
        } else {
          self.builtin.boolean
        }
      }
      _ => self.type_from_type_expr(t),
    });
    let body_id = func.body.as_ref().map(|_| self.alloc_body(file, Some(def)));
    if let Some(body) = body_id {
      match func.body.unwrap() {
        FuncBody::Block(stmts) => {
          let mut builder = BodyBuilder::new(body, file);
          for stmt in stmts {
            builder.lower_stmt(stmt, self);
          }
          let data = builder.finish(Some(def));
          self.body_data.insert(body, data);
        }
        FuncBody::Expression(expr) => {
          let mut builder = BodyBuilder::new(body, file);
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
    FuncData {
      params,
      return_ann,
      body: body_id,
      predicate,
    }
  }

  fn lower_param(&mut self, file: FileId, param: &Node<ParamDecl>) -> Option<ParamData> {
    let name = match param.stx.pattern.stx.pat.stx.as_ref() {
      Pat::Id(id) => id.stx.name.clone(),
      _ => {
        self.diagnostics.push(Diagnostic::error(
          CODE_UNSUPPORTED_PARAM_PATTERN,
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
    self.record_symbol(file, loc_to_span(file, param.loc).range, symbol);
    Some(ParamData { name, typ, symbol })
  }

  fn check_body(&mut self, body_id: BodyId) -> Arc<BodyCheckResult> {
    let cache_hit = self.body_results.contains_key(&body_id);
    let body_meta = self.body_data.get(&body_id).cloned();
    let mut span = QuerySpan::enter(
      query_span!(
        "typecheck_ts.check_body",
        body_meta.as_ref().map(|b| b.file.0),
        body_meta.as_ref().and_then(|b| b.owner.map(|d| d.0)),
        Some(body_id.0),
        cache_hit
      ),
      None,
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
          diagnostics: vec![Diagnostic::error(
            CODE_MISSING_BODY,
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
    let mut env = self.initial_env(body.owner, body.file);
    let mut result = BodyCheckResult {
      body: body.id,
      expr_types: vec![self.builtin.unknown; body.expr_spans.len()],
      expr_spans: body.expr_spans.clone(),
      pat_types: Vec::new(),
      diagnostics: Vec::new(),
      return_types: Vec::new(),
    };
    let mut pat_ids: HashMap<String, PatId> = HashMap::new();
    if let Some(owner) = body.owner {
      if let Some(DefKind::Function(func)) = self.def_data.get(&owner).map(|d| &d.kind) {
        for param in func.params.iter() {
          let pat_id = PatId(result.pat_types.len() as u32);
          pat_ids.insert(param.name.clone(), pat_id);
          let ty = param.typ.unwrap_or(self.builtin.unknown);
          result.pat_types.push(ty);
          if let Some(binding) = env.get_mut(&param.name) {
            binding.type_id = Some(ty);
          }
        }
      }
    }

    let expected_return = body.owner.and_then(|def| {
      self.def_data.get(&def).and_then(|d| match &d.kind {
        DefKind::Function(func) => func.return_ann,
        _ => None,
      })
    });

    for stmt in body.stmts.iter() {
      self.check_stmt(
        stmt,
        &mut env,
        &mut pat_ids,
        &mut result,
        expected_return,
        body.file,
      );
    }

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
    pat_ids: &mut HashMap<String, PatId>,
    result: &mut BodyCheckResult,
    expected_return: Option<TypeId>,
    file: FileId,
  ) {
    match stmt {
      HirStmt::Var {
        name,
        typ,
        init,
        span,
        symbol,
        def,
      } => {
        let mode = def
          .and_then(|id| self.def_data.get(&id))
          .and_then(|d| match &d.kind {
            DefKind::Var(var) => Some(var.mode),
            _ => None,
          })
          .unwrap_or(VarDeclMode::Var);
        let init_checked = init.as_ref().map(|e| self.check_expr(e, env, result, file));
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
          let should_widen = match mode {
            VarDeclMode::Const => match init.as_ref().map(|expr| &expr.kind) {
              Some(
                HirExprKind::NumberLiteral(_)
                | HirExprKind::StringLiteral(_)
                | HirExprKind::BooleanLiteral(_),
              ) => false,
              Some(HirExprKind::TypeAssertion {
                _const_assertion: true,
                ..
              }) => false,
              Some(HirExprKind::TypeAssertion { typ, .. }) if typ.is_none() => false,
              _ => true,
            },
            _ => true,
          };
          if should_widen {
            self.widen_type(init_ty)
          } else {
            init_ty
          }
        } else {
          self.builtin.unknown
        };
        let pat_id = pat_ids.entry(name.clone()).or_insert_with(|| {
          let id = PatId(result.pat_types.len() as u32);
          result.pat_types.push(self.builtin.unknown);
          id
        });
        if let Some(slot) = result.pat_types.get_mut(pat_id.0 as usize) {
          *slot = declared;
        }
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
      }
      HirStmt::Return { expr, .. } => {
        let ty = expr
          .as_ref()
          .map(|e| self.check_expr(e, env, result, file).0)
          .unwrap_or(self.builtin.undefined);
        if let Some(expected) = expected_return {
          if let Some(expr_ref) = expr.as_ref() {
            check::assign::check_assignment(self, Some(expr_ref), ty, expected, result, file);
          }
        }
        result.return_types.push(ty);
      }
      HirStmt::Expr(expr) => {
        let (_, facts) = self.check_expr(expr, env, result, file);
        self.apply_fact_map(env, &facts.assertions);
      }
      HirStmt::If {
        test,
        consequent,
        alternate,
        ..
      } => {
        let (_, cond_facts) = self.check_expr(test, env, result, file);
        let mut then_env = env.clone();
        self.apply_fact_map(&mut then_env, &cond_facts.truthy);
        self.apply_fact_map(&mut then_env, &cond_facts.assertions);
        let mut else_env = env.clone();
        self.apply_fact_map(&mut else_env, &cond_facts.falsy);
        self.apply_fact_map(&mut else_env, &cond_facts.assertions);

        for stmt in consequent {
          self.check_stmt(stmt, &mut then_env, pat_ids, result, expected_return, file);
        }
        for stmt in alternate {
          self.check_stmt(stmt, &mut else_env, pat_ids, result, expected_return, file);
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
          self.check_stmt(stmt, env, pat_ids, result, expected_return, file);
        }
      }
      HirStmt::While { test, body, .. } => {
        let (_, cond_facts) = self.check_expr(test, env, result, file);
        let mut body_env = env.clone();
        self.apply_fact_map(&mut body_env, &cond_facts.truthy);
        self.apply_fact_map(&mut body_env, &cond_facts.assertions);
        for stmt in body {
          self.check_stmt(stmt, &mut body_env, pat_ids, result, expected_return, file);
        }
        let mut merged = self.merge_envs(env, &body_env);
        self.apply_fact_map(&mut merged, &cond_facts.falsy);
        *env = merged;
      }
    }
  }

  fn check_expr(
    &mut self,
    expr: &HirExpr,
    env: &mut HashMap<String, SymbolBinding>,
    result: &mut BodyCheckResult,
    file: FileId,
  ) -> (TypeId, Facts) {
    let mut facts = Facts::default();
    let ty = match &expr.kind {
      HirExprKind::NumberLiteral(value) => self.literal_number(value),
      HirExprKind::StringLiteral(value) => self.literal_string(value),
      HirExprKind::BooleanLiteral(value) => self.literal_boolean(*value),
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
          result.diagnostics.push(Diagnostic::error(
            CODE_UNKNOWN_IDENTIFIER,
            format!("Cannot find name '{name}'."),
            Span::new(file, expr.span),
          ));
        }
        if let Some(binding) = env.get_mut(name) {
          if binding.type_id.is_none() {
            binding.type_id = Some(ty);
          }
        }
        let (truthy, falsy) = truthy_falsy_types(ty, self.type_store.as_ref(), &self.builtin);
        if truthy != self.builtin.never {
          facts.truthy.insert(name.clone(), truthy);
        }
        if falsy != self.builtin.never {
          facts.falsy.insert(name.clone(), falsy);
        }
        ty
      }
      HirExprKind::Member { object, property } => {
        let (obj_ty, _) = self.check_expr(object, env, result, file);
        match self.type_store.type_kind(obj_ty) {
          TypeKind::Union(members) => {
            let mut collected = Vec::new();
            for member in members {
              if let Some(t) = lookup_property_type(self.type_store.as_ref(), member, property) {
                collected.push(t);
              }
            }
            if collected.is_empty() {
              self.builtin.unknown
            } else {
              self.union_types(collected)
            }
          }
          _ => lookup_property_type(self.type_store.as_ref(), obj_ty, property)
            .unwrap_or(self.builtin.unknown),
        }
      }
      HirExprKind::Unary { op, expr: inner } => match op {
        OperatorName::LogicalNot => {
          let (_inner_ty, inner_facts) = self.check_expr(inner, env, result, file);
          facts.truthy = inner_facts.falsy;
          facts.falsy = inner_facts.truthy;
          facts.assertions = inner_facts.assertions;
          self.builtin.boolean
        }
        OperatorName::Typeof => self.literal_string("string"),
        _ => {
          let _ = self.check_expr(inner, env, result, file);
          self.builtin.unknown
        }
      },
      HirExprKind::Binary { op, left, right } => match op {
        OperatorName::LogicalAnd => {
          let (lt, lf) = self.check_expr(left, env, result, file);
          let mut right_env = env.clone();
          self.apply_fact_map(&mut right_env, &lf.truthy);
          self.apply_fact_map(&mut right_env, &lf.assertions);
          let (rt, rf) = self.check_expr(right, &mut right_env, result, file);

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
            self.type_store.as_ref(),
            &self.builtin,
          );

          self.union_types(vec![lt, rt])
        }
        OperatorName::LogicalOr => {
          let (lt, lf) = self.check_expr(left, env, result, file);
          let mut right_env = env.clone();
          self.apply_fact_map(&mut right_env, &lf.falsy);
          self.apply_fact_map(&mut right_env, &lf.assertions);
          let (rt, rf) = self.check_expr(right, &mut right_env, result, file);

          facts.truthy = lf.truthy;
          facts.merge(
            Facts {
              truthy: rf.truthy,
              ..Default::default()
            },
            self.type_store.as_ref(),
            &self.builtin,
          );
          facts.falsy = rf.falsy;
          facts.assertions = lf.assertions;
          facts.merge(
            Facts {
              assertions: rf.assertions,
              ..Default::default()
            },
            self.type_store.as_ref(),
            &self.builtin,
          );

          self.union_types(vec![lt, rt])
        }
        OperatorName::Equality | OperatorName::StrictEquality => {
          let (_lt, lfacts) = self.check_expr(left, env, result, file);
          let (_rt, rfacts) = self.check_expr(right, env, result, file);
          // typeof x === "string"
          if let HirExprKind::Unary {
            op: OperatorName::Typeof,
            expr: inner,
          } = &left.kind
          {
            if let HirExprKind::StringLiteral(value) = &right.kind {
              let (inner_ty, _) = self.check_expr(inner, env, result, file);
              if let HirExprKind::Ident(name) = &inner.kind {
                let (yes, no) = narrow_by_typeof(
                  inner_ty,
                  value.as_str(),
                  self.type_store.as_ref(),
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
              let (obj_ty, _) = self.check_expr(object, env, result, file);
              if let HirExprKind::Ident(obj_name) = &object.kind {
                let (yes, no) = narrow_by_discriminant(
                  obj_ty,
                  property,
                  value,
                  self.type_store.as_ref(),
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
              let (obj_ty, _) = self.check_expr(object, env, result, file);
              if let HirExprKind::Ident(obj_name) = &object.kind {
                let (yes, no) = narrow_by_discriminant(
                  obj_ty,
                  property,
                  value,
                  self.type_store.as_ref(),
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
          facts.merge(lfacts, self.type_store.as_ref(), &self.builtin);
          facts.merge(rfacts, self.type_store.as_ref(), &self.builtin);
          self.builtin.boolean
        }
        OperatorName::Instanceof => {
          let (_lt, lf) = self.check_expr(left, env, result, file);
          let (_rt, rf) = self.check_expr(right, env, result, file);
          facts.merge(lf, self.type_store.as_ref(), &self.builtin);
          facts.merge(rf, self.type_store.as_ref(), &self.builtin);
          self.builtin.boolean
        }
        OperatorName::In => {
          let (_lt, lf) = self.check_expr(left, env, result, file);
          let (rt, rf) = self.check_expr(right, env, result, file);
          if let HirExprKind::StringLiteral(prop) = &left.kind {
            if let HirExprKind::Ident(name) = &right.kind {
              let (yes, no) = narrow_by_in_check(rt, prop, self.type_store.as_ref(), &self.builtin);
              if yes != self.builtin.never {
                facts.truthy.insert(name.clone(), yes);
              }
              if no != self.builtin.never {
                facts.falsy.insert(name.clone(), no);
              }
            }
          }
          facts.merge(lf, self.type_store.as_ref(), &self.builtin);
          facts.merge(rf, self.type_store.as_ref(), &self.builtin);
          self.builtin.boolean
        }
        _ => {
          let (left_ty, lfacts) = self.check_expr(left, env, result, file);
          let (right_ty, rfacts) = self.check_expr(right, env, result, file);
          facts.merge(lfacts, self.type_store.as_ref(), &self.builtin);
          facts.merge(rfacts, self.type_store.as_ref(), &self.builtin);
          match op {
            OperatorName::Addition => {
              let left_kind = self.type_store.type_kind(left_ty);
              let right_kind = self.type_store.type_kind(right_ty);
              let left_is_string =
                matches!(left_kind, TypeKind::String | TypeKind::StringLiteral(_));
              let right_is_string =
                matches!(right_kind, TypeKind::String | TypeKind::StringLiteral(_));
              let left_is_number =
                matches!(left_kind, TypeKind::Number | TypeKind::NumberLiteral(_));
              let right_is_number =
                matches!(right_kind, TypeKind::Number | TypeKind::NumberLiteral(_));
              if left_is_string || right_is_string {
                self.builtin.string
              } else if left_is_number && right_is_number {
                self.builtin.number
              } else {
                self.union_types(vec![left_ty, right_ty])
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
        let (callee_ty, _) = self.check_expr(callee, env, result, file);
        let callee_def = if let HirExprKind::Ident(name) = &callee.kind {
          env.get(name).and_then(|b| b.def)
        } else {
          None
        };
        if let TypeKind::Callable { overloads } = self.type_store.type_kind(callee_ty) {
          if let Some(sig_id) = overloads.first() {
            let sig = self.type_store.signature(*sig_id);
            if sig.params.len() != args.len() {
              result.diagnostics.push(Diagnostic::error(
                CODE_ARGUMENT_COUNT_MISMATCH,
                "argument count mismatch",
                Span {
                  file,
                  range: expr.span,
                },
              ));
            }
            let mut arg_types = Vec::new();
            for (idx, arg) in args.iter().enumerate() {
              let (arg_ty, _) = self.check_expr(arg, env, result, file);
              arg_types.push(arg_ty);
              if let Some(expected) = sig.params.get(idx) {
                check::assign::check_assignment(self, Some(arg), arg_ty, expected.ty, result, file);
              }
            }
            let mut ret_ty = sig.ret;
            if let Some(def_id) = callee_def {
              if let Some(pred) = self.predicates.get(&def_id) {
                let arg_ty = arg_types.get(0).copied().unwrap_or(self.builtin.unknown);
                if let Some(first_arg) = args.get(0) {
                  if let HirExprKind::Ident(name) = &first_arg.kind {
                    if let Some(asserted_ty) = pred.asserted {
                      if pred.asserts {
                        facts.assertions.insert(name.clone(), asserted_ty);
                      } else {
                        facts.truthy.insert(name.clone(), asserted_ty);
                        let complement = match self.type_store.type_kind(arg_ty) {
                          TypeKind::Union(members) => {
                            let remaining: Vec<_> =
                              members.into_iter().filter(|m| *m != asserted_ty).collect();
                            self.union_types(remaining)
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
                ret_ty = if pred.asserts {
                  self.builtin.void
                } else {
                  self.builtin.boolean
                };
              }
            }
            ret_ty
          } else {
            self.builtin.unknown
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
        let (_, cond_facts) = self.check_expr(test, env, result, file);
        let mut then_env = env.clone();
        self.apply_fact_map(&mut then_env, &cond_facts.truthy);
        self.apply_fact_map(&mut then_env, &cond_facts.assertions);
        let mut else_env = env.clone();
        self.apply_fact_map(&mut else_env, &cond_facts.falsy);
        self.apply_fact_map(&mut else_env, &cond_facts.assertions);
        let (cons_ty, cons_facts) = self.check_expr(consequent, &mut then_env, result, file);
        let (alt_ty, alt_facts) = self.check_expr(alternate, &mut else_env, result, file);
        facts.merge(cons_facts, self.type_store.as_ref(), &self.builtin);
        facts.merge(alt_facts, self.type_store.as_ref(), &self.builtin);
        self.union_types(vec![cons_ty, alt_ty])
      }
      HirExprKind::Object(props) => {
        let mut properties = Vec::new();
        for (k, v) in props.iter() {
          if k == "..." {
            continue;
          }
          let (ty, _) = self.check_expr(v, env, result, file);
          properties.push(TsProperty {
            key: PropKey::String(self.type_store.intern_name(k.clone())),
            data: PropData {
              ty,
              optional: false,
              readonly: false,
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          });
        }
        self.object_type_from_parts(properties, Vec::new(), Vec::new(), Vec::new())
      }
      HirExprKind::Array(values) => {
        let mut tys = Vec::new();
        for v in values {
          let elem_ty = self.check_expr(v, env, result, file).0;
          tys.push(self.widen_literal(elem_ty));
        }
        let elem = self.union_types(tys);
        self.array_type(elem)
      }
      HirExprKind::TypeAssertion {
        expr,
        typ,
        _const_assertion,
      } => {
        let (inner_ty, inner_facts) = self.check_expr(expr, env, result, file);
        facts = inner_facts;
        if *_const_assertion {
          self.const_assertion_type(expr, result, inner_ty)
        } else {
          (*typ).unwrap_or(inner_ty)
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
            (Some(a), Some(b)) => Some(self.union_types(vec![a, b])),
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
      _ => false,
    })
  }

  fn is_assignable(&self, src: TypeId, dst: TypeId) -> bool {
    self.relate_ctx().is_assignable(src, dst)
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
      query_span!(
        "typecheck_ts.type_of_def",
        self.def_data.get(&def).map(|d| d.file.0),
        Some(def.0),
        self.body_of_def(def).map(|b| b.0),
        cache_hit
      ),
      self.def_types.get(&def).copied(),
    );
    let cached = self.def_types.get(&def).copied();
    let should_recompute = match (cached, self.def_data.get(&def)) {
      (Some(existing), Some(data)) => {
        matches!(&data.kind, DefKind::Type(type_data) if type_data.type_expr.is_some() && matches!(self.type_store.type_kind(existing), TypeKind::Unknown))
      }
      _ => false,
    };
    if let (Some(existing), false) = (cached, should_recompute) {
      if let Some(span) = span.take() {
        span.finish(Some(existing));
      }
      return existing;
    }
    if self.type_stack.contains(&def) {
      if let Some(span) = span.take() {
        span.finish(Some(self.builtin.any));
      }
      return self.builtin.any;
    }
    self.type_stack.push(def);
    let data = match self.def_data.get(&def).cloned() {
      Some(d) => d,
      None => {
        if let Some(span) = span.take() {
          span.finish(Some(self.builtin.unknown));
        }
        self.type_stack.pop();
        return self.builtin.unknown;
      }
    };
    let ty = match data.kind {
      DefKind::Function(func) => self.function_type(def, func),
      DefKind::Var(var) => {
        if let Some(t) = var.typ {
          t
        } else if let Some(binding_ty) = self
          .files
          .get(&data.file)
          .and_then(|f| f.bindings.get(&data.name))
          .and_then(|b| b.type_id)
        {
          binding_ty
        } else if let Some(init) = var.init {
          let res = self.check_body(var.body);
          res.expr_type(init).unwrap_or(self.builtin.unknown)
        } else {
          self.builtin.unknown
        }
      }
      DefKind::Import(import) => {
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
      DefKind::Type(ty) => {
        if let Some(expr) = ty.type_expr.as_ref() {
          self.type_from_type_expr(expr)
        } else {
          ty.ty
        }
      }
    };
    self.type_stack.pop();
    if let Some(data) = self.def_data.get_mut(&def) {
      if let DefKind::Type(type_data) = &mut data.kind {
        type_data.ty = ty;
      }
    }
    self.def_types.insert(def, ty);
    if let Some(span) = span.take() {
      span.finish(Some(ty));
    }
    ty
  }

  fn function_type(&mut self, def: DefId, func: FuncData) -> TypeId {
    if let Some(pred) = func.predicate.clone() {
      self.predicates.insert(def, pred);
    } else {
      self.predicates.remove(&def);
    }
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
        self.widen_literal(self.union_types(res.return_types.clone()))
      }
    } else {
      self.builtin.unknown
    };
    let ty = self.callable_type(param_types, ret, None);
    self.def_types.insert(def, ty);
    ty
  }

  fn exports_of_file(&mut self, file: FileId) -> ExportMap {
    if self.file_kinds.get(&file) != Some(&FileKind::Dts) && self.semantics.is_some() {
      let sem_file = sem_ts::FileId(file.0);
      let pending: Vec<(String, sem_ts::SymbolId, Option<DefId>, Option<DefId>)> = {
        let semantics = self.semantics.as_ref().expect("checked above");
        let exports = semantics.exports_of(sem_file);
        let symbols = semantics.symbols();
        let mut pending = Vec::new();
        for (name, group) in exports.iter() {
          let Some(symbol_id) = group.symbol_for(sem_ts::Namespace::VALUE, symbols) else {
            continue;
          };
          let symbol = symbols.symbol(symbol_id);
          let mut local_def = None;
          let mut any_def = None;
          for decl_id in symbol.decls_for(sem_ts::Namespace::VALUE).iter() {
            let decl = symbols.decl(*decl_id);
            let def = DefId(decl.def_id.0);
            if any_def.is_none() {
              any_def = Some(def);
            }
            if decl.file == sem_file && local_def.is_none() {
              local_def = Some(def);
            }
          }
          pending.push((name.clone(), symbol_id, local_def, any_def));
        }
        pending
      };

      let mut map = ExportMap::new();
      for (name, symbol_id, local_def, any_def) in pending {
        let symbol = any_def
          .or(local_def)
          .and_then(|def| self.def_data.get(&def).map(|data| data.symbol))
          .unwrap_or_else(|| semantic_js::SymbolId::from(symbol_id));
        let type_id = any_def.or(local_def).map(|def| self.type_of_def(def));
        map.insert(
          name,
          ExportEntry {
            symbol,
            def: local_def,
            type_id,
          },
        );
      }
      return map;
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

  fn symbol_at(
    &mut self,
    file: FileId,
    offset: u32,
    host: &Arc<dyn Host>,
    roots: &[FileId],
  ) -> Option<semantic_js::SymbolId> {
    let lowered = self.ensure_lowered(file, host)?;
    let semantics = self.ensure_hir_semantics(host, roots).cloned();
    let locals = self.hir_locals.get(&file)?;
    let mut candidates: Vec<(TextRange, semantic_js::SymbolId)> = Vec::new();

    if let Some((expr_id, span)) = lowered.hir.span_map.expr_span_at_offset(offset) {
      if let Some(symbol) = self.resolve_expr_symbol(
        &lowered,
        expr_id,
        span,
        sem_ts::Namespace::VALUE,
        locals,
        semantics.as_ref(),
      ) {
        candidates.push((span, symbol));
      }
    }

    if let Some((_, span)) = lowered.hir.span_map.pat_span_at_offset(offset) {
      if let Some(sym) = locals.resolve_expr_span(span) {
        let symbol = self.map_local_symbol(
          sym,
          sem_ts::Namespace::VALUE,
          &lowered,
          locals,
          semantics.as_ref(),
        );
        candidates.push((span, symbol));
      }
    }

    if let Some((_, span)) = lowered.hir.span_map.type_expr_span_at_offset(offset) {
      if let Some(sym) = locals.resolve_type_span(span) {
        let symbol = self.map_local_symbol(
          sym,
          sem_ts::Namespace::TYPE,
          &lowered,
          locals,
          semantics.as_ref(),
        );
        candidates.push((span, symbol));
      } else if let Some(def) = lowered.hir.span_map.def_at_offset(span.start) {
        if let Some(symbol) = self.symbol_for_def(
          def,
          Some(sem_ts::Namespace::TYPE),
          &lowered,
          semantics.as_ref(),
        ) {
          candidates.push((span, symbol));
        }
      }
    }

    if let Some((spec_id, span)) = lowered.hir.span_map.import_specifier_span_at_offset(offset) {
      if let Some((def, ns)) = Self::import_specifier_def(&lowered, spec_id) {
        if let Some(symbol) = self.symbol_for_def(def, Some(ns), &lowered, semantics.as_ref()) {
          candidates.push((span, symbol));
        }
      }
    }

    if let Some((spec_id, span)) = lowered.hir.span_map.export_specifier_span_at_offset(offset) {
      if let Some((def, ns)) = Self::export_specifier_def(&lowered, spec_id) {
        if let Some(symbol) = self.symbol_for_def(def, Some(ns), &lowered, semantics.as_ref()) {
          candidates.push((span, symbol));
        }
      }
    }

    if let Some((def, span)) = lowered.hir.span_map.def_span_at_offset(offset) {
      if let Some(symbol) = self.symbol_for_def(def, None, &lowered, semantics.as_ref()) {
        candidates.push((span, symbol));
      }
    }

    Self::pick_best_symbol(candidates)
  }

  fn pick_best_symbol(
    candidates: Vec<(TextRange, semantic_js::SymbolId)>,
  ) -> Option<semantic_js::SymbolId> {
    candidates
      .into_iter()
      .min_by_key(|(range, symbol)| (range.len(), range.start, symbol.0))
      .map(|(_, symbol)| symbol)
  }

  fn ensure_lowered(&mut self, file: FileId, host: &Arc<dyn Host>) -> Option<Arc<LowerResult>> {
    if !self.hir_lowered.contains_key(&file) {
      let _ = self.parse_lower_file(file, host)?;
    }
    self.hir_lowered.get(&file).cloned()
  }

  fn parse_lower_file(&mut self, file: FileId, host: &Arc<dyn Host>) -> Option<Arc<LowerResult>> {
    let text = self.load_text(file, host).ok()?;
    let mut ast = parse(&text).ok()?;
    let locals = sem_locals::bind_ts_locals(&mut ast, true);
    let file_kind = *self
      .file_kinds
      .entry(file)
      .or_insert_with(|| host.file_kind(file));
    let hir_kind = Self::map_file_kind(file_kind);
    let lowered = lower_file(file, hir_kind, &ast);
    let sem_hir = lower_to_ts_hir(&ast, &lowered);
    self.hir_locals.insert(file, locals);
    let lowered = Arc::new(lowered);
    self.hir_lowered.insert(file, Arc::clone(&lowered));
    self.hir_sem_hir.insert(file, Arc::new(sem_hir));
    self.hir_semantics = None;
    Some(lowered)
  }

  fn ensure_hir_semantics(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileId],
  ) -> Option<&sem_ts::TsProgramSemantics> {
    if self.hir_semantics.is_some() {
      return self.hir_semantics.as_ref();
    }
    let files: Vec<FileId> = self
      .files
      .keys()
      .copied()
      .chain(self.lib_texts.keys().copied())
      .chain(roots.iter().copied())
      .collect();
    for file in files {
      let _ = self.ensure_lowered(file, host);
    }
    let resolver = HostResolver {
      host: Arc::clone(host),
    };
    let sem_roots: Vec<sem_ts::FileId> = roots.iter().map(|f| sem_ts::FileId(f.0)).collect();
    let files = self.hir_sem_hir.clone();
    let (semantics, _diags) = sem_ts::bind_ts_program(&sem_roots, &resolver, |file_id| {
      files
        .get(&FileId(file_id.0))
        .cloned()
        .unwrap_or_else(|| Arc::new(sem_ts::HirFile::module(file_id)))
    });
    self.hir_semantics = Some(semantics);
    self.hir_semantics.as_ref()
  }

  fn map_local_symbol(
    &self,
    local_sym: sem_locals::SymbolId,
    preferred_ns: sem_ts::Namespace,
    lower: &LowerResult,
    locals: &sem_locals::TsLocalSemantics,
    semantics: Option<&sem_ts::TsProgramSemantics>,
  ) -> semantic_js::SymbolId {
    if let Some(symbol) = locals.symbols.get(local_sym.index()) {
      if symbol.decl_scope.index() == 0 {
        if let (Some(semantics), Some(name)) = (semantics, locals.names.get(symbol.name.index())) {
          if let Some(resolved) =
            semantics.resolve_in_module(sem_ts::FileId(lower.hir.file.0), name, preferred_ns)
          {
            let symbol = semantic_js::SymbolId::from(resolved);
            return self.canonical_symbol(symbol, preferred_ns, Some(semantics));
          }
        }
      }
    }
    if let Some(span) = Self::local_symbol_span(locals, local_sym) {
      if let Some(def) = lower.hir.span_map.def_at_offset(span.start) {
        if let Some(symbol) = self.symbol_for_def(def, Some(preferred_ns), lower, semantics) {
          return symbol;
        }
        return self.synthetic_symbol_for_def(def);
      }
    }
    let synthetic = semantic_js::SymbolId(LOCAL_SYMBOL_OFFSET | local_sym.0);
    self.canonical_symbol(synthetic, preferred_ns, semantics)
  }

  fn local_symbol_span(
    locals: &sem_locals::TsLocalSemantics,
    symbol: sem_locals::SymbolId,
  ) -> Option<TextRange> {
    locals.symbols.get(symbol.index()).and_then(|s| s.span)
  }

  fn hir_def_kind(lower: &LowerResult, def: DefId) -> Option<HirDefKind> {
    let idx = lower.def_index.get(&def).copied()?;
    lower.defs.get(idx).map(|d| d.path.kind)
  }

  fn symbol_for_def(
    &self,
    def: DefId,
    preferred_ns: Option<sem_ts::Namespace>,
    lower: &LowerResult,
    semantics: Option<&sem_ts::TsProgramSemantics>,
  ) -> Option<semantic_js::SymbolId> {
    let kind = Self::hir_def_kind(lower, def)?;
    let namespaces = Self::def_kind_namespaces(kind);
    let target = preferred_ns.unwrap_or_else(|| {
      if namespaces.contains(sem_ts::Namespace::VALUE) {
        sem_ts::Namespace::VALUE
      } else if namespaces.contains(sem_ts::Namespace::TYPE) {
        sem_ts::Namespace::TYPE
      } else {
        sem_ts::Namespace::NAMESPACE
      }
    });
    if let Some(semantics) = semantics {
      if let Some(symbol) = semantics.symbol_for_def(def, target) {
        let symbol = semantic_js::SymbolId::from(symbol);
        return Some(self.canonical_symbol(symbol, target, Some(semantics)));
      }
      for ns in [
        sem_ts::Namespace::VALUE,
        sem_ts::Namespace::TYPE,
        sem_ts::Namespace::NAMESPACE,
      ] {
        if ns == target || !namespaces.contains(ns) {
          continue;
        }
        if let Some(symbol) = semantics.symbol_for_def(def, ns) {
          let symbol = semantic_js::SymbolId::from(symbol);
          return Some(self.canonical_symbol(symbol, ns, Some(semantics)));
        }
      }
    }
    Some(self.canonical_symbol(self.synthetic_symbol_for_def(def), target, semantics))
  }

  fn canonical_symbol(
    &self,
    symbol: semantic_js::SymbolId,
    ns: sem_ts::Namespace,
    semantics: Option<&sem_ts::TsProgramSemantics>,
  ) -> semantic_js::SymbolId {
    if symbol.0 & LOCAL_SYMBOL_OFFSET != 0 {
      return symbol;
    }
    let Some(semantics) = semantics else {
      return symbol;
    };

    let mut current = ::semantic_js::ts::SymbolId::from(symbol);
    let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();
    while seen.insert(current.0) {
      let data = semantics.symbols().symbol(current);
      if let sem_ts::SymbolOrigin::Import {
        from: Some(file),
        imported,
      } = &data.origin
      {
        if let Some(resolved) = semantics.resolve_export(*file, imported, ns) {
          current = resolved;
          continue;
        }
      }
      break;
    }
    semantic_js::SymbolId::from(current)
  }

  fn resolve_expr_symbol(
    &self,
    lower: &LowerResult,
    expr: hir_js::ids::ExprId,
    span: TextRange,
    preferred_ns: sem_ts::Namespace,
    locals: &sem_locals::TsLocalSemantics,
    semantics: Option<&sem_ts::TsProgramSemantics>,
  ) -> Option<semantic_js::SymbolId> {
    if let Some(sym) = locals.resolve_expr_span(span) {
      return Some(self.map_local_symbol(sym, preferred_ns, lower, locals, semantics));
    }
    self.resolve_hir_expr_symbol(lower, expr, Some(span), preferred_ns, locals, semantics)
  }

  fn resolve_hir_expr_symbol(
    &self,
    lower: &LowerResult,
    expr: hir_js::ids::ExprId,
    span_hint: Option<TextRange>,
    preferred_ns: sem_ts::Namespace,
    locals: &sem_locals::TsLocalSemantics,
    semantics: Option<&sem_ts::TsProgramSemantics>,
  ) -> Option<semantic_js::SymbolId> {
    for body in lower.bodies.iter() {
      if let Some(data) = body.exprs.get(expr.0 as usize) {
        if let Some(hint) = span_hint {
          if data.span != hint && !(data.span.is_empty() && hint.is_empty()) {
            continue;
          }
        }
        match &data.kind {
          hir_js::hir::ExprKind::Ident(name_id) => {
            if let Some(sym) = locals.resolve_expr_span(data.span) {
              return Some(self.map_local_symbol(sym, preferred_ns, lower, locals, semantics));
            }
            if let Some(semantics) = semantics {
              if let Some(name) = lower.names.resolve(*name_id) {
                if let Some(resolved) =
                  semantics.resolve_in_module(sem_ts::FileId(lower.hir.file.0), name, preferred_ns)
                {
                  let symbol = semantic_js::SymbolId::from(resolved);
                  return Some(self.canonical_symbol(symbol, preferred_ns, Some(semantics)));
                }
              }
            }
          }
          hir_js::hir::ExprKind::Call(call) => {
            if let Some(symbol) = self.resolve_hir_expr_symbol(
              lower,
              call.callee,
              None,
              preferred_ns,
              locals,
              semantics,
            ) {
              return Some(symbol);
            }
          }
          hir_js::hir::ExprKind::Member(member) => {
            if let Some(symbol) = self.resolve_hir_expr_symbol(
              lower,
              member.object,
              None,
              preferred_ns,
              locals,
              semantics,
            ) {
              return Some(symbol);
            }
          }
          _ => {}
        }
      }
    }
    None
  }

  fn synthetic_symbol_for_def(&self, def: DefId) -> semantic_js::SymbolId {
    semantic_js::SymbolId(LOCAL_SYMBOL_OFFSET | def.0)
  }

  fn import_specifier_def(
    lower: &LowerResult,
    id: hir_js::ids::ImportSpecifierId,
  ) -> Option<(DefId, sem_ts::Namespace)> {
    for import in lower.hir.imports.iter() {
      if let hir_js::ImportKind::Es(es) = &import.kind {
        for named in es.named.iter() {
          if named.id == id {
            let ns = if named.is_type_only || es.is_type_only {
              sem_ts::Namespace::TYPE
            } else {
              sem_ts::Namespace::VALUE
            };
            if let Some(def) = named.local_def {
              return Some((def, ns));
            }
          }
        }
      }
    }
    None
  }

  fn export_specifier_def(
    lower: &LowerResult,
    id: hir_js::ids::ExportSpecifierId,
  ) -> Option<(DefId, sem_ts::Namespace)> {
    for export in lower.hir.exports.iter() {
      if let hir_js::ExportKind::Named(named) = &export.kind {
        for spec in named.specifiers.iter() {
          if spec.id == id {
            let ns = if spec.is_type_only || named.is_type_only {
              sem_ts::Namespace::TYPE
            } else {
              sem_ts::Namespace::VALUE
            };
            if let Some(def) = spec.local_def {
              return Some((def, ns));
            }
          }
        }
      }
    }
    None
  }

  fn def_kind_namespaces(kind: HirDefKind) -> sem_ts::Namespace {
    match kind {
      HirDefKind::Class => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
      HirDefKind::Constructor
      | HirDefKind::Field
      | HirDefKind::Function
      | HirDefKind::Method
      | HirDefKind::Var
      | HirDefKind::Param => sem_ts::Namespace::VALUE,
      HirDefKind::TypeAlias | HirDefKind::Interface | HirDefKind::TypeParam => {
        sem_ts::Namespace::TYPE
      }
      HirDefKind::Enum => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
      HirDefKind::Namespace | HirDefKind::Module => {
        sem_ts::Namespace::VALUE | sem_ts::Namespace::NAMESPACE
      }
      HirDefKind::ImportBinding | HirDefKind::ExportAlias => {
        sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
      }
      _ => sem_ts::Namespace::VALUE,
    }
  }

  fn map_file_kind(kind: FileKind) -> HirFileKind {
    match kind {
      FileKind::Js => HirFileKind::Js,
      FileKind::Ts => HirFileKind::Ts,
      FileKind::Tsx => HirFileKind::Tsx,
      FileKind::Jsx => HirFileKind::Jsx,
      FileKind::Dts => HirFileKind::Dts,
    }
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
      DefKind::Import(_) | DefKind::Type(_) => None,
    })
  }

  fn type_members_to_parts(
    &mut self,
    members: &[Node<TypeMember>],
  ) -> (
    Vec<TsProperty>,
    Vec<SignatureId>,
    Vec<SignatureId>,
    Vec<Indexer>,
  ) {
    let mut properties = Vec::new();
    let mut call_signatures = Vec::new();
    let mut construct_signatures = Vec::new();
    let mut indexers = Vec::new();
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
            properties.push(TsProperty {
              key: PropKey::String(self.type_store.intern_name(name)),
              data: PropData {
                ty,
                optional: prop.stx.optional,
                readonly: prop.stx.readonly,
                accessibility: None,
                is_method: false,
                origin: None,
                declared_on: None,
              },
            });
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
            let func_ty = self.callable_type(params, ret, None);
            properties.push(TsProperty {
              key: PropKey::String(self.type_store.intern_name(name)),
              data: PropData {
                ty: func_ty,
                optional: method.stx.optional,
                readonly: false,
                accessibility: None,
                is_method: true,
                origin: None,
                declared_on: None,
              },
            });
          }
        }
        TypeMember::Constructor(cons) => {
          let sig = self.signature_from_member(&cons.stx.parameters, cons.stx.return_type.as_ref());
          construct_signatures.push(self.type_store.intern_signature(sig));
        }
        TypeMember::CallSignature(call) => {
          let sig = self.signature_from_member(&call.stx.parameters, call.stx.return_type.as_ref());
          call_signatures.push(self.type_store.intern_signature(sig));
        }
        TypeMember::IndexSignature(index) => {
          let value = self.type_from_type_expr(&index.stx.type_annotation);
          let param_type = self.type_from_type_expr(&index.stx.parameter_type);
          indexers.push(Indexer {
            key_type: param_type,
            value_type: value,
            readonly: index.stx.readonly,
          });
        }
        _ => {}
      }
    }
    (properties, call_signatures, construct_signatures, indexers)
  }

  fn signature_from_member(
    &mut self,
    params: &[Node<TypeFunctionParameter>],
    ret: Option<&Node<TypeExpr>>,
  ) -> Signature {
    let params: Vec<Param> = params
      .iter()
      .map(|param| {
        let TypeFunctionParameter {
          name,
          optional,
          rest,
          type_expr,
        } = param.stx.as_ref();
        Param {
          name: name
            .as_ref()
            .map(|n| self.type_store.intern_name(n.clone())),
          ty: self.type_from_type_expr(type_expr),
          optional: *optional,
          rest: *rest,
        }
      })
      .collect();
    let ret = ret
      .map(|ty| self.type_from_type_expr(ty))
      .unwrap_or(self.builtin.unknown);
    Signature {
      params,
      ret,
      type_params: Vec::new(),
      this_param: None,
    }
  }

  fn interface_type(&mut self, members: &[Node<TypeMember>], extends: &[Node<TypeExpr>]) -> TypeId {
    let (properties, call_signatures, construct_signatures, indexers) =
      self.type_members_to_parts(members);
    let mut types = Vec::new();
    if !properties.is_empty()
      || !call_signatures.is_empty()
      || !construct_signatures.is_empty()
      || !indexers.is_empty()
    {
      let shape = self.type_store.intern_shape(types_ts_interned::Shape {
        properties,
        call_signatures,
        construct_signatures,
        indexers,
      });
      types.push(self.type_store.intern_type(TypeKind::Object(
        self.type_store.intern_object(InternedObjectType { shape }),
      )));
    }
    for base in extends {
      types.push(self.type_from_type_expr(base));
    }
    match types.len() {
      0 => self.builtin.any,
      1 => types[0],
      _ => self.type_store.intersection(types),
    }
  }

  fn lookup_type_def(&self, name: &str) -> Option<DefId> {
    self.def_data.iter().find_map(|(id, data)| {
      (matches!(data.kind, DefKind::Type(_)) && data.name == name).then(|| *id)
    })
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
      TypeExpr::TypeReference(reference) => {
        let reference = reference.stx.as_ref();
        let def = match &reference.name {
          TypeEntityName::Identifier(name) => self.lookup_type_def(name),
          TypeEntityName::Qualified(qualified) => self.lookup_type_def(&qualified.right),
          TypeEntityName::Import(_) => None,
        };
        let args = reference
          .type_arguments
          .as_ref()
          .map(|args| {
            args
              .iter()
              .map(|arg| self.type_from_type_expr(arg))
              .collect()
          })
          .unwrap_or_default();
        match def {
          Some(def) => self.type_store.intern_type(TypeKind::Ref { def, args }),
          None => self.builtin.unknown,
        }
      }
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types.iter().map(|t| self.type_from_type_expr(t)).collect();
        self.union_types(members)
      }
      TypeExpr::IntersectionType(intersection) => {
        let members = intersection
          .stx
          .types
          .iter()
          .map(|t| self.type_from_type_expr(t))
          .collect();
        self.type_store.intersection(members)
      }
      TypeExpr::ArrayType(arr) => {
        let TypeArray { element_type, .. } = arr.stx.as_ref();
        let elem = self.type_from_type_expr(element_type);
        self.array_type(elem)
      }
      TypeExpr::TupleType(tuple) => {
        let tuple = tuple.stx.as_ref();
        let elems: Vec<TupleElem> = tuple
          .elements
          .iter()
          .map(|elem| {
            let TypeTupleElement {
              optional,
              rest,
              type_expr,
              ..
            } = elem.stx.as_ref();
            TupleElem {
              ty: self.type_from_type_expr(type_expr),
              optional: *optional,
              rest: *rest,
              readonly: tuple.readonly,
            }
          })
          .collect();
        self.type_store.intern_type(TypeKind::Tuple(elems))
      }
      TypeExpr::FunctionType(func) => {
        let params = func
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&func.stx.return_type);
        self.callable_type(params, ret, None)
      }
      TypeExpr::ConstructorType(cons) => {
        let params = cons
          .stx
          .parameters
          .iter()
          .map(|p| self.type_from_type_expr(&p.stx.type_expr))
          .collect();
        let ret = self.type_from_type_expr(&cons.stx.return_type);
        self.callable_type(params, ret, None)
      }
      TypeExpr::ObjectType(obj) => {
        let (properties, call_signatures, construct_signatures, indexers) =
          self.type_members_to_parts(&obj.stx.members);
        self.object_type_from_parts(properties, call_signatures, construct_signatures, indexers)
      }
      TypeExpr::ParenthesizedType(inner) => self.type_from_type_expr(&inner.stx.type_expr),
      TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
        TypeLiteral::Boolean(value) => self.literal_boolean(*value),
        TypeLiteral::Number(n) => self.literal_number(n),
        TypeLiteral::String(s) => self.literal_string(s),
        TypeLiteral::Null => self.builtin.null,
        _ => self.builtin.unknown,
      },
      TypeExpr::TypePredicate(pred) => {
        if pred.stx.asserts {
          self.builtin.void
        } else {
          self.builtin.boolean
        }
      }
      TypeExpr::ThisType(_) => self.type_store.intern_type(TypeKind::This),
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
}

impl BodyBuilder {
  fn new(id: BodyId, file: FileId) -> BodyBuilder {
    BodyBuilder {
      id,
      file,
      stmts: Vec::new(),
      expr_spans: Vec::new(),
    }
  }

  fn new_expr(&mut self, span: TextRange, kind: HirExprKind) -> HirExpr {
    let id = ExprId(self.expr_spans.len() as u32);
    self.expr_spans.push(span);
    HirExpr { id, span, kind }
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
              state.diagnostics.push(Diagnostic::error(
                CODE_UNSUPPORTED_PATTERN,
                "unsupported pattern",
                loc_to_span(self.file, pat.loc),
              ));
              continue;
            }
          };
          let typ = declarator
            .type_annotation
            .as_ref()
            .map(|t| state.type_from_type_expr(t));
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
        }
      }
      Expr::SatisfiesExpr(satisfies) => {
        let expr = self.lower_expr(*satisfies.stx.expression, state);
        let _ = satisfies.stx.type_annotation;
        HirExprKind::TypeAssertion {
          expr: Box::new(expr),
          typ: None,
          _const_assertion: false,
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
    }
  }
}

fn lower_object_literal(
  file: FileId,
  obj: LitObjExpr,
  state: &mut ProgramState,
  builder: &mut BodyBuilder,
) -> Vec<(String, HirExpr)> {
  let mut props = Vec::new();
  for member in obj.members.into_iter() {
    let _member_span = loc_to_span(file, member.loc).range;
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
          props.push((key_name, value));
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
        props.push((name, expr));
      }
      ObjMember {
        typ: ObjMemberType::Rest { val },
      } => {
        let expr = builder.lower_expr(val, state);
        props.push(("...".to_string(), expr));
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
    FatalError::Host(err) => diagnostics::host_error(None, err.to_string()),
    FatalError::Cancelled => Diagnostic::error("CANCEL0001", "operation cancelled", placeholder)
      .with_note("operation was cancelled by the host"),
    FatalError::Ice(ice) => {
      let span = span_from_context(&ice.context, placeholder);
      let mut diagnostic =
        diagnostics::ice(span, format!("internal compiler error: {}", ice.message));
      if let Some(backtrace) = ice.backtrace {
        diagnostic.push_note(backtrace);
      }
      diagnostic
    }
    FatalError::OutOfMemory => Diagnostic::error("OOM0001", "out of memory", placeholder)
      .with_note("the checker ran out of memory while processing this program"),
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
