use ::semantic_js::ts as sem_ts;
pub use diagnostics::{Diagnostic, FileId, Label, Severity, Span, TextRange};
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
  TypeArray, TypeExpr, TypeLiteral, TypeMember, TypePropertyKey, TypeUnion,
};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::parse;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;
use tracing::debug_span;

use crate::{FatalError, HostError, Ice, IceContext};

#[path = "check/mod.rs"]
pub(crate) mod check;

use check::narrow::{
  narrow_by_discriminant, narrow_by_in_check, narrow_by_typeof, truthy_falsy_types, Facts,
};

use crate::lib_support::{CompilerOptions, FileKind, LibFile, LibManager};
pub(crate) const CODE_NON_DTS_LIB: &str = "TC0004";
pub(crate) const CODE_UNKNOWN_IDENTIFIER: &str = "TC0005";
pub(crate) const CODE_EXCESS_PROPERTY: &str = "TC0006";
pub(crate) const CODE_TYPE_MISMATCH: &str = "TC0007";
pub use hir_js::{BodyId, DefId, ExprId};

/// Interned type handle.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
pub struct TypeId(pub u32);

const CODE_UNRESOLVED_MODULE: &str = "TC1001";
const CODE_UNKNOWN_EXPORT: &str = "TC1002";
const CODE_UNSUPPORTED_IMPORT_PATTERN: &str = "TC1003";
const CODE_UNSUPPORTED_PATTERN: &str = "TC1004";
const CODE_UNSUPPORTED_PARAM_PATTERN: &str = "TC1005";
const CODE_MISSING_BODY: &str = "ICE0002";
const CODE_ARGUMENT_COUNT_MISMATCH: &str = "TC1006";

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
  use serde::{Deserialize, Serialize};

  /// Opaque symbol identifier.
  #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
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
#[derive(Clone, Debug, Serialize, Deserialize)]
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
  program: &'a Program,
  ty: TypeId,
}

impl<'a> std::fmt::Display for TypeDisplay<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut state = self.program.lock_state();
    state.ensure_analyzed(
      &self.program.host,
      &self.program.roots,
      &self.program.cancelled,
    );
    let TypeDisplay { program: _, ty } = *self;
    let kind = state.type_store.kind(ty).clone();
    drop(state);
    format_type(kind, self.program, f)
  }
}

fn format_type(
  kind: TypeKind,
  program: &Program,
  f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
  match kind {
    TypeKind::Any => write!(f, "any"),
    TypeKind::Unknown => write!(f, "unknown"),
    TypeKind::Number => write!(f, "number"),
    TypeKind::String => write!(f, "string"),
    TypeKind::Boolean => write!(f, "boolean"),
    TypeKind::Null => write!(f, "null"),
    TypeKind::Undefined => write!(f, "undefined"),
    TypeKind::LiteralString(s) => write!(f, "\"{}\"", s),
    TypeKind::LiteralNumber(n) => write!(f, "{}", n),
    TypeKind::LiteralBoolean(b) => write!(f, "{}", b),
    TypeKind::Void => write!(f, "void"),
    TypeKind::Never => write!(f, "never"),
    TypeKind::Array(inner) => write!(f, "{}[]", program.display_type(inner)),
    TypeKind::ReadonlyArray(inner) => write!(f, "readonly {}[]", program.display_type(inner)),
    TypeKind::Tuple(elements, readonly) => {
      if readonly {
        write!(f, "readonly ")?;
      }
      write!(f, "[")?;
      for (idx, el) in elements.iter().enumerate() {
        if idx > 0 {
          write!(f, ", ")?;
        }
        write!(f, "{}", program.display_type(*el))?;
      }
      write!(f, "]")
    }
    TypeKind::Union(types) => {
      let mut first = true;
      for ty in types {
        if !first {
          write!(f, " | ")?;
        }
        first = false;
        write!(f, "{}", program.display_type(ty))?;
      }
      Ok(())
    }
    TypeKind::Function { params, ret } => {
      write!(f, "(")?;
      for (idx, p) in params.iter().enumerate() {
        if idx > 0 {
          write!(f, ", ")?;
        }
        write!(f, "{}", program.display_type(*p))?;
      }
      write!(f, ") -> {}", program.display_type(ret))
    }
    TypeKind::Object(obj) => {
      write!(f, "{{")?;
      let mut first = true;
      for (k, v) in obj.props.iter() {
        if !first {
          write!(f, ", ")?;
        }
        first = false;
        write!(
          f,
          "{}{}{}: {}",
          if v.readonly { "readonly " } else { "" },
          k,
          if v.optional { "?" } else { "" },
          program.display_type(v.typ)
        )?;
      }
      if let Some(ty) = obj.string_index {
        if !first {
          write!(f, ", ")?;
        }
        first = false;
        write!(f, "[key: string]: {}", program.display_type(ty))?;
      }
      if let Some(ty) = obj.number_index {
        if !first {
          write!(f, ", ")?;
        }
        write!(f, "[index: number]: {}", program.display_type(ty))?;
      }
      write!(f, "}}")
    }
    TypeKind::Predicate {
      parameter,
      asserted,
      asserts,
    } => {
      if asserts {
        write!(f, "asserts {}", parameter)?;
      } else {
        write!(f, "{}", parameter)?;
      }
      if let Some(ty) = asserted {
        if asserts {
          write!(f, " is {}", program.display_type(ty))?;
        } else {
          write!(f, " is {}", program.display_type(ty))?;
        }
      }
      Ok(())
    }
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
    TypeDisplay { program: self, ty }
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
}

#[derive(Clone, Debug)]
struct FuncData {
  params: Vec<ParamData>,
  return_ann: Option<TypeId>,
  body: Option<BodyId>,
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
}

#[derive(Clone, Debug)]
struct ImportData {
  from: FileId,
  original: String,
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
    mode: VarDeclMode,
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
  Satisfies {
    expr: Box<HirExpr>,
    typ: TypeId,
  },
  Array(Vec<HirExpr>),
  Unknown,
}

#[derive(Clone, Copy, Default)]
struct ExprContext {
  no_widen: bool,
  const_assertion: bool,
  contextual_type: Option<TypeId>,
}

impl ExprContext {
  fn prefer_literals(&self) -> bool {
    self.no_widen || self.const_assertion || self.contextual_type.is_some()
  }

  fn for_child(&self, contextual_type: Option<TypeId>) -> ExprContext {
    ExprContext {
      no_widen: self.const_assertion || contextual_type.is_some(),
      const_assertion: self.const_assertion,
      contextual_type,
    }
  }
}

#[derive(Clone, Debug)]
pub(crate) struct TypeStore {
  kinds: Vec<TypeKind>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ObjectProperty {
  pub(crate) typ: TypeId,
  pub(crate) optional: bool,
  pub(crate) readonly: bool,
}

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
  Array(TypeId),
  ReadonlyArray(TypeId),
  Tuple(Vec<TypeId>, bool),
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
      return TypeId(idx as u32);
    }
    let id = TypeId(self.kinds.len() as u32);
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

  pub(crate) fn readonly_array(&mut self, element: TypeId) -> TypeId {
    self.alloc(TypeKind::ReadonlyArray(element))
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

struct ProgramState {
  analyzed: bool,
  lib_manager: Arc<LibManager>,
  compiler_options: CompilerOptions,
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  body_data: HashMap<BodyId, BodyData>,
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
  builtin: BuiltinTypes,
  next_def: u32,
  next_body: u32,
  next_symbol: u32,
  type_stack: Vec<DefId>,
}

impl ProgramState {
  fn new(lib_manager: Arc<LibManager>) -> ProgramState {
    let (type_store, builtin) = TypeStore::new();
    ProgramState {
      analyzed: false,
      lib_manager,
      compiler_options: CompilerOptions::default(),
      files: HashMap::new(),
      def_data: HashMap::new(),
      body_data: HashMap::new(),
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
      builtin,
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
    self.recompute_global_bindings();
    if !self.sem_hir.is_empty() {
      self.compute_semantics(host, roots);
    }
    self.analyzed = true;
    Ok(())
  }

  fn collect_libraries(&mut self, host: &dyn Host) -> Vec<LibFile> {
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
            mode: VarDeclMode::Const,
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
                  CODE_UNKNOWN_EXPORT,
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
          kind: DefKind::Var(VarData {
            typ: type_ann,
            init: init_id,
            body: builder.id,
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
    let return_ann = func
      .return_type
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
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
      diagnostics: Vec::new(),
      return_types: Vec::new(),
    };

    for stmt in body.stmts.iter() {
      self.check_stmt(stmt, &mut env, &mut result, body.file);
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
    result: &mut BodyCheckResult,
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
        mode,
      } => {
        let expr_ctx = ExprContext {
          no_widen: matches!(mode, VarDeclMode::Const),
          const_assertion: false,
          contextual_type: *typ,
        };
        let init_checked = init
          .as_ref()
          .map(|e| self.check_expr_with_context(e, env, result, file, expr_ctx));
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
          self.check_stmt(stmt, &mut then_env, result, file);
        }
        for stmt in alternate {
          self.check_stmt(stmt, &mut else_env, result, file);
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
          self.check_stmt(stmt, env, result, file);
        }
      }
      HirStmt::While { test, body, .. } => {
        let (_, cond_facts) = self.check_expr(test, env, result, file);
        let mut body_env = env.clone();
        self.apply_fact_map(&mut body_env, &cond_facts.truthy);
        self.apply_fact_map(&mut body_env, &cond_facts.assertions);
        for stmt in body {
          self.check_stmt(stmt, &mut body_env, result, file);
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
    self.check_expr_with_context(expr, env, result, file, ExprContext::default())
  }

  fn check_expr_with_context(
    &mut self,
    expr: &HirExpr,
    env: &mut HashMap<String, SymbolBinding>,
    result: &mut BodyCheckResult,
    file: FileId,
    ctx: ExprContext,
  ) -> (TypeId, Facts) {
    let mut facts = Facts::default();
    let preserve_literals = ctx.prefer_literals();
    let ty = match &expr.kind {
      HirExprKind::NumberLiteral(value) => {
        if preserve_literals {
          self.type_store.literal_number(value.clone())
        } else {
          self.builtin.number
        }
      }
      HirExprKind::StringLiteral(value) => {
        if preserve_literals {
          self.type_store.literal_string(value.clone())
        } else {
          self.builtin.string
        }
      }
      HirExprKind::BooleanLiteral(value) => {
        if preserve_literals {
          self.type_store.literal_boolean(*value)
        } else {
          self.builtin.boolean
        }
      }
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
        let (obj_ty, _) =
          self.check_expr_with_context(object, env, result, file, ctx.for_child(None));
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
          let (_inner_ty, inner_facts) =
            self.check_expr_with_context(inner, env, result, file, ctx.for_child(None));
          facts.truthy = inner_facts.falsy;
          facts.falsy = inner_facts.truthy;
          facts.assertions = inner_facts.assertions;
          self.builtin.boolean
        }
        OperatorName::Typeof => self.type_store.literal_string("string".to_string()),
        _ => {
          let _ = self.check_expr_with_context(inner, env, result, file, ctx.for_child(None));
          self.builtin.unknown
        }
      },
      HirExprKind::Binary { op, left, right } => match op {
        OperatorName::LogicalAnd => {
          let (lt, lf) = self.check_expr_with_context(left, env, result, file, ctx.for_child(None));
          let mut right_env = env.clone();
          self.apply_fact_map(&mut right_env, &lf.truthy);
          self.apply_fact_map(&mut right_env, &lf.assertions);
          let (rt, rf) =
            self.check_expr_with_context(right, &mut right_env, result, file, ctx.for_child(None));

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
          let (lt, lf) = self.check_expr_with_context(left, env, result, file, ctx.for_child(None));
          let mut right_env = env.clone();
          self.apply_fact_map(&mut right_env, &lf.falsy);
          self.apply_fact_map(&mut right_env, &lf.assertions);
          let (rt, rf) =
            self.check_expr_with_context(right, &mut right_env, result, file, ctx.for_child(None));

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
          let (_lt, lfacts) =
            self.check_expr_with_context(left, env, result, file, ctx.for_child(None));
          let (_rt, rfacts) =
            self.check_expr_with_context(right, env, result, file, ctx.for_child(None));
          // typeof x === "string"
          if let HirExprKind::Unary {
            op: OperatorName::Typeof,
            expr: inner,
          } = &left.kind
          {
            if let HirExprKind::StringLiteral(value) = &right.kind {
              let (inner_ty, _) =
                self.check_expr_with_context(inner, env, result, file, ctx.for_child(None));
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
              let (obj_ty, _) =
                self.check_expr_with_context(object, env, result, file, ctx.for_child(None));
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
              let (obj_ty, _) =
                self.check_expr_with_context(object, env, result, file, ctx.for_child(None));
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
          let (_lt, lf) =
            self.check_expr_with_context(left, env, result, file, ctx.for_child(None));
          let (_rt, rf) =
            self.check_expr_with_context(right, env, result, file, ctx.for_child(None));
          facts.merge(lf, &mut self.type_store, &self.builtin);
          facts.merge(rf, &mut self.type_store, &self.builtin);
          self.builtin.boolean
        }
        OperatorName::In => {
          let (_lt, lf) =
            self.check_expr_with_context(left, env, result, file, ctx.for_child(None));
          let (rt, rf) =
            self.check_expr_with_context(right, env, result, file, ctx.for_child(None));
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
          let (left_ty, lfacts) =
            self.check_expr_with_context(left, env, result, file, ctx.for_child(None));
          let (right_ty, rfacts) =
            self.check_expr_with_context(right, env, result, file, ctx.for_child(None));
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
        let (callee_ty, _) =
          self.check_expr_with_context(callee, env, result, file, ctx.for_child(None));
        if let TypeKind::Function { params, ret } = self.type_store.kind(callee_ty).clone() {
          if params.len() != args.len() {
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
            let arg_ctx = ctx.for_child(params.get(idx).copied());
            let (arg_ty, _) = self.check_expr_with_context(arg, env, result, file, arg_ctx);
            arg_types.push(arg_ty);
            if let Some(expected) = params.get(idx) {
              check::assign::check_assignment(self, Some(arg), arg_ty, *expected, result, file);
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
        let (_, cond_facts) =
          self.check_expr_with_context(test, env, result, file, ctx.for_child(None));
        let mut then_env = env.clone();
        self.apply_fact_map(&mut then_env, &cond_facts.truthy);
        self.apply_fact_map(&mut then_env, &cond_facts.assertions);
        let mut else_env = env.clone();
        self.apply_fact_map(&mut else_env, &cond_facts.falsy);
        self.apply_fact_map(&mut else_env, &cond_facts.assertions);
        let branch_ctx = ctx.for_child(ctx.contextual_type);
        let (cons_ty, cons_facts) =
          self.check_expr_with_context(consequent, &mut then_env, result, file, branch_ctx);
        let (alt_ty, alt_facts) =
          self.check_expr_with_context(alternate, &mut else_env, result, file, branch_ctx);
        facts.merge(cons_facts, &mut self.type_store, &self.builtin);
        facts.merge(alt_facts, &mut self.type_store, &self.builtin);
        self.type_store.union(vec![cons_ty, alt_ty], &self.builtin)
      }
      HirExprKind::Object(props) => {
        let contextual_object = ctx
          .contextual_type
          .and_then(|ty| self.expect_object_type(ty));
        let mut obj = ObjectType::empty();
        for (k, v) in props.iter() {
          if k == "..." {
            continue;
          }
          let expected_prop = contextual_object.as_ref().and_then(|obj| obj.props.get(k));
          let child_ctx = ctx.for_child(expected_prop.map(|p| p.typ));
          let (ty, _) = self.check_expr_with_context(v, env, result, file, child_ctx);
          let readonly = ctx.const_assertion || expected_prop.map(|p| p.readonly).unwrap_or(false);
          obj.props.insert(
            k.clone(),
            ObjectProperty {
              typ: ty,
              optional: false,
              readonly,
            },
          );
        }
        self.type_store.object(obj)
      }
      HirExprKind::Array(values) => {
        let contextual_kind = ctx
          .contextual_type
          .map(|ty| self.type_store.kind(ty).clone());
        let mut expected_tuple: Option<(Vec<TypeId>, bool)> = None;
        let mut expected_array: Option<(TypeId, bool)> = None;
        if let Some(kind) = contextual_kind {
          match kind {
            TypeKind::Tuple(elements, readonly) => {
              expected_tuple = Some((elements, readonly));
            }
            TypeKind::ReadonlyArray(elem) => {
              expected_array = Some((elem, true));
            }
            TypeKind::Array(elem) => {
              expected_array = Some((elem, false));
            }
            _ => {}
          }
        }
        let mut elem_types = Vec::new();
        for (idx, v) in values.iter().enumerate() {
          let expected_elem = expected_tuple
            .as_ref()
            .and_then(|(elements, _)| elements.get(idx).copied())
            .or_else(|| expected_array.map(|(elem, _)| elem));
          let child_ctx = ctx.for_child(expected_elem);
          let (elem_ty, _) = self.check_expr_with_context(v, env, result, file, child_ctx);
          elem_types.push(elem_ty);
        }
        if ctx.const_assertion || expected_tuple.is_some() {
          let readonly = ctx.const_assertion
            || expected_tuple
              .as_ref()
              .map(|(_, readonly)| *readonly)
              .unwrap_or(false);
          self.type_store.tuple(elem_types, readonly)
        } else {
          let elem = self.type_store.union(elem_types, &self.builtin);
          if let Some((_, true)) = expected_array {
            self.type_store.readonly_array(elem)
          } else {
            self.type_store.array(elem)
          }
        }
      }
      HirExprKind::Satisfies { expr, typ } => {
        let (inner_ty, inner_facts) =
          self.check_expr_with_context(expr, env, result, file, ctx.for_child(Some(*typ)));
        facts = inner_facts;
        check::assign::check_assignment(self, Some(expr.as_ref()), inner_ty, *typ, result, file);
        inner_ty
      }
      HirExprKind::TypeAssertion {
        expr,
        typ,
        _const_assertion,
      } => {
        if *_const_assertion {
          let (inner_ty, inner_facts) = self.check_expr_with_context(
            expr,
            env,
            result,
            file,
            ExprContext {
              no_widen: true,
              const_assertion: true,
              contextual_type: None,
            },
          );
          facts = inner_facts;
          inner_ty
        } else {
          let (inner_ty, inner_facts) =
            self.check_expr_with_context(expr, env, result, file, ctx.for_child(*typ));
          facts = inner_facts;
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

  fn expect_object_type(&self, ty: TypeId) -> Option<ObjectType> {
    match self.type_store.kind(ty) {
      TypeKind::Object(obj) => Some(obj.clone()),
      TypeKind::Union(members) => {
        members
          .iter()
          .find_map(|member| match self.type_store.kind(*member) {
            TypeKind::Object(obj) => Some(obj.clone()),
            _ => None,
          })
      }
      _ => None,
    }
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
      _ => false,
    })
  }

  fn is_assignable(&self, src: TypeId, dst: TypeId) -> bool {
    if src == dst || dst == self.builtin.any || src == self.builtin.never {
      return true;
    }
    match (self.type_store.kind(src), self.type_store.kind(dst)) {
      (TypeKind::LiteralNumber(_), TypeKind::Number) => true,
      (TypeKind::LiteralString(_), TypeKind::String) => true,
      (TypeKind::LiteralBoolean(_), TypeKind::Boolean) => true,
      (TypeKind::Union(members), _) => members.iter().all(|m| self.is_assignable(*m, dst)),
      (_, TypeKind::Union(members)) => members.iter().any(|m| self.is_assignable(src, *m)),
      (TypeKind::Array(source_elem), TypeKind::Array(target_elem)) => {
        self.is_assignable(*source_elem, *target_elem)
      }
      (TypeKind::Array(source_elem), TypeKind::ReadonlyArray(target_elem)) => {
        self.is_assignable(*source_elem, *target_elem)
      }
      (TypeKind::ReadonlyArray(source_elem), TypeKind::ReadonlyArray(target_elem)) => {
        self.is_assignable(*source_elem, *target_elem)
      }
      (TypeKind::Tuple(source_elems, source_readonly), TypeKind::Array(target_elem)) => {
        if *source_readonly {
          return false;
        }
        source_elems
          .iter()
          .copied()
          .all(|elem| self.is_assignable(elem, *target_elem))
      }
      (TypeKind::Tuple(source_elems, _), TypeKind::ReadonlyArray(target_elem)) => source_elems
        .iter()
        .copied()
        .all(|elem| self.is_assignable(elem, *target_elem)),
      (
        TypeKind::Tuple(source_elems, source_readonly),
        TypeKind::Tuple(target_elems, target_readonly),
      ) => {
        if !*target_readonly && *source_readonly {
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
      query_span!(
        "typecheck_ts.type_of_def",
        self.def_data.get(&def).map(|d| d.file.0),
        Some(def.0),
        self.body_of_def(def).map(|b| b.0),
        cache_hit
      ),
      self.def_types.get(&def).copied(),
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
        if let Some(t) = var.typ {
          t
        } else if let Some(init) = var.init {
          let res = self.check_body(var.body);
          res.expr_type(init).unwrap_or(self.builtin.unknown)
        } else {
          self.builtin.unknown
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
        self
          .type_store
          .union(res.return_types.clone(), &self.builtin)
      }
    } else {
      self.builtin.unknown
    };
    let ty = self.type_store.function(param_types, ret);
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
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types.iter().map(|t| self.type_from_type_expr(t)).collect();
        self.type_store.union(members, &self.builtin)
      }
      TypeExpr::ArrayType(arr) => {
        let TypeArray { element_type, .. } = arr.stx.as_ref();
        let elem = self.type_from_type_expr(element_type);
        if arr.stx.readonly {
          self.type_store.readonly_array(elem)
        } else {
          self.type_store.array(elem)
        }
      }
      TypeExpr::TupleType(tuple) => {
        let mut elements = Vec::new();
        for el in tuple.stx.elements.iter() {
          elements.push(self.type_from_type_expr(&el.stx.type_expr));
        }
        self.type_store.tuple(elements, tuple.stx.readonly)
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
        let mut object = ObjectType::empty();
        for member in obj.stx.members.iter() {
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
            mode: var.stx.mode,
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
        let typ = state.type_from_type_expr(&satisfies.stx.type_annotation);
        HirExprKind::Satisfies {
          expr: Box::new(expr),
          typ,
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
