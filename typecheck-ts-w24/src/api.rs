use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::class_or_object::ObjMember;
use parse_js::ast::class_or_object::ObjMemberType;
use parse_js::ast::expr::lit::LitArrElem;
use parse_js::ast::expr::lit::LitObjExpr;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::import_export::ExportNames;
use parse_js::ast::import_export::ImportNames;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::ParamDecl;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::TypeArray;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::ast::type_expr::TypeLiteral;
use parse_js::ast::type_expr::TypeUnion;
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::parse;
use serde::Deserialize;
use serde::Serialize;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Arc;
use thiserror::Error;

/// Identifier for a file in a [`Program`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
pub struct FileId(pub u32);

/// Identifier for a definition (function/variable/import).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
pub struct DefId(pub u32);

/// Identifier for an executable body (top-level or function body).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
pub struct BodyId(pub u32);

/// Identifier for an expression inside a specific [`BodyId`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
pub struct ExprId(pub u32);

/// Interned type handle.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
pub struct TypeId(pub u32);

/// Simple range inside a file (UTF-8 byte offsets).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct TextRange {
  /// Starting byte offset, inclusive.
  pub start: u32,
  /// Ending byte offset, exclusive.
  pub end: u32,
}

/// Range paired with a [`FileId`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Span {
  /// File containing the span.
  pub file: FileId,
  /// Byte range inside the file.
  pub range: TextRange,
}

/// Severity for diagnostics.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum Severity {
  /// Error that prevents successful checking.
  Error,
  /// Warning that does not block checking.
  Warning,
  /// Informational note.
  Info,
}

/// Diagnostic produced while parsing/binding/checking.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Diagnostic {
  /// Machine-consumable code, if available.
  pub code: Option<String>,
  /// Human-readable message.
  pub message: String,
  /// Where the issue occurred.
  pub span: Option<Span>,
  /// Severity level.
  pub severity: Severity,
}

impl Diagnostic {
  fn error(message: impl Into<String>, span: Option<Span>) -> Diagnostic {
    Diagnostic {
      code: None,
      message: message.into(),
      span,
      severity: Severity::Error,
    }
  }
}

/// Error returned by a [`Host`].
#[derive(Debug, Error, Serialize, Deserialize, Clone)]
#[error("{message}")]
pub struct HostError {
  message: String,
}

impl HostError {
  /// Create a new host error with the given message.
  pub fn new(message: impl Into<String>) -> HostError {
    HostError {
      message: message.into(),
    }
  }
}

/// Environment provider for [`Program`].
pub trait Host: Send + Sync + 'static {
  /// Return the full text for a file.
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError>;
  /// Resolve a module specifier relative to `from`.
  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId>;
}

/// Public symbol identifier exposed through [`Program::symbol_at`].
pub mod semantic_js {
  use serde::Deserialize;
  use serde::Serialize;

  /// Opaque symbol identifier.
  #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Ord, PartialOrd)]
  pub struct SymbolId(pub u32);
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
    let mut best: Option<(ExprId, TypeId, u32)> = None;
    for (idx, span) in self.expr_spans.iter().enumerate() {
      if span.start <= offset && offset < span.end {
        let width = span.end - span.start;
        let entry = (ExprId(idx as u32), *self.expr_types.get(idx)?, width);
        best = match best {
          Some((_, _, existing)) if existing <= width => best,
          _ => Some(entry),
        };
      }
    }
    best.map(|(id, ty, _)| (id, ty))
  }
}

/// Helper returned from [`Program::display_type`].
pub struct TypeDisplay<'a> {
  program: &'a Program,
  ty: TypeId,
}

impl<'a> std::fmt::Display for TypeDisplay<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut state = self.program.state.lock().unwrap();
    state.ensure_analyzed(&self.program.host, &self.program.roots);
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
    TypeKind::Void => write!(f, "void"),
    TypeKind::Never => write!(f, "never"),
    TypeKind::Array(inner) => write!(f, "{}[]", program.display_type(inner)),
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
    TypeKind::Object(map) => {
      write!(f, "{{")?;
      let mut first = true;
      for (k, v) in map.iter() {
        if !first {
          write!(f, ", ")?;
        }
        first = false;
        write!(f, "{}: {}", k, program.display_type(*v))?;
      }
      write!(f, "}}")
    }
  }
}

/// Primary entry point for parsing and type checking.
pub struct Program {
  host: Arc<dyn Host>,
  roots: Vec<FileId>,
  state: std::sync::Mutex<ProgramState>,
}

impl Program {
  /// Create a new program from a host and root file list.
  pub fn new(host: impl Host, roots: Vec<FileId>) -> Program {
    Program {
      host: Arc::new(host),
      roots,
      state: std::sync::Mutex::new(ProgramState::new()),
    }
  }

  /// Parse, bind, and type-check all known files, returning accumulated diagnostics.
  pub fn check(&self) -> Vec<Diagnostic> {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    let body_ids: Vec<BodyId> = state.body_data.keys().copied().collect();
    let mut diagnostics = state.diagnostics.clone();
    for body in body_ids {
      let res = state.check_body(body);
      diagnostics.extend(res.diagnostics.iter().cloned());
    }
    diagnostics
  }

  /// Type for a definition.
  pub fn type_of_def(&self, def: DefId) -> TypeId {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state.type_of_def(def)
  }

  /// Check a body, returning the cached result.
  pub fn check_body(&self, body: BodyId) -> Arc<BodyCheckResult> {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state.check_body(body)
  }

  /// Type of a specific expression in a body.
  pub fn type_of_expr(&self, body: BodyId, expr: ExprId) -> TypeId {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    let result = state.check_body(body);
    result.expr_type(expr).unwrap_or(state.builtin.unknown)
  }

  /// Return symbol at a given file offset, if any.
  pub fn symbol_at(&self, file: FileId, offset: u32) -> Option<semantic_js::SymbolId> {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state.ensure_symbols_for_file(file);
    state
      .symbol_occurrences
      .get(&file)
      .and_then(|occurs| {
        occurs
          .iter()
          .find(|o| o.range.start <= offset && offset < o.range.end)
      })
      .map(|o| o.symbol)
  }

  /// Export map for a file.
  pub fn exports_of(&self, file: FileId) -> ExportMap {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state.exports_of_file(file)
  }

  /// Helper to render a type as displayable string.
  pub fn display_type(&self, ty: TypeId) -> TypeDisplay<'_> {
    TypeDisplay { program: self, ty }
  }

  /// Definitions declared in a file.
  pub fn definitions_in_file(&self, file: FileId) -> Vec<DefId> {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state
      .files
      .get(&file)
      .map(|f| f.defs.clone())
      .unwrap_or_default()
  }

  /// Friendly name for a definition.
  pub fn def_name(&self, def: DefId) -> Option<String> {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state.def_data.get(&def).map(|d| d.name.clone())
  }

  /// Body attached to a definition, if any.
  pub fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state.def_data.get(&def).and_then(|d| match &d.kind {
      DefKind::Function(func) => func.body,
      DefKind::Var(var) => Some(var.body),
      DefKind::Import(_) => None,
    })
  }

  /// Implicit top-level body for a file, if any.
  pub fn file_body(&self, file: FileId) -> Option<BodyId> {
    let mut state = self.state.lock().unwrap();
    state.ensure_analyzed(&self.host, &self.roots);
    state.files.get(&file).and_then(|f| f.top_body)
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
}

#[derive(Clone, Debug)]
struct HirExpr {
  id: ExprId,
  span: TextRange,
  kind: HirExprKind,
}

#[derive(Clone, Debug)]
enum HirExprKind {
  Number,
  String,
  Boolean,
  Null,
  Ident(String),
  Binary {
    op: OperatorName,
    left: Box<HirExpr>,
    right: Box<HirExpr>,
  },
  Call {
    callee: Box<HirExpr>,
    args: Vec<HirExpr>,
  },
  Object(Vec<(String, HirExpr)>),
  Array(Vec<HirExpr>),
  Unknown,
}

#[derive(Clone, Debug)]
struct TypeStore {
  kinds: Vec<TypeKind>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TypeKind {
  Any,
  Unknown,
  Never,
  Void,
  Number,
  String,
  Boolean,
  Null,
  Undefined,
  Array(TypeId),
  Union(Vec<TypeId>),
  Function { params: Vec<TypeId>, ret: TypeId },
  Object(BTreeMap<String, TypeId>),
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
struct BuiltinTypes {
  any: TypeId,
  unknown: TypeId,
  never: TypeId,
  void: TypeId,
  number: TypeId,
  string: TypeId,
  boolean: TypeId,
  null: TypeId,
  undefined: TypeId,
  object: TypeId,
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
    let object = store.alloc(TypeKind::Object(BTreeMap::new()));
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

  fn kind(&self, id: TypeId) -> &TypeKind {
    self.kinds.get(id.0 as usize).unwrap()
  }

  fn union(&mut self, mut types: Vec<TypeId>, builtin: &BuiltinTypes) -> TypeId {
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

  fn array(&mut self, element: TypeId) -> TypeId {
    self.alloc(TypeKind::Array(element))
  }

  fn function(&mut self, params: Vec<TypeId>, ret: TypeId) -> TypeId {
    self.alloc(TypeKind::Function { params, ret })
  }

  fn object(&mut self, props: BTreeMap<String, TypeId>) -> TypeId {
    self.alloc(TypeKind::Object(props))
  }
}

struct ProgramState {
  analyzed: bool,
  files: HashMap<FileId, FileState>,
  def_data: HashMap<DefId, DefData>,
  body_data: HashMap<BodyId, BodyData>,
  def_types: HashMap<DefId, TypeId>,
  body_results: HashMap<BodyId, Arc<BodyCheckResult>>,
  symbol_occurrences: HashMap<FileId, Vec<SymbolOccurrence>>,
  diagnostics: Vec<Diagnostic>,
  type_store: TypeStore,
  builtin: BuiltinTypes,
  next_def: u32,
  next_body: u32,
  next_symbol: u32,
  type_stack: Vec<DefId>,
}

impl ProgramState {
  fn new() -> ProgramState {
    let (type_store, builtin) = TypeStore::new();
    ProgramState {
      analyzed: false,
      files: HashMap::new(),
      def_data: HashMap::new(),
      body_data: HashMap::new(),
      def_types: HashMap::new(),
      body_results: HashMap::new(),
      symbol_occurrences: HashMap::new(),
      diagnostics: Vec::new(),
      type_store,
      builtin,
      next_def: 0,
      next_body: 0,
      next_symbol: 0,
      type_stack: Vec::new(),
    }
  }

  fn ensure_analyzed(&mut self, host: &Arc<dyn Host>, roots: &[FileId]) {
    if self.analyzed {
      return;
    }
    let mut queue: VecDeque<FileId> = roots.iter().copied().collect();
    while let Some(file) = queue.pop_front() {
      if self.files.contains_key(&file) {
        continue;
      }
      match host.file_text(file) {
        Ok(text) => match parse(&text) {
          Ok(ast) => self.bind_file(file, ast, host, &mut queue),
          Err(err) => {
            let span = loc_to_span(file, err.loc);
            self
              .diagnostics
              .push(Diagnostic::error(err.to_string(), Some(span)));
          }
        },
        Err(err) => {
          self
            .diagnostics
            .push(Diagnostic::error(err.to_string(), None));
        }
      }
    }
    self.analyzed = true;
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
          let (new_defs, stmts) =
            self.handle_var_decl(file, var_span.range, *var.stx, &mut top_body);
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
            self.handle_function_decl(file, span.range, *func.stx)
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
          defs.push(def_id);
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
                format!("unresolved module {module}"),
                Some(loc_to_span(file, stmt.loc)),
              ));
            }
          }
          if let ExportNames::Specific(names) = &export_list.stx.names {
            for name in names {
              let exportable = name.stx.exportable.clone();
              let alias = name.stx.alias.stx.name.clone();
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
                  format!("unknown export {exportable}"),
                  Some(loc_to_span(file, name.loc)),
                ));
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
              format!("unresolved module {module}"),
              Some(loc_to_span(file, stmt.loc)),
            ));
          }
          match import_stmt.stx.names {
            Some(ImportNames::Specific(ref list)) => {
              for entry in list {
                let name = entry.stx.importable.clone();
                let alias_pat = &entry.stx.alias;
                let alias_name = match &alias_pat.stx.pat.stx.as_ref() {
                  Pat::Id(id) => id.stx.name.clone(),
                  _ => {
                    self.diagnostics.push(Diagnostic::error(
                      "unsupported import pattern",
                      Some(loc_to_span(file, alias_pat.loc)),
                    ));
                    continue;
                  }
                };
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
                    "unsupported import pattern",
                    Some(loc_to_span(file, pat.loc)),
                  ));
                  continue;
                }
              };
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
        }
        Stmt::Expr(expr_stmt) => {
          let expr = top_body.lower_expr(expr_stmt.stx.expr, self);
          top_body.stmts.push(HirStmt::Expr(expr));
        }
        _ => {}
      }
    }

    let body_data = top_body.finish(None);
    self.body_data.insert(top_body_id, body_data);
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
            "unsupported pattern",
            Some(loc_to_span(file, pat.loc)),
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
          }),
        },
      );
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
        if var.export { Some(name) } else { None },
      ));
    }
    (defs, stmts)
  }

  fn handle_function_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    func: FuncDecl,
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
          "unsupported parameter pattern",
          Some(loc_to_span(file, param.loc)),
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
    if let Some(existing) = self.body_results.get(&body_id) {
      return existing.clone();
    }
    let body = match self.body_data.get(&body_id) {
      Some(b) => b.clone(),
      None => {
        let res = Arc::new(BodyCheckResult {
          body: body_id,
          expr_types: Vec::new(),
          expr_spans: Vec::new(),
          diagnostics: vec![Diagnostic::error("missing body", None)],
          return_types: Vec::new(),
        });
        self.body_results.insert(body_id, res.clone());
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
      } => {
        let init_ty = init.as_ref().map(|e| self.check_expr(e, env, result, file));
        let declared = typ.or(init_ty).unwrap_or(self.builtin.unknown);
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
          .map(|e| self.check_expr(e, env, result, file))
          .unwrap_or(self.builtin.undefined);
        result.return_types.push(ty);
      }
      HirStmt::Expr(expr) => {
        self.check_expr(expr, env, result, file);
      }
    }
  }

  fn check_expr(
    &mut self,
    expr: &HirExpr,
    env: &mut HashMap<String, SymbolBinding>,
    result: &mut BodyCheckResult,
    file: FileId,
  ) -> TypeId {
    let ty = match &expr.kind {
      HirExprKind::Number => self.builtin.number,
      HirExprKind::String => self.builtin.string,
      HirExprKind::Boolean => self.builtin.boolean,
      HirExprKind::Null => self.builtin.null,
      HirExprKind::Ident(name) => {
        if let Some(binding) = env.get(name).cloned() {
          self.record_symbol(file, expr.span, binding.symbol);
          if let Some(ty) = binding.type_id {
            ty
          } else if let Some(def_id) = binding.def {
            let ty = self.type_of_def(def_id);
            env.insert(
              name.clone(),
              SymbolBinding {
                type_id: Some(ty),
                ..binding
              },
            );
            ty
          } else {
            self.builtin.unknown
          }
        } else {
          self.builtin.unknown
        }
      }
      HirExprKind::Binary { op, left, right } => {
        let left_ty = self.check_expr(left, env, result, file);
        let right_ty = self.check_expr(right, env, result, file);
        match op {
          OperatorName::Addition => {
            if left_ty == self.builtin.string || right_ty == self.builtin.string {
              self.builtin.string
            } else if left_ty == self.builtin.number && right_ty == self.builtin.number {
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
          | OperatorName::BitwiseUnsignedRightShift
          | OperatorName::GreaterThan
          | OperatorName::GreaterThanOrEqual
          | OperatorName::LessThan
          | OperatorName::LessThanOrEqual => self.builtin.number,
          OperatorName::Equality
          | OperatorName::Inequality
          | OperatorName::StrictEquality
          | OperatorName::StrictInequality => self.builtin.boolean,
          _ => self.builtin.unknown,
        }
      }
      HirExprKind::Call { callee, args } => {
        let callee_ty = self.check_expr(callee, env, result, file);
        if let TypeKind::Function { params, ret } = self.type_store.kind(callee_ty).clone() {
          if params.len() != args.len() {
            result.diagnostics.push(Diagnostic::error(
              "argument count mismatch",
              Some(Span {
                file,
                range: expr.span,
              }),
            ));
          }
          for (idx, arg) in args.iter().enumerate() {
            let arg_ty = self.check_expr(arg, env, result, file);
            if let Some(expected) = params.get(idx) {
              if expected != &self.builtin.any && expected != &arg_ty {
                result.diagnostics.push(Diagnostic::error(
                  format!("argument {} has incompatible type", idx + 1),
                  Some(Span {
                    file,
                    range: arg.span,
                  }),
                ));
              }
            }
          }
          ret
        } else {
          self.builtin.unknown
        }
      }
      HirExprKind::Object(props) => {
        let mut map = BTreeMap::new();
        for (k, v) in props.iter() {
          let ty = self.check_expr(v, env, result, file);
          map.insert(k.clone(), ty);
        }
        self.type_store.object(map)
      }
      HirExprKind::Array(values) => {
        let mut tys = Vec::new();
        for v in values {
          tys.push(self.check_expr(v, env, result, file));
        }
        let elem = self.type_store.union(tys, &self.builtin);
        self.type_store.array(elem)
      }
      HirExprKind::Unknown => self.builtin.unknown,
    };
    if let Some(slot) = result.expr_types.get_mut(expr.id.0 as usize) {
      *slot = ty;
    }
    ty
  }

  fn initial_env(&self, owner: Option<DefId>, file: FileId) -> HashMap<String, SymbolBinding> {
    let mut env = self
      .files
      .get(&file)
      .map(|f| f.bindings.clone())
      .unwrap_or_default();
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
    if let Some(existing) = self.def_types.get(&def) {
      return *existing;
    }
    if self.type_stack.contains(&def) {
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

  fn body_of_def(&self, def: DefId) -> Option<BodyId> {
    self.def_data.get(&def).and_then(|d| match &d.kind {
      DefKind::Function(func) => func.body,
      DefKind::Var(var) => Some(var.body),
      DefKind::Import(_) => None,
    })
  }

  fn type_from_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    match expr.stx.as_ref() {
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
      TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
        TypeLiteral::Boolean(value) => {
          if *value {
            self.builtin.boolean
          } else {
            self.builtin.boolean
          }
        }
        TypeLiteral::Number(_) => self.builtin.number,
        TypeLiteral::String(_) => self.builtin.string,
        TypeLiteral::Null => self.builtin.null,
        _ => self.builtin.unknown,
      },
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

  fn lower_stmt(&mut self, stmt: Node<Stmt>, state: &mut ProgramState) {
    match *stmt.stx {
      Stmt::VarDecl(var) => {
        let stmt_span = loc_to_span(self.file, stmt.loc).range;
        for declarator in var.stx.declarators.into_iter() {
          let pat = declarator.pattern;
          let name = match pat.stx.pat.stx.as_ref() {
            Pat::Id(id) => id.stx.name.clone(),
            _ => {
              state.diagnostics.push(Diagnostic::error(
                "unsupported pattern",
                Some(loc_to_span(self.file, pat.loc)),
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
          self.stmts.push(HirStmt::Var {
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
        self.stmts.push(HirStmt::Return {
          expr,
          span: loc_to_span(self.file, ret.loc).range,
        });
      }
      Stmt::Expr(expr_stmt) => {
        let expr = self.lower_expr(expr_stmt.stx.expr, state);
        self.stmts.push(HirStmt::Expr(expr));
      }
      Stmt::Block(block) => {
        for stmt in block.stx.body {
          self.lower_stmt(stmt, state);
        }
      }
      _ => {}
    }
  }

  fn lower_expr(&mut self, expr: Node<Expr>, state: &mut ProgramState) -> HirExpr {
    let span = loc_to_span(self.file, expr.loc).range;
    let kind = match *expr.stx {
      Expr::LitNum(_) => HirExprKind::Number,
      Expr::LitStr(_) => HirExprKind::String,
      Expr::LitBool(_) => HirExprKind::Boolean,
      Expr::LitNull(_) => HirExprKind::Null,
      Expr::Id(id) => HirExprKind::Ident(id.stx.name.clone()),
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
      Expr::LitTemplate(_) => HirExprKind::String,
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

fn loc_to_span(file: FileId, loc: Loc) -> Span {
  Span {
    file,
    range: TextRange {
      start: loc.0.min(u32::MAX as usize) as u32,
      end: loc.1.min(u32::MAX as usize) as u32,
    },
  }
}
