use crate::{ts_lower, Diagnostic, TopLevelMode};
use derive_visitor::{Drive, DriveMut, VisitorMut};
use diagnostics::{FileId, Span};
use parse_js::ast::class_or_object::{
  ClassMember, ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::jsx::*;
use parse_js::ast::expr::lit::{
  LitArrElem, LitBoolExpr, LitNullExpr, LitObjExpr, LitStrExpr, LitTemplatePart,
};
use parse_js::ast::expr::pat::{ArrPat, ClassOrFuncName, IdPat, ObjPat, Pat};
use parse_js::ast::expr::*;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::import_export::{ExportName, ExportNames, ImportNames, ModuleExportImportName};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::decl::{
  ClassDecl, FuncDecl, ParamDecl, PatDecl, VarDecl, VarDeclMode, VarDeclarator,
};
use parse_js::ast::stmt::*;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{
  AmbientClassDecl, AmbientFunctionDecl, AmbientVarDecl, EnumDecl, ExportAsNamespaceDecl,
  ImportEqualsDecl, ImportEqualsRhs, ModuleDecl, ModuleName, NamespaceBody, NamespaceDecl,
};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::token::{keyword_from_str, TT};
use std::collections::{HashMap, HashSet};

const ERR_TS_UNSUPPORTED: &str = "MINIFYTS0001";

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;
type ClassOrFuncNameNode = Node<ClassOrFuncName>;
type ExportListStmtNode = Node<ExportListStmt>;
type EnumDeclNode = Node<EnumDecl>;
type NamespaceDeclNode = Node<NamespaceDecl>;
type ModuleDeclNode = Node<ModuleDecl>;
type ImportEqualsDeclNode = Node<ImportEqualsDecl>;
type AmbientVarDeclNode = Node<AmbientVarDecl>;
type AmbientFunctionDeclNode = Node<AmbientFunctionDecl>;
type AmbientClassDeclNode = Node<AmbientClassDecl>;
type ExportAsNamespaceDeclNode = Node<ExportAsNamespaceDecl>;

#[derive(Debug)]
struct FreshInternalNameGenerator {
  used: HashSet<String>,
}

impl FreshInternalNameGenerator {
  fn new(used: HashSet<String>) -> Self {
    Self { used }
  }

  fn fresh(&mut self, preferred: String) -> String {
    if self.used.insert(preferred.clone()) {
      return preferred;
    }
    for suffix in 1usize.. {
      let candidate = format!("{preferred}_{suffix}");
      if self.used.insert(candidate.clone()) {
        return candidate;
      }
    }
    unreachable!();
  }
}

fn collect_all_identifier_strings(top_level: &mut Node<TopLevel>) -> HashSet<String> {
  #[derive(VisitorMut)]
  #[visitor(
    IdExprNode(enter),
    IdPatNode(enter),
    ClassOrFuncNameNode(enter),
    ExportListStmtNode(enter),
    EnumDeclNode(enter),
    NamespaceDeclNode(enter),
    ModuleDeclNode(enter),
    ImportEqualsDeclNode(enter),
    AmbientVarDeclNode(enter),
    AmbientFunctionDeclNode(enter),
    AmbientClassDeclNode(enter),
    ExportAsNamespaceDeclNode(enter)
  )]
  struct Collector {
    names: HashSet<String>,
  }

  impl Collector {
    fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_class_or_func_name_node(&mut self, node: &mut ClassOrFuncNameNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_export_list_stmt_node(&mut self, node: &mut ExportListStmtNode) {
      if node.stx.type_only || node.stx.from.is_some() {
        return;
      }
      let ExportNames::Specific(entries) = &node.stx.names else {
        return;
      };
      for entry in entries {
        if entry.stx.type_only {
          continue;
        }
        if let ModuleExportImportName::Ident(local) = &entry.stx.exportable {
          self.names.insert(local.clone());
        }
      }
    }

    fn enter_enum_decl_node(&mut self, node: &mut EnumDeclNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_namespace_decl_node(&mut self, node: &mut NamespaceDeclNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_module_decl_node(&mut self, node: &mut ModuleDeclNode) {
      if let ModuleName::Identifier(name) = &node.stx.name {
        self.names.insert(name.clone());
      }
    }

    fn enter_import_equals_decl_node(&mut self, node: &mut ImportEqualsDeclNode) {
      self.names.insert(node.stx.name.clone());
      if let ImportEqualsRhs::EntityName { path } = &node.stx.rhs {
        self.names.extend(path.iter().cloned());
      }
    }

    fn enter_ambient_var_decl_node(&mut self, node: &mut AmbientVarDeclNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_ambient_function_decl_node(&mut self, node: &mut AmbientFunctionDeclNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_ambient_class_decl_node(&mut self, node: &mut AmbientClassDeclNode) {
      self.names.insert(node.stx.name.clone());
    }

    fn enter_export_as_namespace_decl_node(&mut self, node: &mut ExportAsNamespaceDeclNode) {
      self.names.insert(node.stx.name.clone());
    }
  }

  let mut collector = Collector {
    names: HashSet::new(),
  };
  top_level.drive_mut(&mut collector);
  collector.names
}

#[derive(VisitorMut)]
#[visitor(IdExprNode(enter))]
struct RewriteIdExprName<'a> {
  from: &'a str,
  to: &'a str,
}

impl RewriteIdExprName<'_> {
  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    if node.stx.name == self.from {
      node.stx.name = self.to.to_string();
    }
  }
}

#[derive(Clone, Copy, Debug)]
pub struct TsEraseOptions {
  pub lower_class_fields: bool,
  pub use_define_for_class_fields: bool,
  /// When enabled, `const enum` declarations are lowered to runtime enums instead of
  /// being erased/inlined like `tsc` does by default.
  pub preserve_const_enums: bool,
}

impl Default for TsEraseOptions {
  fn default() -> Self {
    Self {
      lower_class_fields: false,
      use_define_for_class_fields: true,
      preserve_const_enums: false,
    }
  }
}

struct StripContext {
  file: FileId,
  top_level_mode: TopLevelMode,
  value_bindings_stack: Vec<HashSet<String>>,
  top_level_module_exports: HashSet<String>,
  erased_const_enum_bindings: HashSet<String>,
  emitted_export_var: HashSet<String>,
  fresh_internal_names: FreshInternalNameGenerator,
  runtime_namespace_param_idents: HashMap<String, String>,
  runtime_enum_object_idents: HashMap<String, String>,
  ts_erase_options: TsEraseOptions,
  diagnostics: Vec<Diagnostic>,
}

impl StripContext {
  fn current_value_bindings(&self) -> &HashSet<String> {
    self
      .value_bindings_stack
      .last()
      .expect("value binding stack must never be empty")
  }

  fn current_value_bindings_mut(&mut self) -> &mut HashSet<String> {
    self
      .value_bindings_stack
      .last_mut()
      .expect("value binding stack must never be empty")
  }

  fn fresh_internal_name(&mut self, preferred: String) -> String {
    self.fresh_internal_names.fresh(preferred)
  }

  fn runtime_namespace_param_ident(&mut self, namespace_name: &str) -> String {
    if let Some(ident) = self.runtime_namespace_param_idents.get(namespace_name) {
      return ident.clone();
    }
    let ident = self.fresh_internal_name(format!("__minify_ts_namespace_{namespace_name}"));
    self
      .runtime_namespace_param_idents
      .insert(namespace_name.to_string(), ident.clone());
    ident
  }

  fn runtime_enum_object_ident(&mut self, enum_name: &str) -> String {
    if let Some(ident) = self.runtime_enum_object_idents.get(enum_name) {
      return ident.clone();
    }
    let ident = self.fresh_internal_name(format!("__minify_ts_enum_obj_{enum_name}"));
    self
      .runtime_enum_object_idents
      .insert(enum_name.to_string(), ident.clone());
    ident
  }
}

fn new_node<T: Drive + DriveMut>(loc: Loc, assoc: NodeAssocData, stx: T) -> Node<T> {
  Node {
    loc,
    assoc,
    stx: Box::new(stx),
  }
}

fn dummy_expr() -> Node<Expr> {
  Node::new(
    Loc(0, 0),
    Expr::LitNull(Node::new(Loc(0, 0), LitNullExpr {})),
  )
}

fn dummy_pat() -> Node<Pat> {
  Node::new(
    Loc(0, 0),
    Pat::Id(Node::new(
      Loc(0, 0),
      IdPat {
        name: String::new(),
      },
    )),
  )
}

fn dummy_jsx_elem() -> Node<JsxElem> {
  Node::new(
    Loc(0, 0),
    JsxElem {
      name: None,
      attributes: Vec::new(),
      children: Vec::new(),
    },
  )
}

fn is_valid_binding_identifier(name: &str, top_level_mode: TopLevelMode) -> bool {
  // `parse-js` intentionally parses some keyword-like names as identifiers in TS namespace
  // dotted paths (e.g. `namespace A.class {}`) for conformance with TypeScript.
  //
  // When lowering runtime namespaces to JS, we must avoid synthesizing binding identifiers
  // (e.g. `var class;` / `function(class){}`) that are invalid in the output mode.
  if matches!(top_level_mode, TopLevelMode::Module)
    && matches!(name, "package" | "eval" | "arguments")
  {
    // `package`, `eval`, and `arguments` are invalid binding identifiers in strict mode but are not
    // tokenized as keywords by the lexer.
    return false;
  }

  let Some(keyword) = keyword_from_str(name) else {
    return true;
  };

  match keyword {
    // Contextual keywords that remain valid identifiers in strict mode.
    TT::KeywordAs
    | TT::KeywordAsync
    | TT::KeywordConstructor
    | TT::KeywordFrom
    | TT::KeywordGet
    | TT::KeywordOf
    | TT::KeywordOut
    | TT::KeywordSet
    | TT::KeywordUsing => true,

    // `await` is reserved in modules, but allowed as an identifier in scripts.
    TT::KeywordAwait => matches!(top_level_mode, TopLevelMode::Global),

    // Strict-mode reserved words (allowed in non-strict scripts).
    TT::KeywordImplements
    | TT::KeywordInterface
    | TT::KeywordLet
    | TT::KeywordPrivate
    | TT::KeywordProtected
    | TT::KeywordPublic
    | TT::KeywordStatic
    | TT::KeywordYield => matches!(top_level_mode, TopLevelMode::Global),

    // TypeScript keywords that are not reserved in JS.
    TT::KeywordAbstract
    | TT::KeywordAccessor
    | TT::KeywordAny
    | TT::KeywordAsserts
    | TT::KeywordBigIntType
    | TT::KeywordBooleanType
    | TT::KeywordDeclare
    | TT::KeywordInfer
    | TT::KeywordIntrinsic
    | TT::KeywordIs
    | TT::KeywordKeyof
    | TT::KeywordModule
    | TT::KeywordNamespace
    | TT::KeywordNever
    | TT::KeywordNumberType
    | TT::KeywordObjectType
    | TT::KeywordOverride
    | TT::KeywordReadonly
    | TT::KeywordSatisfies
    | TT::KeywordStringType
    | TT::KeywordSymbolType
    | TT::KeywordType
    | TT::KeywordUndefinedType
    | TT::KeywordUnique
    | TT::KeywordUnknown => true,

    // Remaining JavaScript keywords (including `class`, `enum`, etc.) are not valid binding ids.
    _ => false,
  }
}

fn is_valid_identifier_reference(name: &str, top_level_mode: TopLevelMode) -> bool {
  // `package` is not tokenized as a keyword but is a reserved word in strict mode.
  if matches!(top_level_mode, TopLevelMode::Module) && name == "package" {
    return false;
  }

  let Some(keyword) = keyword_from_str(name) else {
    return true;
  };

  match keyword {
    // Contextual keywords that remain valid identifiers in strict mode.
    TT::KeywordAs
    | TT::KeywordAsync
    | TT::KeywordConstructor
    | TT::KeywordFrom
    | TT::KeywordGet
    | TT::KeywordOf
    | TT::KeywordOut
    | TT::KeywordSet
    | TT::KeywordUsing => true,

    // `await` is reserved in modules, but allowed as an identifier in scripts.
    TT::KeywordAwait => matches!(top_level_mode, TopLevelMode::Global),

    // Strict-mode reserved words (allowed in non-strict scripts).
    TT::KeywordImplements
    | TT::KeywordInterface
    | TT::KeywordLet
    | TT::KeywordPrivate
    | TT::KeywordProtected
    | TT::KeywordPublic
    | TT::KeywordStatic
    | TT::KeywordYield => matches!(top_level_mode, TopLevelMode::Global),

    // All remaining keywords are not valid identifier references.
    _ => false,
  }
}

fn take_expr(expr: &mut Node<Expr>) -> Node<Expr> {
  std::mem::replace(expr, dummy_expr())
}

fn take_pat(pat: &mut Node<Pat>) -> Node<Pat> {
  std::mem::replace(pat, dummy_pat())
}

fn take_jsx_elem(elem: &mut Node<JsxElem>) -> Node<JsxElem> {
  std::mem::replace(elem, dummy_jsx_elem())
}

#[cfg(any(test, feature = "fuzzing"))]
pub fn erase_types(
  file: FileId,
  top_level_mode: TopLevelMode,
  source: &str,
  top_level: &mut Node<TopLevel>,
) -> Result<(), Vec<Diagnostic>> {
  erase_types_with_options(
    file,
    top_level_mode,
    source,
    top_level,
    TsEraseOptions::default(),
  )
}

pub fn erase_types_with_options(
  file: FileId,
  top_level_mode: TopLevelMode,
  _source: &str,
  top_level: &mut Node<TopLevel>,
  ts_erase_options: TsEraseOptions,
) -> Result<(), Vec<Diagnostic>> {
  let erased_const_enum_bindings = if ts_erase_options.preserve_const_enums {
    HashSet::new()
  } else {
    inline_const_enums(top_level)
  };
  let all_identifier_strings = collect_all_identifier_strings(top_level);
  let top_level_value_bindings = collect_top_level_value_bindings(&top_level.stx.body);
  let top_level_module_exports = if matches!(top_level_mode, TopLevelMode::Module) {
    collect_top_level_module_exports(&top_level.stx.body, &erased_const_enum_bindings)
  } else {
    HashSet::new()
  };
  let mut ctx = StripContext {
    file,
    top_level_mode,
    value_bindings_stack: vec![top_level_value_bindings],
    top_level_module_exports,
    erased_const_enum_bindings,
    emitted_export_var: HashSet::new(),
    fresh_internal_names: FreshInternalNameGenerator::new(all_identifier_strings),
    runtime_namespace_param_idents: HashMap::new(),
    runtime_enum_object_idents: HashMap::new(),
    ts_erase_options,
    diagnostics: Vec::new(),
  };
  strip_stmts(&mut ctx, &mut top_level.stx.body, true);
  if ctx.diagnostics.is_empty() {
    Ok(())
  } else {
    Err(ctx.diagnostics)
  }
}

fn strip_stmts(ctx: &mut StripContext, stmts: &mut Vec<Node<Stmt>>, is_top_level: bool) {
  let mut new_stmts = Vec::with_capacity(stmts.len());
  for stmt in stmts.drain(..) {
    new_stmts.extend(strip_stmt(ctx, stmt, is_top_level));
  }
  *stmts = new_stmts;
}

fn empty_stmt(loc: Loc) -> Node<Stmt> {
  Node::new(loc, Stmt::Empty(Node::new(loc, EmptyStmt {})))
}

fn export_binding_stmt(loc: Loc, name: String) -> Node<Stmt> {
  let export_name = Node::new(
    loc,
    ExportName {
      type_only: false,
      exportable: ModuleExportImportName::Ident(name.clone()),
      alias: Node::new(loc, IdPat { name }),
    },
  );
  Node::new(
    loc,
    Stmt::ExportList(Node::new(
      loc,
      ExportListStmt {
        type_only: false,
        names: ExportNames::Specific(vec![export_name]),
        from: None,
        attributes: None,
      },
    )),
  )
}

fn export_binding_as_stmt(loc: Loc, local: String, exported: String) -> Node<Stmt> {
  let export_name = Node::new(
    loc,
    ExportName {
      type_only: false,
      exportable: ModuleExportImportName::Ident(local),
      alias: Node::new(loc, IdPat { name: exported }),
    },
  );
  Node::new(
    loc,
    Stmt::ExportList(Node::new(
      loc,
      ExportListStmt {
        type_only: false,
        names: ExportNames::Specific(vec![export_name]),
        from: None,
        attributes: None,
      },
    )),
  )
}

fn strip_stmt_required(
  ctx: &mut StripContext,
  mut stmt: Node<Stmt>,
  is_top_level: bool,
) -> Node<Stmt> {
  let loc = stmt.loc;
  let assoc = std::mem::take(&mut stmt.assoc);
  let mut lowered = strip_stmt(ctx, stmt, is_top_level);
  match lowered.len() {
    0 => new_node(loc, assoc, *empty_stmt(loc).stx),
    1 => lowered.pop().unwrap(),
    _ => new_node(
      loc,
      assoc,
      Stmt::Block(Node::new(loc, BlockStmt { body: lowered })),
    ),
  }
}

fn strip_stmt_optional(
  ctx: &mut StripContext,
  mut stmt: Node<Stmt>,
  is_top_level: bool,
) -> Option<Node<Stmt>> {
  let loc = stmt.loc;
  let assoc = std::mem::take(&mut stmt.assoc);
  let mut lowered = strip_stmt(ctx, stmt, is_top_level);
  match lowered.len() {
    0 => None,
    1 => lowered.pop(),
    _ => Some(new_node(
      loc,
      assoc,
      Stmt::Block(Node::new(loc, BlockStmt { body: lowered })),
    )),
  }
}

fn strip_stmt(ctx: &mut StripContext, stmt: Node<Stmt>, is_top_level: bool) -> Vec<Node<Stmt>> {
  let loc = stmt.loc;
  let assoc = stmt.assoc;
  match *stmt.stx {
    Stmt::Block(block) => {
      let mut block = block;
      strip_stmts(ctx, &mut block.stx.body, false);
      vec![new_node(loc, assoc, Stmt::Block(block))]
    }
    Stmt::Expr(expr_stmt) => {
      let mut expr_stmt = expr_stmt;
      expr_stmt.stx.expr = strip_expr(ctx, expr_stmt.stx.expr);
      vec![new_node(loc, assoc, Stmt::Expr(expr_stmt))]
    }
    Stmt::If(mut if_stmt) => {
      if_stmt.stx.test = strip_expr(ctx, if_stmt.stx.test);
      if_stmt.stx.consequent = strip_stmt_required(ctx, if_stmt.stx.consequent, false);
      if let Some(alt) = if_stmt.stx.alternate.take() {
        if_stmt.stx.alternate = strip_stmt_optional(ctx, alt, false);
      }
      vec![new_node(loc, assoc, Stmt::If(if_stmt))]
    }
    Stmt::ForTriple(mut for_stmt) => {
      match &mut for_stmt.stx.init {
        ForTripleStmtInit::Expr(expr) => {
          let owned = take_expr(expr);
          *expr = strip_expr(ctx, owned);
        }
        ForTripleStmtInit::Decl(decl) => strip_var_decl(ctx, &mut decl.stx),
        ForTripleStmtInit::None => {}
      }
      if let Some(cond) = for_stmt.stx.cond.take() {
        for_stmt.stx.cond = Some(strip_expr(ctx, cond));
      }
      if let Some(post) = for_stmt.stx.post.take() {
        for_stmt.stx.post = Some(strip_expr(ctx, post));
      }
      strip_for_body(ctx, &mut for_stmt.stx.body);
      vec![new_node(loc, assoc, Stmt::ForTriple(for_stmt))]
    }
    Stmt::ForIn(mut for_stmt) => {
      strip_for_in_of_lhs(ctx, &mut for_stmt.stx.lhs);
      for_stmt.stx.rhs = strip_expr(ctx, for_stmt.stx.rhs);
      strip_for_body(ctx, &mut for_stmt.stx.body);
      vec![new_node(loc, assoc, Stmt::ForIn(for_stmt))]
    }
    Stmt::ForOf(mut for_stmt) => {
      strip_for_in_of_lhs(ctx, &mut for_stmt.stx.lhs);
      for_stmt.stx.rhs = strip_expr(ctx, for_stmt.stx.rhs);
      strip_for_body(ctx, &mut for_stmt.stx.body);
      vec![new_node(loc, assoc, Stmt::ForOf(for_stmt))]
    }
    Stmt::While(mut while_stmt) => {
      while_stmt.stx.condition = strip_expr(ctx, while_stmt.stx.condition);
      while_stmt.stx.body = strip_stmt_required(ctx, while_stmt.stx.body, false);
      vec![new_node(loc, assoc, Stmt::While(while_stmt))]
    }
    Stmt::DoWhile(mut do_stmt) => {
      do_stmt.stx.body = strip_stmt_required(ctx, do_stmt.stx.body, false);
      do_stmt.stx.condition = strip_expr(ctx, do_stmt.stx.condition);
      vec![new_node(loc, assoc, Stmt::DoWhile(do_stmt))]
    }
    Stmt::Switch(mut switch_stmt) => {
      switch_stmt.stx.test = strip_expr(ctx, switch_stmt.stx.test);
      let mut new_branches = Vec::with_capacity(switch_stmt.stx.branches.len());
      for branch in switch_stmt.stx.branches.drain(..) {
        new_branches.push(strip_switch_branch(ctx, branch));
      }
      switch_stmt.stx.branches = new_branches;
      vec![new_node(loc, assoc, Stmt::Switch(switch_stmt))]
    }
    Stmt::Try(mut try_stmt) => {
      try_stmt.stx.wrapped = strip_block(ctx, try_stmt.stx.wrapped);
      if let Some(catch) = try_stmt.stx.catch.take() {
        try_stmt.stx.catch = Some(strip_catch(ctx, catch));
      }
      if let Some(finally) = try_stmt.stx.finally.take() {
        try_stmt.stx.finally = Some(strip_block(ctx, finally));
      }
      vec![new_node(loc, assoc, Stmt::Try(try_stmt))]
    }
    Stmt::Throw(mut throw_stmt) => {
      throw_stmt.stx.value = strip_expr(ctx, throw_stmt.stx.value);
      vec![new_node(loc, assoc, Stmt::Throw(throw_stmt))]
    }
    Stmt::Return(mut ret_stmt) => {
      if let Some(value) = ret_stmt.stx.value.take() {
        ret_stmt.stx.value = Some(strip_expr(ctx, value));
      }
      vec![new_node(loc, assoc, Stmt::Return(ret_stmt))]
    }
    Stmt::Break(_) | Stmt::Continue(_) | Stmt::Debugger(_) | Stmt::Empty(_) => {
      vec![new_node(loc, assoc, *stmt.stx)]
    }
    Stmt::With(mut with_stmt) => {
      with_stmt.stx.object = strip_expr(ctx, with_stmt.stx.object);
      with_stmt.stx.body = strip_stmt_required(ctx, with_stmt.stx.body, false);
      vec![new_node(loc, assoc, Stmt::With(with_stmt))]
    }
    Stmt::Label(mut label_stmt) => {
      label_stmt.stx.statement = strip_stmt_required(ctx, label_stmt.stx.statement, false);
      vec![new_node(loc, assoc, Stmt::Label(label_stmt))]
    }
    Stmt::VarDecl(mut decl) => {
      strip_var_decl(ctx, &mut decl.stx);
      vec![new_node(loc, assoc, Stmt::VarDecl(decl))]
    }
    Stmt::FunctionDecl(func_decl) => strip_func_decl(ctx, func_decl, loc, assoc)
      .into_iter()
      .collect(),
    Stmt::ClassDecl(class_decl) => strip_class_decl(ctx, class_decl, loc, assoc)
      .into_iter()
      .collect(),
    Stmt::Import(import_stmt) => strip_import(ctx, import_stmt, loc, assoc)
      .into_iter()
      .collect(),
    Stmt::ExportList(export_stmt) => strip_export_list(ctx, export_stmt, loc, assoc)
      .into_iter()
      .collect(),
    Stmt::ExportDefaultExpr(mut expr) => {
      expr.stx.expression = strip_expr(ctx, expr.stx.expression);
      vec![new_node(loc, assoc, Stmt::ExportDefaultExpr(expr))]
    }
    Stmt::InterfaceDecl(_)
    | Stmt::TypeAliasDecl(_)
    | Stmt::ImportTypeDecl(_)
    | Stmt::ExportTypeDecl(_)
    | Stmt::ExportAsNamespaceDecl(_)
    | Stmt::AmbientVarDecl(_)
    | Stmt::AmbientFunctionDecl(_)
    | Stmt::AmbientClassDecl(_)
    | Stmt::GlobalDecl(_) => vec![],
    Stmt::EnumDecl(decl) => strip_enum_decl(ctx, decl, loc, assoc, is_top_level, None),
    Stmt::NamespaceDecl(decl) => strip_namespace_decl(ctx, decl, loc, assoc, is_top_level, None),
    Stmt::ModuleDecl(decl) => strip_module_decl(ctx, decl, loc, assoc, is_top_level, None),
    Stmt::ImportEqualsDecl(decl) => lower_import_equals_decl(ctx, decl, loc, assoc, is_top_level)
      .into_iter()
      .collect(),
    Stmt::ExportAssignmentDecl(decl) => {
      let expr = strip_expr(ctx, decl.stx.expression);
      lower_export_assignment(ctx, loc, assoc, expr, is_top_level)
        .into_iter()
        .collect()
    }
  }
}

fn collect_top_level_value_bindings(stmts: &[Node<Stmt>]) -> HashSet<String> {
  let mut names = HashSet::new();
  for stmt in stmts {
    match stmt.stx.as_ref() {
      Stmt::FunctionDecl(func) => {
        if func.stx.function.stx.body.is_some() {
          if let Some(name) = func.stx.name.as_ref().map(|name| name.stx.name.clone()) {
            names.insert(name);
          }
        }
      }
      Stmt::ClassDecl(class) => {
        if !class.stx.declare {
          if let Some(name) = class.stx.name.as_ref().map(|name| name.stx.name.clone()) {
            names.insert(name);
          }
        }
      }
      Stmt::VarDecl(decl) => {
        for declarator in &decl.stx.declarators {
          let mut bindings = Vec::new();
          collect_pat_binding_names(&declarator.pattern.stx.pat, &mut bindings);
          names.extend(bindings);
        }
      }
      Stmt::Import(import) if !import.stx.type_only => {
        if let Some(default) = import.stx.default.as_ref() {
          let mut bindings = Vec::new();
          collect_pat_binding_names(&default.stx.pat, &mut bindings);
          names.extend(bindings);
        }
        if let Some(import_names) = import.stx.names.as_ref() {
          match import_names {
            ImportNames::All(pat) => {
              let mut bindings = Vec::new();
              collect_pat_binding_names(&pat.stx.pat, &mut bindings);
              names.extend(bindings);
            }
            ImportNames::Specific(entries) => {
              for entry in entries {
                if entry.stx.type_only {
                  continue;
                }
                let mut bindings = Vec::new();
                collect_pat_binding_names(&entry.stx.alias.stx.pat, &mut bindings);
                names.extend(bindings);
              }
            }
          }
        }
      }
      Stmt::ImportEqualsDecl(decl) => {
        if !decl.stx.type_only {
          names.insert(decl.stx.name.clone());
        }
      }
      _ => {}
    }
  }
  names
}

fn collect_top_level_module_exports(
  stmts: &[Node<Stmt>],
  erased_const_enum_bindings: &HashSet<String>,
) -> HashSet<String> {
  let mut names = HashSet::new();
  for stmt in stmts {
    match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) if decl.stx.export => {
        for declarator in &decl.stx.declarators {
          let mut bindings = Vec::new();
          collect_pat_binding_names(&declarator.pattern.stx.pat, &mut bindings);
          names.extend(bindings);
        }
      }
      Stmt::FunctionDecl(func) if func.stx.export && !func.stx.export_default => {
        if func.stx.function.stx.body.is_some() {
          if let Some(name) = func.stx.name.as_ref().map(|name| name.stx.name.clone()) {
            names.insert(name);
          }
        }
      }
      Stmt::ClassDecl(class) if class.stx.export && !class.stx.export_default => {
        if !class.stx.declare {
          if let Some(name) = class.stx.name.as_ref().map(|name| name.stx.name.clone()) {
            names.insert(name);
          }
        }
      }
      Stmt::ExportList(export_stmt) if !export_stmt.stx.type_only => match &export_stmt.stx.names {
        ExportNames::Specific(entries) => {
          for entry in entries {
            if !entry.stx.type_only {
              if export_stmt.stx.from.is_none() {
                if let ModuleExportImportName::Ident(local) = &entry.stx.exportable {
                  if erased_const_enum_bindings.contains(local) {
                    continue;
                  }
                }
              }
              names.insert(entry.stx.alias.stx.name.clone());
            }
          }
        }
        ExportNames::All(Some(alias)) => {
          names.insert(alias.stx.name.clone());
        }
        ExportNames::All(None) => {}
      },
      Stmt::ImportEqualsDecl(decl) if decl.stx.export => {
        if !decl.stx.type_only {
          names.insert(decl.stx.name.clone());
        }
      }
      _ => {}
    }
  }
  names
}

fn lower_import_equals_decl(
  ctx: &mut StripContext,
  decl: Node<ImportEqualsDecl>,
  loc: Loc,
  assoc: NodeAssocData,
  is_top_level: bool,
) -> Option<Node<Stmt>> {
  if decl.stx.type_only {
    return None;
  }
  if decl.stx.export && !is_top_level {
    unsupported_ts(
      ctx,
      loc,
      "exported import= assignments must be at top level",
    );
    return None;
  }
  let initializer = match &decl.stx.rhs {
    ImportEqualsRhs::Require { module } => Some(require_call(loc, module.clone())),
    ImportEqualsRhs::EntityName { path } => qualified_path_expr(loc, path),
  };
  let initializer = match initializer {
    Some(expr) => expr,
    None => {
      unsupported_ts(
        ctx,
        loc,
        "import= assignments must target require(\"...\") or qualified names",
      );
      return None;
    }
  };
  let pattern = Node::new(
    loc,
    PatDecl {
      pat: Node::new(
        loc,
        Pat::Id(Node::new(
          loc,
          IdPat {
            name: decl.stx.name,
          },
        )),
      ),
    },
  );
  let declarator = VarDeclarator {
    pattern,
    definite_assignment: false,
    type_annotation: None,
    initializer: Some(initializer),
  };
  let var_decl = VarDecl {
    export: decl.stx.export,
    mode: match ctx.top_level_mode {
      TopLevelMode::Module => VarDeclMode::Const,
      TopLevelMode::Global => VarDeclMode::Var,
    },
    declarators: vec![declarator],
  };
  Some(new_node(
    loc,
    assoc,
    Stmt::VarDecl(Node::new(loc, var_decl)),
  ))
}

fn lower_export_assignment(
  ctx: &mut StripContext,
  loc: Loc,
  assoc: NodeAssocData,
  expr: Node<Expr>,
  is_top_level: bool,
) -> Option<Node<Stmt>> {
  if !is_top_level {
    unsupported_ts(ctx, loc, "export = assignments must be at top level");
    return None;
  }
  let target = Node::new(
    loc,
    Expr::Member(Node::new(
      loc,
      MemberExpr {
        optional_chaining: false,
        left: Node::new(
          loc,
          Expr::Id(Node::new(
            loc,
            IdExpr {
              name: "module".into(),
            },
          )),
        ),
        right: "exports".into(),
      },
    )),
  );
  let assignment = Node::new(
    loc,
    Expr::Binary(Node::new(
      loc,
      BinaryExpr {
        operator: OperatorName::Assignment,
        left: target,
        right: expr,
      },
    )),
  );
  Some(new_node(
    loc,
    assoc,
    Stmt::Expr(Node::new(loc, ExprStmt { expr: assignment })),
  ))
}

fn require_call(loc: Loc, module: String) -> Node<Expr> {
  Node::new(
    loc,
    Expr::Call(Node::new(
      loc,
      CallExpr {
        optional_chaining: false,
        callee: Node::new(
          loc,
          Expr::Id(Node::new(
            loc,
            IdExpr {
              name: "require".into(),
            },
          )),
        ),
        arguments: vec![Node::new(
          loc,
          CallArg {
            spread: false,
            value: Node::new(
              loc,
              Expr::LitStr(Node::new(loc, LitStrExpr { value: module })),
            ),
          },
        )],
      },
    )),
  )
}

fn qualified_path_expr(loc: Loc, path: &[String]) -> Option<Node<Expr>> {
  let mut segments = path.iter();
  let first = segments.next()?;
  let mut expr = Node::new(
    loc,
    Expr::Id(Node::new(
      loc,
      IdExpr {
        name: first.clone(),
      },
    )),
  );
  for part in segments {
    expr = Node::new(
      loc,
      Expr::Member(Node::new(
        loc,
        MemberExpr {
          optional_chaining: false,
          left: expr,
          right: part.clone(),
        },
      )),
    );
  }
  Some(expr)
}

fn strip_func_decl(
  ctx: &mut StripContext,
  func_decl: Node<FuncDecl>,
  loc: Loc,
  assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  let mut func_decl = func_decl;
  if !strip_func(ctx, &mut func_decl.stx.function.stx) {
    return None;
  }
  Some(new_node(loc, assoc, Stmt::FunctionDecl(func_decl)))
}

fn strip_class_decl(
  ctx: &mut StripContext,
  class_decl: Node<ClassDecl>,
  loc: Loc,
  assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  let mut class_decl = class_decl;
  if class_decl.stx.declare {
    return None;
  }
  class_decl.stx.abstract_ = false;
  class_decl.stx.type_parameters = None;
  class_decl.stx.implements.clear();
  if let Some(extends) = class_decl.stx.extends.take() {
    class_decl.stx.extends = Some(strip_expr(ctx, extends));
  }
  for decorator in &mut class_decl.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
  strip_class_members(
    ctx,
    &mut class_decl.stx.members,
    class_decl.stx.extends.is_some(),
  );
  Some(new_node(loc, assoc, Stmt::ClassDecl(class_decl)))
}

fn strip_import(
  ctx: &mut StripContext,
  import_stmt: Node<ImportStmt>,
  loc: Loc,
  assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  let mut import_stmt = import_stmt;
  if import_stmt.stx.type_only {
    return None;
  }
  let was_side_effect_only = import_stmt.stx.default.is_none()
    && match import_stmt.stx.names.as_ref() {
      None => true,
      Some(ImportNames::Specific(names)) => names.is_empty(),
      Some(ImportNames::All(_)) => false,
    };
  if let Some(names) = import_stmt.stx.names.as_mut() {
    match names {
      ImportNames::Specific(list) => {
        list.retain(|entry| !entry.stx.type_only);
        for entry in list.iter_mut() {
          entry.stx.type_only = false;
          let pat = take_pat(&mut entry.stx.alias.stx.pat);
          entry.stx.alias.stx.pat = strip_pat(ctx, pat);
        }
        if list.is_empty() {
          import_stmt.stx.names = None;
        }
      }
      ImportNames::All(pat) => {
        let pat_node = take_pat(&mut pat.stx.pat);
        pat.stx.pat = strip_pat(ctx, pat_node);
      }
    }
  }
  if let Some(default) = import_stmt.stx.default.as_mut() {
    let pat = take_pat(&mut default.stx.pat);
    default.stx.pat = strip_pat(ctx, pat);
  }
  let keep_import = if import_stmt.stx.default.is_none() && import_stmt.stx.names.is_none() {
    // Preserve true side-effect imports:
    // - `import "side";`
    // - `import {} from "side";`
    // while still removing imports that became empty after stripping type-only specifiers.
    was_side_effect_only
  } else {
    true
  };
  if !keep_import {
    return None;
  }
  if let Some(attrs) = import_stmt.stx.attributes.take() {
    import_stmt.stx.attributes = Some(strip_expr(ctx, attrs));
  }
  Some(new_node(loc, assoc, Stmt::Import(import_stmt)))
}

fn strip_export_list(
  ctx: &mut StripContext,
  export_stmt: Node<ExportListStmt>,
  loc: Loc,
  assoc: NodeAssocData,
) -> Option<Node<Stmt>> {
  let mut export_stmt = export_stmt;
  if export_stmt.stx.type_only {
    return None;
  }
  match &mut export_stmt.stx.names {
    ExportNames::Specific(names) => {
      let was_empty = names.is_empty();
      names.retain(|name| {
        if name.stx.type_only {
          return false;
        }
        if export_stmt.stx.from.is_some() {
          return true;
        }
        let ModuleExportImportName::Ident(local) = &name.stx.exportable else {
          return true;
        };
        !ctx.erased_const_enum_bindings.contains(local)
      });
      for name in names.iter_mut() {
        name.stx.type_only = false;
      }
      if names.is_empty() && !(was_empty && export_stmt.stx.from.is_some()) {
        return None;
      }
    }
    ExportNames::All(_) => {}
  }
  if let Some(attrs) = export_stmt.stx.attributes.take() {
    export_stmt.stx.attributes = Some(strip_expr(ctx, attrs));
  }
  Some(new_node(loc, assoc, Stmt::ExportList(export_stmt)))
}

fn is_template_literal_without_substitutions(expr: &Node<Expr>) -> bool {
  let Expr::LitTemplate(tpl) = expr.stx.as_ref() else {
    return false;
  };
  tpl
    .stx
    .parts
    .iter()
    .all(|part| matches!(part, LitTemplatePart::String(_)))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EnumValueKind {
  Number,
  String,
  Unknown,
}

fn enum_value_kind(
  enum_name: &str,
  expr: &Node<Expr>,
  known: &HashMap<String, EnumValueKind>,
) -> EnumValueKind {
  if matches!(expr.stx.as_ref(), Expr::LitStr(_)) || is_template_literal_without_substitutions(expr)
  {
    return EnumValueKind::String;
  }
  if eval_number_expr(expr).is_some() {
    return EnumValueKind::Number;
  }
  match expr.stx.as_ref() {
    Expr::Id(id) => known
      .get(&id.stx.name)
      .copied()
      .unwrap_or(EnumValueKind::Unknown),
    Expr::Member(member) => {
      if let Expr::Id(left) = member.stx.left.stx.as_ref() {
        if left.stx.name == enum_name {
          return known
            .get(&member.stx.right)
            .copied()
            .unwrap_or(EnumValueKind::Unknown);
        }
      }
      EnumValueKind::Unknown
    }
    Expr::ComputedMember(member) => {
      if let Expr::Id(left) = member.stx.object.stx.as_ref() {
        if left.stx.name == enum_name {
          if let Expr::LitStr(key) = member.stx.member.stx.as_ref() {
            return known
              .get(&key.stx.value)
              .copied()
              .unwrap_or(EnumValueKind::Unknown);
          }
        }
      }
      EnumValueKind::Unknown
    }
    _ => EnumValueKind::Unknown,
  }
}

fn eval_number_expr(expr: &Node<Expr>) -> Option<f64> {
  match expr.stx.as_ref() {
    Expr::LitNum(num) => Some(num.stx.value.0),
    Expr::Unary(unary) if unary.stx.operator == OperatorName::UnaryNegation => {
      eval_number_expr(&unary.stx.argument).map(|v| -v)
    }
    Expr::Unary(unary) if unary.stx.operator == OperatorName::UnaryPlus => {
      eval_number_expr(&unary.stx.argument)
    }
    _ => None,
  }
}

#[derive(Clone, Debug)]
enum ConstEnumValue {
  Number(f64),
  String(String),
}

#[derive(Debug)]
enum ConstEnumBinding {
  Values(HashMap<String, ConstEnumValue>),
  Blocked,
}

#[derive(Debug)]
enum ConstEnumLookupResult {
  NotFound,
  NotInlinable,
  Value(ConstEnumValue),
}

fn unwrap_ts_const_expr<'a>(mut expr: &'a Node<Expr>) -> &'a Node<Expr> {
  loop {
    match expr.stx.as_ref() {
      Expr::TypeAssertion(assert) => expr = assert.stx.expression.as_ref(),
      Expr::NonNullAssertion(assert) => expr = assert.stx.expression.as_ref(),
      Expr::SatisfiesExpr(assert) => expr = assert.stx.expression.as_ref(),
      _ => return expr,
    }
  }
}

fn eval_const_enum_expr(
  enum_name: &str,
  expr: &Node<Expr>,
  prior_members: &HashMap<String, ConstEnumValue>,
) -> Option<ConstEnumValue> {
  let expr = unwrap_ts_const_expr(expr);
  match expr.stx.as_ref() {
    Expr::LitNum(num) => Some(ConstEnumValue::Number(num.stx.value.0)),
    Expr::LitStr(str) => Some(ConstEnumValue::String(str.stx.value.clone())),
    Expr::LitTemplate(tpl) if is_template_literal_without_substitutions(expr) => {
      let mut value = String::new();
      for part in &tpl.stx.parts {
        if let LitTemplatePart::String(seg) = part {
          value.push_str(seg);
        }
      }
      Some(ConstEnumValue::String(value))
    }
    Expr::Unary(unary)
      if matches!(
        unary.stx.operator,
        OperatorName::UnaryNegation | OperatorName::UnaryPlus
      ) =>
    {
      let value = eval_const_enum_expr(enum_name, &unary.stx.argument, prior_members)?;
      let ConstEnumValue::Number(num) = value else {
        return None;
      };
      match unary.stx.operator {
        OperatorName::UnaryNegation => Some(ConstEnumValue::Number(-num)),
        OperatorName::UnaryPlus => Some(ConstEnumValue::Number(num)),
        _ => unreachable!(),
      }
    }
    Expr::Binary(bin)
      if matches!(
        bin.stx.operator,
        OperatorName::Addition | OperatorName::Subtraction
      ) =>
    {
      let left = eval_const_enum_expr(enum_name, &bin.stx.left, prior_members)?;
      let right = eval_const_enum_expr(enum_name, &bin.stx.right, prior_members)?;
      let (ConstEnumValue::Number(left), ConstEnumValue::Number(right)) = (left, right) else {
        return None;
      };
      match bin.stx.operator {
        OperatorName::Addition => Some(ConstEnumValue::Number(left + right)),
        OperatorName::Subtraction => Some(ConstEnumValue::Number(left - right)),
        _ => unreachable!(),
      }
    }
    Expr::Id(id) => prior_members.get(&id.stx.name).cloned(),
    Expr::Member(member) => match member.stx.left.stx.as_ref() {
      Expr::Id(left) if left.stx.name == enum_name => prior_members.get(&member.stx.right).cloned(),
      _ => None,
    },
    Expr::ComputedMember(member) => {
      let Expr::Id(left) = member.stx.object.stx.as_ref() else {
        return None;
      };
      if left.stx.name != enum_name {
        return None;
      }
      let member_expr = unwrap_ts_const_expr(&member.stx.member);
      let Expr::LitStr(key) = member_expr.stx.as_ref() else {
        return None;
      };
      prior_members.get(&key.stx.value).cloned()
    }
    _ => None,
  }
}

fn compute_const_enum_values(decl: &EnumDecl) -> Option<HashMap<String, ConstEnumValue>> {
  let mut out = HashMap::new();
  let mut next_numeric: Option<f64> = Some(0.0);
  for member in &decl.members {
    let name = member.stx.name.clone();
    let value = match member.stx.initializer.as_ref() {
      Some(initializer) => {
        let value = eval_const_enum_expr(&decl.name, initializer, &out)?;
        if let ConstEnumValue::Number(num) = value {
          next_numeric = Some(num + 1.0);
        } else {
          next_numeric = None;
        }
        value
      }
      None => {
        let value = ConstEnumValue::Number(next_numeric?);
        if let ConstEnumValue::Number(num) = value {
          next_numeric = Some(num + 1.0);
        }
        value
      }
    };
    out.insert(name, value);
  }
  Some(out)
}

fn extract_static_member_chain(expr: &Node<Expr>) -> Option<(String, Vec<String>)> {
  let mut parts = Vec::new();
  let mut cursor = expr;
  loop {
    let current = unwrap_ts_const_expr(cursor);
    match current.stx.as_ref() {
      Expr::Member(member) if !member.stx.optional_chaining => {
        parts.push(member.stx.right.clone());
        cursor = &member.stx.left;
      }
      Expr::ComputedMember(member) if !member.stx.optional_chaining => {
        let member_expr = unwrap_ts_const_expr(&member.stx.member);
        let Expr::LitStr(key) = member_expr.stx.as_ref() else {
          return None;
        };
        parts.push(key.stx.value.clone());
        cursor = &member.stx.object;
      }
      Expr::Id(id) => {
        parts.reverse();
        return Some((id.stx.name.clone(), parts));
      }
      _ => return None,
    }
  }
}

fn inline_const_enums(top_level: &mut Node<TopLevel>) -> HashSet<String> {
  #[derive(Default)]
  struct Inliner {
    const_enums: Vec<HashMap<Vec<String>, ConstEnumBinding>>,
    shadowed: Vec<HashSet<String>>,
    namespace_path: Vec<String>,
    erased_top_level: HashSet<String>,
  }

  impl Inliner {
    fn is_shadowed(&self, name: &str) -> bool {
      self.shadowed.iter().any(|scope| scope.contains(name))
    }

    fn lookup_const_enum_member(
      &self,
      enum_path: &[String],
      member: &str,
    ) -> ConstEnumLookupResult {
      for scope in self.const_enums.iter().rev() {
        let Some(binding) = scope.get(enum_path) else {
          continue;
        };
        return match binding {
          ConstEnumBinding::Blocked => ConstEnumLookupResult::NotInlinable,
          ConstEnumBinding::Values(members) => match members.get(member) {
            Some(value) => ConstEnumLookupResult::Value(value.clone()),
            None => ConstEnumLookupResult::NotInlinable,
          },
        };
      }
      ConstEnumLookupResult::NotFound
    }

    fn try_inline_member_access(&self, expr: &mut Node<Expr>) -> bool {
      let Some((base, parts)) = extract_static_member_chain(expr) else {
        return false;
      };
      if parts.is_empty() || self.is_shadowed(&base) {
        return false;
      }
      let (enum_parts, member) = parts.split_at(parts.len() - 1);
      let member = &member[0];
      let mut enum_path = Vec::with_capacity(1 + enum_parts.len());
      enum_path.push(base);
      enum_path.extend(enum_parts.iter().cloned());
      let value = match self.lookup_const_enum_member(&enum_path, member) {
        ConstEnumLookupResult::Value(value) => value,
        ConstEnumLookupResult::NotInlinable => return false,
        ConstEnumLookupResult::NotFound => {
          if self.namespace_path.is_empty() {
            return false;
          }
          let mut qualified_path =
            Vec::with_capacity(self.namespace_path.len().saturating_add(enum_path.len()));
          qualified_path.extend(self.namespace_path.iter().cloned());
          qualified_path.extend(enum_path);
          match self.lookup_const_enum_member(&qualified_path, member) {
            ConstEnumLookupResult::Value(value) => value,
            _ => return false,
          }
        }
      };

      let loc = expr.loc;
      let assoc = std::mem::take(&mut expr.assoc);
      let mut replacement = match value {
        ConstEnumValue::Number(num) => ts_lower::number(loc, num),
        ConstEnumValue::String(value) => ts_lower::string(loc, value),
      };
      replacement.assoc = assoc;
      *expr = replacement;
      true
    }

    fn collect_pat_declared(&self, pat: &Node<Pat>, out: &mut HashSet<String>) {
      match pat.stx.as_ref() {
        Pat::Id(id) => {
          out.insert(id.stx.name.clone());
        }
        Pat::Arr(arr) => {
          for elem in arr.stx.elements.iter().flatten() {
            self.collect_pat_declared(&elem.target, out);
          }
          if let Some(rest) = &arr.stx.rest {
            self.collect_pat_declared(rest, out);
          }
        }
        Pat::Obj(obj) => {
          for prop in &obj.stx.properties {
            self.collect_pat_declared(&prop.stx.target, out);
          }
          if let Some(rest) = &obj.stx.rest {
            self.collect_pat_declared(rest, out);
          }
        }
        Pat::AssignTarget(_) => {}
      }
    }

    fn collect_var_declared_names_in_stmt(&self, stmt: &Node<Stmt>, out: &mut HashSet<String>) {
      match stmt.stx.as_ref() {
        Stmt::VarDecl(decl) if decl.stx.mode == VarDeclMode::Var => {
          for declarator in &decl.stx.declarators {
            self.collect_pat_declared(&declarator.pattern.stx.pat, out);
          }
        }
        Stmt::ForTriple(for_stmt) => {
          if let ForTripleStmtInit::Decl(decl) = &for_stmt.stx.init {
            if decl.stx.mode == VarDeclMode::Var {
              for declarator in &decl.stx.declarators {
                self.collect_pat_declared(&declarator.pattern.stx.pat, out);
              }
            }
          }
          for stmt in &for_stmt.stx.body.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::ForIn(for_stmt) => {
          if let ForInOfLhs::Decl((VarDeclMode::Var, pat)) = &for_stmt.stx.lhs {
            self.collect_pat_declared(&pat.stx.pat, out);
          }
          for stmt in &for_stmt.stx.body.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::ForOf(for_stmt) => {
          if let ForInOfLhs::Decl((VarDeclMode::Var, pat)) = &for_stmt.stx.lhs {
            self.collect_pat_declared(&pat.stx.pat, out);
          }
          for stmt in &for_stmt.stx.body.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::Block(block) => {
          for stmt in &block.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::If(if_stmt) => {
          self.collect_var_declared_names_in_stmt(&if_stmt.stx.consequent, out);
          if let Some(alt) = &if_stmt.stx.alternate {
            self.collect_var_declared_names_in_stmt(alt, out);
          }
        }
        Stmt::While(while_stmt) => {
          self.collect_var_declared_names_in_stmt(&while_stmt.stx.body, out)
        }
        Stmt::DoWhile(do_stmt) => self.collect_var_declared_names_in_stmt(&do_stmt.stx.body, out),
        Stmt::With(with_stmt) => self.collect_var_declared_names_in_stmt(&with_stmt.stx.body, out),
        Stmt::Label(label) => self.collect_var_declared_names_in_stmt(&label.stx.statement, out),
        Stmt::Switch(switch_stmt) => {
          for branch in &switch_stmt.stx.branches {
            for stmt in &branch.stx.body {
              self.collect_var_declared_names_in_stmt(stmt, out);
            }
          }
        }
        Stmt::Try(try_stmt) => {
          for stmt in &try_stmt.stx.wrapped.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
          if let Some(catch) = &try_stmt.stx.catch {
            for stmt in &catch.stx.body {
              self.collect_var_declared_names_in_stmt(stmt, out);
            }
          }
          if let Some(finally) = &try_stmt.stx.finally {
            for stmt in &finally.stx.body {
              self.collect_var_declared_names_in_stmt(stmt, out);
            }
          }
        }
        Stmt::FunctionDecl(_) | Stmt::ClassDecl(_) => {}
        _ => {}
      }
    }

    fn collect_block_declared_names(&self, stmts: &[Node<Stmt>]) -> HashSet<String> {
      let mut out = HashSet::new();
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::VarDecl(decl)
            if matches!(
              decl.stx.mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) =>
          {
            for declarator in &decl.stx.declarators {
              self.collect_pat_declared(&declarator.pattern.stx.pat, &mut out);
            }
          }
          Stmt::FunctionDecl(func_decl) => {
            if let Some(name) = func_decl
              .stx
              .name
              .as_ref()
              .map(|name| name.stx.name.clone())
            {
              out.insert(name);
            }
          }
          Stmt::ClassDecl(class_decl) => {
            if let Some(name) = class_decl
              .stx
              .name
              .as_ref()
              .map(|name| name.stx.name.clone())
            {
              out.insert(name);
            }
          }
          Stmt::EnumDecl(decl) if !decl.stx.const_ => {
            out.insert(decl.stx.name.clone());
          }
          _ => {}
        }
      }
      out
    }

    fn collect_exported_const_enums_from_namespace(
      &self,
      decl: &NamespaceDecl,
      prefix: &mut Vec<String>,
      out: &mut HashMap<Vec<String>, ConstEnumBinding>,
    ) {
      match &decl.body {
        NamespaceBody::Block(stmts) => {
          for stmt in stmts {
            match stmt.stx.as_ref() {
              Stmt::EnumDecl(enum_decl) if enum_decl.stx.export && enum_decl.stx.const_ => {
                if let Some(values) = compute_const_enum_values(&enum_decl.stx) {
                  let mut path = prefix.clone();
                  path.push(enum_decl.stx.name.clone());
                  out.insert(path, ConstEnumBinding::Values(values));
                }
              }
              Stmt::NamespaceDecl(ns_decl) if ns_decl.stx.export => {
                prefix.push(ns_decl.stx.name.clone());
                self.collect_exported_const_enums_from_namespace(&ns_decl.stx, prefix, out);
                prefix.pop();
              }
              _ => {}
            }
          }
        }
        NamespaceBody::Namespace(inner) => {
          prefix.push(inner.stx.name.clone());
          self.collect_exported_const_enums_from_namespace(&inner.stx, prefix, out);
          prefix.pop();
        }
      }
    }

    fn collect_const_enums_in_scope(
      &mut self,
      stmts: &mut [Node<Stmt>],
      is_top_level: bool,
    ) -> HashMap<Vec<String>, ConstEnumBinding> {
      let mut out = HashMap::new();
      for stmt in stmts.iter_mut() {
        match stmt.stx.as_mut() {
          Stmt::EnumDecl(decl) if decl.stx.const_ => {
            let name = decl.stx.name.clone();
            let values = compute_const_enum_values(&decl.stx);
            if values.is_none() && decl.stx.declare {
              decl.stx.declare = false;
            }
            let binding = match values {
              Some(values) => {
                if is_top_level {
                  self.erased_top_level.insert(name.clone());
                }
                ConstEnumBinding::Values(values)
              }
              None => ConstEnumBinding::Blocked,
            };
            out.insert(vec![name], binding);
          }
          Stmt::NamespaceDecl(decl) => {
            let mut prefix = vec![decl.stx.name.clone()];
            self.collect_exported_const_enums_from_namespace(&decl.stx, &mut prefix, &mut out);
          }
          _ => {}
        }
      }
      out
    }

    fn rewrite_stmts_in_block(&mut self, stmts: &mut Vec<Node<Stmt>>, is_top_level: bool) {
      let scope = self.collect_block_declared_names(stmts);
      let enums = self.collect_const_enums_in_scope(stmts, is_top_level);
      self.shadowed.push(scope);
      self.const_enums.push(enums);

      let mut rewritten = Vec::with_capacity(stmts.len());
      for mut stmt in stmts.drain(..) {
        if let Stmt::EnumDecl(decl) = stmt.stx.as_ref() {
          if decl.stx.const_ {
            let current_scope = self
              .const_enums
              .last()
              .expect("const enum stack should never be empty");
            let key = vec![decl.stx.name.clone()];
            let should_erase = matches!(current_scope.get(&key), Some(ConstEnumBinding::Values(_)));
            if should_erase {
              continue;
            }
          }
        }
        self.rewrite_stmt(&mut stmt);
        rewritten.push(stmt);
      }
      *stmts = rewritten;

      self.const_enums.pop();
      self.shadowed.pop();
    }

    fn rewrite_pat(&mut self, pat: &mut Node<Pat>) {
      match pat.stx.as_mut() {
        Pat::Arr(arr) => {
          for elem in arr.stx.elements.iter_mut().flatten() {
            self.rewrite_pat(&mut elem.target);
            if let Some(default) = elem.default_value.as_mut() {
              self.rewrite_expr(default);
            }
          }
          if let Some(rest) = arr.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Pat::Obj(obj) => {
          for prop in obj.stx.properties.iter_mut() {
            self.rewrite_pat(&mut prop.stx.target);
            if let Some(default) = prop.stx.default_value.as_mut() {
              self.rewrite_expr(default);
            }
          }
          if let Some(rest) = obj.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Pat::AssignTarget(expr) => self.rewrite_expr(expr),
        Pat::Id(_) => {}
      }
    }

    fn rewrite_var_decl(&mut self, decl: &mut VarDecl) {
      for declarator in decl.declarators.iter_mut() {
        self.rewrite_pat(&mut declarator.pattern.stx.pat);
        if let Some(init) = declarator.initializer.as_mut() {
          self.rewrite_expr(init);
        }
      }
    }

    fn rewrite_func(&mut self, func: &mut Func, func_name: Option<&str>) {
      let mut scope = HashSet::new();
      for param in func.parameters.iter() {
        self.collect_pat_declared(&param.stx.pattern.stx.pat, &mut scope);
      }
      if let Some(name) = func_name {
        scope.insert(name.to_string());
      }
      if let Some(FuncBody::Block(body)) = &func.body {
        for stmt in body {
          self.collect_var_declared_names_in_stmt(stmt, &mut scope);
        }
      }

      self.shadowed.push(scope);
      for param in func.parameters.iter_mut() {
        self.rewrite_pat(&mut param.stx.pattern.stx.pat);
        if let Some(default) = param.stx.default_value.as_mut() {
          self.rewrite_expr(default);
        }
        for decorator in param.stx.decorators.iter_mut() {
          self.rewrite_expr(&mut decorator.stx.expression);
        }
      }
      match func.body.as_mut() {
        Some(FuncBody::Block(body)) => self.rewrite_stmts_in_block(body, false),
        Some(FuncBody::Expression(expr)) => self.rewrite_expr(expr),
        None => {}
      }
      self.shadowed.pop();
    }

    fn rewrite_class_members(&mut self, members: &mut Vec<Node<ClassMember>>) {
      for member in members.iter_mut() {
        if let ClassOrObjKey::Computed(expr) = &mut member.stx.key {
          self.rewrite_expr(expr);
        }
        for decorator in member.stx.decorators.iter_mut() {
          self.rewrite_expr(&mut decorator.stx.expression);
        }
        match &mut member.stx.val {
          ClassOrObjVal::Getter(get) => self.rewrite_func(&mut get.stx.func.stx, None),
          ClassOrObjVal::Setter(set) => self.rewrite_func(&mut set.stx.func.stx, None),
          ClassOrObjVal::Method(method) => self.rewrite_func(&mut method.stx.func.stx, None),
          ClassOrObjVal::Prop(Some(expr)) => self.rewrite_expr(expr),
          ClassOrObjVal::Prop(None) | ClassOrObjVal::IndexSignature(_) => {}
          ClassOrObjVal::StaticBlock(block) => {
            self.rewrite_stmts_in_block(&mut block.stx.body, false)
          }
        }
      }
    }

    fn rewrite_jsx_elem(&mut self, elem: &mut Node<JsxElem>) {
      for attr in elem.stx.attributes.iter_mut() {
        match attr {
          JsxAttr::Named { value, .. } => {
            if let Some(value) = value {
              match value {
                JsxAttrVal::Expression(expr) => self.rewrite_expr(&mut expr.stx.value),
                JsxAttrVal::Element(elem) => self.rewrite_jsx_elem(elem),
                JsxAttrVal::Text(_) => {}
              }
            }
          }
          JsxAttr::Spread { value } => self.rewrite_expr(&mut value.stx.value),
        }
      }
      for child in elem.stx.children.iter_mut() {
        match child {
          JsxElemChild::Element(elem) => self.rewrite_jsx_elem(elem),
          JsxElemChild::Expr(expr) => self.rewrite_expr(&mut expr.stx.value),
          JsxElemChild::Text(_) => {}
        }
      }
    }

    fn rewrite_obj_member(&mut self, member: &mut Node<ObjMember>) {
      match &mut member.stx.typ {
        ObjMemberType::Valued { key, val } => {
          if let ClassOrObjKey::Computed(expr) = key {
            self.rewrite_expr(expr);
          }
          match val {
            ClassOrObjVal::Getter(get) => self.rewrite_func(&mut get.stx.func.stx, None),
            ClassOrObjVal::Setter(set) => self.rewrite_func(&mut set.stx.func.stx, None),
            ClassOrObjVal::Method(method) => self.rewrite_func(&mut method.stx.func.stx, None),
            ClassOrObjVal::Prop(Some(expr)) => self.rewrite_expr(expr),
            ClassOrObjVal::Prop(None)
            | ClassOrObjVal::IndexSignature(_)
            | ClassOrObjVal::StaticBlock(_) => {}
          }
        }
        ObjMemberType::Rest { val } => self.rewrite_expr(val),
        ObjMemberType::Shorthand { .. } => {}
      }
    }

    fn rewrite_switch(&mut self, switch_stmt: &mut SwitchStmt) {
      let mut scope = HashSet::new();
      for branch in switch_stmt.branches.iter() {
        for stmt in branch.stx.body.iter() {
          match stmt.stx.as_ref() {
            Stmt::VarDecl(decl)
              if matches!(
                decl.stx.mode,
                VarDeclMode::Const
                  | VarDeclMode::Let
                  | VarDeclMode::Using
                  | VarDeclMode::AwaitUsing
              ) =>
            {
              for declarator in &decl.stx.declarators {
                self.collect_pat_declared(&declarator.pattern.stx.pat, &mut scope);
              }
            }
            Stmt::FunctionDecl(func_decl) => {
              if let Some(name) = func_decl
                .stx
                .name
                .as_ref()
                .map(|name| name.stx.name.clone())
              {
                scope.insert(name);
              }
            }
            Stmt::ClassDecl(class_decl) => {
              if let Some(name) = class_decl
                .stx
                .name
                .as_ref()
                .map(|name| name.stx.name.clone())
              {
                scope.insert(name);
              }
            }
            Stmt::EnumDecl(decl) if !decl.stx.const_ => {
              scope.insert(decl.stx.name.clone());
            }
            _ => {}
          }
        }
      }

      self.shadowed.push(scope);
      self.rewrite_expr(&mut switch_stmt.test);
      for branch in switch_stmt.branches.iter_mut() {
        if let Some(case) = branch.stx.case.as_mut() {
          self.rewrite_expr(case);
        }
        for stmt in branch.stx.body.iter_mut() {
          self.rewrite_stmt(stmt);
        }
      }
      self.shadowed.pop();
    }

    fn rewrite_namespace_decl(&mut self, decl: &mut NamespaceDecl) {
      self.namespace_path.push(decl.name.clone());
      match &mut decl.body {
        NamespaceBody::Block(stmts) => self.rewrite_stmts_in_block(stmts, false),
        NamespaceBody::Namespace(inner) => self.rewrite_namespace_decl(&mut inner.stx),
      }
      self.namespace_path.pop();
    }

    fn rewrite_stmt(&mut self, stmt: &mut Node<Stmt>) {
      match stmt.stx.as_mut() {
        Stmt::Block(block) => self.rewrite_stmts_in_block(&mut block.stx.body, false),
        Stmt::Expr(expr_stmt) => self.rewrite_expr(&mut expr_stmt.stx.expr),
        Stmt::If(if_stmt) => {
          self.rewrite_expr(&mut if_stmt.stx.test);
          self.rewrite_stmt(&mut if_stmt.stx.consequent);
          if let Some(alt) = if_stmt.stx.alternate.as_mut() {
            self.rewrite_stmt(alt);
          }
        }
        Stmt::ForTriple(for_stmt) => {
          let mut loop_scope = HashSet::new();
          if let ForTripleStmtInit::Decl(decl) = &for_stmt.stx.init {
            if matches!(
              decl.stx.mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) {
              for declarator in &decl.stx.declarators {
                self.collect_pat_declared(&declarator.pattern.stx.pat, &mut loop_scope);
              }
            }
          }
          self.shadowed.push(loop_scope);
          match &mut for_stmt.stx.init {
            ForTripleStmtInit::Expr(expr) => self.rewrite_expr(expr),
            ForTripleStmtInit::Decl(decl) => self.rewrite_var_decl(&mut decl.stx),
            ForTripleStmtInit::None => {}
          }
          if let Some(cond) = for_stmt.stx.cond.as_mut() {
            self.rewrite_expr(cond);
          }
          if let Some(post) = for_stmt.stx.post.as_mut() {
            self.rewrite_expr(post);
          }
          self.rewrite_stmts_in_block(&mut for_stmt.stx.body.stx.body, false);
          self.shadowed.pop();
        }
        Stmt::ForIn(for_stmt) => {
          let mut loop_scope = HashSet::new();
          if let ForInOfLhs::Decl((mode, pat)) = &for_stmt.stx.lhs {
            if matches!(
              mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) {
              self.collect_pat_declared(&pat.stx.pat, &mut loop_scope);
            }
          }
          self.shadowed.push(loop_scope);
          match &mut for_stmt.stx.lhs {
            ForInOfLhs::Assign(pat) => self.rewrite_pat(pat),
            ForInOfLhs::Decl((_, pat)) => self.rewrite_pat(&mut pat.stx.pat),
          }
          self.rewrite_expr(&mut for_stmt.stx.rhs);
          self.rewrite_stmts_in_block(&mut for_stmt.stx.body.stx.body, false);
          self.shadowed.pop();
        }
        Stmt::ForOf(for_stmt) => {
          let mut loop_scope = HashSet::new();
          if let ForInOfLhs::Decl((mode, pat)) = &for_stmt.stx.lhs {
            if matches!(
              mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) {
              self.collect_pat_declared(&pat.stx.pat, &mut loop_scope);
            }
          }
          self.shadowed.push(loop_scope);
          match &mut for_stmt.stx.lhs {
            ForInOfLhs::Assign(pat) => self.rewrite_pat(pat),
            ForInOfLhs::Decl((_, pat)) => self.rewrite_pat(&mut pat.stx.pat),
          }
          self.rewrite_expr(&mut for_stmt.stx.rhs);
          self.rewrite_stmts_in_block(&mut for_stmt.stx.body.stx.body, false);
          self.shadowed.pop();
        }
        Stmt::While(while_stmt) => {
          self.rewrite_expr(&mut while_stmt.stx.condition);
          self.rewrite_stmt(&mut while_stmt.stx.body);
        }
        Stmt::DoWhile(do_stmt) => {
          self.rewrite_stmt(&mut do_stmt.stx.body);
          self.rewrite_expr(&mut do_stmt.stx.condition);
        }
        Stmt::With(with_stmt) => {
          self.rewrite_expr(&mut with_stmt.stx.object);
          self.rewrite_stmt(&mut with_stmt.stx.body);
        }
        Stmt::Label(label) => self.rewrite_stmt(&mut label.stx.statement),
        Stmt::Switch(switch_stmt) => self.rewrite_switch(&mut switch_stmt.stx),
        Stmt::Try(try_stmt) => {
          self.rewrite_stmts_in_block(&mut try_stmt.stx.wrapped.stx.body, false);
          if let Some(catch) = try_stmt.stx.catch.as_mut() {
            let mut scope = HashSet::new();
            if let Some(param) = &catch.stx.parameter {
              self.collect_pat_declared(&param.stx.pat, &mut scope);
            }
            scope.extend(self.collect_block_declared_names(&catch.stx.body));
            self.shadowed.push(scope);
            for stmt in catch.stx.body.iter_mut() {
              self.rewrite_stmt(stmt);
            }
            self.shadowed.pop();
          }
          if let Some(finally) = try_stmt.stx.finally.as_mut() {
            self.rewrite_stmts_in_block(&mut finally.stx.body, false);
          }
        }
        Stmt::Throw(throw_stmt) => self.rewrite_expr(&mut throw_stmt.stx.value),
        Stmt::Return(ret_stmt) => {
          if let Some(expr) = ret_stmt.stx.value.as_mut() {
            self.rewrite_expr(expr);
          }
        }
        Stmt::VarDecl(decl) => self.rewrite_var_decl(&mut decl.stx),
        Stmt::FunctionDecl(func_decl) => {
          let func_name = func_decl
            .stx
            .name
            .as_ref()
            .map(|name| name.stx.name.as_str());
          self.rewrite_func(&mut func_decl.stx.function.stx, func_name);
        }
        Stmt::ClassDecl(class_decl) => {
          if let Some(extends) = class_decl.stx.extends.as_mut() {
            self.rewrite_expr(extends);
          }
          for decorator in class_decl.stx.decorators.iter_mut() {
            self.rewrite_expr(&mut decorator.stx.expression);
          }
          self.rewrite_class_members(&mut class_decl.stx.members);
        }
        Stmt::EnumDecl(enum_decl) => {
          for member in enum_decl.stx.members.iter_mut() {
            if let Some(init) = member.stx.initializer.as_mut() {
              self.rewrite_expr(init);
            }
          }
        }
        Stmt::NamespaceDecl(ns_decl) => self.rewrite_namespace_decl(&mut ns_decl.stx),
        Stmt::ModuleDecl(module_decl) => {
          if let Some(body) = module_decl.stx.body.as_mut() {
            self.rewrite_stmts_in_block(body, false);
          }
        }
        Stmt::ExportDefaultExpr(export_default) => {
          self.rewrite_expr(&mut export_default.stx.expression)
        }
        Stmt::Debugger(_)
        | Stmt::Break(_)
        | Stmt::Continue(_)
        | Stmt::Empty(_)
        | Stmt::ExportList(_)
        | Stmt::Import(_)
        | Stmt::InterfaceDecl(_)
        | Stmt::TypeAliasDecl(_)
        | Stmt::GlobalDecl(_)
        | Stmt::AmbientVarDecl(_)
        | Stmt::AmbientFunctionDecl(_)
        | Stmt::AmbientClassDecl(_)
        | Stmt::ImportTypeDecl(_)
        | Stmt::ExportTypeDecl(_)
        | Stmt::ImportEqualsDecl(_)
        | Stmt::ExportAssignmentDecl(_)
        | Stmt::ExportAsNamespaceDecl(_) => {}
      }
    }

    fn rewrite_expr(&mut self, expr: &mut Node<Expr>) {
      if self.try_inline_member_access(expr) {
        return;
      }

      match expr.stx.as_mut() {
        Expr::ArrowFunc(arrow) => self.rewrite_func(&mut arrow.stx.func.stx, None),
        Expr::Func(func_expr) => {
          let func_name = func_expr
            .stx
            .name
            .as_ref()
            .map(|name| name.stx.name.as_str());
          self.rewrite_func(&mut func_expr.stx.func.stx, func_name);
        }
        Expr::Class(class_expr) => {
          let mut scope = HashSet::new();
          if let Some(name) = class_expr
            .stx
            .name
            .as_ref()
            .map(|name| name.stx.name.clone())
          {
            scope.insert(name);
          }
          self.shadowed.push(scope);
          if let Some(extends) = class_expr.stx.extends.as_mut() {
            self.rewrite_expr(extends);
          }
          for decorator in class_expr.stx.decorators.iter_mut() {
            self.rewrite_expr(&mut decorator.stx.expression);
          }
          self.rewrite_class_members(&mut class_expr.stx.members);
          self.shadowed.pop();
        }
        Expr::Binary(bin) => {
          self.rewrite_expr(&mut bin.stx.left);
          self.rewrite_expr(&mut bin.stx.right);
        }
        Expr::Call(call) => {
          self.rewrite_expr(&mut call.stx.callee);
          for arg in call.stx.arguments.iter_mut() {
            self.rewrite_expr(&mut arg.stx.value);
          }
        }
        Expr::ComputedMember(member) => {
          self.rewrite_expr(&mut member.stx.object);
          self.rewrite_expr(&mut member.stx.member);
        }
        Expr::Cond(cond) => {
          self.rewrite_expr(&mut cond.stx.test);
          self.rewrite_expr(&mut cond.stx.consequent);
          self.rewrite_expr(&mut cond.stx.alternate);
        }
        Expr::Import(import) => {
          self.rewrite_expr(&mut import.stx.module);
          if let Some(attrs) = import.stx.attributes.as_mut() {
            self.rewrite_expr(attrs);
          }
        }
        Expr::Member(member) => {
          self.rewrite_expr(&mut member.stx.left);
        }
        Expr::TaggedTemplate(tagged) => {
          self.rewrite_expr(&mut tagged.stx.function);
          for part in tagged.stx.parts.iter_mut() {
            if let LitTemplatePart::Substitution(expr) = part {
              self.rewrite_expr(expr);
            }
          }
        }
        Expr::Unary(unary) => self.rewrite_expr(&mut unary.stx.argument),
        Expr::UnaryPostfix(unary) => self.rewrite_expr(&mut unary.stx.argument),
        Expr::LitArr(arr) => {
          for elem in arr.stx.elements.iter_mut() {
            if let LitArrElem::Single(expr) | LitArrElem::Rest(expr) = elem {
              self.rewrite_expr(expr);
            }
          }
        }
        Expr::LitObj(obj) => {
          for member in obj.stx.members.iter_mut() {
            self.rewrite_obj_member(member);
          }
        }
        Expr::LitTemplate(tpl) => {
          for part in tpl.stx.parts.iter_mut() {
            if let LitTemplatePart::Substitution(expr) = part {
              self.rewrite_expr(expr);
            }
          }
        }
        Expr::ArrPat(pat) => {
          for elem in pat.stx.elements.iter_mut().flatten() {
            self.rewrite_pat(&mut elem.target);
            if let Some(default) = elem.default_value.as_mut() {
              self.rewrite_expr(default);
            }
          }
          if let Some(rest) = pat.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Expr::ObjPat(pat) => {
          for prop in pat.stx.properties.iter_mut() {
            if let ClassOrObjKey::Computed(expr) = &mut prop.stx.key {
              self.rewrite_expr(expr);
            }
            self.rewrite_pat(&mut prop.stx.target);
            if let Some(default) = prop.stx.default_value.as_mut() {
              self.rewrite_expr(default);
            }
          }
          if let Some(rest) = pat.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Expr::JsxElem(elem) => self.rewrite_jsx_elem(elem),
        Expr::JsxExprContainer(expr) => self.rewrite_expr(&mut expr.stx.value),
        Expr::JsxSpreadAttr(spread) => self.rewrite_expr(&mut spread.stx.value),
        Expr::TypeAssertion(assert) => self.rewrite_expr(assert.stx.expression.as_mut()),
        Expr::NonNullAssertion(assert) => self.rewrite_expr(assert.stx.expression.as_mut()),
        Expr::SatisfiesExpr(assert) => self.rewrite_expr(assert.stx.expression.as_mut()),
        Expr::Id(_)
        | Expr::ImportMeta(_)
        | Expr::NewTarget(_)
        | Expr::Super(_)
        | Expr::This(_)
        | Expr::JsxMember(_)
        | Expr::JsxName(_)
        | Expr::JsxText(_)
        | Expr::LitBigInt(_)
        | Expr::LitBool(_)
        | Expr::LitNull(_)
        | Expr::LitNum(_)
        | Expr::LitRegex(_)
        | Expr::LitStr(_)
        | Expr::IdPat(_) => {}
      }
    }
  }

  let mut inliner = Inliner::default();
  inliner.shadowed.push(HashSet::new());
  inliner.const_enums.push(HashMap::new());
  inliner.rewrite_stmts_in_block(&mut top_level.stx.body, true);
  inliner.erased_top_level
}

fn rewrite_enum_member_refs(
  expr: &mut Node<Expr>,
  enum_object_ident: &str,
  enum_source_name: &str,
  enum_alias: &str,
  member_names: &HashSet<String>,
  rewrite_enum_source_name_refs: bool,
) -> bool {
  struct Rewriter<'a> {
    enum_name: &'a str,
    enum_source_name: &'a str,
    enum_alias: &'a str,
    member_names: &'a HashSet<String>,
    rewrite_enum_source_name_refs: bool,
    shadowed: Vec<HashSet<String>>,
    used_alias: bool,
  }

  impl<'a> Rewriter<'a> {
    fn is_shadowed(&self, name: &str) -> bool {
      self.shadowed.iter().any(|scope| scope.contains(name))
    }

    fn enum_object_ident(&mut self) -> &'a str {
      if self.is_shadowed(self.enum_name) {
        self.used_alias = true;
        self.enum_alias
      } else {
        self.enum_name
      }
    }

    fn with_scope<F: FnOnce(&mut Self)>(&mut self, scope: HashSet<String>, f: F) {
      self.shadowed.push(scope);
      f(self);
      self.shadowed.pop();
    }

    fn replace_with_member_access(&mut self, expr: &mut Node<Expr>, member: String) {
      let loc = expr.loc;
      let assoc = std::mem::take(&mut expr.assoc);
      let object_ident = self.enum_object_ident();
      let mut replacement = ts_lower::member_expr(
        loc,
        ts_lower::id(loc, object_ident.to_string()),
        ts_lower::MemberKey::Name(member),
      );
      replacement.assoc = assoc;
      *expr = replacement;
    }

    fn collect_pat_declared(&self, pat: &Node<Pat>, out: &mut HashSet<String>) {
      match pat.stx.as_ref() {
        Pat::Id(id) => {
          if self.member_names.contains(&id.stx.name)
            || id.stx.name == self.enum_name
            || id.stx.name == self.enum_source_name
          {
            out.insert(id.stx.name.clone());
          }
        }
        Pat::Arr(arr) => {
          for elem in arr.stx.elements.iter().flatten() {
            self.collect_pat_declared(&elem.target, out);
          }
          if let Some(rest) = &arr.stx.rest {
            self.collect_pat_declared(rest, out);
          }
        }
        Pat::Obj(obj) => {
          for prop in &obj.stx.properties {
            self.collect_pat_declared(&prop.stx.target, out);
          }
          if let Some(rest) = &obj.stx.rest {
            self.collect_pat_declared(rest, out);
          }
        }
        Pat::AssignTarget(_) => {}
      }
    }

    fn collect_var_declared_names_in_stmt(&self, stmt: &Node<Stmt>, out: &mut HashSet<String>) {
      match stmt.stx.as_ref() {
        Stmt::VarDecl(decl) if decl.stx.mode == VarDeclMode::Var => {
          for declarator in &decl.stx.declarators {
            self.collect_pat_declared(&declarator.pattern.stx.pat, out);
          }
        }
        Stmt::ForTriple(for_stmt) => {
          if let ForTripleStmtInit::Decl(decl) = &for_stmt.stx.init {
            if decl.stx.mode == VarDeclMode::Var {
              for declarator in &decl.stx.declarators {
                self.collect_pat_declared(&declarator.pattern.stx.pat, out);
              }
            }
          }
          for stmt in &for_stmt.stx.body.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::ForIn(for_stmt) => {
          if let ForInOfLhs::Decl((VarDeclMode::Var, pat)) = &for_stmt.stx.lhs {
            self.collect_pat_declared(&pat.stx.pat, out);
          }
          for stmt in &for_stmt.stx.body.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::ForOf(for_stmt) => {
          if let ForInOfLhs::Decl((VarDeclMode::Var, pat)) = &for_stmt.stx.lhs {
            self.collect_pat_declared(&pat.stx.pat, out);
          }
          for stmt in &for_stmt.stx.body.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::Block(block) => {
          for stmt in &block.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
        }
        Stmt::If(if_stmt) => {
          self.collect_var_declared_names_in_stmt(&if_stmt.stx.consequent, out);
          if let Some(alt) = &if_stmt.stx.alternate {
            self.collect_var_declared_names_in_stmt(alt, out);
          }
        }
        Stmt::While(while_stmt) => {
          self.collect_var_declared_names_in_stmt(&while_stmt.stx.body, out)
        }
        Stmt::DoWhile(do_stmt) => self.collect_var_declared_names_in_stmt(&do_stmt.stx.body, out),
        Stmt::With(with_stmt) => self.collect_var_declared_names_in_stmt(&with_stmt.stx.body, out),
        Stmt::Label(label) => self.collect_var_declared_names_in_stmt(&label.stx.statement, out),
        Stmt::Switch(switch_stmt) => {
          for branch in &switch_stmt.stx.branches {
            for stmt in &branch.stx.body {
              self.collect_var_declared_names_in_stmt(stmt, out);
            }
          }
        }
        Stmt::Try(try_stmt) => {
          for stmt in &try_stmt.stx.wrapped.stx.body {
            self.collect_var_declared_names_in_stmt(stmt, out);
          }
          if let Some(catch) = &try_stmt.stx.catch {
            for stmt in &catch.stx.body {
              self.collect_var_declared_names_in_stmt(stmt, out);
            }
          }
          if let Some(finally) = &try_stmt.stx.finally {
            for stmt in &finally.stx.body {
              self.collect_var_declared_names_in_stmt(stmt, out);
            }
          }
        }
        Stmt::FunctionDecl(_) | Stmt::ClassDecl(_) => {}
        _ => {}
      }
    }

    fn collect_block_declared_names(&self, stmts: &[Node<Stmt>]) -> HashSet<String> {
      let mut out = HashSet::new();
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::VarDecl(decl)
            if matches!(
              decl.stx.mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) =>
          {
            for declarator in &decl.stx.declarators {
              self.collect_pat_declared(&declarator.pattern.stx.pat, &mut out);
            }
          }
          Stmt::FunctionDecl(func_decl) => {
            if let Some(name) = func_decl
              .stx
              .name
              .as_ref()
              .map(|name| name.stx.name.clone())
            {
              if self.member_names.contains(&name)
                || name == self.enum_name
                || name == self.enum_source_name
              {
                out.insert(name);
              }
            }
          }
          Stmt::ClassDecl(class_decl) => {
            if let Some(name) = class_decl
              .stx
              .name
              .as_ref()
              .map(|name| name.stx.name.clone())
            {
              if self.member_names.contains(&name)
                || name == self.enum_name
                || name == self.enum_source_name
              {
                out.insert(name);
              }
            }
          }
          _ => {}
        }
      }
      out
    }

    fn rewrite_pat(&mut self, pat: &mut Node<Pat>) {
      match pat.stx.as_mut() {
        Pat::Arr(arr) => {
          for elem in arr.stx.elements.iter_mut() {
            if let Some(elem) = elem {
              self.rewrite_pat(&mut elem.target);
              if let Some(default) = elem.default_value.as_mut() {
                self.rewrite_expr(default);
              }
            }
          }
          if let Some(rest) = arr.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Pat::Obj(obj) => {
          for prop in obj.stx.properties.iter_mut() {
            if let ClassOrObjKey::Computed(expr) = &mut prop.stx.key {
              self.rewrite_expr(expr);
            }
            self.rewrite_pat(&mut prop.stx.target);
            if let Some(default) = prop.stx.default_value.as_mut() {
              self.rewrite_expr(default);
            }
          }
          if let Some(rest) = obj.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Pat::AssignTarget(expr) => self.rewrite_expr(expr),
        Pat::Id(_) => {}
      }
    }

    fn rewrite_var_decl(&mut self, decl: &mut VarDecl) {
      for declarator in decl.declarators.iter_mut() {
        self.rewrite_pat(&mut declarator.pattern.stx.pat);
        if let Some(init) = declarator.initializer.as_mut() {
          self.rewrite_expr(init);
        }
      }
    }

    fn rewrite_func(&mut self, func: &mut Func, func_name: Option<&str>) {
      let mut scope = HashSet::new();
      for param in func.parameters.iter() {
        self.collect_pat_declared(&param.stx.pattern.stx.pat, &mut scope);
      }
      if let Some(name) = func_name {
        if self.member_names.contains(name)
          || name == self.enum_name
          || name == self.enum_source_name
        {
          scope.insert(name.to_string());
        }
      }
      if let Some(FuncBody::Block(body)) = &func.body {
        for stmt in body {
          self.collect_var_declared_names_in_stmt(stmt, &mut scope);
        }
      }
      self.with_scope(scope, |rewriter| {
        for param in func.parameters.iter_mut() {
          rewriter.rewrite_pat(&mut param.stx.pattern.stx.pat);
          if let Some(default) = param.stx.default_value.as_mut() {
            rewriter.rewrite_expr(default);
          }
        }
        match func.body.as_mut() {
          Some(FuncBody::Block(body)) => rewriter.rewrite_stmts_in_block(body),
          Some(FuncBody::Expression(expr)) => rewriter.rewrite_expr(expr),
          None => {}
        }
      });
    }

    fn rewrite_class_members(&mut self, members: &mut Vec<Node<ClassMember>>) {
      for member in members.iter_mut() {
        if let ClassOrObjKey::Computed(expr) = &mut member.stx.key {
          self.rewrite_expr(expr);
        }
        for decorator in member.stx.decorators.iter_mut() {
          self.rewrite_expr(&mut decorator.stx.expression);
        }
        match &mut member.stx.val {
          ClassOrObjVal::Getter(get) => self.rewrite_func(&mut get.stx.func.stx, None),
          ClassOrObjVal::Setter(set) => self.rewrite_func(&mut set.stx.func.stx, None),
          ClassOrObjVal::Method(method) => self.rewrite_func(&mut method.stx.func.stx, None),
          ClassOrObjVal::Prop(Some(expr)) => self.rewrite_expr(expr),
          ClassOrObjVal::Prop(None) | ClassOrObjVal::IndexSignature(_) => {}
          ClassOrObjVal::StaticBlock(block) => self.rewrite_stmts_in_block(&mut block.stx.body),
        }
      }
    }

    fn rewrite_jsx_expr_container(&mut self, expr: &mut Node<JsxExprContainer>) {
      self.rewrite_expr(&mut expr.stx.value);
    }

    fn rewrite_jsx_elem_name(&mut self, name: &mut JsxElemName) {
      match name {
        JsxElemName::Id(id) => {
          if self.member_names.contains(&id.stx.name) && !self.is_shadowed(&id.stx.name) {
            let loc = id.loc;
            let member = id.stx.name.clone();
            let object_ident = self.enum_object_ident();
            *name = JsxElemName::Member(Node::new(
              loc,
              JsxMemberExpr {
                base: Node::new(
                  loc,
                  IdExpr {
                    name: object_ident.to_string(),
                  },
                ),
                path: vec![member],
              },
            ));
          }
        }
        JsxElemName::Member(member) => {
          let base_name = member.stx.base.stx.name.clone();
          if self.member_names.contains(&base_name) && !self.is_shadowed(&base_name) {
            let object_ident = self.enum_object_ident();
            member.stx.base.stx.name = object_ident.to_string();
            member.stx.path.insert(0, base_name);
          }
        }
        JsxElemName::Name(_) => {}
      }
    }

    fn rewrite_jsx_elem(&mut self, elem: &mut Node<JsxElem>) {
      if let Some(name) = elem.stx.name.as_mut() {
        self.rewrite_jsx_elem_name(name);
      }
      for attr in elem.stx.attributes.iter_mut() {
        match attr {
          JsxAttr::Named { value, .. } => {
            if let Some(value) = value {
              match value {
                JsxAttrVal::Expression(expr) => self.rewrite_jsx_expr_container(expr),
                JsxAttrVal::Element(elem) => self.rewrite_jsx_elem(elem),
                JsxAttrVal::Text(_) => {}
              }
            }
          }
          JsxAttr::Spread { value } => self.rewrite_expr(&mut value.stx.value),
        }
      }

      for child in elem.stx.children.iter_mut() {
        match child {
          JsxElemChild::Element(elem) => self.rewrite_jsx_elem(elem),
          JsxElemChild::Expr(expr) => self.rewrite_jsx_expr_container(expr),
          JsxElemChild::Text(_) => {}
        }
      }
    }

    fn rewrite_obj_member(&mut self, member: &mut Node<ObjMember>) {
      match &mut member.stx.typ {
        ObjMemberType::Valued { key, val } => {
          if let ClassOrObjKey::Computed(expr) = key {
            self.rewrite_expr(expr);
          }
          match val {
            ClassOrObjVal::Getter(get) => self.rewrite_func(&mut get.stx.func.stx, None),
            ClassOrObjVal::Setter(set) => self.rewrite_func(&mut set.stx.func.stx, None),
            ClassOrObjVal::Method(method) => self.rewrite_func(&mut method.stx.func.stx, None),
            ClassOrObjVal::Prop(Some(expr)) => self.rewrite_expr(expr),
            ClassOrObjVal::Prop(None)
            | ClassOrObjVal::IndexSignature(_)
            | ClassOrObjVal::StaticBlock(_) => {}
          }
        }
        ObjMemberType::Rest { val } => self.rewrite_expr(val),
        ObjMemberType::Shorthand { id } => {
          if self.member_names.contains(&id.stx.name) && !self.is_shadowed(&id.stx.name) {
            let loc = id.loc;
            let member_name = id.stx.name.clone();
            let key = ClassOrObjKey::Direct(Node::new(
              loc,
              ClassOrObjMemberDirectKey {
                key: member_name.clone(),
                tt: TT::Identifier,
              },
            ));
            let mut value = Node::new(
              loc,
              Expr::Id(Node::new(
                loc,
                IdExpr {
                  name: member_name.clone(),
                },
              )),
            );
            self.replace_with_member_access(&mut value, member_name);
            member.stx.typ = ObjMemberType::Valued {
              key,
              val: ClassOrObjVal::Prop(Some(value)),
            };
          }
        }
      }
    }

    fn rewrite_stmts_in_block(&mut self, stmts: &mut Vec<Node<Stmt>>) {
      let scope = self.collect_block_declared_names(stmts);
      self.with_scope(scope, |rewriter| {
        for stmt in stmts.iter_mut() {
          rewriter.rewrite_stmt(stmt);
        }
      });
    }

    fn rewrite_for_body(&mut self, body: &mut Node<ForBody>) {
      self.rewrite_stmts_in_block(&mut body.stx.body);
    }

    fn rewrite_switch(&mut self, switch_stmt: &mut SwitchStmt) {
      let mut scope = HashSet::new();
      for branch in switch_stmt.branches.iter() {
        for stmt in branch.stx.body.iter() {
          match stmt.stx.as_ref() {
            Stmt::VarDecl(decl)
              if matches!(
                decl.stx.mode,
                VarDeclMode::Const
                  | VarDeclMode::Let
                  | VarDeclMode::Using
                  | VarDeclMode::AwaitUsing
              ) =>
            {
              for declarator in &decl.stx.declarators {
                self.collect_pat_declared(&declarator.pattern.stx.pat, &mut scope);
              }
            }
            Stmt::FunctionDecl(func_decl) => {
              if let Some(name) = func_decl
                .stx
                .name
                .as_ref()
                .map(|name| name.stx.name.clone())
              {
                if self.member_names.contains(&name) {
                  scope.insert(name);
                }
              }
            }
            Stmt::ClassDecl(class_decl) => {
              if let Some(name) = class_decl
                .stx
                .name
                .as_ref()
                .map(|name| name.stx.name.clone())
              {
                if self.member_names.contains(&name) {
                  scope.insert(name);
                }
              }
            }
            _ => {}
          }
        }
      }

      self.with_scope(scope, |rewriter| {
        rewriter.rewrite_expr(&mut switch_stmt.test);
        for branch in switch_stmt.branches.iter_mut() {
          if let Some(case) = branch.stx.case.as_mut() {
            rewriter.rewrite_expr(case);
          }
          for stmt in branch.stx.body.iter_mut() {
            rewriter.rewrite_stmt(stmt);
          }
        }
      });
    }

    fn rewrite_stmt(&mut self, stmt: &mut Node<Stmt>) {
      match stmt.stx.as_mut() {
        Stmt::Block(block) => self.rewrite_stmts_in_block(&mut block.stx.body),
        Stmt::Expr(expr_stmt) => self.rewrite_expr(&mut expr_stmt.stx.expr),
        Stmt::If(if_stmt) => {
          self.rewrite_expr(&mut if_stmt.stx.test);
          self.rewrite_stmt(&mut if_stmt.stx.consequent);
          if let Some(alt) = if_stmt.stx.alternate.as_mut() {
            self.rewrite_stmt(alt);
          }
        }
        Stmt::ForTriple(for_stmt) => {
          let mut loop_scope = HashSet::new();
          if let ForTripleStmtInit::Decl(decl) = &for_stmt.stx.init {
            if matches!(
              decl.stx.mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) {
              for declarator in &decl.stx.declarators {
                self.collect_pat_declared(&declarator.pattern.stx.pat, &mut loop_scope);
              }
            }
          }
          self.with_scope(loop_scope, |rewriter| {
            match &mut for_stmt.stx.init {
              ForTripleStmtInit::Expr(expr) => rewriter.rewrite_expr(expr),
              ForTripleStmtInit::Decl(decl) => rewriter.rewrite_var_decl(&mut decl.stx),
              ForTripleStmtInit::None => {}
            }
            if let Some(cond) = for_stmt.stx.cond.as_mut() {
              rewriter.rewrite_expr(cond);
            }
            if let Some(post) = for_stmt.stx.post.as_mut() {
              rewriter.rewrite_expr(post);
            }
            rewriter.rewrite_for_body(&mut for_stmt.stx.body);
          });
        }
        Stmt::ForIn(for_stmt) => {
          let mut loop_scope = HashSet::new();
          if let ForInOfLhs::Decl((mode, pat)) = &for_stmt.stx.lhs {
            if matches!(
              mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) {
              self.collect_pat_declared(&pat.stx.pat, &mut loop_scope);
            }
          }
          self.with_scope(loop_scope, |rewriter| {
            match &mut for_stmt.stx.lhs {
              ForInOfLhs::Assign(pat) => rewriter.rewrite_pat(pat),
              ForInOfLhs::Decl((_, pat)) => rewriter.rewrite_pat(&mut pat.stx.pat),
            }
            rewriter.rewrite_expr(&mut for_stmt.stx.rhs);
            rewriter.rewrite_for_body(&mut for_stmt.stx.body);
          });
        }
        Stmt::ForOf(for_stmt) => {
          let mut loop_scope = HashSet::new();
          if let ForInOfLhs::Decl((mode, pat)) = &for_stmt.stx.lhs {
            if matches!(
              mode,
              VarDeclMode::Const | VarDeclMode::Let | VarDeclMode::Using | VarDeclMode::AwaitUsing
            ) {
              self.collect_pat_declared(&pat.stx.pat, &mut loop_scope);
            }
          }
          self.with_scope(loop_scope, |rewriter| {
            match &mut for_stmt.stx.lhs {
              ForInOfLhs::Assign(pat) => rewriter.rewrite_pat(pat),
              ForInOfLhs::Decl((_, pat)) => rewriter.rewrite_pat(&mut pat.stx.pat),
            }
            rewriter.rewrite_expr(&mut for_stmt.stx.rhs);
            rewriter.rewrite_for_body(&mut for_stmt.stx.body);
          });
        }
        Stmt::While(while_stmt) => {
          self.rewrite_expr(&mut while_stmt.stx.condition);
          self.rewrite_stmt(&mut while_stmt.stx.body);
        }
        Stmt::DoWhile(do_stmt) => {
          self.rewrite_stmt(&mut do_stmt.stx.body);
          self.rewrite_expr(&mut do_stmt.stx.condition);
        }
        Stmt::With(with_stmt) => {
          self.rewrite_expr(&mut with_stmt.stx.object);
          self.rewrite_stmt(&mut with_stmt.stx.body);
        }
        Stmt::Label(label) => self.rewrite_stmt(&mut label.stx.statement),
        Stmt::Switch(switch_stmt) => self.rewrite_switch(&mut switch_stmt.stx),
        Stmt::Try(try_stmt) => {
          self.rewrite_stmts_in_block(&mut try_stmt.stx.wrapped.stx.body);
          if let Some(catch) = try_stmt.stx.catch.as_mut() {
            let mut scope = HashSet::new();
            if let Some(param) = &catch.stx.parameter {
              self.collect_pat_declared(&param.stx.pat, &mut scope);
            }
            scope.extend(self.collect_block_declared_names(&catch.stx.body));
            self.with_scope(scope, |rewriter| {
              for stmt in catch.stx.body.iter_mut() {
                rewriter.rewrite_stmt(stmt);
              }
            });
          }
          if let Some(finally) = try_stmt.stx.finally.as_mut() {
            self.rewrite_stmts_in_block(&mut finally.stx.body);
          }
        }
        Stmt::Throw(throw_stmt) => self.rewrite_expr(&mut throw_stmt.stx.value),
        Stmt::Return(ret_stmt) => {
          if let Some(expr) = ret_stmt.stx.value.as_mut() {
            self.rewrite_expr(expr);
          }
        }
        Stmt::VarDecl(decl) => self.rewrite_var_decl(&mut decl.stx),
        Stmt::FunctionDecl(func_decl) => {
          let func_name = func_decl
            .stx
            .name
            .as_ref()
            .map(|name| name.stx.name.as_str());
          self.rewrite_func(&mut func_decl.stx.function.stx, func_name);
        }
        Stmt::ClassDecl(class_decl) => {
          if let Some(extends) = class_decl.stx.extends.as_mut() {
            self.rewrite_expr(extends);
          }
          for decorator in class_decl.stx.decorators.iter_mut() {
            self.rewrite_expr(&mut decorator.stx.expression);
          }
          self.rewrite_class_members(&mut class_decl.stx.members);
        }
        Stmt::Debugger(_)
        | Stmt::Break(_)
        | Stmt::Continue(_)
        | Stmt::Empty(_)
        | Stmt::ExportDefaultExpr(_)
        | Stmt::ExportList(_)
        | Stmt::Import(_)
        | Stmt::InterfaceDecl(_)
        | Stmt::TypeAliasDecl(_)
        | Stmt::EnumDecl(_)
        | Stmt::NamespaceDecl(_)
        | Stmt::ModuleDecl(_)
        | Stmt::GlobalDecl(_)
        | Stmt::AmbientVarDecl(_)
        | Stmt::AmbientFunctionDecl(_)
        | Stmt::AmbientClassDecl(_)
        | Stmt::ImportTypeDecl(_)
        | Stmt::ExportTypeDecl(_)
        | Stmt::ImportEqualsDecl(_)
        | Stmt::ExportAssignmentDecl(_)
        | Stmt::ExportAsNamespaceDecl(_) => {}
      }
    }

    fn rewrite_expr(&mut self, expr: &mut Node<Expr>) {
      if self.rewrite_enum_source_name_refs && self.enum_source_name != self.enum_name {
        if let Some(loc) = match expr.stx.as_ref() {
          Expr::Id(id)
            if id.stx.name == self.enum_source_name && !self.is_shadowed(self.enum_source_name) =>
          {
            Some(id.loc)
          }
          _ => None,
        } {
          let assoc = std::mem::take(&mut expr.assoc);
          let object_ident = self.enum_object_ident();
          let mut replacement = ts_lower::id(loc, object_ident.to_string());
          replacement.assoc = assoc;
          *expr = replacement;
          return;
        }
      }

      if let Some(member) = match expr.stx.as_ref() {
        Expr::Id(id)
          if self.member_names.contains(&id.stx.name) && !self.is_shadowed(&id.stx.name) =>
        {
          Some(id.stx.name.clone())
        }
        _ => None,
      } {
        self.replace_with_member_access(expr, member);
        return;
      }

      match expr.stx.as_mut() {
        Expr::ArrowFunc(arrow) => self.rewrite_func(&mut arrow.stx.func.stx, None),
        Expr::Func(func_expr) => {
          let func_name = func_expr
            .stx
            .name
            .as_ref()
            .map(|name| name.stx.name.as_str());
          self.rewrite_func(&mut func_expr.stx.func.stx, func_name);
        }
        Expr::Class(class_expr) => {
          if let Some(name) = class_expr
            .stx
            .name
            .as_ref()
            .map(|name| name.stx.name.clone())
          {
            if self.member_names.contains(&name)
              || name == self.enum_name
              || name == self.enum_source_name
            {
              let mut scope = HashSet::new();
              scope.insert(name);
              self.with_scope(scope, |rewriter| {
                rewriter.rewrite_class_members(&mut class_expr.stx.members);
              });
              return;
            }
          }
          if let Some(extends) = class_expr.stx.extends.as_mut() {
            self.rewrite_expr(extends);
          }
          for decorator in class_expr.stx.decorators.iter_mut() {
            self.rewrite_expr(&mut decorator.stx.expression);
          }
          self.rewrite_class_members(&mut class_expr.stx.members);
        }
        Expr::Binary(bin) => {
          self.rewrite_expr(&mut bin.stx.left);
          self.rewrite_expr(&mut bin.stx.right);
        }
        Expr::Call(call) => {
          self.rewrite_expr(&mut call.stx.callee);
          for arg in call.stx.arguments.iter_mut() {
            self.rewrite_expr(&mut arg.stx.value);
          }
        }
        Expr::ComputedMember(member) => {
          self.rewrite_expr(&mut member.stx.object);
          self.rewrite_expr(&mut member.stx.member);
        }
        Expr::Cond(cond) => {
          self.rewrite_expr(&mut cond.stx.test);
          self.rewrite_expr(&mut cond.stx.consequent);
          self.rewrite_expr(&mut cond.stx.alternate);
        }
        Expr::Import(import) => {
          self.rewrite_expr(&mut import.stx.module);
          if let Some(attrs) = import.stx.attributes.as_mut() {
            self.rewrite_expr(attrs);
          }
        }
        Expr::Member(member) => {
          self.rewrite_expr(&mut member.stx.left);
        }
        Expr::TaggedTemplate(tagged) => {
          self.rewrite_expr(&mut tagged.stx.function);
          for part in tagged.stx.parts.iter_mut() {
            if let LitTemplatePart::Substitution(expr) = part {
              self.rewrite_expr(expr);
            }
          }
        }
        Expr::Unary(unary) => self.rewrite_expr(&mut unary.stx.argument),
        Expr::UnaryPostfix(unary) => self.rewrite_expr(&mut unary.stx.argument),
        Expr::LitArr(arr) => {
          for elem in arr.stx.elements.iter_mut() {
            if let LitArrElem::Single(expr) | LitArrElem::Rest(expr) = elem {
              self.rewrite_expr(expr);
            }
          }
        }
        Expr::LitObj(obj) => {
          for member in obj.stx.members.iter_mut() {
            self.rewrite_obj_member(member);
          }
        }
        Expr::LitTemplate(tpl) => {
          for part in tpl.stx.parts.iter_mut() {
            if let LitTemplatePart::Substitution(expr) = part {
              self.rewrite_expr(expr);
            }
          }
        }
        Expr::ArrPat(pat) => {
          for elem in pat.stx.elements.iter_mut() {
            if let Some(elem) = elem {
              self.rewrite_pat(&mut elem.target);
              if let Some(default) = elem.default_value.as_mut() {
                self.rewrite_expr(default);
              }
            }
          }
          if let Some(rest) = pat.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Expr::ObjPat(pat) => {
          for prop in pat.stx.properties.iter_mut() {
            if let ClassOrObjKey::Computed(expr) = &mut prop.stx.key {
              self.rewrite_expr(expr);
            }
            self.rewrite_pat(&mut prop.stx.target);
            if let Some(default) = prop.stx.default_value.as_mut() {
              self.rewrite_expr(default);
            }
          }
          if let Some(rest) = pat.stx.rest.as_mut() {
            self.rewrite_pat(rest);
          }
        }
        Expr::Id(_)
        | Expr::ImportMeta(_)
        | Expr::NewTarget(_)
        | Expr::Super(_)
        | Expr::This(_)
        | Expr::JsxMember(_)
        | Expr::JsxName(_)
        | Expr::JsxText(_)
        | Expr::LitBigInt(_)
        | Expr::LitBool(_)
        | Expr::LitNull(_)
        | Expr::LitNum(_)
        | Expr::LitRegex(_)
        | Expr::LitStr(_)
        | Expr::IdPat(_) => {}
        Expr::JsxElem(elem) => self.rewrite_jsx_elem(elem),
        Expr::JsxExprContainer(expr) => self.rewrite_jsx_expr_container(expr),
        Expr::JsxSpreadAttr(spread) => self.rewrite_expr(&mut spread.stx.value),
        Expr::TypeAssertion(_) | Expr::NonNullAssertion(_) | Expr::SatisfiesExpr(_) => {}
      }
    }
  }

  let mut rewriter = Rewriter {
    enum_name: enum_object_ident,
    enum_source_name,
    enum_alias,
    member_names,
    rewrite_enum_source_name_refs,
    shadowed: Vec::new(),
    used_alias: false,
  };
  rewriter.rewrite_expr(expr);
  rewriter.used_alias
}

fn enum_assign_stmt(loc: Loc, enum_ident: &str, member: &str, value: Node<Expr>) -> Node<Stmt> {
  ts_lower::member_assignment_stmt(
    loc,
    ts_lower::id(loc, enum_ident),
    ts_lower::MemberKey::Name(member.to_string()),
    value,
  )
}

fn enum_reverse_mapping_stmt(
  loc: Loc,
  enum_ident: &str,
  member: &str,
  value: Node<Expr>,
) -> Node<Stmt> {
  let enum_obj = ts_lower::id(loc, enum_ident);
  let name_assign = ts_lower::assign_expr(
    loc,
    ts_lower::member_expr(
      loc,
      ts_lower::id(loc, enum_ident),
      ts_lower::MemberKey::Name(member.to_string()),
    ),
    value,
  );
  let reverse_left = ts_lower::member_expr(loc, enum_obj, ts_lower::MemberKey::Expr(name_assign));
  ts_lower::expr_stmt(
    loc,
    ts_lower::assign_expr(loc, reverse_left, ts_lower::string(loc, member.to_string())),
  )
}

fn enum_iife_arg(
  loc: Loc,
  local_ident: &str,
  property_name: &str,
  parent_namespace: Option<&str>,
  bind_to_local: bool,
) -> Node<Expr> {
  match parent_namespace {
    None => ts_lower::binary_expr(
      loc,
      OperatorName::LogicalOr,
      ts_lower::id(loc, local_ident),
      ts_lower::assign_expr(
        loc,
        ts_lower::id(loc, local_ident),
        ts_lower::empty_object(loc),
      ),
    ),
    Some(namespace_param) => {
      let prop_read = ts_lower::member_expr(
        loc,
        ts_lower::id(loc, namespace_param),
        ts_lower::MemberKey::Name(property_name.to_string()),
      );
      let prop_write = ts_lower::member_expr(
        loc,
        ts_lower::id(loc, namespace_param),
        ts_lower::MemberKey::Name(property_name.to_string()),
      );
      let prop_or = ts_lower::binary_expr(
        loc,
        OperatorName::LogicalOr,
        prop_read,
        ts_lower::assign_expr(loc, prop_write, ts_lower::empty_object(loc)),
      );
      if bind_to_local {
        ts_lower::assign_expr(loc, ts_lower::id(loc, local_ident), prop_or)
      } else {
        prop_or
      }
    }
  }
}

fn strip_enum_decl(
  ctx: &mut StripContext,
  decl: Node<EnumDecl>,
  loc: Loc,
  _assoc: NodeAssocData,
  is_top_level: bool,
  parent_namespace: Option<&str>,
) -> Vec<Node<Stmt>> {
  if decl.stx.declare {
    return vec![];
  }

  let enum_name = decl.stx.name.clone();
  let name_is_binding_identifier = is_valid_binding_identifier(&enum_name, ctx.top_level_mode);
  if parent_namespace.is_none() && !name_is_binding_identifier {
    let allow_top_level_export =
      is_top_level && decl.stx.export && matches!(ctx.top_level_mode, TopLevelMode::Module);
    if !allow_top_level_export {
      unsupported_ts(
        ctx,
        loc,
        format!("runtime enum name `{enum_name}` is not a valid JavaScript identifier"),
      );
      return vec![];
    }
  }
  let enum_param_ident = if name_is_binding_identifier {
    enum_name.clone()
  } else {
    ctx.runtime_enum_object_ident(&enum_name)
  };
  let binding_ident = if name_is_binding_identifier {
    enum_name.clone()
  } else {
    enum_param_ident.clone()
  };
  let has_value_binding = ctx.current_value_bindings().contains(&binding_ident);
  let member_names: HashSet<String> = decl
    .stx
    .members
    .iter()
    .map(|member| member.stx.name.clone())
    .collect();
  let should_export_binding = parent_namespace.is_none()
    && is_top_level
    && matches!(ctx.top_level_mode, TopLevelMode::Module)
    && decl.stx.export
    && !ctx.top_level_module_exports.contains(&enum_name)
    && ctx.emitted_export_var.insert(enum_name.clone());

  let mut out = Vec::new();
  if should_export_binding {
    if name_is_binding_identifier {
      if has_value_binding {
        out.push(export_binding_stmt(loc, enum_name.clone()));
      }
    } else {
      out.push(export_binding_as_stmt(
        loc,
        binding_ident.clone(),
        enum_name.clone(),
      ));
    }
  }
  let should_export_var = should_export_binding && name_is_binding_identifier && !has_value_binding;

  // When exporting enums to runtime namespaces (`parent_namespace`), a pre-existing value binding
  // should be attached to the namespace object before the enum IIFE runs, otherwise we would
  // overwrite the binding with a fresh object.
  if let Some(namespace_param) = parent_namespace {
    if has_value_binding {
      out.push(ts_lower::member_assignment_stmt(
        loc,
        ts_lower::id(loc, namespace_param),
        ts_lower::MemberKey::Name(enum_name.clone()),
        ts_lower::id(loc, binding_ident.clone()),
      ));
    }
  }

  if (name_is_binding_identifier || parent_namespace.is_none()) && !has_value_binding {
    out.push(ts_lower::var_decl_stmt(
      loc,
      binding_ident.clone(),
      None,
      should_export_var,
      VarDeclMode::Var,
    ));
    ctx
      .current_value_bindings_mut()
      .insert(binding_ident.clone());
  }

  let enum_alias = ctx.fresh_internal_name(format!("__minify_ts_enum_{enum_name}"));
  let mut used_enum_alias = false;
  let mut body = Vec::with_capacity(decl.stx.members.len());
  let rewrite_enum_source_name_refs =
    !is_valid_identifier_reference(&enum_name, ctx.top_level_mode);
  let mut next_auto: Option<f64> = Some(0.0);
  let mut last_numeric_member: Option<String> = None;
  let mut known_member_kinds: HashMap<String, EnumValueKind> = HashMap::new();
  for member in decl.stx.members {
    let member_name = member.stx.name.clone();
    let mut initializer = member.stx.initializer.map(|expr| strip_expr(ctx, expr));
    let kind = initializer
      .as_ref()
      .map(|expr| enum_value_kind(&enum_name, expr, &known_member_kinds))
      .unwrap_or(EnumValueKind::Number);
    if let Some(expr) = initializer.as_mut() {
      used_enum_alias |= rewrite_enum_member_refs(
        expr,
        &enum_param_ident,
        &enum_name,
        &enum_alias,
        &member_names,
        rewrite_enum_source_name_refs,
      );
    }

    match (kind, initializer) {
      (EnumValueKind::String, Some(expr)) => {
        body.push(enum_assign_stmt(loc, &enum_param_ident, &member_name, expr));
        next_auto = None;
        last_numeric_member = None;
      }
      (_, Some(expr)) => {
        next_auto = eval_number_expr(&expr).map(|v| v + 1.0);
        body.push(enum_reverse_mapping_stmt(
          loc,
          &enum_param_ident,
          &member_name,
          expr,
        ));
        last_numeric_member = Some(member_name.clone());
      }
      (_, None) => {
        let value_expr = match (next_auto, last_numeric_member.as_ref()) {
          (Some(value), _) => {
            next_auto = Some(value + 1.0);
            ts_lower::number(loc, value)
          }
          (None, Some(prev)) => ts_lower::binary_expr(
            loc,
            OperatorName::Addition,
            ts_lower::member_expr(
              loc,
              ts_lower::id(loc, enum_param_ident.clone()),
              ts_lower::MemberKey::Name(prev.to_string()),
            ),
            ts_lower::number(loc, 1.0),
          ),
          (None, None) => {
            next_auto = Some(1.0);
            ts_lower::number(loc, 0.0)
          }
        };
        body.push(enum_reverse_mapping_stmt(
          loc,
          &enum_param_ident,
          &member_name,
          value_expr,
        ));
        last_numeric_member = Some(member_name.clone());
      }
    }

    known_member_kinds.insert(member_name, kind);
  }

  if used_enum_alias {
    body.insert(
      0,
      ts_lower::var_decl_stmt(
        loc,
        enum_alias,
        Some(ts_lower::id(loc, enum_param_ident.clone())),
        false,
        VarDeclMode::Var,
      ),
    );
  }

  let arg = enum_iife_arg(
    loc,
    &enum_param_ident,
    &enum_name,
    parent_namespace,
    name_is_binding_identifier,
  );
  out.push(ts_lower::iife_stmt(loc, enum_param_ident, arg, body));
  out
}

fn namespace_iife_arg(
  loc: Loc,
  local_ident: &str,
  property_name: &str,
  parent_namespace: Option<&str>,
  bind_to_local: bool,
) -> Node<Expr> {
  match parent_namespace {
    None => ts_lower::binary_expr(
      loc,
      OperatorName::LogicalOr,
      ts_lower::id(loc, local_ident),
      ts_lower::assign_expr(
        loc,
        ts_lower::id(loc, local_ident),
        ts_lower::empty_object(loc),
      ),
    ),
    Some(namespace_param) => {
      let prop_read = ts_lower::member_expr(
        loc,
        ts_lower::id(loc, namespace_param),
        ts_lower::MemberKey::Name(property_name.to_string()),
      );
      let prop_write = ts_lower::member_expr(
        loc,
        ts_lower::id(loc, namespace_param),
        ts_lower::MemberKey::Name(property_name.to_string()),
      );
      let prop_or = ts_lower::binary_expr(
        loc,
        OperatorName::LogicalOr,
        prop_read,
        ts_lower::assign_expr(loc, prop_write, ts_lower::empty_object(loc)),
      );
      if bind_to_local {
        ts_lower::assign_expr(loc, ts_lower::id(loc, local_ident), prop_or)
      } else {
        prop_or
      }
    }
  }
}

fn namespace_export_assignments(
  loc: Loc,
  namespace_param: &str,
  names: &[String],
) -> Vec<Node<Stmt>> {
  names
    .iter()
    .map(|name| {
      ts_lower::member_assignment_stmt(
        loc,
        ts_lower::id(loc, namespace_param),
        ts_lower::MemberKey::Name(name.clone()),
        ts_lower::id(loc, name.clone()),
      )
    })
    .collect()
}

fn collect_pat_binding_names(pat: &Node<Pat>, out: &mut Vec<String>) {
  match pat.stx.as_ref() {
    Pat::Id(id) => out.push(id.stx.name.clone()),
    Pat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_pat_binding_names(&elem.target, out);
      }
      if let Some(rest) = &arr.stx.rest {
        collect_pat_binding_names(rest, out);
      }
    }
    Pat::Obj(obj) => {
      for prop in &obj.stx.properties {
        collect_pat_binding_names(&prop.stx.target, out);
      }
      if let Some(rest) = &obj.stx.rest {
        collect_pat_binding_names(rest, out);
      }
    }
    Pat::AssignTarget(_) => {}
  }
}

fn strip_namespace_body_stmt(
  ctx: &mut StripContext,
  stmt: Node<Stmt>,
  namespace_param: &str,
) -> Vec<Node<Stmt>> {
  let loc = stmt.loc;
  let assoc = stmt.assoc;
  match *stmt.stx {
    Stmt::ImportEqualsDecl(mut decl) if decl.stx.export => {
      if decl.stx.type_only {
        return vec![];
      }
      let name = decl.stx.name.clone();
      decl.stx.export = false;
      let Some(stmt) = lower_import_equals_decl(ctx, decl, loc, assoc, false) else {
        return vec![];
      };
      let mut out = Vec::new();
      out.push(stmt);
      out.extend(namespace_export_assignments(loc, namespace_param, &[name]));
      out
    }
    Stmt::VarDecl(mut decl) if decl.stx.export => {
      decl.stx.export = false;
      strip_var_decl(ctx, &mut decl.stx);
      let mut names = Vec::new();
      for declarator in &decl.stx.declarators {
        collect_pat_binding_names(&declarator.pattern.stx.pat, &mut names);
      }
      let mut out = Vec::with_capacity(1 + names.len());
      out.push(new_node(loc, assoc, Stmt::VarDecl(decl)));
      out.extend(namespace_export_assignments(loc, namespace_param, &names));
      out
    }
    Stmt::FunctionDecl(mut func_decl) if func_decl.stx.export => {
      func_decl.stx.export = false;
      func_decl.stx.export_default = false;
      if !strip_func(ctx, &mut func_decl.stx.function.stx) {
        return vec![];
      }
      let Some(name) = func_decl
        .stx
        .name
        .as_ref()
        .map(|name| name.stx.name.clone())
      else {
        unsupported_ts(ctx, loc, "exported functions in namespaces must have names");
        return vec![];
      };
      let mut out = Vec::new();
      out.push(new_node(loc, assoc, Stmt::FunctionDecl(func_decl)));
      out.extend(namespace_export_assignments(loc, namespace_param, &[name]));
      out
    }
    Stmt::ClassDecl(mut class_decl) if class_decl.stx.export => {
      if class_decl.stx.declare {
        return vec![];
      }
      class_decl.stx.export = false;
      class_decl.stx.export_default = false;
      let Some(name) = class_decl
        .stx
        .name
        .as_ref()
        .map(|name| name.stx.name.clone())
      else {
        unsupported_ts(ctx, loc, "exported classes in namespaces must have names");
        return vec![];
      };
      let mut out = Vec::new();
      if let Some(stmt) = strip_class_decl(ctx, class_decl, loc, assoc) {
        out.push(stmt);
        out.extend(namespace_export_assignments(loc, namespace_param, &[name]));
      }
      out
    }
    Stmt::EnumDecl(decl) if decl.stx.export => {
      strip_enum_decl(ctx, decl, loc, assoc, false, Some(namespace_param))
    }
    Stmt::NamespaceDecl(decl) if decl.stx.export => {
      strip_namespace_decl(ctx, decl, loc, assoc, false, Some(namespace_param))
    }
    Stmt::ModuleDecl(decl) if decl.stx.export => {
      strip_module_decl(ctx, decl, loc, assoc, false, Some(namespace_param))
    }
    // ES module exports do not make sense inside runtime namespaces.
    Stmt::ExportList(_) | Stmt::ExportDefaultExpr(_) => {
      unsupported_ts(
        ctx,
        loc,
        "export statements are not supported inside runtime namespaces",
      );
      vec![]
    }
    other => strip_stmt(
      ctx,
      Node {
        loc,
        assoc,
        stx: Box::new(other),
      },
      false,
    ),
  }
}

fn strip_namespace_body(
  ctx: &mut StripContext,
  body: NamespaceBody,
  namespace_param: &str,
) -> Vec<Node<Stmt>> {
  match body {
    NamespaceBody::Block(stmts) => {
      ctx
        .value_bindings_stack
        .push(collect_top_level_value_bindings(&stmts));
      let out = stmts
        .into_iter()
        .flat_map(|stmt| strip_namespace_body_stmt(ctx, stmt, namespace_param))
        .collect();
      ctx.value_bindings_stack.pop();
      out
    }
    NamespaceBody::Namespace(inner) => {
      let inner = *inner;
      let inner_loc = inner.loc;
      ctx.value_bindings_stack.push(HashSet::new());
      let out = strip_namespace_decl(
        ctx,
        inner,
        inner_loc,
        NodeAssocData::default(),
        false,
        Some(namespace_param),
      );
      ctx.value_bindings_stack.pop();
      out
    }
  }
}

fn strip_namespace_decl(
  ctx: &mut StripContext,
  decl: Node<NamespaceDecl>,
  loc: Loc,
  _assoc: NodeAssocData,
  is_top_level: bool,
  parent_namespace: Option<&str>,
) -> Vec<Node<Stmt>> {
  if decl.stx.declare {
    return vec![];
  }

  let namespace_name = decl.stx.name.clone();
  let name_is_binding_identifier = is_valid_binding_identifier(&namespace_name, ctx.top_level_mode);
  if parent_namespace.is_none() && !name_is_binding_identifier {
    let allow_top_level_export =
      is_top_level && decl.stx.export && matches!(ctx.top_level_mode, TopLevelMode::Module);
    if !allow_top_level_export {
      unsupported_ts(
        ctx,
        loc,
        format!("runtime namespace name `{namespace_name}` is not a valid JavaScript identifier"),
      );
      return vec![];
    }
  }
  let namespace_param_ident = if name_is_binding_identifier {
    namespace_name.clone()
  } else {
    ctx.runtime_namespace_param_ident(&namespace_name)
  };
  let binding_ident = if name_is_binding_identifier {
    namespace_name.clone()
  } else {
    namespace_param_ident.clone()
  };
  let has_value_binding = ctx.current_value_bindings().contains(&binding_ident);
  let mut out = Vec::new();

  let should_export_binding = parent_namespace.is_none()
    && is_top_level
    && matches!(ctx.top_level_mode, TopLevelMode::Module)
    && decl.stx.export
    && !ctx.top_level_module_exports.contains(&namespace_name)
    && ctx.emitted_export_var.insert(namespace_name.clone());

  if should_export_binding {
    if name_is_binding_identifier {
      if has_value_binding {
        out.push(export_binding_stmt(loc, namespace_name.clone()));
      }
    } else {
      out.push(export_binding_as_stmt(
        loc,
        binding_ident.clone(),
        namespace_name.clone(),
      ));
    }
  }
  let should_export_var = should_export_binding && name_is_binding_identifier && !has_value_binding;

  if let Some(namespace_param) = parent_namespace {
    if has_value_binding {
      out.push(ts_lower::member_assignment_stmt(
        loc,
        ts_lower::id(loc, namespace_param),
        ts_lower::MemberKey::Name(namespace_name.clone()),
        ts_lower::id(loc, binding_ident.clone()),
      ));
    }
  }

  if (name_is_binding_identifier || parent_namespace.is_none()) && !has_value_binding {
    out.push(ts_lower::var_decl_stmt(
      loc,
      binding_ident.clone(),
      None,
      should_export_var,
      VarDeclMode::Var,
    ));
    ctx
      .current_value_bindings_mut()
      .insert(binding_ident.clone());
  }

  let mut body = strip_namespace_body(ctx, decl.stx.body, &namespace_param_ident);
  if namespace_param_ident != namespace_name
    && !is_valid_identifier_reference(&namespace_name, ctx.top_level_mode)
  {
    let mut visitor = RewriteIdExprName {
      from: &namespace_name,
      to: &namespace_param_ident,
    };
    for stmt in body.iter_mut() {
      stmt.drive_mut(&mut visitor);
    }
  }
  let arg = namespace_iife_arg(
    loc,
    &namespace_param_ident,
    &namespace_name,
    parent_namespace,
    name_is_binding_identifier,
  );
  out.push(ts_lower::iife_stmt(loc, namespace_param_ident, arg, body));
  out
}

fn strip_module_decl(
  ctx: &mut StripContext,
  decl: Node<ModuleDecl>,
  loc: Loc,
  assoc: NodeAssocData,
  is_top_level: bool,
  parent_namespace: Option<&str>,
) -> Vec<Node<Stmt>> {
  if decl.stx.declare {
    return vec![];
  }
  let Some(body) = decl.stx.body else {
    // Ambient modules may omit bodies; they are type-only.
    return vec![];
  };
  let ModuleName::Identifier(name) = decl.stx.name else {
    // String modules are used for module augmentation and have no runtime
    // representation, even when not marked `declare`.
    return vec![];
  };

  let ns_decl = Node::new(
    decl.loc,
    NamespaceDecl {
      export: decl.stx.export,
      declare: false,
      name,
      body: NamespaceBody::Block(body),
    },
  );
  strip_namespace_decl(ctx, ns_decl, loc, assoc, is_top_level, parent_namespace)
}

fn strip_switch_branch(ctx: &mut StripContext, branch: Node<SwitchBranch>) -> Node<SwitchBranch> {
  let mut branch = branch;
  if let Some(case) = branch.stx.case.take() {
    branch.stx.case = Some(strip_expr(ctx, case));
  }
  strip_stmts(ctx, &mut branch.stx.body, false);
  branch
}

fn strip_catch(ctx: &mut StripContext, mut catch: Node<CatchBlock>) -> Node<CatchBlock> {
  catch.stx.type_annotation = None;
  if let Some(param) = catch.stx.parameter.as_mut() {
    let pat = take_pat(&mut param.stx.pat);
    param.stx.pat = strip_pat(ctx, pat);
  }
  strip_stmts(ctx, &mut catch.stx.body, false);
  catch
}

fn strip_for_body(ctx: &mut StripContext, body: &mut Node<ForBody>) {
  strip_stmts(ctx, &mut body.stx.body, false);
}

fn strip_block(ctx: &mut StripContext, block: Node<BlockStmt>) -> Node<BlockStmt> {
  let mut block = block;
  strip_stmts(ctx, &mut block.stx.body, false);
  block
}

fn strip_for_in_of_lhs(ctx: &mut StripContext, lhs: &mut ForInOfLhs) {
  match lhs {
    ForInOfLhs::Assign(pat) => {
      let owned = take_pat(pat);
      *pat = strip_pat(ctx, owned);
    }
    ForInOfLhs::Decl((_, pat)) => {
      let owned = take_pat(&mut pat.stx.pat);
      pat.stx.pat = strip_pat(ctx, owned);
    }
  }
}

fn strip_var_decl(ctx: &mut StripContext, decl: &mut VarDecl) {
  for declarator in decl.declarators.iter_mut() {
    strip_var_declarator(ctx, declarator);
  }
}

fn strip_var_declarator(ctx: &mut StripContext, decl: &mut VarDeclarator) {
  decl.type_annotation = None;
  decl.definite_assignment = false;
  let pat = take_pat(&mut decl.pattern.stx.pat);
  decl.pattern.stx.pat = strip_pat(ctx, pat);
  if let Some(init) = decl.initializer.take() {
    decl.initializer = Some(strip_expr(ctx, init));
  }
}

fn strip_func(ctx: &mut StripContext, func: &mut Func) -> bool {
  func.type_parameters = None;
  func.return_type = None;
  func.parameters.retain(|param| {
    !matches!(
      param.stx.pattern.stx.pat.stx.as_ref(),
      Pat::Id(id) if id.stx.name == "this"
    )
  });
  func
    .parameters
    .iter_mut()
    .for_each(|param| strip_param(ctx, param));
  match func.body.take() {
    Some(FuncBody::Block(body)) => {
      let mut block = body;
      ctx
        .value_bindings_stack
        .push(collect_top_level_value_bindings(&block));
      strip_stmts(ctx, &mut block, false);
      ctx.value_bindings_stack.pop();
      func.body = Some(FuncBody::Block(block));
      true
    }
    Some(FuncBody::Expression(expr)) => {
      func.body = Some(FuncBody::Expression(strip_expr(ctx, expr)));
      true
    }
    None => false,
  }
}

fn strip_param(ctx: &mut StripContext, param: &mut Node<ParamDecl>) {
  param.stx.optional = false;
  param.stx.accessibility = None;
  param.stx.readonly = false;
  param.stx.type_annotation = None;
  let pat = take_pat(&mut param.stx.pattern.stx.pat);
  param.stx.pattern.stx.pat = strip_pat(ctx, pat);
  if let Some(default) = param.stx.default_value.take() {
    param.stx.default_value = Some(strip_expr(ctx, default));
  }
  for decorator in &mut param.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
}

fn strip_pat(ctx: &mut StripContext, pat: Node<Pat>) -> Node<Pat> {
  let Node { loc, assoc, stx } = pat;
  match *stx {
    Pat::Arr(arr) => new_node(loc, assoc, Pat::Arr(strip_arr_pat(ctx, arr))),
    Pat::Obj(obj) => new_node(loc, assoc, Pat::Obj(strip_obj_pat(ctx, obj))),
    Pat::AssignTarget(expr) => new_node(loc, assoc, Pat::AssignTarget(strip_expr(ctx, expr))),
    Pat::Id(_) => Node { loc, assoc, stx },
  }
}

fn strip_arr_pat(ctx: &mut StripContext, pat: Node<ArrPat>) -> Node<ArrPat> {
  let mut pat = pat;
  for elem in pat.stx.elements.iter_mut() {
    if let Some(elem) = elem {
      let target = take_pat(&mut elem.target);
      elem.target = strip_pat(ctx, target);
      if let Some(default) = elem.default_value.take() {
        elem.default_value = Some(strip_expr(ctx, default));
      }
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let rest_pat = take_pat(rest);
    *rest = strip_pat(ctx, rest_pat);
  }
  pat
}

fn strip_obj_pat(ctx: &mut StripContext, pat: Node<ObjPat>) -> Node<ObjPat> {
  let mut pat = pat;
  for prop in pat.stx.properties.iter_mut() {
    let target = take_pat(&mut prop.stx.target);
    prop.stx.target = strip_pat(ctx, target);
    if let Some(default) = prop.stx.default_value.take() {
      prop.stx.default_value = Some(strip_expr(ctx, default));
    }
  }
  if let Some(rest) = pat.stx.rest.as_mut() {
    let rest_pat = take_pat(rest);
    *rest = strip_pat(ctx, rest_pat);
  }
  pat
}

fn strip_expr(ctx: &mut StripContext, expr: Node<Expr>) -> Node<Expr> {
  let loc = expr.loc;
  let assoc = expr.assoc;
  match *expr.stx {
    Expr::ArrowFunc(func) => {
      let mut func = func;
      strip_func(ctx, &mut func.stx.func.stx);
      new_node(loc, assoc, Expr::ArrowFunc(func))
    }
    Expr::Binary(mut bin) => {
      bin.stx.left = strip_expr(ctx, bin.stx.left);
      bin.stx.right = strip_expr(ctx, bin.stx.right);
      new_node(loc, assoc, Expr::Binary(bin))
    }
    Expr::Call(mut call) => {
      call.stx.callee = strip_expr(ctx, call.stx.callee);
      for arg in call.stx.arguments.iter_mut() {
        let value = take_expr(&mut arg.stx.value);
        arg.stx.value = strip_expr(ctx, value);
      }
      new_node(loc, assoc, Expr::Call(call))
    }
    Expr::Class(class) => new_node(loc, assoc, Expr::Class(strip_class_expr(ctx, class))),
    Expr::ComputedMember(mut member) => {
      member.stx.object = strip_expr(ctx, member.stx.object);
      member.stx.member = strip_expr(ctx, member.stx.member);
      new_node(loc, assoc, Expr::ComputedMember(member))
    }
    Expr::Cond(mut cond) => {
      cond.stx.test = strip_expr(ctx, cond.stx.test);
      cond.stx.consequent = strip_expr(ctx, cond.stx.consequent);
      cond.stx.alternate = strip_expr(ctx, cond.stx.alternate);
      new_node(loc, assoc, Expr::Cond(cond))
    }
    Expr::Func(mut func) => {
      strip_func(ctx, &mut func.stx.func.stx);
      new_node(loc, assoc, Expr::Func(func))
    }
    Expr::Id(_)
    | Expr::ImportMeta(_)
    | Expr::NewTarget(_)
    | Expr::Super(_)
    | Expr::This(_)
    | Expr::JsxName(_)
    | Expr::JsxText(_)
    | Expr::LitBool(_)
    | Expr::LitNull(_)
    | Expr::LitNum(_)
    | Expr::LitBigInt(_)
    | Expr::LitRegex(_)
    | Expr::LitStr(_)
    | Expr::IdPat(_)
    | Expr::JsxMember(_) => new_node(loc, assoc, *expr.stx),
    Expr::Import(mut import) => {
      import.stx.module = strip_expr(ctx, import.stx.module);
      if let Some(attrs) = import.stx.attributes.take() {
        import.stx.attributes = Some(strip_expr(ctx, attrs));
      }
      new_node(loc, assoc, Expr::Import(import))
    }
    Expr::Member(mut member) => {
      member.stx.left = strip_expr(ctx, member.stx.left);
      new_node(loc, assoc, Expr::Member(member))
    }
    Expr::TaggedTemplate(mut tagged) => {
      tagged.stx.function = strip_expr(ctx, tagged.stx.function);
      for part in tagged.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let inner = take_expr(expr);
          *expr = strip_expr(ctx, inner);
        }
      }
      new_node(loc, assoc, Expr::TaggedTemplate(tagged))
    }
    Expr::Unary(mut unary) => {
      unary.stx.argument = strip_expr(ctx, unary.stx.argument);
      new_node(loc, assoc, Expr::Unary(unary))
    }
    Expr::UnaryPostfix(mut unary) => {
      unary.stx.argument = strip_expr(ctx, unary.stx.argument);
      new_node(loc, assoc, Expr::UnaryPostfix(unary))
    }
    Expr::JsxElem(elem) => new_node(loc, assoc, Expr::JsxElem(strip_jsx_elem(ctx, elem))),
    Expr::JsxExprContainer(mut expr) => {
      expr.stx.value = strip_expr(ctx, expr.stx.value);
      new_node(loc, assoc, Expr::JsxExprContainer(expr))
    }
    Expr::JsxSpreadAttr(mut spread) => {
      spread.stx.value = strip_expr(ctx, spread.stx.value);
      new_node(loc, assoc, Expr::JsxSpreadAttr(spread))
    }
    Expr::LitArr(mut arr) => {
      for elem in arr.stx.elements.iter_mut() {
        if let LitArrElem::Single(expr) | LitArrElem::Rest(expr) = elem {
          let value = take_expr(expr);
          *expr = strip_expr(ctx, value);
        }
      }
      new_node(loc, assoc, Expr::LitArr(arr))
    }
    Expr::LitObj(mut obj) => {
      for member in obj.stx.members.iter_mut() {
        strip_obj_member(ctx, member);
      }
      new_node(loc, assoc, Expr::LitObj(obj))
    }
    Expr::LitTemplate(mut tpl) => {
      for part in tpl.stx.parts.iter_mut() {
        if let LitTemplatePart::Substitution(expr) = part {
          let inner = take_expr(expr);
          *expr = strip_expr(ctx, inner);
        }
      }
      new_node(loc, assoc, Expr::LitTemplate(tpl))
    }
    Expr::ArrPat(pat) => new_node(loc, assoc, Expr::ArrPat(strip_arr_pat(ctx, pat))),
    Expr::ObjPat(pat) => new_node(loc, assoc, Expr::ObjPat(strip_obj_pat(ctx, pat))),
    Expr::TypeAssertion(assert) => strip_expr(ctx, *assert.stx.expression),
    Expr::NonNullAssertion(assert) => strip_expr(ctx, *assert.stx.expression),
    Expr::SatisfiesExpr(assert) => strip_expr(ctx, *assert.stx.expression),
  }
}

fn strip_class_expr(ctx: &mut StripContext, class: Node<ClassExpr>) -> Node<ClassExpr> {
  let mut class = class;
  class.stx.type_parameters = None;
  class.stx.implements.clear();
  if let Some(extends) = class.stx.extends.take() {
    class.stx.extends = Some(strip_expr(ctx, extends));
  }
  for decorator in &mut class.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
  strip_class_members(ctx, &mut class.stx.members, class.stx.extends.is_some());
  class
}

fn void_0_expr(loc: Loc) -> Node<Expr> {
  Node::new(
    loc,
    Expr::Unary(Node::new(
      loc,
      UnaryExpr {
        operator: OperatorName::Void,
        argument: ts_lower::number(loc, 0.0),
      },
    )),
  )
}

fn boolean_expr(loc: Loc, value: bool) -> Node<Expr> {
  Node::new(loc, Expr::LitBool(Node::new(loc, LitBoolExpr { value })))
}

fn is_super_call(expr: &Node<Expr>) -> bool {
  matches!(
    expr.stx.as_ref(),
    Expr::Call(call) if matches!(call.stx.callee.stx.as_ref(), Expr::Super(_))
  )
}

enum SuperCallInsert {
  After(usize),
  AfterWithReturnThis { insert_at: usize, loc: Loc },
}

fn super_call_insert_after(stmts: &mut Vec<Node<Stmt>>) -> Option<SuperCallInsert> {
  for idx in 0..stmts.len() {
    let stmt = &mut stmts[idx];
    match stmt.stx.as_mut() {
      Stmt::Expr(expr_stmt) if is_super_call(&expr_stmt.stx.expr) => {
        return Some(SuperCallInsert::After(idx + 1));
      }
      Stmt::VarDecl(decl)
        if decl
          .stx
          .declarators
          .iter()
          .any(|declarator| declarator.initializer.as_ref().is_some_and(is_super_call)) =>
      {
        return Some(SuperCallInsert::After(idx + 1));
      }
      Stmt::Return(ret_stmt) => {
        let Some(value) = ret_stmt.stx.value.take() else {
          continue;
        };
        if is_super_call(&value) {
          let loc = stmt.loc;
          let assoc = std::mem::take(&mut stmt.assoc);
          let mut expr_stmt = ts_lower::expr_stmt(loc, value);
          expr_stmt.assoc = assoc;
          *stmt = expr_stmt;
          return Some(SuperCallInsert::AfterWithReturnThis {
            insert_at: idx + 1,
            loc,
          });
        }
        ret_stmt.stx.value = Some(value);
      }
      _ => {}
    }
  }
  None
}

fn directive_prologue_len(stmts: &[Node<Stmt>]) -> usize {
  let mut len = 0;
  for stmt in stmts {
    match stmt.stx.as_ref() {
      Stmt::Expr(expr_stmt) if matches!(expr_stmt.stx.expr.stx.as_ref(), Expr::LitStr(_)) => {
        len += 1;
      }
      _ => break,
    }
  }
  len
}

fn define_property_descriptor(loc: Loc, value: Node<Expr>) -> Node<Expr> {
  fn direct_key(loc: Loc, name: &str) -> ClassOrObjKey {
    ClassOrObjKey::Direct(Node::new(
      loc,
      ClassOrObjMemberDirectKey {
        key: name.to_string(),
        tt: TT::Identifier,
      },
    ))
  }

  fn prop_member(loc: Loc, name: &str, value: Node<Expr>) -> Node<ObjMember> {
    Node::new(
      loc,
      ObjMember {
        typ: ObjMemberType::Valued {
          key: direct_key(loc, name),
          val: ClassOrObjVal::Prop(Some(value)),
        },
      },
    )
  }

  Node::new(
    loc,
    Expr::LitObj(Node::new(
      loc,
      LitObjExpr {
        members: vec![
          prop_member(loc, "value", value),
          prop_member(loc, "enumerable", boolean_expr(loc, true)),
          prop_member(loc, "configurable", boolean_expr(loc, true)),
          prop_member(loc, "writable", boolean_expr(loc, true)),
        ],
      },
    )),
  )
}

fn define_property_stmt(loc: Loc, key: Node<Expr>, value: Node<Expr>) -> Node<Stmt> {
  let callee = Node::new(
    loc,
    Expr::Member(Node::new(
      loc,
      MemberExpr {
        optional_chaining: false,
        left: ts_lower::id(loc, "Object"),
        right: "defineProperty".to_string(),
      },
    )),
  );
  let call = Node::new(
    loc,
    Expr::Call(Node::new(
      loc,
      CallExpr {
        optional_chaining: false,
        callee,
        arguments: vec![
          Node::new(
            loc,
            CallArg {
              spread: false,
              value: Node::new(loc, Expr::This(Node::new(loc, ThisExpr {}))),
            },
          ),
          Node::new(
            loc,
            CallArg {
              spread: false,
              value: key,
            },
          ),
          Node::new(
            loc,
            CallArg {
              spread: false,
              value: define_property_descriptor(loc, value),
            },
          ),
        ],
      },
    )),
  );
  ts_lower::expr_stmt(loc, call)
}

fn class_field_init_stmt(
  ctx: &StripContext,
  loc: Loc,
  key: ClassOrObjKey,
  init: Option<Node<Expr>>,
) -> Node<Stmt> {
  let value = init.unwrap_or_else(|| void_0_expr(loc));
  if ctx.ts_erase_options.use_define_for_class_fields {
    let key_expr = match key {
      ClassOrObjKey::Direct(key) => ts_lower::string(loc, key.stx.key),
      ClassOrObjKey::Computed(expr) => expr,
    };
    define_property_stmt(loc, key_expr, value)
  } else {
    let member_key = match key {
      ClassOrObjKey::Direct(key) => ts_lower::MemberKey::Name(key.stx.key),
      ClassOrObjKey::Computed(expr) => ts_lower::MemberKey::Expr(expr),
    };
    ts_lower::member_assignment_stmt(
      loc,
      Node::new(loc, Expr::This(Node::new(loc, ThisExpr {}))),
      member_key,
      value,
    )
  }
}

fn strip_class_members(
  ctx: &mut StripContext,
  members: &mut Vec<Node<ClassMember>>,
  is_derived: bool,
) {
  fn return_this_stmt(loc: Loc) -> Node<Stmt> {
    let this_expr = Node::new(loc, Expr::This(Node::new(loc, ThisExpr {})));
    Node::new(
      loc,
      Stmt::Return(Node::new(
        loc,
        ReturnStmt {
          value: Some(this_expr),
        },
      )),
    )
  }

  fn is_param_prop_assignment(stmt: &Node<Stmt>) -> bool {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      return false;
    };
    let Expr::Binary(bin) = expr_stmt.stx.expr.stx.as_ref() else {
      return false;
    };
    if bin.stx.operator != OperatorName::Assignment {
      return false;
    }
    let Expr::ComputedMember(member) = bin.stx.left.stx.as_ref() else {
      return false;
    };
    if member.stx.optional_chaining {
      return false;
    }
    if !matches!(member.stx.object.stx.as_ref(), Expr::This(_)) {
      return false;
    }
    let Expr::LitStr(key) = member.stx.member.stx.as_ref() else {
      return false;
    };
    let Expr::Id(id) = bin.stx.right.stx.as_ref() else {
      return false;
    };
    key.stx.value == id.stx.name
  }

  fn count_param_prop_assignments(stmts: &[Node<Stmt>], start: usize) -> usize {
    let mut count = 0usize;
    for stmt in stmts.iter().skip(start) {
      if is_param_prop_assignment(stmt) {
        count += 1;
      } else {
        break;
      }
    }
    count
  }

  let mut new_members = Vec::with_capacity(members.len());
  let mut field_inits: Vec<Node<Stmt>> = Vec::new();
  for member in members.drain(..) {
    if let Some(stripped) = strip_class_member(ctx, member, is_derived) {
      if ctx.ts_erase_options.lower_class_fields
        && !stripped.stx.static_
        && stripped.stx.decorators.is_empty()
        && matches!(&stripped.stx.val, ClassOrObjVal::Prop(_))
      {
        let Node { loc, stx, .. } = stripped;
        let member = *stx;
        let ClassOrObjVal::Prop(init) = member.val else {
          unreachable!("matches! guard ensures ClassOrObjVal::Prop");
        };
        field_inits.push(class_field_init_stmt(ctx, loc, member.key, init));
        continue;
      }
      new_members.push(stripped);
    }
  }

  if ctx.ts_erase_options.lower_class_fields && !field_inits.is_empty() {
    let ctor_idx = new_members.iter().position(|member| {
      !member.stx.static_
        && matches!(
          &member.stx.key,
          ClassOrObjKey::Direct(key) if key.stx.key == "constructor"
        )
    });

    if let Some(idx) = ctor_idx {
      let member = new_members
        .get_mut(idx)
        .expect("constructor index should be valid");
      let ctor_loc = member.loc;
      if let ClassOrObjVal::Method(method) = &mut member.stx.val {
        if let Some(FuncBody::Block(stmts)) = method.stx.func.stx.body.as_mut() {
          let base_insert_at = if is_derived {
            match super_call_insert_after(stmts) {
              Some(SuperCallInsert::After(insert_at)) => insert_at,
              Some(SuperCallInsert::AfterWithReturnThis { insert_at, loc }) => {
                field_inits.push(return_this_stmt(loc));
                insert_at
              }
              None => {
                unsupported_ts(
                  ctx,
                  ctor_loc,
                  "instance class fields in derived constructors require a top-level `super(...)` call",
                );
                // Still insert at the end to keep lowering deterministic, even though we emit an
                // error diagnostic and the pipeline will abort.
                stmts.len()
              }
            }
          } else {
            directive_prologue_len(stmts)
          };
          let insert_at = if ctx.ts_erase_options.use_define_for_class_fields {
            base_insert_at
          } else {
            base_insert_at + count_param_prop_assignments(stmts, base_insert_at)
          };
          stmts.splice(insert_at..insert_at, field_inits);
        }
      }
    } else {
      let loc = field_inits
        .first()
        .map(|stmt| stmt.loc)
        .unwrap_or(Loc(0, 0));
      let mut body = Vec::new();
      if is_derived {
        body.push(ts_lower::expr_stmt(
          loc,
          Node::new(
            loc,
            Expr::Call(Node::new(
              loc,
              CallExpr {
                optional_chaining: false,
                callee: Node::new(loc, Expr::Super(Node::new(loc, SuperExpr {}))),
                arguments: vec![Node::new(
                  loc,
                  CallArg {
                    spread: true,
                    value: ts_lower::id(loc, "arguments"),
                  },
                )],
              },
            )),
          ),
        ));
      }
      body.extend(field_inits);
      let func = Func {
        arrow: false,
        async_: false,
        generator: false,
        type_parameters: None,
        parameters: Vec::new(),
        return_type: None,
        body: Some(FuncBody::Block(body)),
      };
      let ctor = ClassMember {
        decorators: Vec::new(),
        key: ClassOrObjKey::Direct(Node::new(
          loc,
          ClassOrObjMemberDirectKey {
            key: "constructor".to_string(),
            tt: TT::KeywordConstructor,
          },
        )),
        static_: false,
        abstract_: false,
        readonly: false,
        accessor: false,
        optional: false,
        override_: false,
        definite_assignment: false,
        accessibility: None,
        type_annotation: None,
        val: ClassOrObjVal::Method(Node::new(
          loc,
          parse_js::ast::class_or_object::ClassOrObjMethod {
            func: Node::new(loc, func),
          },
        )),
      };
      new_members.insert(0, Node::new(loc, ctor));
    }
  }
  *members = new_members;
}

fn strip_class_member(
  ctx: &mut StripContext,
  member: Node<ClassMember>,
  is_derived: bool,
) -> Option<Node<ClassMember>> {
  fn param_property_names(params: &[Node<ParamDecl>]) -> Vec<(String, Loc)> {
    let mut out = Vec::new();
    for param in params {
      if param.stx.accessibility.is_some() || param.stx.readonly {
        if let Pat::Id(id) = param.stx.pattern.stx.pat.stx.as_ref() {
          out.push((id.stx.name.clone(), param.loc));
        }
      }
    }
    out
  }

  fn constructor_param_property_assignments(props: Vec<(String, Loc)>) -> Vec<Node<Stmt>> {
    props
      .into_iter()
      .map(|(name, loc)| {
        ts_lower::member_assignment_stmt(
          loc,
          Node::new(loc, Expr::This(Node::new(loc, ThisExpr {}))),
          ts_lower::MemberKey::Name(name.clone()),
          ts_lower::id(loc, name),
        )
      })
      .collect()
  }

  fn return_this_stmt(loc: Loc) -> Node<Stmt> {
    let this_expr = Node::new(loc, Expr::This(Node::new(loc, ThisExpr {})));
    Node::new(
      loc,
      Stmt::Return(Node::new(
        loc,
        ReturnStmt {
          value: Some(this_expr),
        },
      )),
    )
  }

  let mut member = member;
  let is_constructor = !member.stx.static_
    && matches!(
      &member.stx.key,
      ClassOrObjKey::Direct(key) if key.stx.key == "constructor"
    );
  let mut ctor_param_props = None;
  match &mut member.stx.val {
    ClassOrObjVal::IndexSignature(_) => return None,
    ClassOrObjVal::Getter(get) => {
      if !strip_func(ctx, &mut get.stx.func.stx) {
        return None;
      }
    }
    ClassOrObjVal::Setter(set) => {
      if !strip_func(ctx, &mut set.stx.func.stx) {
        return None;
      }
    }
    ClassOrObjVal::Method(method) => {
      if is_constructor {
        ctor_param_props = Some(param_property_names(&method.stx.func.stx.parameters));
      }
      if !strip_func(ctx, &mut method.stx.func.stx) {
        return None;
      }
    }
    ClassOrObjVal::Prop(init) => {
      if let Some(init) = init {
        let value = take_expr(init);
        *init = strip_expr(ctx, value);
      }
    }
    ClassOrObjVal::StaticBlock(block) => strip_stmts(ctx, &mut block.stx.body, false),
  }

  if let Some(props) = ctor_param_props {
    if !props.is_empty() {
      if let ClassOrObjVal::Method(method) = &mut member.stx.val {
        if let Some(FuncBody::Block(stmts)) = method.stx.func.stx.body.as_mut() {
          let mut assignments = constructor_param_property_assignments(props);
          let insert_at = if is_derived {
            match super_call_insert_after(stmts) {
              Some(SuperCallInsert::After(insert_at)) => insert_at,
              Some(SuperCallInsert::AfterWithReturnThis { insert_at, loc }) => {
                assignments.push(return_this_stmt(loc));
                insert_at
              }
              None => {
                unsupported_ts(
                  ctx,
                  member.loc,
                  "parameter properties in derived constructors require a top-level `super(...)` call",
                );
                // Still insert at the end to keep lowering deterministic, even though we emit an
                // error diagnostic and the pipeline will abort.
                stmts.len()
              }
            }
          } else {
            directive_prologue_len(stmts)
          };
          stmts.splice(insert_at..insert_at, assignments);
        }
      }
    }
  }

  member.stx.type_annotation = None;
  member.stx.optional = false;
  member.stx.definite_assignment = false;
  member.stx.abstract_ = false;
  member.stx.readonly = false;
  member.stx.accessor = false;
  member.stx.override_ = false;
  member.stx.accessibility = None;
  match &mut member.stx.key {
    ClassOrObjKey::Computed(expr) => {
      let expr_node = take_expr(expr);
      *expr = strip_expr(ctx, expr_node);
    }
    ClassOrObjKey::Direct(_) => {}
  }
  for decorator in &mut member.stx.decorators {
    let expr = take_expr(&mut decorator.stx.expression);
    decorator.stx.expression = strip_expr(ctx, expr);
  }
  Some(member)
}

fn strip_obj_member(ctx: &mut StripContext, member: &mut Node<ObjMember>) {
  match &mut member.stx.typ {
    ObjMemberType::Valued { key, val } => {
      match key {
        ClassOrObjKey::Computed(expr) => {
          let expr_node = take_expr(expr);
          *expr = strip_expr(ctx, expr_node);
        }
        ClassOrObjKey::Direct(_) => {}
      }
      match val {
        ClassOrObjVal::Method(method) => {
          strip_func(ctx, &mut method.stx.func.stx);
        }
        ClassOrObjVal::Getter(get) => {
          strip_func(ctx, &mut get.stx.func.stx);
        }
        ClassOrObjVal::Setter(set) => {
          strip_func(ctx, &mut set.stx.func.stx);
        }
        ClassOrObjVal::Prop(init) => {
          if let Some(init) = init {
            let value = take_expr(init);
            *init = strip_expr(ctx, value);
          }
        }
        ClassOrObjVal::StaticBlock(block) => strip_stmts(ctx, &mut block.stx.body, false),
        ClassOrObjVal::IndexSignature(_) => {}
      }
    }
    ObjMemberType::Shorthand { .. } => {}
    ObjMemberType::Rest { val } => {
      let value = take_expr(val);
      *val = strip_expr(ctx, value);
    }
  }
}

fn strip_jsx_elem(ctx: &mut StripContext, elem: Node<JsxElem>) -> Node<JsxElem> {
  let mut elem = elem;
  for attr in elem.stx.attributes.iter_mut() {
    match attr {
      JsxAttr::Named { value, .. } => {
        if let Some(JsxAttrVal::Expression(expr)) = value {
          let inner = take_expr(&mut expr.stx.value);
          expr.stx.value = strip_expr(ctx, inner);
        } else if let Some(JsxAttrVal::Element(elem)) = value {
          let owned = take_jsx_elem(elem);
          *elem = strip_jsx_elem(ctx, owned);
        }
      }
      JsxAttr::Spread { value } => {
        let inner = take_expr(&mut value.stx.value);
        value.stx.value = strip_expr(ctx, inner);
      }
    }
  }
  for child in elem.stx.children.iter_mut() {
    match child {
      JsxElemChild::Element(elem) => {
        let owned = take_jsx_elem(elem);
        *elem = strip_jsx_elem(ctx, owned);
      }
      JsxElemChild::Expr(expr) => {
        let value = take_expr(&mut expr.stx.value);
        expr.stx.value = strip_expr(ctx, value);
      }
      JsxElemChild::Text(_) => {}
    }
  }
  elem
}

fn unsupported_ts(ctx: &mut StripContext, loc: Loc, message: impl Into<String>) {
  ctx.diagnostics.push(Diagnostic::error(
    ERR_TS_UNSUPPORTED,
    message.into(),
    Span {
      file: ctx.file,
      range: loc.to_diagnostics_range(),
    },
  ));
}
