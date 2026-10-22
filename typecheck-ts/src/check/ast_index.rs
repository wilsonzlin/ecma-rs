//! Span-keyed AST index for body checking.
use std::collections::{HashMap, HashSet};
use std::panic::panic_any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use diagnostics::{FileId, TextRange};
use parse_js::ast::class_or_object::{
  ClassMember, ClassOrObjKey, ClassOrObjVal, ClassStaticBlock, ObjMemberType,
};
use parse_js::ast::expr::jsx::{JsxAttr, JsxAttrVal, JsxElem, JsxElemChild};
use parse_js::ast::expr::pat::Pat as AstPat;
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::{NamespaceBody, NamespaceDecl};
use parse_js::ast::type_expr::TypeExpr;
use parse_js::token::TT;

use super::{is_empty_jsx_expr_placeholder, loc_to_range, span_for_stmt_list};

/// Span-keyed lookup index over one file's AST, borrowed for the duration of a
/// single body check. All node references borrow from the caller-owned parsed
/// AST (typically behind an `Arc` kept alive by the salsa `parse` memo), so the
/// index is entirely safe — no raw pointers, no manual `Send`/`Sync` claims.
pub struct AstIndex<'ast> {
  pub(crate) ast: &'ast Node<parse_js::ast::stx::TopLevel>,
  pub(crate) exprs: HashMap<TextRange, &'ast Node<AstExpr>>,
  pub(crate) pats: HashMap<TextRange, &'ast Node<AstPat>>,
  pub(crate) vars: HashMap<TextRange, VarInfo<'ast>>,
  pub(crate) class_field_initializers: HashMap<TextRange, ClassFieldInitializerInfo>,
  pub(crate) classes: Vec<ClassInfo<'ast>>,
  pub(crate) classes_by_name: HashMap<String, usize>,
  /// Class declaration / expression span → index into [`Self::classes`].
  pub(crate) classes_by_span: HashMap<TextRange, usize>,
  pub(crate) functions: Vec<FunctionInfo<'ast>>,
  pub(crate) class_static_blocks: Vec<ClassStaticBlockInfo<'ast>>,
  pub(crate) class_field_param_props: HashMap<TextRange, Vec<String>>,
  /// Class method/ctor/accessor `Func.loc` span → owning class + static/ctor flags
  /// (for contextual `this` typing and TS2715 class-init flow).
  pub(crate) class_member_func_by_span: HashMap<TextRange, ClassMemberFuncInfo>,
  /// Nesting stack while indexing (lexical parent for nested class expressions /
  /// declarations). Cleared when indexing finishes; not part of the public
  /// query surface.
  class_nesting: Vec<usize>,
  /// True when any `async *` method / function appears (tsc may require
  /// `AsyncIterableIterator` → TS2318 under older lib targets).
  pub(crate) uses_async_generator: bool,
}

#[derive(Clone, Copy)]
pub(crate) struct VarInfo<'ast> {
  pub(crate) initializer: Option<&'ast Node<AstExpr>>,
  /// Residual AST annotation. Body checking prefers HIR
  /// `VarDeclarator.type_annotation` (`TypeExprId`) when type arenas are
  /// present (including named refs / `typeof` / function / object / mapped /
  /// conditional via body `TypeResolver`). Type assertions / `satisfies`
  /// similarly prefer HIR `TypeExprId` on the expression (see
  /// `hir_body_assertions` tests). This field remains for `import(...)` /
  /// `typeof import(...)`, missing arenas, and JSDoc-only declarations.
  pub(crate) type_annotation: Option<&'ast Node<parse_js::ast::type_expr::TypeExpr>>,
  pub(crate) mode: VarDeclMode,
  /// Span of the enclosing `var`/`let`/`const` statement (for leading JSDoc).
  pub(crate) decl_loc: parse_js::loc::Loc,
}

/// Kind of a private-identifier class element (for TS2300 / TS2804 uniqueness).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PrivateMemberKind {
  Field,
  Method,
  Getter,
  Setter,
}

/// One private-identifier declaration site in a class body (declaration order).
#[derive(Clone, Debug)]
pub(crate) struct PrivateNameDecl {
  pub(crate) name: String,
  pub(crate) key_range: TextRange,
  /// Start of the class member (first modifier / decorator / key). Used to
  /// underline illegal modifiers the way tsc does (keyword, not `#name`).
  pub(crate) member_start: u32,
  pub(crate) is_static: bool,
  pub(crate) kind: PrivateMemberKind,
  /// `public` / `private` / `protected` present (illegal with `#`, TS18010).
  pub(crate) accessibility_keyword: Option<&'static str>,
  /// `declare` present (illegal with `#`, TS18019; also TS1031 on non-fields).
  pub(crate) declare_: bool,
  /// `abstract` present (illegal with `#`, TS18019).
  pub(crate) abstract_: bool,
  /// `readonly` present (illegal on methods/accessors, TS1024).
  pub(crate) readonly: bool,
  /// `async` on a getter/setter (illegal, TS1042).
  pub(crate) async_on_accessor: bool,
  /// `async` appeared before `static` in source (TS1029).
  pub(crate) async_before_static: bool,
}

/// Kind of a class value-namespace member tracked for TS2393 / TS2717.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClassValueMemberKind {
  Field,
  Method,
}

/// One field/method declaration site in a class body (declaration order).
///
/// Used for duplicate method implementations (TS2393) and subsequent property
/// type identity (TS2717). Accessors are intentionally omitted (getter+setter
/// pairs are allowed; same-kind accessor duplicates are handled elsewhere).
#[derive(Clone, Debug)]
pub(crate) struct ClassValueMemberDecl<'ast> {
  pub(crate) name: String,
  pub(crate) key_range: TextRange,
  pub(crate) is_static: bool,
  pub(crate) kind: ClassValueMemberKind,
  /// Method only: whether the declaration has an implementation body.
  pub(crate) has_body: bool,
  pub(crate) type_annotation: Option<&'ast Node<TypeExpr>>,
  pub(crate) initializer: Option<&'ast Node<AstExpr>>,
  pub(crate) func: Option<&'ast Node<Func>>,
}

#[derive(Clone, Debug)]
pub(crate) struct ClassInfo<'ast> {
  pub(crate) name: Option<String>,
  pub(crate) extends: Option<String>,
  /// Full class declaration / expression span (for enclosing-class lookup).
  pub(crate) span: TextRange,
  /// Lexically enclosing class when this class is nested (for TS18014 shadowing).
  pub(crate) parent_class_index: Option<usize>,
  /// Class type-parameter names (`class C<T, U>`) for heritage Instantiation
  /// checking (`extends Parent<T>` in the class body HIR).
  pub(crate) type_param_names: Vec<String>,
  /// `declare class` / ambient class body — skip TS2564.
  pub(crate) declare: bool,
  pub(crate) instance_fields: Vec<ClassFieldDecl<'ast>>,
  pub(crate) static_fields: Vec<ClassFieldDecl<'ast>>,
  pub(crate) instance_param_props: Vec<String>,
  pub(crate) instance_param_props_private: HashSet<String>,
  pub(crate) instance_member_names: HashSet<String>,
  /// Abstract instance fields/accessors (not methods) declared on this class.
  pub(crate) abstract_instance_props: HashSet<String>,
  /// Concrete (non-abstract) instance fields/accessors declared on this class.
  pub(crate) concrete_instance_props: HashSet<String>,
  /// Instance getter names (including private `#foo`), for TS2540 / TS2806.
  pub(crate) instance_getters: HashSet<String>,
  /// Instance setter names (including private `#foo`).
  pub(crate) instance_setters: HashSet<String>,
  /// Static getter names (including private `#foo`), for TS2540 / TS2806.
  pub(crate) static_getters: HashSet<String>,
  /// Static setter names (including private `#foo`).
  pub(crate) static_setters: HashSet<String>,
  /// Instance getter function nodes (for setter-param contextual typing).
  pub(crate) instance_getter_funcs: HashMap<String, &'ast Node<Func>>,
  /// Static getter function nodes (for setter-param contextual typing).
  pub(crate) static_getter_funcs: HashMap<String, &'ast Node<Func>>,
  /// Private method names (`#m`, instance or static) for TS2803.
  pub(crate) private_methods: HashSet<String>,
  /// Instance method names (including private `#m`) for synthesizing `this` types.
  pub(crate) instance_methods: HashSet<String>,
  /// Static method names (including private `#m`) for synthesizing constructor types.
  pub(crate) static_methods: HashSet<String>,
  /// Private-identifier members in source order (TS2300 / TS2804 uniqueness).
  pub(crate) private_name_decls: Vec<PrivateNameDecl>,
  /// Field/method members in source order (TS2393 / TS2717).
  pub(crate) value_member_decls: Vec<ClassValueMemberDecl<'ast>>,
  /// `abstract prop = expr` sites for TS1267 (name + property-name span).
  pub(crate) abstract_props_with_initializer: Vec<(String, TextRange)>,
  /// Instance constructor function, if any (for definite-assignment analysis).
  pub(crate) constructor: Option<&'ast Node<Func>>,
  /// Span of the `constructor` keyword / name (TS2376 primary).
  pub(crate) constructor_key_range: Option<TextRange>,
}

#[derive(Clone, Debug)]
pub(crate) struct ClassFieldDecl<'ast> {
  pub(crate) name: String,
  pub(crate) member_index: usize,
  pub(crate) optional: bool,
  pub(crate) has_initializer: bool,
  pub(crate) definite_assignment: bool,
  pub(crate) abstract_: bool,
  /// TypeScript `declare` field — exempt from SPI (TS2564).
  pub(crate) declare_: bool,
  /// Whether tsc would subject this name to SPI (identifier / private / keyword;
  /// not string/numeric literal keys).
  pub(crate) spi_checked_name: bool,
  pub(crate) is_private: bool,
  pub(crate) key_range: TextRange,
  pub(crate) type_annotation: Option<&'ast Node<TypeExpr>>,
}

#[derive(Clone, Debug)]
pub(crate) struct ClassFieldInitializerInfo {
  pub(crate) class_index: usize,
  pub(crate) member_index: usize,
  pub(crate) is_static: bool,
  /// Property key as accessed at runtime (`#foo`, `#bar` for `["#bar"]`, …).
  pub(crate) prop_name: String,
  /// Display name for diagnostics (`#foo`, `["#bar"]`).
  pub(crate) display_name: String,
  /// Span of the member name for TS7022/TS7008 (`#foo` / `["#bar"]`).
  pub(crate) key_range: TextRange,
}

#[derive(Clone, Debug)]
pub(crate) struct ClassMemberFuncInfo {
  pub(crate) class_index: usize,
  pub(crate) is_static: bool,
  pub(crate) is_constructor: bool,
  /// Accessor property name (`foo` / `#foo`) when this member is get/set.
  pub(crate) accessor_name: Option<String>,
  /// True when this member is a `set` accessor (paired getter supplies
  /// contextual typing for the setter parameter).
  pub(crate) is_setter: bool,
}

#[derive(Clone, Copy)]
pub(crate) struct FunctionInfo<'ast> {
  pub(crate) func_span: TextRange,
  pub(crate) func: &'ast Node<Func>,
  /// Best source offset for a leading JSDoc block. For function *declarations*,
  /// `Func.loc` starts at the parameter list (after `function name`), so this
  /// carries the outer `FunctionDecl`/`function` keyword loc instead.
  pub(crate) jsdoc_loc: parse_js::loc::Loc,
}

#[derive(Clone, Copy)]
pub(crate) struct ClassStaticBlockInfo<'ast> {
  pub(crate) span: TextRange,
  pub(crate) block: &'ast Node<ClassStaticBlock>,
  pub(crate) class_index: usize,
  pub(crate) member_index: usize,
}

impl<'ast> AstIndex<'ast> {
  pub fn new(
    ast: &'ast Node<parse_js::ast::stx::TopLevel>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) -> Self {
    let mut index = AstIndex {
      ast,
      exprs: HashMap::new(),
      pats: HashMap::new(),
      vars: HashMap::new(),
      class_field_initializers: HashMap::new(),
      classes: Vec::new(),
      classes_by_name: HashMap::new(),
      classes_by_span: HashMap::new(),
      functions: Vec::new(),
      class_static_blocks: Vec::new(),
      class_field_param_props: HashMap::new(),
      class_member_func_by_span: HashMap::new(),
      class_nesting: Vec::new(),
      uses_async_generator: false,
    };
    index.index_top_level(file, cancelled);
    index.class_nesting.clear();
    index
  }

  pub(crate) fn ast(&self) -> &'ast Node<parse_js::ast::stx::TopLevel> {
    self.ast
  }

  fn check_cancelled(cancelled: Option<&Arc<AtomicBool>>) {
    if let Some(flag) = cancelled {
      if flag.load(Ordering::Relaxed) {
        panic_any(crate::FatalError::Cancelled);
      }
    }
  }

  fn index_top_level(&mut self, file: FileId, cancelled: Option<&Arc<AtomicBool>>) {
    let ast = self.ast;
    for (idx, stmt) in ast.stx.body.iter().enumerate() {
      if idx % 1024 == 0 {
        Self::check_cancelled(cancelled);
      }
      self.index_stmt(stmt, file, cancelled);
    }
  }

  fn index_stmt(
    &mut self,
    stmt: &'ast Node<Stmt>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::Expr(expr_stmt) => {
        self.index_expr(&expr_stmt.stx.expr, file, cancelled);
      }
      Stmt::Return(ret) => {
        if let Some(value) = &ret.stx.value {
          self.index_expr(value, file, cancelled);
        }
      }
      Stmt::Block(block) => self.index_stmt_list(&block.stx.body, file, cancelled),
      Stmt::If(if_stmt) => {
        self.index_expr(&if_stmt.stx.test, file, cancelled);
        self.index_stmt(&if_stmt.stx.consequent, file, cancelled);
        if let Some(alt) = &if_stmt.stx.alternate {
          self.index_stmt(alt, file, cancelled);
        }
      }
      Stmt::While(while_stmt) => {
        self.index_expr(&while_stmt.stx.condition, file, cancelled);
        self.index_stmt(&while_stmt.stx.body, file, cancelled);
      }
      Stmt::DoWhile(do_while) => {
        self.index_expr(&do_while.stx.condition, file, cancelled);
        self.index_stmt(&do_while.stx.body, file, cancelled);
      }
      Stmt::ForTriple(for_stmt) => {
        use parse_js::ast::stmt::ForTripleStmtInit;
        match &for_stmt.stx.init {
          ForTripleStmtInit::Expr(expr) => self.index_expr(expr, file, cancelled),
          ForTripleStmtInit::Decl(decl) => self.index_var_decl(decl, file, cancelled),
          ForTripleStmtInit::None => {}
        }
        if let Some(cond) = &for_stmt.stx.cond {
          self.index_expr(cond, file, cancelled);
        }
        if let Some(post) = &for_stmt.stx.post {
          self.index_expr(post, file, cancelled);
        }
        self.index_stmt_list(&for_stmt.stx.body.stx.body, file, cancelled);
      }
      Stmt::ForIn(for_in) => {
        use parse_js::ast::stmt::ForInOfLhs;
        match &for_in.stx.lhs {
          ForInOfLhs::Assign(pat) => self.index_pat(pat, file, cancelled),
          ForInOfLhs::Decl((_, pat_decl)) => self.index_pat(&pat_decl.stx.pat, file, cancelled),
        }
        self.index_expr(&for_in.stx.rhs, file, cancelled);
        self.index_stmt_list(&for_in.stx.body.stx.body, file, cancelled);
      }
      Stmt::ForOf(for_of) => {
        use parse_js::ast::stmt::ForInOfLhs;
        match &for_of.stx.lhs {
          ForInOfLhs::Assign(pat) => self.index_pat(pat, file, cancelled),
          ForInOfLhs::Decl((_, pat_decl)) => self.index_pat(&pat_decl.stx.pat, file, cancelled),
        }
        self.index_expr(&for_of.stx.rhs, file, cancelled);
        self.index_stmt_list(&for_of.stx.body.stx.body, file, cancelled);
      }
      Stmt::Switch(sw) => {
        self.index_expr(&sw.stx.test, file, cancelled);
        for branch in sw.stx.branches.iter() {
          if let Some(case) = &branch.stx.case {
            self.index_expr(case, file, cancelled);
          }
          for stmt in branch.stx.body.iter() {
            self.index_stmt(stmt, file, cancelled);
          }
        }
      }
      Stmt::Try(tr) => {
        self.index_stmt_list(&tr.stx.wrapped.stx.body, file, cancelled);
        if let Some(catch) = &tr.stx.catch {
          if let Some(param) = &catch.stx.parameter {
            self.index_pat(&param.stx.pat, file, cancelled);
          }
          self.index_stmt_list(&catch.stx.body, file, cancelled);
        }
        if let Some(finally) = &tr.stx.finally {
          self.index_stmt_list(&finally.stx.body, file, cancelled);
        }
      }
      Stmt::Throw(th) => self.index_expr(&th.stx.value, file, cancelled),
      Stmt::Label(label) => self.index_stmt(&label.stx.statement, file, cancelled),
      Stmt::With(w) => {
        self.index_expr(&w.stx.object, file, cancelled);
        self.index_stmt(&w.stx.body, file, cancelled);
      }
      Stmt::VarDecl(decl) => {
        self.index_var_decl(decl, file, cancelled);
      }
      Stmt::FunctionDecl(func) => {
        // `Func.loc` starts at `(…)` for decls; use the decl node for JSDoc.
        self.index_function(&func.stx.function, file, cancelled, Some(func.loc));
      }
      Stmt::ClassDecl(class_decl) => {
        let class_name = class_decl
          .stx
          .name
          .as_ref()
          .map(|name| name.stx.name.clone());
        let extends_name =
          class_decl
            .stx
            .extends
            .as_ref()
            .and_then(|expr| match expr.stx.as_ref() {
              AstExpr::Id(id) => Some(id.stx.name.clone()),
              AstExpr::Instantiation(inst) => match inst.stx.expression.stx.as_ref() {
                AstExpr::Id(id) => Some(id.stx.name.clone()),
                _ => None,
              },
              _ => None,
            });
        let class_span = loc_to_range(file, class_decl.loc);
        let type_param_names = class_decl
          .stx
          .type_parameters
          .as_ref()
          .map(|params| params.iter().map(|p| p.stx.name.clone()).collect())
          .unwrap_or_default();
        let class_index = self.register_class(
          class_name,
          extends_name,
          class_decl.stx.declare,
          class_span,
          type_param_names,
        );
        for decorator in class_decl.stx.decorators.iter() {
          self.index_expr(&decorator.stx.expression, file, cancelled);
        }
        if let Some(extends) = class_decl.stx.extends.as_ref() {
          self.index_expr(extends, file, cancelled);
        }
        for implements in class_decl.stx.implements.iter() {
          self.index_expr(implements, file, cancelled);
        }
        self.index_class_members_in_class(&class_decl.stx.members, class_index, file, cancelled);
      }
      Stmt::NamespaceDecl(ns) => self.index_namespace(ns, file, cancelled),
      Stmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          self.index_stmt_list(body, file, cancelled);
        }
      }
      Stmt::GlobalDecl(global) => {
        self.index_stmt_list(&global.stx.body, file, cancelled);
      }
      _ => {}
    }
  }

  fn index_stmt_list(
    &mut self,
    stmts: &'ast [Node<Stmt>],
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    for (idx, stmt) in stmts.iter().enumerate() {
      if idx % 1024 == 0 {
        Self::check_cancelled(cancelled);
      }
      self.index_stmt(stmt, file, cancelled);
    }
  }

  fn index_namespace(
    &mut self,
    ns: &'ast Node<NamespaceDecl>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    match &ns.stx.body {
      NamespaceBody::Block(stmts) => self.index_stmt_list(stmts, file, cancelled),
      NamespaceBody::Namespace(inner) => self.index_namespace(inner, file, cancelled),
    }
  }

  fn index_var_decl(
    &mut self,
    decl: &'ast Node<VarDecl>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    for declarator in decl.stx.declarators.iter() {
      let pat_span = loc_to_range(file, declarator.pattern.loc);
      self.pats.insert(pat_span, &declarator.pattern.stx.pat);
      self.vars.insert(
        pat_span,
        VarInfo {
          initializer: declarator.initializer.as_ref(),
          type_annotation: declarator.type_annotation.as_ref(),
          mode: decl.stx.mode,
          decl_loc: decl.loc,
        },
      );
      self.index_pat(&declarator.pattern.stx.pat, file, cancelled);
      if let Some(init) = &declarator.initializer {
        self.index_expr(init, file, cancelled);
      }
    }
  }

  fn index_function(
    &mut self,
    func: &'ast Node<Func>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
    jsdoc_loc: Option<parse_js::loc::Loc>,
  ) {
    if func.stx.async_ && func.stx.generator {
      self.uses_async_generator = true;
    }
    let func_span = loc_to_range(file, func.loc);
    if func.stx.body.is_some() {
      self.functions.push(FunctionInfo {
        func_span,
        func,
        jsdoc_loc: jsdoc_loc.unwrap_or(func.loc),
      });
    }

    for param in func.stx.parameters.iter() {
      let pat_span = loc_to_range(file, param.stx.pattern.loc);
      self.pats.insert(pat_span, &param.stx.pattern.stx.pat);
      self.index_pat(&param.stx.pattern.stx.pat, file, cancelled);
      if let Some(default) = &param.stx.default_value {
        self.index_expr(default, file, cancelled);
      }
    }

    if let Some(body) = &func.stx.body {
      match body {
        FuncBody::Block(block) => self.index_stmt_list(block, file, cancelled),
        FuncBody::Expression(expr) => self.index_expr(expr, file, cancelled),
      }
    }
  }

  fn index_jsx_elem(
    &mut self,
    elem: &'ast Node<JsxElem>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    for (idx, attr) in elem.stx.attributes.iter().enumerate() {
      if idx % 256 == 0 {
        Self::check_cancelled(cancelled);
      }
      match attr {
        JsxAttr::Named { value, .. } => match value {
          Some(JsxAttrVal::Expression(container)) => {
            if !is_empty_jsx_expr_placeholder(&container.stx.value) {
              self.index_expr(&container.stx.value, file, cancelled);
            }
          }
          Some(JsxAttrVal::Element(child)) => self.index_jsx_elem(child, file, cancelled),
          Some(JsxAttrVal::Text(_)) | None => {}
        },
        JsxAttr::Spread { value } => {
          if !is_empty_jsx_expr_placeholder(&value.stx.value) {
            self.index_expr(&value.stx.value, file, cancelled);
          }
        }
      }
    }

    for (idx, child) in elem.stx.children.iter().enumerate() {
      if idx % 256 == 0 {
        Self::check_cancelled(cancelled);
      }
      match child {
        JsxElemChild::Element(child_elem) => self.index_jsx_elem(child_elem, file, cancelled),
        JsxElemChild::Expr(container) => {
          if !is_empty_jsx_expr_placeholder(&container.stx.value) {
            self.index_expr(&container.stx.value, file, cancelled);
          }
        }
        JsxElemChild::Text(_) => {}
      }
    }
  }

  fn index_expr(
    &mut self,
    expr: &'ast Node<AstExpr>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    let span = loc_to_range(file, expr.loc);
    self.exprs.insert(span, expr);
    match expr.stx.as_ref() {
      AstExpr::Binary(bin) => {
        self.index_expr(&bin.stx.left, file, cancelled);
        self.index_expr(&bin.stx.right, file, cancelled);
      }
      AstExpr::Call(call) => {
        self.index_expr(&call.stx.callee, file, cancelled);
        for arg in call.stx.arguments.iter() {
          self.index_expr(&arg.stx.value, file, cancelled);
        }
      }
      AstExpr::Instantiation(inst) => {
        self.index_expr(&inst.stx.expression, file, cancelled);
      }
      AstExpr::Member(mem) => {
        self.index_expr(&mem.stx.left, file, cancelled);
      }
      AstExpr::ComputedMember(mem) => {
        self.index_expr(&mem.stx.object, file, cancelled);
        self.index_expr(&mem.stx.member, file, cancelled);
      }
      AstExpr::Cond(cond) => {
        self.index_expr(&cond.stx.test, file, cancelled);
        self.index_expr(&cond.stx.consequent, file, cancelled);
        self.index_expr(&cond.stx.alternate, file, cancelled);
      }
      AstExpr::Import(import) => {
        self.index_expr(&import.stx.module, file, cancelled);
        if let Some(attributes) = import.stx.attributes.as_ref() {
          self.index_expr(attributes, file, cancelled);
        }
      }
      AstExpr::Unary(un) => {
        self.index_expr(&un.stx.argument, file, cancelled);
      }
      AstExpr::UnaryPostfix(post) => {
        self.index_expr(&post.stx.argument, file, cancelled);
      }
      AstExpr::TaggedTemplate(tagged) => {
        self.index_expr(&tagged.stx.function, file, cancelled);
        for part in tagged.stx.parts.iter() {
          match part {
            parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) => {
              self.index_expr(expr, file, cancelled)
            }
            parse_js::ast::expr::lit::LitTemplatePart::String(_) => {}
          }
        }
      }
      AstExpr::LitArr(arr) => {
        for elem in arr.stx.elements.iter() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(v)
            | parse_js::ast::expr::lit::LitArrElem::Rest(v) => self.index_expr(v, file, cancelled),
            parse_js::ast::expr::lit::LitArrElem::Empty => {}
          }
        }
      }
      AstExpr::LitObj(obj) => {
        for member in obj.stx.members.iter() {
          match &member.stx.typ {
            ObjMemberType::Valued { key, val } => {
              if let ClassOrObjKey::Computed(expr) = key {
                self.index_expr(expr, file, cancelled);
              }
              match val {
                ClassOrObjVal::Getter(getter) => {
                  self.index_function(&getter.stx.func, file, cancelled, Some(member.loc))
                }
                ClassOrObjVal::Setter(setter) => {
                  self.index_function(&setter.stx.func, file, cancelled, Some(member.loc))
                }
                ClassOrObjVal::Method(method) => {
                  self.index_function(&method.stx.func, file, cancelled, Some(member.loc))
                }
                ClassOrObjVal::Prop(Some(expr)) => self.index_expr(expr, file, cancelled),
                ClassOrObjVal::StaticBlock(block) => {
                  self.index_stmt_list(&block.stx.body, file, cancelled)
                }
                ClassOrObjVal::Prop(None) | ClassOrObjVal::IndexSignature(_) => {}
              }
            }
            ObjMemberType::Rest { val } => self.index_expr(val, file, cancelled),
            ObjMemberType::Shorthand { .. } => {}
          }
        }
      }
      AstExpr::LitTemplate(template) => {
        for part in template.stx.parts.iter() {
          match part {
            parse_js::ast::expr::lit::LitTemplatePart::Substitution(expr) => {
              self.index_expr(expr, file, cancelled)
            }
            parse_js::ast::expr::lit::LitTemplatePart::String(_) => {}
          }
        }
      }
      AstExpr::Class(class_expr) => {
        let class_name = class_expr
          .stx
          .name
          .as_ref()
          .map(|name| name.stx.name.clone());
        let extends_name =
          class_expr
            .stx
            .extends
            .as_ref()
            .and_then(|expr| match expr.stx.as_ref() {
              AstExpr::Id(id) => Some(id.stx.name.clone()),
              AstExpr::Instantiation(inst) => match inst.stx.expression.stx.as_ref() {
                AstExpr::Id(id) => Some(id.stx.name.clone()),
                _ => None,
              },
              _ => None,
            });
        let class_span = loc_to_range(file, class_expr.loc);
        let type_param_names = class_expr
          .stx
          .type_parameters
          .as_ref()
          .map(|params| params.iter().map(|p| p.stx.name.clone()).collect())
          .unwrap_or_default();
        let class_index = self.register_class(
          class_name,
          extends_name,
          false,
          class_span,
          type_param_names,
        );
        for decorator in class_expr.stx.decorators.iter() {
          self.index_expr(&decorator.stx.expression, file, cancelled);
        }
        if let Some(extends) = class_expr.stx.extends.as_ref() {
          self.index_expr(extends, file, cancelled);
        }
        self.index_class_members_in_class(&class_expr.stx.members, class_index, file, cancelled);
      }
      // Expression node loc includes `function` / arrow head for leading JSDoc.
      AstExpr::Func(func) => self.index_function(&func.stx.func, file, cancelled, Some(func.loc)),
      AstExpr::ArrowFunc(func) => {
        self.index_function(&func.stx.func, file, cancelled, Some(func.loc))
      }
      AstExpr::JsxElem(elem) => self.index_jsx_elem(elem, file, cancelled),
      AstExpr::JsxExprContainer(container) => {
        if !is_empty_jsx_expr_placeholder(&container.stx.value) {
          self.index_expr(&container.stx.value, file, cancelled);
        }
      }
      AstExpr::JsxSpreadAttr(spread) => {
        if !is_empty_jsx_expr_placeholder(&spread.stx.value) {
          self.index_expr(&spread.stx.value, file, cancelled);
        }
      }
      AstExpr::TypeAssertion(assert) => self.index_expr(&assert.stx.expression, file, cancelled),
      AstExpr::NonNullAssertion(assert) => self.index_expr(&assert.stx.expression, file, cancelled),
      AstExpr::SatisfiesExpr(expr) => self.index_expr(&expr.stx.expression, file, cancelled),
      AstExpr::Id(..)
      | AstExpr::LitNull(..)
      | AstExpr::LitStr(..)
      | AstExpr::LitNum(..)
      | AstExpr::LitBool(..)
      | AstExpr::LitBigInt(..)
      | AstExpr::This(..)
      | AstExpr::Super(..)
      | AstExpr::IdPat(..)
      | AstExpr::ArrPat(..)
      | AstExpr::ObjPat(..)
      | AstExpr::ImportMeta(..)
      | AstExpr::JsxMember(..)
      | AstExpr::JsxName(..)
      | AstExpr::JsxText(..)
      | AstExpr::LitRegex(..)
      | AstExpr::NewTarget(..) => {}
    }
  }

  fn register_class(
    &mut self,
    name: Option<String>,
    extends: Option<String>,
    declare: bool,
    span: TextRange,
    type_param_names: Vec<String>,
  ) -> usize {
    let index = self.classes.len();
    if let Some(name) = name.as_ref() {
      self.classes_by_name.entry(name.clone()).or_insert(index);
    }
    self.classes_by_span.insert(span, index);
    let parent_class_index = self.class_nesting.last().copied();
    self.classes.push(ClassInfo {
      name,
      extends,
      span,
      parent_class_index,
      type_param_names,
      declare,
      instance_fields: Vec::new(),
      static_fields: Vec::new(),
      instance_param_props: Vec::new(),
      instance_param_props_private: HashSet::new(),
      instance_member_names: HashSet::new(),
      abstract_instance_props: HashSet::new(),
      concrete_instance_props: HashSet::new(),
      instance_getters: HashSet::new(),
      instance_setters: HashSet::new(),
      static_getters: HashSet::new(),
      static_setters: HashSet::new(),
      instance_getter_funcs: HashMap::new(),
      static_getter_funcs: HashMap::new(),
      private_methods: HashSet::new(),
      instance_methods: HashSet::new(),
      static_methods: HashSet::new(),
      private_name_decls: Vec::new(),
      value_member_decls: Vec::new(),
      abstract_props_with_initializer: Vec::new(),
      constructor: None,
      constructor_key_range: None,
    });
    index
  }

  /// Primary span for a class member key, matching tsc underlines.
  fn member_key_range(
    file: FileId,
    key: &Node<parse_js::ast::class_or_object::ClassOrObjMemberDirectKey>,
  ) -> TextRange {
    let range = loc_to_range(file, key.loc);
    let name = key.stx.key.as_str();
    // `parse-js` key locs can span past the identifier (e.g. into a type
    // annotation). Shrink the name to its textual length.
    TextRange::new(
      range.start,
      range.start.saturating_add(name.len() as u32).min(range.end),
    )
  }

  /// Primary span for a private identifier key (`#foo`), matching tsc underlines.
  fn private_key_range(
    file: FileId,
    key: &Node<parse_js::ast::class_or_object::ClassOrObjMemberDirectKey>,
  ) -> TextRange {
    Self::member_key_range(file, key)
  }

  fn index_class_members_in_class(
    &mut self,
    members: &'ast [Node<ClassMember>],
    class_index: usize,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    self.class_nesting.push(class_index);
    let mut param_props: Vec<String> = Vec::new();
    let mut param_props_private: HashSet<String> = HashSet::new();
    for (idx, member) in members.iter().enumerate() {
      if idx % 128 == 0 {
        Self::check_cancelled(cancelled);
      }
      if member.stx.static_ {
        continue;
      }
      let is_constructor = matches!(
        &member.stx.key,
        ClassOrObjKey::Direct(key) if key.stx.key == "constructor"
      );
      if !is_constructor {
        continue;
      }
      let ClassOrObjVal::Method(method) = &member.stx.val else {
        continue;
      };
      for param in method.stx.func.stx.parameters.iter() {
        if param.stx.accessibility.is_some() || param.stx.readonly {
          if let AstPat::Id(id) = param.stx.pattern.stx.pat.stx.as_ref() {
            param_props.push(id.stx.name.clone());
            if matches!(
              param.stx.accessibility,
              Some(parse_js::ast::stmt::decl::Accessibility::Private)
            ) {
              param_props_private.insert(id.stx.name.clone());
            }
          }
        }
      }
    }
    if !param_props.is_empty() {
      param_props.sort();
      param_props.dedup();
    }
    if let Some(info) = self.classes.get_mut(class_index) {
      info.instance_param_props = param_props.clone();
      info.instance_param_props_private = param_props_private;
      for prop in param_props.iter() {
        info.instance_member_names.insert(prop.clone());
      }
    }

    for (idx, member) in members.iter().enumerate() {
      if idx % 128 == 0 {
        Self::check_cancelled(cancelled);
      }
      self.index_class_member(member, class_index, idx, &param_props, file, cancelled);
    }
    self.class_nesting.pop();
  }

  fn index_class_member(
    &mut self,
    member: &'ast Node<ClassMember>,
    class_index: usize,
    member_index: usize,
    param_props: &[String],
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    for decorator in member.stx.decorators.iter() {
      self.index_expr(&decorator.stx.expression, file, cancelled);
    }
    match &member.stx.key {
      ClassOrObjKey::Computed(expr) => self.index_expr(expr, file, cancelled),
      ClassOrObjKey::Direct(_) => {}
    }
    if let ClassOrObjKey::Direct(key) = &member.stx.key {
      let name = key.stx.key.clone();
      let is_constructor_method =
        name == "constructor" && matches!(member.stx.val, ClassOrObjVal::Method(_));
      if !member.stx.static_ && !is_constructor_method {
        if let Some(info) = self.classes.get_mut(class_index) {
          info.instance_member_names.insert(name.clone());
        }
        // TS2715 tracks abstract *properties* (fields/accessors), not methods.
        let is_prop_like = matches!(
          member.stx.val,
          ClassOrObjVal::Prop(_) | ClassOrObjVal::Getter(_) | ClassOrObjVal::Setter(_)
        );
        if is_prop_like {
          if let Some(info) = self.classes.get_mut(class_index) {
            if member.stx.abstract_ {
              info.abstract_instance_props.insert(name.clone());
            } else {
              info.concrete_instance_props.insert(name.clone());
            }
          }
        }
      }
      // Private-identifier uniqueness (tsc `checkClassForDuplicateDeclarations`).
      if (key.stx.tt == TT::PrivateMember || name.starts_with('#')) && !is_constructor_method {
        let kind = match &member.stx.val {
          ClassOrObjVal::Prop(_) => Some(PrivateMemberKind::Field),
          ClassOrObjVal::Method(_) => Some(PrivateMemberKind::Method),
          ClassOrObjVal::Getter(_) => Some(PrivateMemberKind::Getter),
          ClassOrObjVal::Setter(_) => Some(PrivateMemberKind::Setter),
          ClassOrObjVal::IndexSignature(_) | ClassOrObjVal::StaticBlock(_) => None,
        };
        if let Some(kind) = kind {
          if let Some(info) = self.classes.get_mut(class_index) {
            let async_on_accessor = match &member.stx.val {
              ClassOrObjVal::Getter(g) => g.stx.func.stx.async_,
              ClassOrObjVal::Setter(s) => s.stx.func.stx.async_,
              _ => false,
            };
            let accessibility_keyword = match member.stx.accessibility {
              Some(parse_js::ast::stmt::decl::Accessibility::Public) => Some("public"),
              Some(parse_js::ast::stmt::decl::Accessibility::Private) => Some("private"),
              Some(parse_js::ast::stmt::decl::Accessibility::Protected) => Some("protected"),
              None => None,
            };
            info.private_name_decls.push(PrivateNameDecl {
              name,
              key_range: Self::private_key_range(file, key),
              member_start: loc_to_range(file, member.loc).start,
              is_static: member.stx.static_,
              kind,
              accessibility_keyword,
              declare_: member.stx.declare_,
              abstract_: member.stx.abstract_,
              readonly: member.stx.readonly,
              async_on_accessor,
              async_before_static: member.stx.async_before_static,
            });
          }
        }
      }
    }
    if let (ClassOrObjKey::Direct(key), ClassOrObjVal::Prop(init)) =
      (&member.stx.key, &member.stx.val)
    {
      if let Some(info) = self.classes.get_mut(class_index) {
        let key_range = {
          let range = loc_to_range(file, key.loc);
          let name = key.stx.key.as_str();
          // `parse-js` key locations can currently span beyond the identifier
          // token (e.g. include a trailing type annotation). TS2612 expects the
          // diagnostic to underline only the member name, so shrink
          // identifier-like keys to their textual length.
          let is_identifier_like = name.chars().enumerate().all(|(idx, ch)| match idx {
            0 => ch == '_' || ch == '$' || ch.is_ascii_alphabetic(),
            _ => ch == '_' || ch == '$' || ch.is_ascii_alphanumeric(),
          });
          if is_identifier_like {
            TextRange::new(range.start, range.start.saturating_add(name.len() as u32))
          } else {
            range
          }
        };
        if member.stx.abstract_ && init.is_some() {
          info
            .abstract_props_with_initializer
            .push((key.stx.key.clone(), key_range));
        }
        let spi_checked_name = !matches!(
          key.stx.tt,
          TT::LiteralString | TT::LiteralNumber | TT::LiteralBigInt
        );
        let field = ClassFieldDecl {
          name: key.stx.key.clone(),
          member_index,
          optional: member.stx.optional,
          has_initializer: init.is_some(),
          definite_assignment: member.stx.definite_assignment,
          abstract_: member.stx.abstract_,
          declare_: member.stx.declare_,
          spi_checked_name,
          is_private: matches!(
            member.stx.accessibility,
            Some(parse_js::ast::stmt::decl::Accessibility::Private)
          ) || key.stx.tt == TT::PrivateMember,
          key_range,
          type_annotation: member.stx.type_annotation.as_ref(),
        };
        info.value_member_decls.push(ClassValueMemberDecl {
          name: key.stx.key.clone(),
          key_range,
          is_static: member.stx.static_,
          kind: ClassValueMemberKind::Field,
          has_body: false,
          type_annotation: member.stx.type_annotation.as_ref(),
          initializer: init.as_ref(),
          func: None,
        });
        if member.stx.static_ {
          info.static_fields.push(field);
        } else {
          info.instance_fields.push(field);
        }
      }
    }
    match &member.stx.val {
      ClassOrObjVal::Getter(getter) => {
        let accessor_name = if let ClassOrObjKey::Direct(key) = &member.stx.key {
          if let Some(info) = self.classes.get_mut(class_index) {
            if member.stx.static_ {
              info.static_getters.insert(key.stx.key.clone());
              info
                .static_getter_funcs
                .insert(key.stx.key.clone(), &getter.stx.func);
            } else {
              info.instance_getters.insert(key.stx.key.clone());
              info
                .instance_getter_funcs
                .insert(key.stx.key.clone(), &getter.stx.func);
            }
          }
          Some(key.stx.key.clone())
        } else {
          None
        };
        let func_span = loc_to_range(file, getter.stx.func.loc);
        self.class_member_func_by_span.insert(
          func_span,
          ClassMemberFuncInfo {
            class_index,
            is_static: member.stx.static_,
            is_constructor: false,
            accessor_name,
            is_setter: false,
          },
        );
        // Member loc includes the method name so leading JSDoc is found.
        self.index_function(&getter.stx.func, file, cancelled, Some(member.loc))
      }
      ClassOrObjVal::Setter(setter) => {
        let accessor_name = if let ClassOrObjKey::Direct(key) = &member.stx.key {
          if let Some(info) = self.classes.get_mut(class_index) {
            if member.stx.static_ {
              info.static_setters.insert(key.stx.key.clone());
            } else {
              info.instance_setters.insert(key.stx.key.clone());
            }
          }
          Some(key.stx.key.clone())
        } else {
          None
        };
        let func_span = loc_to_range(file, setter.stx.func.loc);
        self.class_member_func_by_span.insert(
          func_span,
          ClassMemberFuncInfo {
            class_index,
            is_static: member.stx.static_,
            is_constructor: false,
            accessor_name,
            is_setter: true,
          },
        );
        self.index_function(&setter.stx.func, file, cancelled, Some(member.loc))
      }
      ClassOrObjVal::Method(method) => {
        let func_span = loc_to_range(file, method.stx.func.loc);
        let is_constructor = matches!(
          &member.stx.key,
          ClassOrObjKey::Direct(key) if !member.stx.static_ && key.stx.key == "constructor"
        );
        self.class_member_func_by_span.insert(
          func_span,
          ClassMemberFuncInfo {
            class_index,
            is_static: member.stx.static_,
            is_constructor,
            accessor_name: None,
            is_setter: false,
          },
        );
        if is_constructor {
          if let Some(info) = self.classes.get_mut(class_index) {
            info.constructor = Some(&method.stx.func);
            if let ClassOrObjKey::Direct(key) = &member.stx.key {
              info.constructor_key_range = Some(Self::member_key_range(file, key));
            }
          }
        } else if let ClassOrObjKey::Direct(key) = &member.stx.key {
          if let Some(info) = self.classes.get_mut(class_index) {
            let name = key.stx.key.clone();
            let key_range = Self::member_key_range(file, key);
            if member.stx.static_ {
              info.static_methods.insert(name.clone());
            } else {
              info.instance_methods.insert(name.clone());
            }
            if key.stx.tt == TT::PrivateMember || name.starts_with('#') {
              info.private_methods.insert(name.clone());
            }
            info.value_member_decls.push(ClassValueMemberDecl {
              name,
              key_range,
              is_static: member.stx.static_,
              kind: ClassValueMemberKind::Method,
              has_body: method.stx.func.stx.body.is_some(),
              type_annotation: None,
              initializer: None,
              func: Some(&method.stx.func),
            });
          }
        }
        self.index_function(&method.stx.func, file, cancelled, Some(member.loc))
      }
      ClassOrObjVal::Prop(Some(expr)) => {
        let init_range = loc_to_range(file, expr.loc);
        let (prop_name, display_name, key_range) =
          class_field_prop_name_and_key_range(file, member);
        self.class_field_initializers.insert(
          init_range,
          ClassFieldInitializerInfo {
            class_index,
            member_index,
            is_static: member.stx.static_,
            prop_name,
            display_name,
            key_range,
          },
        );
        if !param_props.is_empty() && !member.stx.static_ {
          self
            .class_field_param_props
            .insert(init_range, param_props.to_vec());
        }
        self.index_expr(expr, file, cancelled);
      }
      ClassOrObjVal::Prop(None) => {}
      ClassOrObjVal::IndexSignature(_) => {}
      ClassOrObjVal::StaticBlock(block) => {
        let span =
          span_for_stmt_list(&block.stx.body, file).unwrap_or(loc_to_range(file, block.loc));
        self.class_static_blocks.push(ClassStaticBlockInfo {
          span,
          block,
          class_index,
          member_index,
        });
        self.index_stmt_list(&block.stx.body, file, cancelled);
      }
    }
  }

  pub(crate) fn class_field_initializer(
    &self,
    span: TextRange,
  ) -> Option<ClassFieldInitializerInfo> {
    self.class_field_initializers.get(&span).cloned()
  }

  pub(crate) fn field_declared_not_before(
    &self,
    class_index: usize,
    member_index: usize,
    name: &str,
    is_static: bool,
  ) -> bool {
    let Some(info) = self.classes.get(class_index) else {
      return false;
    };
    let fields = if is_static {
      info.static_fields.as_slice()
    } else {
      info.instance_fields.as_slice()
    };
    fields
      .iter()
      .any(|field| !field.optional && field.name == name && field.member_index >= member_index)
  }

  /// If `name` is still an abstract instance property for `class_index` (not
  /// overridden by a concrete field/accessor on this class or between it and
  /// the declaring abstract member), return the declaring class's name.
  pub(crate) fn unresolved_abstract_instance_prop(
    &self,
    class_index: usize,
    name: &str,
  ) -> Option<&str> {
    let mut current = Some(class_index);
    let mut visited = HashSet::<usize>::new();
    while let Some(idx) = current.take() {
      if !visited.insert(idx) {
        break;
      }
      let Some(info) = self.classes.get(idx) else {
        break;
      };
      if info.concrete_instance_props.contains(name) {
        return None;
      }
      if info.abstract_instance_props.contains(name) {
        return info.name.as_deref();
      }
      current = info
        .extends
        .as_ref()
        .and_then(|base| self.classes_by_name.get(base).copied());
    }
    None
  }

  /// True when `ancestor_index` is on `class_index`'s `extends` chain
  /// (inclusive), i.e. `class_index` is the ancestor or derives from it.
  pub(crate) fn class_extends_chain_includes(
    &self,
    class_index: usize,
    ancestor_index: usize,
  ) -> bool {
    let mut current = Some(class_index);
    let mut visited = HashSet::<usize>::new();
    while let Some(idx) = current.take() {
      if !visited.insert(idx) {
        break;
      }
      if idx == ancestor_index {
        return true;
      }
      current = self
        .classes
        .get(idx)
        .and_then(|info| info.extends.as_ref())
        .and_then(|base| self.classes_by_name.get(base).copied());
    }
    false
  }

  pub(crate) fn instance_prop_declared_in_ancestor(&self, class_index: usize, name: &str) -> bool {
    let mut current = self
      .classes
      .get(class_index)
      .and_then(|info| info.extends.clone());
    let mut visited = HashSet::<String>::new();
    while let Some(base_name) = current.take() {
      if !visited.insert(base_name.clone()) {
        break;
      }
      let Some(base_index) = self.classes_by_name.get(&base_name).copied() else {
        break;
      };
      let Some(base) = self.classes.get(base_index) else {
        break;
      };
      if base.instance_member_names.contains(name) {
        return true;
      }
      current = base.extends.clone();
    }
    false
  }

  pub(crate) fn instance_data_prop_declared_in_base_chain(
    &self,
    base_name: &str,
    prop: &str,
  ) -> bool {
    let mut current = Some(base_name.to_string());
    let mut visited = HashSet::<String>::new();
    while let Some(base_name) = current.take() {
      if !visited.insert(base_name.clone()) {
        break;
      }
      let Some(base_index) = self.classes_by_name.get(&base_name).copied() else {
        break;
      };
      let Some(base) = self.classes.get(base_index) else {
        break;
      };

      if base
        .instance_fields
        .iter()
        .any(|field| field.name == prop && !field.name.starts_with('#') && !field.is_private)
      {
        return true;
      }
      if base
        .instance_param_props
        .iter()
        .any(|name| name == prop && !base.instance_param_props_private.contains(prop))
      {
        return true;
      }

      current = base.extends.clone();
    }
    false
  }

  /// Whether `class_index` declares private identifier `prop` (field / method /
  /// accessor, instance or static).
  pub(crate) fn class_declares_private_name(&self, class_index: usize, prop: &str) -> bool {
    if !prop.starts_with('#') {
      return false;
    }
    let Some(info) = self.classes.get(class_index) else {
      return false;
    };
    info.private_methods.contains(prop)
      || info.instance_getters.contains(prop)
      || info.instance_setters.contains(prop)
      || info.static_getters.contains(prop)
      || info.static_setters.contains(prop)
      || info.instance_fields.iter().any(|f| f.name == prop)
      || info.static_fields.iter().any(|f| f.name == prop)
  }

  /// Whether private identifier `prop` is a *static* member of `class_index`
  /// (field / method / accessor). Used for `#x in` CFA targets (`typeof C`
  /// vs instance `C`).
  pub(crate) fn class_private_is_static(&self, class_index: usize, prop: &str) -> bool {
    if !prop.starts_with('#') {
      return false;
    }
    let Some(info) = self.classes.get(class_index) else {
      return false;
    };
    info.static_fields.iter().any(|f| f.name == prop)
      || info.static_methods.contains(prop)
      || info.static_getters.contains(prop)
      || info.static_setters.contains(prop)
  }

  /// All private identifier spellings declared on `class_index`.
  pub(crate) fn class_private_names(&self, class_index: usize) -> Vec<String> {
    let Some(info) = self.classes.get(class_index) else {
      return Vec::new();
    };
    let mut names = HashSet::new();
    for f in info.instance_fields.iter().chain(info.static_fields.iter()) {
      if f.name.starts_with('#') {
        names.insert(f.name.clone());
      }
    }
    for name in info
      .private_methods
      .iter()
      .chain(info.instance_getters.iter())
      .chain(info.instance_setters.iter())
      .chain(info.static_getters.iter())
      .chain(info.static_setters.iter())
    {
      if name.starts_with('#') {
        names.insert(name.clone());
      }
    }
    let mut out: Vec<String> = names.into_iter().collect();
    out.sort();
    out
  }

  /// Lexical private-identifier lookup (tsc `lookupSymbolForPrivateIdentifierDeclaration`):
  /// walk from `from_class` through lexically enclosing parents.
  pub(crate) fn lookup_lexical_private_class(
    &self,
    from_class: Option<usize>,
    prop: &str,
  ) -> Option<usize> {
    if !prop.starts_with('#') {
      return None;
    }
    let mut current = from_class;
    let mut visited = HashSet::<usize>::new();
    while let Some(idx) = current.take() {
      if !visited.insert(idx) {
        break;
      }
      if self.class_declares_private_name(idx, prop) {
        return Some(idx);
      }
      current = self.classes.get(idx).and_then(|c| c.parent_class_index);
    }
    None
  }

  /// First class in the `extends` heritage chain (starting at `class_index`) that
  /// declares private identifier `prop`.
  pub(crate) fn private_declarer_in_heritage(
    &self,
    class_index: usize,
    prop: &str,
  ) -> Option<usize> {
    if !prop.starts_with('#') {
      return None;
    }
    let mut current = Some(class_index);
    let mut visited = HashSet::<usize>::new();
    while let Some(idx) = current.take() {
      if !visited.insert(idx) {
        break;
      }
      if self.class_declares_private_name(idx, prop) {
        return Some(idx);
      }
      current = self
        .classes
        .get(idx)
        .and_then(|c| c.extends.as_ref())
        .and_then(|base| self.classes_by_name.get(base).copied());
    }
    None
  }

  /// Whether `inner` is lexically nested inside `outer` (or is `outer`).
  pub(crate) fn class_is_nested_in(&self, inner: usize, outer: usize) -> bool {
    if inner == outer {
      return true;
    }
    let mut current = self.classes.get(inner).and_then(|c| c.parent_class_index);
    let mut visited = HashSet::<usize>::new();
    while let Some(idx) = current.take() {
      if idx == outer {
        return true;
      }
      if !visited.insert(idx) {
        break;
      }
      current = self.classes.get(idx).and_then(|c| c.parent_class_index);
    }
    false
  }

  /// Diagnostic display name for a class (tsc uses `(anonymous)` when unnamed).
  pub(crate) fn class_diagnostic_name(&self, class_index: usize) -> String {
    self
      .classes
      .get(class_index)
      .and_then(|c| c.name.clone())
      .unwrap_or_else(|| "(anonymous)".to_string())
  }

  fn index_pat(
    &mut self,
    pat: &'ast Node<AstPat>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    let span = loc_to_range(file, pat.loc);
    self.pats.insert(span, pat);
    match pat.stx.as_ref() {
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.index_pat(&elem.target, file, cancelled);
          if let Some(default) = &elem.default_value {
            self.index_expr(default, file, cancelled);
          }
        }
        if let Some(rest) = &arr.stx.rest {
          self.index_pat(rest, file, cancelled);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.index_pat(&prop.stx.target, file, cancelled);
          if let Some(default) = &prop.stx.default_value {
            self.index_expr(default, file, cancelled);
          }
        }
        if let Some(rest) = &obj.stx.rest {
          self.index_pat(rest, file, cancelled);
        }
      }
      AstPat::Id(_) | AstPat::AssignTarget(_) => {}
    }
  }
}

fn class_field_prop_name_and_key_range(
  file: FileId,
  member: &Node<ClassMember>,
) -> (String, String, TextRange) {
  let member_range = loc_to_range(file, member.loc);
  match &member.stx.key {
    ClassOrObjKey::Direct(key) => {
      let range = loc_to_range(file, key.loc);
      let name = key.stx.key.clone();
      let is_identifier_like = name.chars().enumerate().all(|(idx, ch)| match idx {
        0 => ch == '#' || ch == '_' || ch == '$' || ch.is_ascii_alphabetic(),
        _ => ch == '_' || ch == '$' || ch.is_ascii_alphanumeric(),
      });
      let key_range = if is_identifier_like {
        TextRange::new(range.start, range.start.saturating_add(name.len() as u32))
      } else {
        range
      };
      (name.clone(), name, key_range)
    }
    ClassOrObjKey::Computed(expr) => {
      let prop_name = match expr.stx.as_ref() {
        AstExpr::LitStr(s) => s.stx.value.clone(),
        AstExpr::LitNum(n) => n.stx.value.0.to_string(),
        _ => format!("<computed:{}>", member_range.start),
      };
      // ComputedPropertyName is `[` + expr + `]` (no trivia in common cases).
      let expr_range = loc_to_range(file, expr.loc);
      let key_range = TextRange::new(
        expr_range.start.saturating_sub(1),
        expr_range.end.saturating_add(1),
      );
      let display_name = match expr.stx.as_ref() {
        AstExpr::LitStr(s) => format!("[\"{}\"]", s.stx.value),
        AstExpr::LitNum(n) => format!("[{}]", n.stx.value.0),
        _ => format!("[{prop_name}]"),
      };
      (prop_name, display_name, key_range)
    }
  }
}
