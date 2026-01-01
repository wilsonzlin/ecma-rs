use std::collections::{HashMap, HashSet, VecDeque};
use std::panic::panic_any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use bumpalo::Bump;
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::hir::SwitchCase;
use hir_js::{
  ArrayElement, AssignOp, BinaryOp, Body, BodyKind, ExprId, ExprKind, ForHead, ForInit, MemberExpr,
  NameId, NameInterner, ObjectKey, ObjectLiteral, ObjectProperty, PatId, PatKind, StmtId, StmtKind,
  UnaryOp, VarDecl as HirVarDecl,
};
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use parse_js::ast::class_or_object::{ClassMember, ClassStaticBlock};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::jsx::{JsxAttr, JsxAttrVal, JsxElem, JsxElemChild, JsxElemName, JsxText};
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat as AstPat};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::{NamespaceBody, NamespaceDecl};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use semantic_js::ts::SymbolId;
use types_ts_interned::{
  ExpandedType, ObjectType, Param as SigParam, PropData, PropKey, RelateCtx, Shape, Signature,
  SignatureId, TypeDisplay, TypeEvaluator, TypeExpander, TypeId, TypeKind, TypeParamDecl,
  TypeStore,
};

use super::cfg::{BlockId, BlockKind, ControlFlowGraph};
use super::flow::{BindingKey, Env, FlowKey, InitState, PathSegment};
use super::flow_bindings::{FlowBindingId, FlowBindings};
use super::flow_narrow::{
  and_facts, narrow_by_assignability, narrow_by_discriminant, narrow_by_in_check,
  narrow_by_instanceof, narrow_by_literal, narrow_by_nullish_equality, narrow_by_typeof,
  narrow_non_nullish, or_facts, truthy_falsy_types, Facts, LiteralValue,
};

use super::caches::BodyCaches;
use super::expr::{resolve_call, resolve_construct};
use super::overload::callable_signatures;
use super::type_expr::{TypeLowerer, TypeResolver};
use crate::lib_support::JsxMode;
pub use crate::BodyCheckResult;
use crate::{codes, BodyId, DefId};

#[derive(Default, Clone)]
struct Scope {
  bindings: HashMap<String, Binding>,
}

#[derive(Clone)]
struct Binding {
  ty: TypeId,
  type_params: Vec<TypeParamDecl>,
}

/// Simple resolver that maps single-segment type names to known definitions.
#[derive(Clone)]
pub struct BindingTypeResolver {
  map: HashMap<String, DefId>,
}

impl BindingTypeResolver {
  pub fn new(map: HashMap<String, DefId>) -> Self {
    Self { map }
  }
}

impl TypeResolver for BindingTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    match path {
      [name] => self.map.get(name).copied(),
      _ => None,
    }
  }
}

pub struct AstIndex {
  ast: Arc<Node<parse_js::ast::stx::TopLevel>>,
  stmts: HashMap<TextRange, *const Node<Stmt>>,
  exprs: HashMap<TextRange, *const Node<AstExpr>>,
  pats: HashMap<TextRange, *const Node<AstPat>>,
  params: HashMap<TextRange, *const Node<ParamDecl>>,
  vars: HashMap<TextRange, VarInfo>,
  functions: Vec<FunctionInfo>,
  class_static_blocks: Vec<ClassStaticBlockInfo>,
}

// Safety: `AstIndex` stores immutable pointers into an `Arc`-owned AST.
unsafe impl Send for AstIndex {}
unsafe impl Sync for AstIndex {}

#[derive(Clone, Copy)]
struct VarInfo {
  initializer: Option<*const Node<AstExpr>>,
  type_annotation: Option<*const Node<parse_js::ast::type_expr::TypeExpr>>,
}

#[derive(Clone, Copy)]
struct FunctionInfo {
  func_span: TextRange,
  body_span: TextRange,
  func: *const Node<Func>,
}

#[derive(Clone, Copy)]
struct ClassStaticBlockInfo {
  span: TextRange,
  block: *const Node<ClassStaticBlock>,
}

impl AstIndex {
  pub fn new(
    ast: Arc<Node<parse_js::ast::stx::TopLevel>>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) -> Self {
    let mut index = AstIndex {
      ast,
      stmts: HashMap::new(),
      exprs: HashMap::new(),
      pats: HashMap::new(),
      params: HashMap::new(),
      vars: HashMap::new(),
      functions: Vec::new(),
      class_static_blocks: Vec::new(),
    };
    index.index_top_level(file, cancelled);
    index
  }

  pub(crate) fn ast(&self) -> &Node<parse_js::ast::stx::TopLevel> {
    self.ast.as_ref()
  }

  fn check_cancelled(cancelled: Option<&Arc<AtomicBool>>) {
    if let Some(flag) = cancelled {
      if flag.load(Ordering::Relaxed) {
        panic_any(crate::FatalError::Cancelled);
      }
    }
  }

  fn index_top_level(&mut self, file: FileId, cancelled: Option<&Arc<AtomicBool>>) {
    let ast = Arc::clone(&self.ast);
    for (idx, stmt) in ast.stx.body.iter().enumerate() {
      if idx % 1024 == 0 {
        Self::check_cancelled(cancelled);
      }
      self.index_stmt(stmt, file, cancelled);
    }
  }

  fn index_stmt(&mut self, stmt: &Node<Stmt>, file: FileId, cancelled: Option<&Arc<AtomicBool>>) {
    let span = loc_to_range(file, stmt.loc);
    self.stmts.insert(span, stmt as *const _);
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
        self.index_function(&func.stx.function, file, cancelled);
      }
      Stmt::ClassDecl(class_decl) => {
        for decorator in class_decl.stx.decorators.iter() {
          self.index_expr(&decorator.stx.expression, file, cancelled);
        }
        if let Some(extends) = class_decl.stx.extends.as_ref() {
          self.index_expr(extends, file, cancelled);
        }
        for implements in class_decl.stx.implements.iter() {
          self.index_expr(implements, file, cancelled);
        }
        for member in class_decl.stx.members.iter() {
          self.index_class_member(member, file, cancelled);
        }
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
    stmts: &[Node<Stmt>],
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
    ns: &Node<NamespaceDecl>,
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
    decl: &Node<VarDecl>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    for declarator in decl.stx.declarators.iter() {
      let pat_span = loc_to_range(file, declarator.pattern.loc);
      self
        .pats
        .insert(pat_span, &declarator.pattern.stx.pat as *const _);
      self.vars.insert(
        pat_span,
        VarInfo {
          initializer: declarator.initializer.as_ref().map(|n| n as *const _),
          type_annotation: declarator.type_annotation.as_ref().map(|n| n as *const _),
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
    func: &Node<Func>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    let func_span = loc_to_range(file, func.loc);
    if let Some(body) = &func.stx.body {
      let body_span = match body {
        FuncBody::Block(block) => {
          span_for_stmt_list(&block, file).unwrap_or(loc_to_range(file, func.loc))
        }
        FuncBody::Expression(expr) => loc_to_range(file, expr.loc),
      };
      self.functions.push(FunctionInfo {
        func_span,
        body_span,
        func: func as *const _,
      });
    }

    for param in func.stx.parameters.iter() {
      let pat_span = loc_to_range(file, param.stx.pattern.loc);
      self
        .pats
        .insert(pat_span, &param.stx.pattern.stx.pat as *const _);
      self.params.insert(pat_span, param as *const _);
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

  fn index_expr(
    &mut self,
    expr: &Node<AstExpr>,
    file: FileId,
    cancelled: Option<&Arc<AtomicBool>>,
  ) {
    let span = loc_to_range(file, expr.loc);
    self.exprs.insert(span, expr as *const _);
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
      AstExpr::Unary(un) => {
        self.index_expr(&un.stx.argument, file, cancelled);
      }
      AstExpr::UnaryPostfix(post) => {
        self.index_expr(&post.stx.argument, file, cancelled);
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
            ObjMemberType::Valued { val, .. } => match val {
              ClassOrObjVal::Prop(Some(expr)) => self.index_expr(expr, file, cancelled),
              ClassOrObjVal::StaticBlock(block) => {
                self.index_stmt_list(&block.stx.body, file, cancelled)
              }
              _ => {}
            },
            ObjMemberType::Rest { val } => self.index_expr(val, file, cancelled),
            ObjMemberType::Shorthand { .. } => {}
          }
        }
      }
      AstExpr::Class(class_expr) => {
        for decorator in class_expr.stx.decorators.iter() {
          self.index_expr(&decorator.stx.expression, file, cancelled);
        }
        if let Some(extends) = class_expr.stx.extends.as_ref() {
          self.index_expr(extends, file, cancelled);
        }
        for member in class_expr.stx.members.iter() {
          self.index_class_member(member, file, cancelled);
        }
      }
      AstExpr::Func(func) => self.index_function(&func.stx.func, file, cancelled),
      AstExpr::ArrowFunc(func) => self.index_function(&func.stx.func, file, cancelled),
      AstExpr::Id(..)
      | AstExpr::LitNull(..)
      | AstExpr::LitStr(..)
      | AstExpr::LitNum(..)
      | AstExpr::LitBool(..)
      | AstExpr::LitBigInt(..)
      | AstExpr::This(..)
      | AstExpr::Super(..)
      | AstExpr::LitTemplate(..)
      | AstExpr::IdPat(..)
      | AstExpr::ArrPat(..)
      | AstExpr::ObjPat(..)
      | AstExpr::TypeAssertion(..)
      | AstExpr::NonNullAssertion(..)
      | AstExpr::SatisfiesExpr(..)
      | AstExpr::Import(..)
      | AstExpr::ImportMeta(..)
      | AstExpr::TaggedTemplate(..)
      | AstExpr::JsxElem(..)
      | AstExpr::JsxExprContainer(..)
      | AstExpr::JsxMember(..)
      | AstExpr::JsxName(..)
      | AstExpr::JsxSpreadAttr(..)
      | AstExpr::JsxText(..)
      | AstExpr::LitRegex(..)
      | AstExpr::NewTarget(..) => {}
    }
  }

  fn index_class_member(
    &mut self,
    member: &Node<ClassMember>,
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
    match &member.stx.val {
      ClassOrObjVal::Getter(getter) => self.index_function(&getter.stx.func, file, cancelled),
      ClassOrObjVal::Setter(setter) => self.index_function(&setter.stx.func, file, cancelled),
      ClassOrObjVal::Method(method) => self.index_function(&method.stx.func, file, cancelled),
      ClassOrObjVal::Prop(Some(expr)) => self.index_expr(expr, file, cancelled),
      ClassOrObjVal::Prop(None) => {}
      ClassOrObjVal::IndexSignature(_) => {}
      ClassOrObjVal::StaticBlock(block) => {
        let span =
          span_for_stmt_list(&block.stx.body, file).unwrap_or(loc_to_range(file, block.loc));
        self.class_static_blocks.push(ClassStaticBlockInfo {
          span,
          block: block as *const _,
        });
        self.index_stmt_list(&block.stx.body, file, cancelled);
      }
    }
  }

  fn index_pat(&mut self, pat: &Node<AstPat>, file: FileId, cancelled: Option<&Arc<AtomicBool>>) {
    let span = loc_to_range(file, pat.loc);
    self.pats.insert(span, pat as *const _);
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

/// Type-check a lowered HIR body, producing per-expression and per-pattern type tables.
pub fn check_body(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  ast_index: &AstIndex,
  store: Arc<TypeStore>,
  caches: &BodyCaches,
  bindings: &HashMap<String, TypeId>,
  resolver: Option<Arc<dyn TypeResolver>>,
) -> BodyCheckResult {
  check_body_with_expander(
    body_id, body, names, file, ast_index, store, caches, bindings, resolver, None, None, false,
    None, None,
  )
}

/// Type-check a lowered HIR body with an optional reference type expander for
/// relation checks. The expander is used to lazily resolve `TypeKind::Ref`
/// nodes during assignability comparisons.
pub fn check_body_with_expander(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  ast_index: &AstIndex,
  store: Arc<TypeStore>,
  caches: &BodyCaches,
  bindings: &HashMap<String, TypeId>,
  resolver: Option<Arc<dyn TypeResolver>>,
  relate_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
  contextual_fn_ty: Option<TypeId>,
  no_implicit_any: bool,
  jsx_mode: Option<JsxMode>,
  cancelled: Option<&Arc<AtomicBool>>,
) -> BodyCheckResult {
  if let Some(flag) = cancelled {
    if flag.load(Ordering::Relaxed) {
      panic_any(crate::FatalError::Cancelled);
    }
  }
  let prim = store.primitive_ids();
  let expr_types = vec![prim.unknown; body.exprs.len()];
  let pat_types = vec![prim.unknown; body.pats.len()];
  let expr_spans: Vec<TextRange> = body.exprs.iter().map(|e| e.span).collect();
  let pat_spans: Vec<TextRange> = body.pats.iter().map(|p| p.span).collect();
  let ast = ast_index.ast();

  let expr_map: HashMap<TextRange, ExprId> = body
    .exprs
    .iter()
    .enumerate()
    .map(|(idx, expr)| (expr.span, ExprId(idx as u32)))
    .collect();
  let pat_map: HashMap<TextRange, PatId> = body
    .pats
    .iter()
    .enumerate()
    .map(|(idx, pat)| (pat.span, PatId(idx as u32)))
    .collect();

  let body_range = body_range(body);
  let mut relate_hooks = super::relate_hooks();
  if let Some(expander) = relate_expander {
    relate_hooks.expander = Some(expander);
  }
  let relate = RelateCtx::with_hooks_and_cache(
    Arc::clone(&store),
    store.options(),
    relate_hooks,
    caches.relation.clone(),
  );
  let type_resolver = resolver.clone();
  let mut lowerer = match resolver {
    Some(resolver) => TypeLowerer::with_resolver(Arc::clone(&store), resolver),
    None => TypeLowerer::new(Arc::clone(&store)),
  };
  lowerer.set_file(file);
  let synthetic_top_level = matches!(body.kind, BodyKind::TopLevel)
    && body.exprs.is_empty()
    && body.stmts.is_empty()
    && body.pats.is_empty();
  let mut checker = Checker {
    store,
    relate,
    lowerer,
    type_resolver,
    jsx_mode,
    jsx_element_ty: None,
    jsx_intrinsic_elements_ty: None,
    expr_types,
    pat_types,
    expr_spans,
    pat_spans,
    expr_map,
    pat_map,
    diagnostics: Vec::new(),
    implicit_any_reported: HashSet::new(),
    return_types: Vec::new(),
    index: ast_index,
    scopes: vec![Scope::default()],
    namespace_scopes: HashMap::new(),
    expected_return: None,
    check_var_assignments: !synthetic_top_level,
    widen_object_literals: true,
    no_implicit_any,
    file,
    ref_expander: relate_expander,
    contextual_fn_ty,
    cancelled,
    _names: names,
    _bump: Bump::new(),
  };

  checker.seed_builtins();
  for (name, ty) in bindings {
    checker.insert_binding(name.clone(), *ty, Vec::new());
  }

  match body.kind {
    BodyKind::TopLevel => {
      checker.check_stmt_list(&ast.stx.body);
    }
    BodyKind::Function => {
      let found = checker.check_enclosing_function(body_range);
      if !found {
        checker.diagnostics.push(codes::MISSING_BODY.error(
          "missing function body for checker",
          Span::new(file, body_range),
        ));
      }
    }
    BodyKind::Initializer => {
      let found = checker.check_matching_initializer(body_range);
      if !found {
        checker.diagnostics.push(codes::MISSING_BODY.error(
          "missing initializer body for checker",
          Span::new(file, body_range),
        ));
      }
    }
    BodyKind::Class => {
      let found = checker.check_enclosing_class(body_range);
      if !found {
        checker.diagnostics.push(codes::MISSING_BODY.error(
          "missing class body for checker",
          Span::new(file, body_range),
        ));
      }
    }
    BodyKind::Unknown => {
      checker
        .diagnostics
        .push(codes::MISSING_BODY.error("missing body for checker", Span::new(file, body_range)));
    }
  }

  checker
    .diagnostics
    .extend(checker.lowerer.take_diagnostics());
  codes::normalize_diagnostics(&mut checker.diagnostics);
  BodyCheckResult {
    body: body_id,
    expr_types: checker.expr_types,
    expr_spans: checker.expr_spans,
    pat_types: checker.pat_types,
    pat_spans: checker.pat_spans,
    diagnostics: checker.diagnostics,
    return_types: checker.return_types,
  }
}

#[derive(Clone, Debug)]
enum ArrayLiteralContext {
  Tuple(Vec<types_ts_interned::TupleElem>),
  Array(TypeId),
}

struct Checker<'a> {
  store: Arc<TypeStore>,
  relate: RelateCtx<'a>,
  lowerer: TypeLowerer,
  type_resolver: Option<Arc<dyn TypeResolver>>,
  jsx_mode: Option<JsxMode>,
  jsx_element_ty: Option<TypeId>,
  jsx_intrinsic_elements_ty: Option<TypeId>,
  expr_types: Vec<TypeId>,
  pat_types: Vec<TypeId>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
  expr_map: HashMap<TextRange, ExprId>,
  pat_map: HashMap<TextRange, PatId>,
  diagnostics: Vec<Diagnostic>,
  implicit_any_reported: HashSet<TextRange>,
  return_types: Vec<TypeId>,
  index: &'a AstIndex,
  scopes: Vec<Scope>,
  namespace_scopes: HashMap<String, Scope>,
  expected_return: Option<TypeId>,
  check_var_assignments: bool,
  widen_object_literals: bool,
  no_implicit_any: bool,
  file: FileId,
  ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
  contextual_fn_ty: Option<TypeId>,
  cancelled: Option<&'a Arc<AtomicBool>>,
  _names: &'a NameInterner,
  _bump: Bump,
}

impl<'a> Checker<'a> {
  fn report_implicit_any(&mut self, range: TextRange, name: Option<&str>) {
    if !self.no_implicit_any {
      return;
    }
    if !self.implicit_any_reported.insert(range) {
      return;
    }
    self.diagnostics.push(codes::IMPLICIT_ANY.error(
      codes::implicit_any_message(name),
      Span::new(self.file, range),
    ));
  }

  fn report_implicit_any_in_pat(&mut self, pat: &Node<AstPat>) {
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        let range = loc_to_range(self.file, pat.loc);
        self.report_implicit_any(range, Some(&id.stx.name));
      }
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.report_implicit_any_in_pat(&elem.target);
        }
        if let Some(rest) = &arr.stx.rest {
          self.report_implicit_any_in_pat(rest);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.report_implicit_any_in_pat(&prop.stx.target);
        }
        if let Some(rest) = &obj.stx.rest {
          self.report_implicit_any_in_pat(rest);
        }
      }
      AstPat::AssignTarget(_) => {}
    }
  }

  fn check_cancelled(&self) {
    if let Some(flag) = self.cancelled {
      if flag.load(Ordering::Relaxed) {
        panic_any(crate::FatalError::Cancelled);
      }
    }
  }

  fn seed_builtins(&mut self) {
    let prim = self.store.primitive_ids();
    self.insert_binding("undefined".to_string(), prim.undefined, Vec::new());
    self.insert_binding("NaN".to_string(), prim.number, Vec::new());
  }

  fn insert_binding(&mut self, name: String, ty: TypeId, type_params: Vec<TypeParamDecl>) {
    if let Some(scope) = self.scopes.last_mut() {
      scope.bindings.insert(name, Binding { ty, type_params });
    }
  }

  fn lookup(&self, name: &str) -> Option<Binding> {
    for scope in self.scopes.iter().rev() {
      if let Some(binding) = scope.bindings.get(name) {
        return Some(binding.clone());
      }
    }
    None
  }

  fn check_enclosing_function(&mut self, body_range: TextRange) -> bool {
    let mut best: Option<FunctionInfo> = None;
    for (idx, func) in self.index.functions.iter().copied().enumerate() {
      if idx % 2048 == 0 {
        self.check_cancelled();
      }
      let contains =
        func.func_span.start <= body_range.start && func.func_span.end >= body_range.end;
      if !contains {
        continue;
      }
      let len = func.func_span.end.saturating_sub(func.func_span.start);
      let replace = match best {
        Some(existing) => {
          let existing_len = existing
            .func_span
            .end
            .saturating_sub(existing.func_span.start);
          len < existing_len
        }
        None => true,
      };
      if replace {
        best = Some(func);
      }
    }
    if let Some(func) = best {
      self.check_cancelled();
      let func_node = unsafe { &*func.func };
      let prev_return = self.expected_return;
      let mut type_param_decls = Vec::new();
      let mut has_type_params = false;
      if let Some(params) = func_node.stx.type_parameters.as_ref() {
        self.lowerer.push_type_param_scope();
        has_type_params = true;
        type_param_decls = self.lower_type_params(params);
      }
      let contextual_sig = self.contextual_signature();
      let annotated_return = func_node
        .stx
        .return_type
        .as_ref()
        .map(|ret| self.lowerer.lower_type_expr(ret));
      self.expected_return =
        annotated_return.or_else(|| contextual_sig.as_ref().map(|sig| sig.ret));
      self.bind_params(func_node, &type_param_decls, contextual_sig.as_ref());
      self.check_function_body(func_node);
      if has_type_params {
        self.lowerer.pop_type_param_scope();
      }
      self.expected_return = prev_return;
      return true;
    }
    false
  }

  fn check_enclosing_class(&mut self, body_range: TextRange) -> bool {
    if body_range.start == body_range.end {
      // Empty class bodies (no static blocks) still count as checked.
      return true;
    }
    let mut matched_blocks: Vec<ClassStaticBlockInfo> = Vec::new();
    for (idx, block) in self.index.class_static_blocks.iter().copied().enumerate() {
      if idx % 256 == 0 {
        self.check_cancelled();
      }
      if ranges_overlap(body_range, block.span) || contains_range(block.span, body_range) {
        matched_blocks.push(block);
      }
    }
    if matched_blocks.is_empty() {
      return false;
    }
    matched_blocks.sort_by_key(|block| (block.span.start, block.span.end));
    matched_blocks.dedup_by_key(|block| (block.span.start, block.span.end, block.block));
    for block in matched_blocks {
      self.check_cancelled();
      let block_node = unsafe { &*block.block };
      self.check_block_body(&block_node.stx.body);
    }
    true
  }

  fn check_matching_initializer(&mut self, body_range: TextRange) -> bool {
    let mut best: Option<(u32, TextRange, VarInfo)> = None;
    for (span, info) in self.index.vars.iter() {
      if let Some(init) = info.initializer {
        let init = unsafe { &*init };
        let init_range = loc_to_range(self.file, init.loc);
        if !ranges_overlap(init_range, body_range) && !contains_range(body_range, init_range) {
          continue;
        }
        let len = init_range.end.saturating_sub(init_range.start);
        let replace = match best {
          Some((best_len, best_span, _)) => {
            len < best_len || (len == best_len && span.start < best_span.start)
          }
          None => true,
        };
        if replace {
          best = Some((len, *span, *info));
        }
      }
    }
    if let Some((_len, pat_span, info)) = best {
      self.check_cancelled();
      if let Some(init) = info.initializer {
        let init = unsafe { &*init };
        let annotation = info
          .type_annotation
          .map(|ann| unsafe { &*ann })
          .map(|ann| self.lowerer.lower_type_expr(ann));
        let init_ty = match annotation {
          Some(expected) => self.check_expr_with_expected(init, expected),
          None => self.check_expr(init),
        };
        if let Some(annotation) = annotation {
          self.check_assignable(init, init_ty, annotation);
        }
        let ty = annotation.unwrap_or(init_ty);
        if let Some(pat) = self.index.pats.get(&pat_span).copied() {
          let pat = unsafe { &*pat };
          self.bind_pattern(pat, ty);
        }
      }
      return true;
    }

    // Fallback for initializer bodies that are not var declarators (e.g. class
    // field initializers). Match the tightest expression overlapping the body
    // range and type-check it.
    let mut best_expr: Option<(u32, TextRange, *const Node<AstExpr>)> = None;
    for (span, expr) in self.index.exprs.iter() {
      let span = *span;
      if !ranges_overlap(span, body_range) && !contains_range(body_range, span) {
        continue;
      }
      let len = span.end.saturating_sub(span.start);
      let replace = match best_expr {
        Some((best_len, best_span, _)) => {
          len < best_len || (len == best_len && span.start < best_span.start)
        }
        None => true,
      };
      if replace {
        best_expr = Some((len, span, *expr));
      }
    }
    if let Some((_len, _span, expr)) = best_expr {
      self.check_cancelled();
      let expr = unsafe { &*expr };
      let _ = self.check_expr(expr);
      return true;
    }
    false
  }

  fn bind_params(
    &mut self,
    func: &Node<Func>,
    type_param_decls: &[TypeParamDecl],
    contextual_sig: Option<&Signature>,
  ) {
    let prim = self.store.primitive_ids();
    for (idx, param) in func.stx.parameters.iter().enumerate() {
      if idx % 64 == 0 {
        self.check_cancelled();
      }
      let pat_span = loc_to_range(self.file, param.stx.pattern.loc);
      let annotation = param
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| self.lowerer.lower_type_expr(ann));
      let default_ty = param.stx.default_value.as_ref().map(|d| self.check_expr(d));
      let contextual_param_ty = contextual_sig
        .and_then(|sig| sig.params.get(idx))
        .map(|param| param.ty);
      let is_this = idx == 0
        && matches!(
          param.stx.pattern.stx.pat.stx.as_ref(),
          AstPat::Id(id) if id.stx.name == "this"
        );
      let implicit_any =
        self.no_implicit_any && !is_this && annotation.is_none() && contextual_param_ty.is_none();
      let mut ty = annotation
        .or(contextual_param_ty)
        .unwrap_or(if implicit_any { prim.any } else { prim.unknown });
      if implicit_any {
        let range = loc_to_range(self.file, param.stx.pattern.stx.pat.loc);
        let name = match param.stx.pattern.stx.pat.stx.as_ref() {
          AstPat::Id(id) => Some(id.stx.name.as_str()),
          _ => None,
        };
        self.report_implicit_any(range, name);
      }
      if let Some(default) = default_ty {
        ty = self.store.union(vec![ty, default]);
      }
      if let Some(pat) = self.index.pats.get(&pat_span).copied() {
        let pat = unsafe { &*pat };
        self.bind_pattern_with_type_params(pat, ty, type_param_decls.to_vec());
      }
    }
  }

  fn lower_type_params(
    &mut self,
    params: &[Node<parse_js::ast::type_expr::TypeParameter>],
  ) -> Vec<TypeParamDecl> {
    self.lowerer.register_type_params(params)
  }

  fn check_function_body(&mut self, func: &Node<Func>) {
    match &func.stx.body {
      Some(FuncBody::Block(block)) => {
        self.check_stmt_list(block);
      }
      Some(FuncBody::Expression(expr)) => {
        let ty = self.check_expr(expr);
        if let Some(expected) = self.expected_return {
          self.check_assignable(expr, ty, expected);
        }
        self.return_types.push(ty);
      }
      None => {}
    }
  }

  fn contextual_signature(&self) -> Option<Signature> {
    let ty = self.contextual_fn_ty?;
    match self.store.type_kind(ty) {
      TypeKind::Callable { overloads } => overloads.first().map(|sig| self.store.signature(*sig)),
      _ => None,
    }
  }

  fn check_stmt_list(&mut self, stmts: &[Node<Stmt>]) {
    for (idx, stmt) in stmts.iter().enumerate() {
      if idx % 128 == 0 {
        self.check_cancelled();
      }
      self.check_stmt(stmt);
    }
  }

  fn check_stmt(&mut self, stmt: &Node<Stmt>) {
    match stmt.stx.as_ref() {
      Stmt::Expr(expr_stmt) => {
        self.check_expr(&expr_stmt.stx.expr);
      }
      Stmt::ExportDefaultExpr(default_expr) => {
        self.check_expr(&default_expr.stx.expression);
      }
      Stmt::Return(ret) => {
        let ty = ret
          .stx
          .value
          .as_ref()
          .map(|v| self.check_expr(v))
          .unwrap_or(self.store.primitive_ids().undefined);
        if let (Some(expected), Some(value)) = (self.expected_return, ret.stx.value.as_ref()) {
          self.check_assignable(value, ty, expected);
        }
        self.return_types.push(ty);
      }
      Stmt::Block(block) => {
        self.scopes.push(Scope::default());
        self.check_stmt_list(&block.stx.body);
        self.scopes.pop();
      }
      Stmt::If(if_stmt) => {
        self.check_expr(&if_stmt.stx.test);
        self.scopes.push(Scope::default());
        self.check_stmt(&if_stmt.stx.consequent);
        self.scopes.pop();
        if let Some(alt) = &if_stmt.stx.alternate {
          self.scopes.push(Scope::default());
          self.check_stmt(alt);
          self.scopes.pop();
        }
      }
      Stmt::While(while_stmt) => {
        self.check_expr(&while_stmt.stx.condition);
        self.scopes.push(Scope::default());
        self.check_stmt(&while_stmt.stx.body);
        self.scopes.pop();
      }
      Stmt::DoWhile(do_while) => {
        self.scopes.push(Scope::default());
        self.check_stmt(&do_while.stx.body);
        self.scopes.pop();
        self.check_expr(&do_while.stx.condition);
      }
      Stmt::ForTriple(for_stmt) => {
        use parse_js::ast::stmt::ForTripleStmtInit;
        self.scopes.push(Scope::default());
        match &for_stmt.stx.init {
          ForTripleStmtInit::Expr(expr) => {
            self.check_expr(expr);
          }
          ForTripleStmtInit::Decl(decl) => {
            self.check_var_decl(decl);
          }
          ForTripleStmtInit::None => {}
        }
        if let Some(cond) = &for_stmt.stx.cond {
          self.check_expr(cond);
        }
        if let Some(post) = &for_stmt.stx.post {
          self.check_expr(post);
        }
        self.check_block_body(&for_stmt.stx.body.stx.body);
        self.scopes.pop();
      }
      Stmt::ForIn(for_in) => {
        use parse_js::ast::stmt::ForInOfLhs;
        self.scopes.push(Scope::default());
        match &for_in.stx.lhs {
          ForInOfLhs::Assign(pat) => {
            self.check_pat(pat, self.store.primitive_ids().unknown);
          }
          ForInOfLhs::Decl((_, pat_decl)) => {
            self.check_pat(&pat_decl.stx.pat, self.store.primitive_ids().unknown);
          }
        }
        self.check_expr(&for_in.stx.rhs);
        self.check_block_body(&for_in.stx.body.stx.body);
        self.scopes.pop();
      }
      Stmt::ForOf(for_of) => {
        use parse_js::ast::stmt::ForInOfLhs;
        self.scopes.push(Scope::default());
        match &for_of.stx.lhs {
          ForInOfLhs::Assign(pat) => {
            self.check_pat(pat, self.store.primitive_ids().unknown);
          }
          ForInOfLhs::Decl((_, pat_decl)) => {
            self.check_pat(&pat_decl.stx.pat, self.store.primitive_ids().unknown);
          }
        }
        self.check_expr(&for_of.stx.rhs);
        self.check_block_body(&for_of.stx.body.stx.body);
        self.scopes.pop();
      }
      Stmt::Switch(sw) => {
        let _ = self.check_expr(&sw.stx.test);
        for branch in sw.stx.branches.iter() {
          if let Some(case) = &branch.stx.case {
            self.check_expr(case);
          }
          self.scopes.push(Scope::default());
          self.check_stmt_list(&branch.stx.body);
          self.scopes.pop();
        }
      }
      Stmt::Try(tr) => {
        self.check_block_body(&tr.stx.wrapped.stx.body);
        if let Some(catch) = &tr.stx.catch {
          self.scopes.push(Scope::default());
          if let Some(param) = &catch.stx.parameter {
            self.check_pat(&param.stx.pat, self.store.primitive_ids().unknown);
          }
          self.check_block_body(&catch.stx.body);
          self.scopes.pop();
        }
        if let Some(finally) = &tr.stx.finally {
          self.check_block_body(&finally.stx.body);
        }
      }
      Stmt::Throw(th) => {
        self.check_expr(&th.stx.value);
      }
      Stmt::Label(label) => {
        self.check_stmt(&label.stx.statement);
      }
      Stmt::With(w) => {
        self.check_expr(&w.stx.object);
        self.scopes.push(Scope::default());
        self.check_stmt(&w.stx.body);
        self.scopes.pop();
      }
      Stmt::VarDecl(decl) => self.check_var_decl(decl),
      Stmt::FunctionDecl(func) => {
        // Function declarations are handled by separate bodies; bind the name for call sites in
        // this body, but preserve any pre-seeded binding (e.g. merged namespace + value types)
        // by intersecting rather than overwriting.
        if let Some(name) = func.stx.name.as_ref() {
          let name_str = name.stx.name.clone();
          let fn_ty = self.function_type(&func.stx.function);
          if let Some(existing) = self.lookup(&name_str) {
            let has_callables = !callable_signatures(self.store.as_ref(), existing.ty).is_empty();
            let ty = if has_callables {
              existing.ty
            } else {
              self.store.intersection(vec![existing.ty, fn_ty])
            };
            self.insert_binding(name_str, ty, Vec::new());
          } else {
            self.insert_binding(name_str, fn_ty, Vec::new());
          }
        }
      }
      Stmt::NamespaceDecl(ns) => self.check_namespace(ns),
      Stmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          self.check_stmt_list(body);
        }
      }
      Stmt::GlobalDecl(global) => self.check_stmt_list(&global.stx.body),
      _ => {}
    }
  }

  fn check_block_body(&mut self, stmts: &[Node<Stmt>]) {
    self.scopes.push(Scope::default());
    self.check_stmt_list(stmts);
    self.scopes.pop();
  }

  fn check_var_decl(&mut self, decl: &Node<VarDecl>) {
    let prim = self.store.primitive_ids();
    for declarator in decl.stx.declarators.iter() {
      let annot_ty = declarator
        .type_annotation
        .as_ref()
        .map(|ann| self.lowerer.lower_type_expr(ann));
      let init_ty = if self.check_var_assignments {
        declarator
          .initializer
          .as_ref()
          .map(|init| match annot_ty {
            Some(expected) => self.check_expr_with_expected(init, expected),
            None => self.check_expr(init),
          })
          .unwrap_or(prim.unknown)
      } else {
        prim.unknown
      };
      let binding_ty = match decl.stx.mode {
        VarDeclMode::Const | VarDeclMode::Using | VarDeclMode::AwaitUsing => init_ty,
        _ => self.base_type(init_ty),
      };
      let mut final_ty = annot_ty.unwrap_or(binding_ty);
      if self.no_implicit_any && annot_ty.is_none() && final_ty == prim.unknown {
        // Like TypeScript `--noImplicitAny`, report untyped bindings that
        // would otherwise become `any`. Use `any` for recovery to keep
        // type checking resilient.
        self.report_implicit_any_in_pat(&declarator.pattern.stx.pat);
        final_ty = prim.any;
      }
      if self.check_var_assignments {
        if let (Some(ann), Some(init)) = (annot_ty, declarator.initializer.as_ref()) {
          self.check_assignable(init, init_ty, ann);
        }
      }
      self.check_pat(&declarator.pattern.stx.pat, final_ty);
    }
  }

  fn check_namespace(&mut self, ns: &Node<NamespaceDecl>) {
    fn namespace_key(path: &[String]) -> String {
      path.join(".")
    }

    fn check_ns(checker: &mut Checker<'_>, ns: &Node<NamespaceDecl>, path: &mut Vec<String>) {
      let name = ns.stx.name.clone();
      path.push(name.clone());
      let key = namespace_key(path);

      let mut scope = checker.namespace_scopes.remove(&key).unwrap_or_default();
      if let Some(binding) = checker.lookup(&name) {
        scope.bindings.insert(name.clone(), binding);
      }

      checker.scopes.push(scope);
      match &ns.stx.body {
        NamespaceBody::Block(stmts) => checker.check_stmt_list(stmts),
        NamespaceBody::Namespace(inner) => check_ns(checker, inner, path),
      }
      let scope = checker.scopes.pop().unwrap_or_default();
      checker.namespace_scopes.insert(key, scope);
      path.pop();
    }

    let mut path = Vec::new();
    check_ns(self, ns, &mut path);
  }

  fn check_pat(&mut self, pat: &Node<AstPat>, value_ty: TypeId) {
    self.bind_pattern(pat, value_ty);
  }

  fn check_expr(&mut self, expr: &Node<AstExpr>) -> TypeId {
    let ty = match expr.stx.as_ref() {
      AstExpr::Id(id) => self.resolve_ident(&id.stx.name, expr),
      AstExpr::LitNum(num) => {
        let value = num.stx.value.0;
        self
          .store
          .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(value)))
      }
      AstExpr::LitStr(str_lit) => {
        let name = self.store.intern_name(str_lit.stx.value.clone());
        self.store.intern_type(TypeKind::StringLiteral(name))
      }
      AstExpr::LitBool(b) => self
        .store
        .intern_type(TypeKind::BooleanLiteral(b.stx.value)),
      AstExpr::LitNull(_) => self.store.primitive_ids().null,
      AstExpr::LitBigInt(value) => {
        let trimmed = value.stx.value.trim_end_matches('n');
        let parsed = trimmed.parse::<i128>().unwrap_or(0);
        self
          .store
          .intern_type(TypeKind::BigIntLiteral(parsed.into()))
      }
      AstExpr::This(_) => self.store.primitive_ids().unknown,
      AstExpr::Super(_) => self.store.primitive_ids().unknown,
      AstExpr::Unary(un) => {
        if matches!(un.stx.operator, OperatorName::New) {
          let (callee_expr, arg_exprs, span_loc) = match un.stx.argument.stx.as_ref() {
            AstExpr::Call(call) => (
              &call.stx.callee,
              Some(call.stx.arguments.as_slice()),
              call.loc,
            ),
            _ => (&un.stx.argument, None, expr.loc),
          };
          let callee_ty = self.check_expr(callee_expr);
          let arg_types: Vec<TypeId> = arg_exprs
            .unwrap_or(&[])
            .iter()
            .map(|arg| self.check_expr(&arg.stx.value))
            .collect();
          let span = Span {
            file: self.file,
            range: loc_to_range(self.file, span_loc),
          };
          let resolution = resolve_construct(
            &self.store,
            &self.relate,
            callee_ty,
            &arg_types,
            None,
            None,
            span,
            self.ref_expander,
          );
          for diag in &resolution.diagnostics {
            self.diagnostics.push(diag.clone());
          }
          if resolution.diagnostics.is_empty() {
            if let Some(sig_id) = resolution.signature {
              let sig = self.store.signature(sig_id);
              if let Some(arg_exprs) = arg_exprs {
                for (idx, arg) in arg_exprs.iter().enumerate() {
                  if let Some(param) = sig.params.get(idx) {
                    let arg_ty = arg_types
                      .get(idx)
                      .copied()
                      .unwrap_or(self.store.primitive_ids().unknown);
                    self.check_assignable(&arg.stx.value, arg_ty, param.ty);
                  }
                }
              }
            }
          }
          resolution.return_type
        } else {
          self.check_unary(un.stx.operator, &un.stx.argument)
        }
      }
      AstExpr::UnaryPostfix(post) => match post.stx.operator {
        OperatorName::PostfixIncrement | OperatorName::PostfixDecrement => {
          self.store.primitive_ids().number
        }
        _ => self.store.primitive_ids().unknown,
      },
      AstExpr::Binary(bin) => self.check_binary(bin.stx.operator, &bin.stx.left, &bin.stx.right),
      AstExpr::Cond(cond) => {
        let cons = self.check_expr(&cond.stx.consequent);
        let alt = self.check_expr(&cond.stx.alternate);
        self.store.union(vec![cons, alt])
      }
      AstExpr::Call(call) => {
        let callee_ty = self.check_expr(&call.stx.callee);
        let mut arg_types: Vec<TypeId> = call
          .stx
          .arguments
          .iter()
          .map(|arg| self.check_expr(&arg.stx.value))
          .collect();
        let span = Span {
          file: self.file,
          range: loc_to_range(self.file, call.loc),
        };
        let mut resolution = resolve_call(
          &self.store,
          &self.relate,
          callee_ty,
          &arg_types,
          None,
          None,
          span,
          self.ref_expander,
        );
        if resolution.diagnostics.is_empty() {
          if let Some(sig_id) = resolution.signature {
            let sig = self.store.signature(sig_id);
            let mut refined = false;
            for (idx, arg) in call.stx.arguments.iter().enumerate() {
              let Some(param) = sig.params.get(idx) else {
                continue;
              };
              let Some(func) = (match arg.stx.value.stx.as_ref() {
                AstExpr::ArrowFunc(arrow) => Some(&arrow.stx.func),
                AstExpr::Func(func) => Some(&func.stx.func),
                _ => None,
              }) else {
                continue;
              };

              let Some(refined_ty) = self.refine_function_expr_with_expected(func, param.ty) else {
                continue;
              };
              if let Some(slot) = arg_types.get_mut(idx) {
                *slot = refined_ty;
                refined = true;
              }
              self.record_expr_type(arg.stx.value.loc, refined_ty);
            }

            if refined {
              let next = resolve_call(
                &self.store,
                &self.relate,
                callee_ty,
                &arg_types,
                None,
                None,
                span,
                self.ref_expander,
              );
              if next.diagnostics.is_empty() && next.signature.is_some() {
                resolution = next;
              }
            }
          }
        }

        let candidate_sigs = callable_signatures(self.store.as_ref(), callee_ty);
        let allow_assignable_fallback = resolution.diagnostics.len() == 1
          && resolution.diagnostics[0].code.as_str() == codes::NO_OVERLOAD.as_str()
          && candidate_sigs.len() == 1;
        let mut reported_assignability = false;
        if allow_assignable_fallback {
          if let Some(sig_id) = candidate_sigs.first().copied() {
            let sig = self.store.signature(sig_id);
            let before = self.diagnostics.len();
            for (idx, arg) in call.stx.arguments.iter().enumerate() {
              if let Some(param) = sig.params.get(idx) {
                let arg_ty = arg_types
                  .get(idx)
                  .copied()
                  .unwrap_or(self.store.primitive_ids().unknown);
                self.check_assignable(&arg.stx.value, arg_ty, param.ty);
              }
            }
            reported_assignability = self.diagnostics.len() > before;
          }
        }

        if !reported_assignability {
          for diag in &resolution.diagnostics {
            self.diagnostics.push(diag.clone());
          }
        }
        if resolution.diagnostics.is_empty() {
          if let Some(sig_id) = resolution.signature {
            let sig = self.store.signature(sig_id);
            for (idx, arg) in call.stx.arguments.iter().enumerate() {
              if let Some(param) = sig.params.get(idx) {
                let arg_ty = arg_types
                  .get(idx)
                  .copied()
                  .unwrap_or(self.store.primitive_ids().unknown);
                self.check_assignable(&arg.stx.value, arg_ty, param.ty);
              }
            }
            if let TypeKind::Predicate {
              parameter: Some(param_name),
              asserted: Some(asserted),
              asserts: true,
            } = self.store.type_kind(sig.ret)
            {
              let target = sig
                .params
                .iter()
                .enumerate()
                .find(|(_, p)| p.name == Some(param_name))
                .or_else(|| sig.params.get(0).map(|p| (0usize, p)));
              if let Some((idx, _)) = target {
                if let Some(arg) = call.stx.arguments.get(idx) {
                  if let AstExpr::Id(id) = arg.stx.value.stx.as_ref() {
                    self.insert_binding(id.stx.name.clone(), asserted.clone(), Vec::new());
                  }
                }
              }
            }
            let required = sig.params.iter().filter(|p| !p.optional && !p.rest).count();
            let has_rest = sig.params.iter().any(|p| p.rest);
            let max = if has_rest {
              None
            } else {
              Some(sig.params.len())
            };
            if arg_types.len() < required || max.map_or(false, |m| arg_types.len() > m) {
              self
                .diagnostics
                .push(codes::ARGUMENT_COUNT_MISMATCH.error("argument count mismatch", span));
            }
          }
        }
        let contextual_sig = resolution
          .signature
          .or_else(|| candidate_sigs.into_iter().next());
        if let Some(sig_id) = contextual_sig {
          let sig = self.store.signature(sig_id);
          for (idx, arg) in call.stx.arguments.iter().enumerate() {
            if let Some(param) = sig.params.get(idx) {
              let arg_ty = arg_types
                .get(idx)
                .copied()
                .unwrap_or(self.store.primitive_ids().unknown);
              let contextual = match arg.stx.value.stx.as_ref() {
                AstExpr::ArrowFunc(_) | AstExpr::Func(_) if self.is_callable_like(param.ty) => {
                  arg_ty
                }
                _ => self.contextual_arg_type(arg_ty, param.ty),
              };
              self.record_expr_type(arg.stx.value.loc, contextual);
            }
          }
        }
        resolution.return_type
      }
      AstExpr::Member(mem) => {
        let obj_ty = self.check_expr(&mem.stx.left);
        self.member_type(obj_ty, &mem.stx.right)
      }
      AstExpr::ComputedMember(mem) => {
        let obj_ty = self.check_expr(&mem.stx.object);
        let _ = self.check_expr(&mem.stx.member);
        self.member_type(obj_ty, "<computed>")
      }
      AstExpr::LitArr(arr) => self.array_literal_type(arr),
      AstExpr::LitObj(obj) => self.object_literal_type(obj),
      AstExpr::Func(func) => self.function_type(&func.stx.func),
      AstExpr::ArrowFunc(func) => self.function_type(&func.stx.func),
      AstExpr::JsxElem(elem) => self.check_jsx_elem(elem),
      AstExpr::IdPat(_) | AstExpr::ArrPat(_) | AstExpr::ObjPat(_) => {
        self.store.primitive_ids().unknown
      }
      AstExpr::TypeAssertion(assert) => {
        if assert.stx.const_assertion {
          self.const_assertion_type(&assert.stx.expression)
        } else {
          let inner = self.check_expr(&assert.stx.expression);
          if let Some(annotation) = assert.stx.type_annotation.as_ref() {
            self.lowerer.lower_type_expr(annotation)
          } else {
            inner
          }
        }
      }
      AstExpr::NonNullAssertion(assert) => self.check_expr(&assert.stx.expression),
      AstExpr::SatisfiesExpr(expr) => {
        let target_ty = self.lowerer.lower_type_expr(&expr.stx.type_annotation);
        let value_ty = self.check_expr_with_expected(&expr.stx.expression, target_ty);
        if !self.relate.is_assignable(value_ty, target_ty) {
          self.diagnostics.push(codes::TYPE_MISMATCH.error(
            "expression does not satisfy target type",
            Span {
              file: self.file,
              range: loc_to_range(self.file, expr.loc),
            },
          ));
        }
        value_ty
      }
      _ => self.store.primitive_ids().unknown,
    };
    self.record_expr_type(expr.loc, ty);
    ty
  }

  fn check_jsx_elem(&mut self, elem: &Node<JsxElem>) -> TypeId {
    let prim = self.store.primitive_ids();
    if self.jsx_mode.is_none() {
      self.diagnostics.push(codes::JSX_DISABLED.error(
        "jsx is disabled",
        Span::new(self.file, loc_to_range(self.file, elem.loc)),
      ));
      return prim.unknown;
    }

    let element_ty = self.jsx_element_type();
    let mut props_ty = prim.unknown;

    match &elem.stx.name {
      None => {
        // Fragment; no attributes, but still typecheck children.
      }
      Some(JsxElemName::Name(name)) => {
        let tag = name.stx.name.as_str();
        let intrinsic_elements = self.jsx_intrinsic_elements_type();
        if intrinsic_elements != prim.unknown {
          let found = self.member_type(intrinsic_elements, tag);
          if found == prim.unknown {
            self
              .diagnostics
              .push(codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.error(
                format!("unknown JSX intrinsic element `{tag}`"),
                Span::new(self.file, loc_to_range(self.file, name.loc)),
              ));
          } else {
            props_ty = found;
          }
        }
      }
      Some(JsxElemName::Id(id)) => {
        let name = id.stx.name.as_str();
        let component_ty = self
          .lookup(name)
          .map(|binding| binding.ty)
          .unwrap_or_else(|| {
            self.diagnostics.push(codes::UNKNOWN_IDENTIFIER.error(
              format!("unknown identifier `{name}`"),
              Span::new(self.file, loc_to_range(self.file, id.loc)),
            ));
            prim.unknown
          });
        props_ty = self
          .jsx_component_props_type(component_ty)
          .unwrap_or(prim.unknown);
      }
      Some(JsxElemName::Member(member)) => {
        // Member expressions like `<Foo.Bar />` are treated like looking up
        // `Foo` and then checking `.Bar` as a value.
        let base_name = member.stx.base.stx.name.as_str();
        let mut current = self
          .lookup(base_name)
          .map(|binding| binding.ty)
          .unwrap_or_else(|| {
            self.diagnostics.push(codes::UNKNOWN_IDENTIFIER.error(
              format!("unknown identifier `{base_name}`"),
              Span::new(self.file, loc_to_range(self.file, member.stx.base.loc)),
            ));
            prim.unknown
          });
        for segment in member.stx.path.iter() {
          current = self.member_type(current, segment);
        }
        props_ty = self
          .jsx_component_props_type(current)
          .unwrap_or(prim.unknown);
      }
    }

    self.check_jsx_attrs(&elem.stx.attributes, props_ty);
    self.check_jsx_children(&elem.stx.children, props_ty);

    element_ty
  }

  fn check_jsx_attrs(&mut self, attrs: &[JsxAttr], props_ty: TypeId) {
    let prim = self.store.primitive_ids();
    for attr in attrs {
      match attr {
        JsxAttr::Named { name, value } => {
          let key = &name.stx.name;
          let expected = if props_ty == prim.unknown {
            prim.unknown
          } else {
            self.member_type(props_ty, key)
          };

          match value {
            None => {
              // Boolean attributes (e.g. `<div hidden />`). Approximate as `true`.
              if expected != prim.unknown && !self.relate.is_assignable(prim.boolean, expected) {
                self.diagnostics.push(codes::TYPE_MISMATCH.error(
                  "type mismatch",
                  Span::new(self.file, loc_to_range(self.file, name.loc)),
                ));
              }
            }
            Some(JsxAttrVal::Text(text)) => {
              if let Some(actual) = self.jsx_text_type(text) {
                if expected != prim.unknown && !self.relate.is_assignable(actual, expected) {
                  self.diagnostics.push(codes::TYPE_MISMATCH.error(
                    "type mismatch",
                    Span::new(self.file, loc_to_range(self.file, text.loc)),
                  ));
                }
              }
            }
            Some(JsxAttrVal::Expression(expr)) => {
              let actual = self.check_expr(&expr.stx.value);
              if expected != prim.unknown {
                self.check_assignable(&expr.stx.value, actual, expected);
              }
            }
            Some(JsxAttrVal::Element(elem)) => {
              let actual = self.check_jsx_elem(elem);
              if expected != prim.unknown && !self.relate.is_assignable(actual, expected) {
                self.diagnostics.push(codes::TYPE_MISMATCH.error(
                  "type mismatch",
                  Span::new(self.file, loc_to_range(self.file, elem.loc)),
                ));
              }
            }
          }
        }
        JsxAttr::Spread { value } => {
          let actual = self.check_expr(&value.stx.value);
          if props_ty != prim.unknown {
            self.check_assignable(&value.stx.value, actual, props_ty);
          }
        }
      }
    }
  }

  fn check_jsx_children(&mut self, children: &[JsxElemChild], props_ty: TypeId) {
    let prim = self.store.primitive_ids();
    let expected = if props_ty == prim.unknown {
      prim.unknown
    } else {
      self.member_type(props_ty, "children")
    };
    for child in children {
      match child {
        JsxElemChild::Text(text) => {
          let Some(actual) = self.jsx_text_type(text) else {
            continue;
          };
          if expected != prim.unknown && !self.relate.is_assignable(actual, expected) {
            self.diagnostics.push(codes::TYPE_MISMATCH.error(
              "type mismatch",
              Span::new(self.file, loc_to_range(self.file, text.loc)),
            ));
          }
        }
        JsxElemChild::Expr(expr) => {
          let actual = self.check_expr(&expr.stx.value);
          if expected != prim.unknown {
            self.check_assignable(&expr.stx.value, actual, expected);
          }
        }
        JsxElemChild::Element(elem) => {
          let actual = self.check_jsx_elem(elem);
          if expected != prim.unknown && !self.relate.is_assignable(actual, expected) {
            self.diagnostics.push(codes::TYPE_MISMATCH.error(
              "type mismatch",
              Span::new(self.file, loc_to_range(self.file, elem.loc)),
            ));
          }
        }
      }
    }
  }

  fn jsx_text_type(&mut self, text: &Node<JsxText>) -> Option<TypeId> {
    let trimmed = text.stx.value.trim();
    if trimmed.is_empty() {
      return None;
    }
    let name = self.store.intern_name(trimmed.to_string());
    Some(self.store.intern_type(TypeKind::StringLiteral(name)))
  }

  fn resolve_type_ref(&mut self, path: &[&str]) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let segments: Vec<String> = path.iter().map(|s| s.to_string()).collect();
    let def = resolver.resolve_type_name(&segments)?;
    Some(self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: Vec::new(),
    })))
  }

  fn jsx_element_type(&mut self) -> TypeId {
    if let Some(ty) = self.jsx_element_ty {
      return ty;
    }
    let prim = self.store.primitive_ids();
    let ty = self
      .resolve_type_ref(&["JSX", "Element"])
      .unwrap_or(prim.unknown);
    self.jsx_element_ty = Some(ty);
    ty
  }

  fn jsx_intrinsic_elements_type(&mut self) -> TypeId {
    if let Some(ty) = self.jsx_intrinsic_elements_ty {
      return ty;
    }
    let prim = self.store.primitive_ids();
    let ty = self
      .resolve_type_ref(&["JSX", "IntrinsicElements"])
      .unwrap_or(prim.unknown);
    self.jsx_intrinsic_elements_ty = Some(ty);
    ty
  }

  fn jsx_component_props_type(&mut self, component_ty: TypeId) -> Option<TypeId> {
    let sig = self.first_callable_signature(component_ty)?;
    sig.params.first().map(|param| param.ty)
  }

  fn const_assertion_type(&mut self, expr: &Node<AstExpr>) -> TypeId {
    let prim = self.store.primitive_ids();
    let ty = match expr.stx.as_ref() {
      AstExpr::LitNum(num) => self
        .store
        .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(num.stx.value.0))),
      AstExpr::LitStr(str_lit) => {
        let name = self.store.intern_name(str_lit.stx.value.clone());
        self.store.intern_type(TypeKind::StringLiteral(name))
      }
      AstExpr::LitBool(b) => self
        .store
        .intern_type(TypeKind::BooleanLiteral(b.stx.value)),
      AstExpr::LitNull(_) => prim.null,
      AstExpr::LitBigInt(value) => {
        let trimmed = value.stx.value.trim_end_matches('n');
        let parsed = trimmed
          .parse::<BigInt>()
          .unwrap_or_else(|_| BigInt::from(0u8));
        self.store.intern_type(TypeKind::BigIntLiteral(parsed))
      }
      AstExpr::LitArr(arr) => {
        let mut elems = Vec::new();
        for elem in arr.stx.elements.iter() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(v) => {
              elems.push(types_ts_interned::TupleElem {
                ty: self.const_assertion_type(v),
                optional: false,
                rest: false,
                readonly: true,
              })
            }
            parse_js::ast::expr::lit::LitArrElem::Rest(v) => {
              elems.push(types_ts_interned::TupleElem {
                ty: self.const_assertion_type(v),
                optional: false,
                rest: true,
                readonly: true,
              })
            }
            parse_js::ast::expr::lit::LitArrElem::Empty => {
              elems.push(types_ts_interned::TupleElem {
                ty: prim.undefined,
                optional: true,
                rest: false,
                readonly: true,
              })
            }
          }
        }
        self.store.intern_type(TypeKind::Tuple(elems))
      }
      AstExpr::LitObj(obj) => {
        let mut shape = Shape::new();
        for member in obj.stx.members.iter() {
          match &member.stx.typ {
            ObjMemberType::Valued { key, val } => {
              if let ClassOrObjKey::Direct(direct) = key {
                if let ClassOrObjVal::Prop(Some(value)) = val {
                  let prop_key = PropKey::String(self.store.intern_name(direct.stx.key.clone()));
                  let value_ty = self.const_assertion_type(value);
                  shape.properties.push(types_ts_interned::Property {
                    key: prop_key,
                    data: PropData {
                      ty: value_ty,
                      optional: false,
                      readonly: true,
                      accessibility: None,
                      is_method: false,
                      origin: None,
                      declared_on: None,
                    },
                  });
                }
              } else if let ClassOrObjVal::Prop(Some(expr)) = val {
                let _ = self.check_expr(expr);
              }
            }
            ObjMemberType::Shorthand { id } => {
              let key = PropKey::String(self.store.intern_name(id.stx.name.clone()));
              let ty = self
                .lookup(&id.stx.name)
                .map(|b| b.ty)
                .unwrap_or(prim.unknown);
              shape.properties.push(types_ts_interned::Property {
                key,
                data: PropData {
                  ty,
                  optional: false,
                  readonly: true,
                  accessibility: None,
                  is_method: false,
                  origin: None,
                  declared_on: None,
                },
              });
            }
            ObjMemberType::Rest { val } => {
              let _ = self.check_expr(val);
            }
          }
        }
        let shape_id = self.store.intern_shape(shape);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      AstExpr::TypeAssertion(assert) => {
        if assert.stx.const_assertion {
          self.const_assertion_type(&assert.stx.expression)
        } else if let Some(annotation) = assert.stx.type_annotation.as_ref() {
          self.lowerer.lower_type_expr(annotation)
        } else {
          self.check_expr(&assert.stx.expression)
        }
      }
      _ => self.check_expr(expr),
    };
    self.record_expr_type(expr.loc, ty);
    ty
  }

  fn member_type(&mut self, obj: TypeId, prop: &str) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(obj) {
      TypeKind::Ref { def, args } => self
        .ref_expander
        .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
        .map(|expanded| self.member_type(expanded, prop))
        .unwrap_or(prim.unknown),
      TypeKind::Callable { .. } if prop == "call" => {
        let sigs = callable_signatures(self.store.as_ref(), obj);
        if sigs.is_empty() {
          prim.unknown
        } else {
          self.build_call_method_type(sigs)
        }
      }
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for candidate in shape.properties.iter() {
          match &candidate.key {
            PropKey::String(name_id) => {
              if self.store.name(*name_id) == prop {
                return candidate.data.ty;
              }
            }
            PropKey::Number(num) => {
              if prop.parse::<i64>().ok() == Some(*num) {
                return candidate.data.ty;
              }
            }
            _ => {}
          }
        }
        if prop == "call" && !shape.call_signatures.is_empty() {
          return self.build_call_method_type(shape.call_signatures.clone());
        }
        shape
          .indexers
          .first()
          .map(|idx| idx.value_type)
          .unwrap_or(prim.unknown)
      }
      TypeKind::Union(members) => {
        let mut collected = Vec::new();
        for member in members {
          let ty = self.member_type(member, prop);
          if ty != prim.unknown {
            collected.push(ty);
          }
        }
        if collected.is_empty() {
          prim.unknown
        } else {
          self.store.union(collected)
        }
      }
      TypeKind::Intersection(members) => {
        let mut collected = Vec::new();
        for member in members {
          let ty = self.member_type(member, prop);
          if ty != prim.unknown {
            collected.push(ty);
          }
        }
        if collected.is_empty() {
          prim.unknown
        } else if collected.len() == 1 {
          collected[0]
        } else {
          self.store.intersection(collected)
        }
      }
      TypeKind::Tuple(elems) => elems.get(0).map(|e| e.ty).unwrap_or(prim.unknown),
      _ => prim.unknown,
    }
  }

  fn build_call_method_type(&self, sigs: Vec<SignatureId>) -> TypeId {
    let prim = self.store.primitive_ids();
    let mut overloads = Vec::new();
    for sig_id in sigs {
      let sig = self.store.signature(sig_id);
      let this_arg = sig.this_param.unwrap_or(prim.any);
      let mut params = Vec::with_capacity(sig.params.len() + 1);
      params.push(SigParam {
        name: None,
        ty: this_arg,
        optional: false,
        rest: false,
      });
      params.extend(sig.params.clone());
      let call_sig = Signature {
        params,
        ret: sig.ret,
        type_params: sig.type_params.clone(),
        this_param: None,
      };
      overloads.push(self.store.intern_signature(call_sig));
    }
    overloads.sort();
    overloads.dedup();
    self.store.intern_type(TypeKind::Callable { overloads })
  }

  fn array_literal_context(&self, expected: TypeId, arity: usize) -> Option<ArrayLiteralContext> {
    let mut queue: VecDeque<TypeId> = VecDeque::from([expected]);
    let mut seen = HashSet::new();
    let mut tuples: Vec<Vec<types_ts_interned::TupleElem>> = Vec::new();
    let mut arrays: Vec<TypeId> = Vec::new();

    while let Some(ty) = queue.pop_front() {
      if !seen.insert(ty) {
        continue;
      }
      match self.store.type_kind(ty) {
        TypeKind::Tuple(elems) => tuples.push(elems),
        TypeKind::Array { ty, .. } => arrays.push(ty),
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          for member in members {
            queue.push_back(member);
          }
        }
        TypeKind::Ref { def, args } => {
          if let Some(expanded) = self
            .ref_expander
            .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
          {
            queue.push_back(expanded);
          }
        }
        _ => {}
      }
    }

    if !tuples.is_empty() {
      let mut best: Option<((u32, usize), Vec<types_ts_interned::TupleElem>)> = None;
      for tuple in tuples.into_iter() {
        let len = tuple.len();
        let diff = len.abs_diff(arity) as u32;
        let key = (diff, len);
        let replace = match best.as_ref() {
          Some((best_key, _)) => key < *best_key,
          None => true,
        };
        if replace {
          best = Some((key, tuple));
        }
      }
      return best.map(|(_, elems)| ArrayLiteralContext::Tuple(elems));
    }

    arrays.into_iter().next().map(ArrayLiteralContext::Array)
  }

  fn expected_contains_primitive(&self, expected: TypeId, primitive: TypeId) -> bool {
    if expected == primitive {
      return true;
    }
    let mut queue: VecDeque<TypeId> = VecDeque::from([expected]);
    let mut seen = HashSet::new();
    while let Some(ty) = queue.pop_front() {
      if !seen.insert(ty) {
        continue;
      }
      if ty == primitive {
        return true;
      }
      match self.store.type_kind(ty) {
        TypeKind::Any => return true,
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          for member in members {
            queue.push_back(member);
          }
        }
        TypeKind::Ref { def, args } => {
          if let Some(expanded) = self
            .ref_expander
            .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
          {
            queue.push_back(expanded);
          }
        }
        _ => {}
      }
    }
    false
  }

  fn contextual_widen_container(&self, inferred: TypeId, expected: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let should_widen = self.expected_contains_primitive(expected, prim.number)
      || self.expected_contains_primitive(expected, prim.string)
      || self.expected_contains_primitive(expected, prim.boolean)
      || self.expected_contains_primitive(expected, prim.bigint);
    if should_widen {
      self.widen_object_prop(inferred)
    } else {
      inferred
    }
  }

  fn spread_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => {
        let members: Vec<_> = elems.into_iter().map(|e| e.ty).collect();
        if members.is_empty() {
          prim.unknown
        } else {
          self.store.union(members)
        }
      }
      TypeKind::Ref { def, args } => self
        .ref_expander
        .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
        .map(|expanded| self.spread_element_type(expanded))
        .unwrap_or(prim.unknown),
      _ => prim.unknown,
    }
  }

  fn array_literal_type(&mut self, arr: &Node<parse_js::ast::expr::lit::LitArrExpr>) -> TypeId {
    let prim = self.store.primitive_ids();
    let mut elems = Vec::new();
    for elem in arr.stx.elements.iter() {
      match elem {
        parse_js::ast::expr::lit::LitArrElem::Single(v) => elems.push(self.check_expr(v)),
        parse_js::ast::expr::lit::LitArrElem::Rest(v) => {
          let spread = self.check_expr(v);
          elems.push(self.spread_element_type(spread));
        }
        parse_js::ast::expr::lit::LitArrElem::Empty => {}
      }
    }
    let elem_ty = if elems.is_empty() {
      prim.unknown
    } else {
      self.store.union(elems)
    };
    let elem_ty = if self.widen_object_literals {
      self.widen_object_prop(elem_ty)
    } else {
      elem_ty
    };
    self.store.intern_type(TypeKind::Array {
      ty: elem_ty,
      readonly: false,
    })
  }

  fn array_literal_type_with_expected(
    &mut self,
    arr: &Node<parse_js::ast::expr::lit::LitArrExpr>,
    expected: TypeId,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    if arr
      .stx
      .elements
      .iter()
      .any(|e| !matches!(e, parse_js::ast::expr::lit::LitArrElem::Single(_)))
    {
      return self.array_literal_type(arr);
    }

    let elems: Vec<_> = arr
      .stx
      .elements
      .iter()
      .filter_map(|e| match e {
        parse_js::ast::expr::lit::LitArrElem::Single(v) => Some(v),
        _ => None,
      })
      .collect();
    let arity = elems.len();
    let Some(context) = self.array_literal_context(expected, arity) else {
      return self.array_literal_type(arr);
    };

    match context {
      ArrayLiteralContext::Tuple(expected_elems) => {
        let mut out = Vec::new();
        for (idx, expr) in elems.into_iter().enumerate() {
          let expected_elem = expected_elems
            .get(idx)
            .map(|e| e.ty)
            .unwrap_or(prim.unknown);
          let expr_ty = if expected_elem != prim.unknown {
            self.check_expr_with_expected(expr, expected_elem)
          } else {
            self.check_expr(expr)
          };
          let stored = if expected_elem != prim.unknown {
            self.contextual_widen_container(expr_ty, expected_elem)
          } else {
            self.widen_object_prop(expr_ty)
          };
          out.push(types_ts_interned::TupleElem {
            ty: stored,
            optional: false,
            rest: false,
            readonly: false,
          });
        }
        self.store.intern_type(TypeKind::Tuple(out))
      }
      ArrayLiteralContext::Array(expected_elem) => {
        let mut out = Vec::new();
        for expr in elems.into_iter() {
          let expr_ty = self.check_expr_with_expected(expr, expected_elem);
          let stored = self.contextual_widen_container(expr_ty, expected_elem);
          out.push(stored);
        }
        let elem_ty = if out.is_empty() {
          prim.unknown
        } else {
          self.store.union(out)
        };
        self.store.intern_type(TypeKind::Array {
          ty: elem_ty,
          readonly: false,
        })
      }
    }
  }

  fn object_literal_type(&mut self, obj: &Node<parse_js::ast::expr::lit::LitObjExpr>) -> TypeId {
    let mut shape = Shape::new();
    for member in obj.stx.members.iter() {
      match &member.stx.typ {
        ObjMemberType::Valued { key, val } => {
          let prop_key = match key {
            ClassOrObjKey::Direct(direct) => {
              PropKey::String(self.store.intern_name(direct.stx.key.clone()))
            }
            ClassOrObjKey::Computed(_) => continue,
          };
          if let ClassOrObjVal::Prop(Some(expr)) = val {
            let ty = self.check_expr(expr);
            let ty = if self.widen_object_literals {
              self.widen_object_prop(ty)
            } else {
              ty
            };
            shape.properties.push(types_ts_interned::Property {
              key: prop_key,
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
        }
        ObjMemberType::Shorthand { id } => {
          let key = PropKey::String(self.store.intern_name(id.stx.name.clone()));
          let ty = self
            .lookup(&id.stx.name)
            .map(|b| b.ty)
            .unwrap_or(self.store.primitive_ids().unknown);
          shape.properties.push(types_ts_interned::Property {
            key,
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
        ObjMemberType::Rest { val } => {
          let _ = self.check_expr(val);
        }
      }
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn object_literal_type_with_expected(
    &mut self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
    expected: TypeId,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let mut shape = Shape::new();
    for member in obj.stx.members.iter() {
      match &member.stx.typ {
        ObjMemberType::Valued { key, val } => {
          let name = match key {
            ClassOrObjKey::Direct(direct) => direct.stx.key.clone(),
            ClassOrObjKey::Computed(_) => continue,
          };
          let prop_key = PropKey::String(self.store.intern_name(name.clone()));
          let expected_prop = self.member_type(expected, &name);
          if let ClassOrObjVal::Prop(Some(expr)) = val {
            let expr_ty = if expected_prop != prim.unknown {
              self.check_expr_with_expected(expr, expected_prop)
            } else {
              self.check_expr(expr)
            };
            let ty = if expected_prop != prim.unknown {
              self.contextual_widen_container(expr_ty, expected_prop)
            } else if self.widen_object_literals {
              self.widen_object_prop(expr_ty)
            } else {
              expr_ty
            };
            shape.properties.push(types_ts_interned::Property {
              key: prop_key,
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
        }
        ObjMemberType::Shorthand { id } => {
          let name = id.stx.name.clone();
          let key = PropKey::String(self.store.intern_name(name.clone()));
          let value = self.lookup(&name).map(|b| b.ty).unwrap_or(prim.unknown);
          let expected_prop = self.member_type(expected, &name);
          let ty = if expected_prop != prim.unknown {
            self.contextual_widen_container(value, expected_prop)
          } else if self.widen_object_literals {
            self.widen_object_prop(value)
          } else {
            value
          };
          shape.properties.push(types_ts_interned::Property {
            key,
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
        ObjMemberType::Rest { val } => {
          let _ = self.check_expr(val);
        }
      }
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn widen_object_prop(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::NumberLiteral(_) => prim.number,
      TypeKind::StringLiteral(_) => prim.string,
      TypeKind::BooleanLiteral(_) => prim.boolean,
      TypeKind::BigIntLiteral(_) => prim.bigint,
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_prop(m))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_prop(m))
          .collect();
        self.store.intersection(mapped)
      }
      _ => ty,
    }
  }

  fn resolve_ident(&mut self, name: &str, expr: &Node<AstExpr>) -> TypeId {
    if let Some(binding) = self.lookup(name) {
      return binding.ty;
    }
    let mut range = loc_to_range(self.file, expr.loc);
    if range.start == range.end {
      let len = name.len() as u32;
      range.start = range.start.saturating_sub(len);
      range.end = range.start.saturating_add(len);
    }
    if std::env::var_os("DEBUG_RESOLVE_IDENT").is_some() {
      let mut scopes: Vec<(usize, usize, bool)> = self
        .scopes
        .iter()
        .enumerate()
        .map(|(idx, scope)| (idx, scope.bindings.len(), scope.bindings.contains_key(name)))
        .collect();
      scopes.reverse();
      let mut keys: Vec<String> = self
        .scopes
        .iter()
        .flat_map(|scope| scope.bindings.keys().cloned())
        .collect();
      keys.sort();
      keys.dedup();
      let preview: Vec<&str> = keys.iter().take(32).map(|s| s.as_str()).collect();
      eprintln!(
        "DEBUG_RESOLVE_IDENT: file={:?} name={:?} range={:?} scopes_rev={:?} keys={} preview={:?}",
        self.file,
        name,
        range,
        scopes,
        keys.len(),
        preview
      );
    }
    self.diagnostics.push(codes::UNKNOWN_IDENTIFIER.error(
      format!("unknown identifier `{}`", name),
      Span {
        file: self.file,
        range,
      },
    ));
    self.store.primitive_ids().unknown
  }

  fn check_unary(&mut self, op: OperatorName, arg: &Node<AstExpr>) -> TypeId {
    match op {
      OperatorName::LogicalNot => self.store.primitive_ids().boolean,
      OperatorName::UnaryPlus | OperatorName::UnaryNegation | OperatorName::BitwiseNot => {
        self.store.primitive_ids().number
      }
      OperatorName::Typeof => self.store.primitive_ids().string,
      OperatorName::Void => self.store.primitive_ids().undefined,
      _ => {
        let _ = self.check_expr(arg);
        self.store.primitive_ids().unknown
      }
    }
  }

  fn check_binary(
    &mut self,
    op: OperatorName,
    left: &Node<AstExpr>,
    right: &Node<AstExpr>,
  ) -> TypeId {
    if op.is_assignment() {
      return self.check_assignment(op, left, right);
    }
    let lty = self.check_expr(left);
    let rty = self.check_expr(right);
    match op {
      OperatorName::Addition => {
        let left_kind = self.store.type_kind(lty);
        let right_kind = self.store.type_kind(rty);
        if matches!(left_kind, TypeKind::String | TypeKind::StringLiteral(_))
          || matches!(right_kind, TypeKind::String | TypeKind::StringLiteral(_))
        {
          self.store.primitive_ids().string
        } else if matches!(left_kind, TypeKind::Number | TypeKind::NumberLiteral(_))
          && matches!(right_kind, TypeKind::Number | TypeKind::NumberLiteral(_))
        {
          self.store.primitive_ids().number
        } else {
          self.store.union(vec![lty, rty])
        }
      }
      OperatorName::Subtraction
      | OperatorName::Multiplication
      | OperatorName::Division
      | OperatorName::Exponentiation
      | OperatorName::Remainder => self.store.primitive_ids().number,
      OperatorName::LogicalAnd | OperatorName::LogicalOr | OperatorName::NullishCoalescing => {
        self.store.union(vec![lty, rty])
      }
      OperatorName::Equality
      | OperatorName::Inequality
      | OperatorName::StrictEquality
      | OperatorName::StrictInequality
      | OperatorName::LessThan
      | OperatorName::LessThanOrEqual
      | OperatorName::GreaterThan
      | OperatorName::GreaterThanOrEqual => self.store.primitive_ids().boolean,
      _ => self.store.union(vec![lty, rty]),
    }
  }

  fn check_assignment(
    &mut self,
    op: OperatorName,
    left: &Node<AstExpr>,
    right: &Node<AstExpr>,
  ) -> TypeId {
    match left.stx.as_ref() {
      AstExpr::Id(id) => {
        if let Some(binding) = self.lookup(&id.stx.name) {
          let value_ty = if matches!(op, OperatorName::Assignment) {
            self.check_expr_with_expected(right, binding.ty)
          } else {
            self.check_expr(right)
          };
          if !self.relate.is_assignable(value_ty, binding.ty) {
            self.diagnostics.push(codes::TYPE_MISMATCH.error(
              "assignment type mismatch",
              Span {
                file: self.file,
                range: loc_to_range(self.file, left.loc),
              },
            ));
          }
          self.insert_binding(id.stx.name.clone(), value_ty, binding.type_params);
          return value_ty;
        } else {
          let value_ty = self.check_expr(right);
          self.insert_binding(id.stx.name.clone(), value_ty, Vec::new());
          return value_ty;
        }
      }
      AstExpr::ArrPat(arr) => {
        let value_ty = self.check_expr(right);
        let span = loc_to_range(self.file, arr.loc);
        if let Some(pat) = self.index.pats.get(&span).copied() {
          let pat = unsafe { &*pat };
          self.bind_pattern(pat, value_ty);
        }
        return value_ty;
      }
      AstExpr::ObjPat(obj) => {
        let value_ty = self.check_expr(right);
        let span = loc_to_range(self.file, obj.loc);
        if let Some(pat) = self.index.pats.get(&span).copied() {
          let pat = unsafe { &*pat };
          self.bind_pattern(pat, value_ty);
        }
        return value_ty;
      }
      _ => {}
    }
    self.check_expr(right)
  }

  fn check_expr_with_expected(&mut self, expr: &Node<AstExpr>, expected: TypeId) -> TypeId {
    let expected = self.store.canon(expected);
    let prim = self.store.primitive_ids();
    if expected == prim.unknown {
      return self.check_expr(expr);
    }

    match expr.stx.as_ref() {
      AstExpr::LitObj(obj) => {
        let ty = self.object_literal_type_with_expected(obj, expected);
        self.record_expr_type(expr.loc, ty);
        ty
      }
      AstExpr::LitArr(arr) => {
        let ty = self.array_literal_type_with_expected(arr, expected);
        self.record_expr_type(expr.loc, ty);
        ty
      }
      AstExpr::ArrowFunc(_) | AstExpr::Func(_) if self.is_callable_like(expected) => {
        self.record_expr_type(expr.loc, expected);
        expected
      }
      _ => self.check_expr(expr),
    }
  }

  fn is_callable_like(&self, ty: TypeId) -> bool {
    match self.store.type_kind(ty) {
      TypeKind::Callable { .. } => true,
      TypeKind::Ref { def, args } => self
        .ref_expander
        .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
        .is_some_and(|expanded| {
          matches!(self.store.type_kind(expanded), TypeKind::Callable { .. })
        }),
      _ => false,
    }
  }

  fn refine_function_expr_with_expected(
    &mut self,
    func: &Node<Func>,
    expected: TypeId,
  ) -> Option<TypeId> {
    let expected_sig = self.first_callable_signature(expected)?;

    let saved_expected = self.expected_return;
    let saved_returns = std::mem::take(&mut self.return_types);

    self.expected_return = Some(expected_sig.ret);
    self.scopes.push(Scope::default());
    self.bind_params(func, &[], Some(&expected_sig));
    self.check_function_body(func);
    self.scopes.pop();

    let prim = self.store.primitive_ids();
    let inferred_ret = if self.return_types.is_empty() {
      prim.void
    } else {
      self.store.union(self.return_types.clone())
    };

    self.return_types = saved_returns;
    self.expected_return = saved_expected;

    let mut instantiated = expected_sig;
    instantiated.ret = inferred_ret;
    let sig_id = self.store.intern_signature(instantiated);
    Some(self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    }))
  }

  fn first_callable_signature(&self, ty: TypeId) -> Option<Signature> {
    match self.store.type_kind(ty) {
      TypeKind::Callable { overloads } => overloads.first().map(|sig| self.store.signature(*sig)),
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        shape
          .call_signatures
          .first()
          .map(|sig_id| self.store.signature(*sig_id))
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .iter()
        .copied()
        .find_map(|member| self.first_callable_signature(member)),
      TypeKind::Ref { def, args } => self
        .ref_expander
        .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
        .and_then(|expanded| self.first_callable_signature(expanded)),
      _ => None,
    }
  }

  fn bind_pattern(&mut self, pat: &Node<AstPat>, value: TypeId) {
    self.bind_pattern_with_type_params(pat, value, Vec::new());
  }

  fn bind_pattern_with_type_params(
    &mut self,
    pat: &Node<AstPat>,
    value: TypeId,
    type_params: Vec<TypeParamDecl>,
  ) {
    self.record_pat_type(pat.loc, value);
    match pat.stx.as_ref() {
      AstPat::Id(id) => {
        self.insert_binding(id.stx.name.clone(), value, type_params);
      }
      AstPat::Arr(arr) => self.bind_array_pattern(arr, value, type_params),
      AstPat::Obj(obj) => self.bind_object_pattern(obj, value, type_params),
      AstPat::AssignTarget(expr) => {
        let target_ty = self.check_expr(expr);
        if !self.relate.is_assignable(value, target_ty) {
          self.diagnostics.push(codes::TYPE_MISMATCH.error(
            "assignment type mismatch",
            Span {
              file: self.file,
              range: loc_to_range(self.file, pat.loc),
            },
          ));
        }
      }
    }
  }

  fn bind_array_pattern(
    &mut self,
    arr: &Node<ArrPat>,
    value: TypeId,
    type_params: Vec<TypeParamDecl>,
  ) {
    let prim = self.store.primitive_ids();
    let element_ty = match self.store.type_kind(value) {
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => elems.first().map(|e| e.ty).unwrap_or(prim.unknown),
      TypeKind::Any => prim.any,
      _ => prim.unknown,
    };
    for (idx, elem) in arr.stx.elements.iter().enumerate() {
      if let Some(elem) = elem {
        let mut target_ty = match self.store.type_kind(value) {
          TypeKind::Tuple(elems) => elems.get(idx).map(|e| e.ty).unwrap_or(element_ty),
          _ => element_ty,
        };
        if let Some(default) = &elem.default_value {
          let default_ty = self.check_expr(default);
          target_ty = self.store.union(vec![target_ty, default_ty]);
        }
        self.bind_pattern(&elem.target, target_ty);
      }
    }
    if let Some(rest) = &arr.stx.rest {
      let rest_ty = match self.store.type_kind(value) {
        TypeKind::Array { ty, readonly } => {
          self.store.intern_type(TypeKind::Array { ty, readonly })
        }
        TypeKind::Any => self.store.intern_type(TypeKind::Array {
          ty: prim.any,
          readonly: false,
        }),
        TypeKind::Tuple(elems) => {
          let elems: Vec<TypeId> = elems.into_iter().map(|e| e.ty).collect();
          let elem_ty = if elems.is_empty() {
            prim.unknown
          } else {
            self.store.union(elems)
          };
          self.store.intern_type(TypeKind::Array {
            ty: elem_ty,
            readonly: false,
          })
        }
        _ => self.store.intern_type(TypeKind::Array {
          ty: prim.unknown,
          readonly: false,
        }),
      };
      self.bind_pattern_with_type_params(rest, rest_ty, type_params.clone());
    }
  }

  fn bind_object_pattern(
    &mut self,
    obj: &Node<ObjPat>,
    value: TypeId,
    type_params: Vec<TypeParamDecl>,
  ) {
    let prim = self.store.primitive_ids();
    let value_is_any = matches!(self.store.type_kind(value), TypeKind::Any);
    let shape = match self.store.type_kind(value) {
      TypeKind::Object(obj_id) => Some(self.store.shape(self.store.object(obj_id).shape)),
      _ => None,
    };
    for prop in obj.stx.properties.iter() {
      let key_name = match &prop.stx.key {
        ClassOrObjKey::Direct(direct) => Some(direct.stx.key.clone()),
        ClassOrObjKey::Computed(_) => None,
      };
      let mut prop_ty = if value_is_any { prim.any } else { prim.unknown };
      if !value_is_any {
        if let Some(shape) = &shape {
          if let Some(key) = key_name.as_ref() {
            for candidate in shape.properties.iter() {
              let matches = match &candidate.key {
                PropKey::String(name) => self.store.name(*name) == *key,
                PropKey::Number(num) => num.to_string() == *key,
                _ => false,
              };
              if matches {
                prop_ty = candidate.data.ty;
                break;
              }
            }
            if prop_ty == prim.unknown {
              if let Some(idx) = shape.indexers.first() {
                prop_ty = idx.value_type;
              }
            }
          }
        }
      }
      if let Some(default) = &prop.stx.default_value {
        let default_ty = self.check_expr(default);
        prop_ty = self.store.union(vec![prop_ty, default_ty]);
      }
      self.bind_pattern(&prop.stx.target, prop_ty);
    }
    if let Some(rest) = &obj.stx.rest {
      self.bind_pattern_with_type_params(rest, value, type_params);
    }
  }

  fn base_type(&self, ty: TypeId) -> TypeId {
    match self.store.type_kind(ty) {
      TypeKind::BooleanLiteral(_) => self.store.primitive_ids().boolean,
      TypeKind::NumberLiteral(_) => self.store.primitive_ids().number,
      TypeKind::StringLiteral(_) => self.store.primitive_ids().string,
      TypeKind::BigIntLiteral(_) => self.store.primitive_ids().bigint,
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members.into_iter().map(|m| self.base_type(m)).collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members.into_iter().map(|m| self.base_type(m)).collect();
        self.store.intersection(mapped)
      }
      _ => ty,
    }
  }

  fn function_type(&mut self, func: &Node<Func>) -> TypeId {
    let mut type_params = Vec::new();
    let pushed_type_params = func.stx.type_parameters.is_some();
    if let Some(params) = func.stx.type_parameters.as_ref() {
      self.lowerer.push_type_param_scope();
      type_params = self.lower_type_params(params);
    }
    let params = func
      .stx
      .parameters
      .iter()
      .map(|p| {
        let name = match p.stx.pattern.stx.pat.stx.as_ref() {
          AstPat::Id(id) => Some(self.store.intern_name(id.stx.name.clone())),
          _ => None,
        };
        SigParam {
          name,
          ty: p
            .stx
            .type_annotation
            .as_ref()
            .map(|t| self.lowerer.lower_type_expr(t))
            .unwrap_or(self.store.primitive_ids().unknown),
          optional: p.stx.optional,
          rest: p.stx.rest,
        }
      })
      .collect::<Vec<_>>();
    let ret = func
      .stx
      .return_type
      .as_ref()
      .map(|t| self.lowerer.lower_type_expr(t))
      .unwrap_or(self.store.primitive_ids().unknown);
    if pushed_type_params {
      self.lowerer.pop_type_param_scope();
    }
    let sig = Signature {
      params,
      ret,
      type_params,
      this_param: None,
    };
    let sig_id = self.store.intern_signature(sig);
    let ty = self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    });
    ty
  }

  fn record_expr_type(&mut self, loc: Loc, ty: TypeId) {
    let range = loc_to_range(self.file, loc);
    if let Some(id) = self.expr_map.get(&range) {
      if let Some(slot) = self.expr_types.get_mut(id.0 as usize) {
        *slot = ty;
      }
    }
  }

  fn record_pat_type(&mut self, loc: Loc, ty: TypeId) {
    let range = loc_to_range(self.file, loc);
    if let Some(id) = self.pat_map.get(&range) {
      if let Some(slot) = self.pat_types.get_mut(id.0 as usize) {
        *slot = ty;
      }
    }
  }

  fn contextual_arg_type(&self, arg_ty: TypeId, param_ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match (self.store.type_kind(arg_ty), self.store.type_kind(param_ty)) {
      (TypeKind::NumberLiteral(_), TypeKind::Number) => prim.number,
      (TypeKind::StringLiteral(_), TypeKind::String) => prim.string,
      (TypeKind::BooleanLiteral(_), TypeKind::Boolean) => prim.boolean,
      (TypeKind::Union(members), TypeKind::Number) => {
        if members
          .iter()
          .all(|m| matches!(self.store.type_kind(*m), TypeKind::NumberLiteral(_)))
        {
          prim.number
        } else {
          arg_ty
        }
      }
      (TypeKind::Union(members), TypeKind::String) => {
        if members
          .iter()
          .all(|m| matches!(self.store.type_kind(*m), TypeKind::StringLiteral(_)))
        {
          prim.string
        } else {
          arg_ty
        }
      }
      (TypeKind::Union(members), TypeKind::Boolean) => {
        if members
          .iter()
          .all(|m| matches!(self.store.type_kind(*m), TypeKind::BooleanLiteral(_)))
        {
          prim.boolean
        } else {
          arg_ty
        }
      }
      _ => arg_ty,
    }
  }

  fn expand_for_props(&self, ty: TypeId) -> TypeId {
    let Some(expander) = self.ref_expander else {
      return ty;
    };
    match self.store.type_kind(ty) {
      TypeKind::Ref { .. } | TypeKind::IndexedAccess { .. } => {}
      _ => return ty,
    }
    struct Adapter<'a> {
      hook: &'a dyn types_ts_interned::RelateTypeExpander,
    }

    impl<'a> TypeExpander for Adapter<'a> {
      fn expand(
        &self,
        store: &TypeStore,
        def: types_ts_interned::DefId,
        args: &[TypeId],
      ) -> Option<ExpandedType> {
        self
          .hook
          .expand_ref(store, def, args)
          .map(|ty| ExpandedType {
            params: Vec::new(),
            ty,
          })
      }
    }

    let adapter = Adapter { hook: expander };
    let mut evaluator = TypeEvaluator::new(Arc::clone(&self.store), &adapter);
    evaluator.evaluate(ty)
  }

  fn has_excess_properties(
    &self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
    target: TypeId,
  ) -> bool {
    let mut props = HashSet::new();
    for member in obj.stx.members.iter() {
      match &member.stx.typ {
        ObjMemberType::Valued { key, .. } => {
          if let ClassOrObjKey::Direct(direct) = key {
            props.insert(direct.stx.key.clone());
          }
        }
        ObjMemberType::Shorthand { id } => {
          props.insert(id.stx.name.clone());
        }
        ObjMemberType::Rest { .. } => return false,
      }
    }
    !self.type_accepts_props(target, &props)
  }

  fn type_accepts_props(&self, target: TypeId, props: &HashSet<String>) -> bool {
    let expanded = self.expand_for_props(target);
    if expanded != target {
      return self.type_accepts_props(expanded, props);
    }
    match self.store.type_kind(target) {
      TypeKind::Union(members) => {
        let mut saw_object = false;
        for member in members {
          match self.store.type_kind(member) {
            TypeKind::Object(_) | TypeKind::Union(_) | TypeKind::Intersection(_) => {
              saw_object = true;
              if self.type_accepts_props(member, props) {
                return true;
              }
            }
            TypeKind::Ref { def, args } => {
              if let Some(expanded) = self
                .ref_expander
                .and_then(|exp| exp.expand_ref(self.store.as_ref(), def, &args))
              {
                saw_object = true;
                if self.type_accepts_props(expanded, props) {
                  return true;
                }
              }
            }
            _ => {}
          }
        }
        !saw_object
      }
      TypeKind::Intersection(members) => members.iter().all(|m| self.type_accepts_props(*m, props)),
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        if !shape.indexers.is_empty() {
          return true;
        }
        let mut allowed: HashSet<String> = HashSet::new();
        for prop in shape.properties.iter() {
          match prop.key {
            PropKey::String(name) | PropKey::Symbol(name) => {
              allowed.insert(self.store.name(name));
            }
            PropKey::Number(num) => {
              allowed.insert(num.to_string());
            }
          }
        }
        props.iter().all(|p| allowed.contains(p))
      }
      TypeKind::Mapped(_) => true,
      TypeKind::Ref { def, args } => self
        .ref_expander
        .and_then(|exp| exp.expand_ref(self.store.as_ref(), def, &args))
        .map(|expanded| self.type_accepts_props(expanded, props))
        .unwrap_or(true),
      _ => true,
    }
  }

  fn is_mapped_type(&self, ty: TypeId) -> bool {
    match self.store.type_kind(ty) {
      TypeKind::Mapped(_) => true,
      TypeKind::Ref { def, args } => self
        .ref_expander
        .and_then(|exp| exp.expand_ref(self.store.as_ref(), def, &args))
        .map(|expanded| self.is_mapped_type(expanded))
        .unwrap_or(false),
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .iter()
        .copied()
        .any(|member| self.is_mapped_type(member)),
      TypeKind::IndexedAccess { .. } => {
        let expanded = self.expand_for_props(ty);
        expanded != ty && self.is_mapped_type(expanded)
      }
      _ => false,
    }
  }

  fn check_assignable(&mut self, expr: &Node<AstExpr>, src: TypeId, dst: TypeId) {
    let prim = self.store.primitive_ids();
    if matches!(self.store.type_kind(src), TypeKind::Any | TypeKind::Unknown)
      || matches!(self.store.type_kind(dst), TypeKind::Any | TypeKind::Unknown)
    {
      return;
    }
    if let TypeKind::Array { ty, .. } = self.store.type_kind(src) {
      if matches!(self.store.type_kind(ty), TypeKind::Unknown) {
        return;
      }
    }
    if matches!(self.store.type_kind(src), TypeKind::Conditional { .. })
      || matches!(self.store.type_kind(dst), TypeKind::Conditional { .. })
    {
      return;
    }
    if self.is_mapped_type(dst) {
      return;
    }
    if let AstExpr::LitObj(obj) = expr.stx.as_ref() {
      if self.has_excess_properties(obj, dst) {
        self.diagnostics.push(codes::EXCESS_PROPERTY.error(
          "excess property",
          Span {
            file: self.file,
            range: loc_to_range(self.file, expr.loc),
          },
        ));
        return;
      }
    }
    if self.relate.is_assignable(src, dst) {
      return;
    }
    if std::env::var("DEBUG_TYPE_MISMATCH").is_ok() {
      eprintln!(
        "DEBUG_TYPE_MISMATCH src={} {:?} dst={} {:?}",
        TypeDisplay::new(self.store.as_ref(), src),
        self.store.type_kind(src),
        TypeDisplay::new(self.store.as_ref(), dst),
        self.store.type_kind(dst)
      );
    }
    let mut range = loc_to_range(self.file, expr.loc);
    if let AstExpr::LitObj(obj) = expr.stx.as_ref() {
      for member in obj.stx.members.iter() {
        let (prop, key_loc) = match &member.stx.typ {
          ObjMemberType::Valued {
            key: ClassOrObjKey::Direct(key),
            ..
          } => (key.stx.key.clone(), Some(key.loc)),
          ObjMemberType::Shorthand { id } => (id.stx.name.clone(), Some(id.loc)),
          _ => continue,
        };
        let prop_src = self.member_type(src, &prop);
        let prop_dst = self.member_type(dst, &prop);
        if prop_src == prim.unknown || prop_dst == prim.unknown {
          continue;
        }
        if !self.relate.is_assignable(prop_src, prop_dst) {
          if let Some(loc) = key_loc {
            let key_range = loc_to_range(self.file, loc);
            range = TextRange::new(
              key_range.start,
              key_range.start.saturating_add(prop.len() as u32),
            );
          }
          break;
        }
      }
    }

    self.diagnostics.push(codes::TYPE_MISMATCH.error(
      "type mismatch",
      Span {
        file: self.file,
        range,
      },
    ));
  }
}

fn contains_range(outer: TextRange, inner: TextRange) -> bool {
  inner.start >= outer.start && inner.end <= outer.end
}

fn ranges_overlap(a: TextRange, b: TextRange) -> bool {
  a.start < b.end && b.start < a.end
}

fn span_for_stmt_list(stmts: &[Node<Stmt>], file: FileId) -> Option<TextRange> {
  let mut start: Option<u32> = None;
  let mut end: Option<u32> = None;
  for stmt in stmts {
    let range = loc_to_range(file, stmt.loc);
    start = Some(start.map_or(range.start, |s| s.min(range.start)));
    end = Some(end.map_or(range.end, |e| e.max(range.end)));
  }
  start.zip(end).map(|(s, e)| TextRange::new(s, e))
}

fn body_range(body: &Body) -> TextRange {
  let mut start = u32::MAX;
  let mut end = 0u32;
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
    match body.kind {
      BodyKind::Class => TextRange::new(0, 0),
      _ => body.span,
    }
  } else {
    TextRange::new(start, end)
  }
}

fn loc_to_range(_file: FileId, loc: Loc) -> TextRange {
  let (range, _) = loc.to_diagnostics_range_with_note();
  TextRange::new(range.start, range.end)
}

/// Flow-sensitive body checker built directly on `hir-js` bodies. This is a
/// lightweight, statement-level analysis that uses a CFG plus a simple lattice
/// of variable environments to drive narrowing.
pub fn check_body_with_env(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  _source: &str,
  store: Arc<TypeStore>,
  initial: &HashMap<NameId, TypeId>,
  relate: RelateCtx,
  ref_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> BodyCheckResult {
  check_body_with_env_with_bindings(
    body_id,
    body,
    names,
    file,
    _source,
    store,
    initial,
    None,
    relate,
    ref_expander,
  )
}

pub fn check_body_with_env_with_bindings(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  _source: &str,
  store: Arc<TypeStore>,
  initial: &HashMap<NameId, TypeId>,
  flow_bindings: Option<&FlowBindings>,
  relate: RelateCtx,
  ref_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> BodyCheckResult {
  let mut checker = FlowBodyChecker::new(
    body_id,
    body,
    names,
    Arc::clone(&store),
    file,
    initial,
    flow_bindings,
    relate,
    ref_expander,
  );
  checker.run();
  codes::normalize_diagnostics(&mut checker.diagnostics);
  checker.into_result()
}

enum Reference {
  Ident {
    name: FlowBindingId,
    ty: TypeId,
  },
  Member {
    base: FlowBindingId,
    prop: String,
    base_ty: TypeId,
    prop_ty: TypeId,
  },
}

impl Reference {
  fn target(&self) -> FlowBindingId {
    match self {
      Reference::Ident { name, .. } => *name,
      Reference::Member { base, .. } => *base,
    }
  }

  fn target_ty(&self) -> TypeId {
    match self {
      Reference::Ident { ty, .. } => *ty,
      Reference::Member { base_ty, .. } => *base_ty,
    }
  }

  fn value_ty(&self) -> TypeId {
    match self {
      Reference::Ident { ty, .. } => *ty,
      Reference::Member { prop_ty, .. } => *prop_ty,
    }
  }
}

struct FlowBodyChecker<'a> {
  body_id: BodyId,
  body: &'a Body,
  names: &'a NameInterner,
  store: Arc<TypeStore>,
  file: FileId,
  relate: RelateCtx<'a>,
  expr_types: Vec<TypeId>,
  pat_types: Vec<TypeId>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
  diagnostics: Vec<Diagnostic>,
  reported_unassigned: HashSet<ExprId>,
  return_types: Vec<TypeId>,
  return_indices: HashMap<StmtId, usize>,
  widen_object_literals: bool,
  ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
  initial: HashMap<FlowBindingId, TypeId>,
  param_bindings: HashSet<BindingKey>,
  bindings: BindingTable,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BindingMode {
  Declare,
  Assign,
}

struct OptionalChainInfo {
  base: FlowBindingId,
  base_ty: TypeId,
  result_ty: Option<TypeId>,
}

enum SwitchDiscriminant {
  Ident {
    name: FlowBindingId,
    ty: TypeId,
  },
  Member {
    name: FlowBindingId,
    prop: String,
    ty: TypeId,
  },
  Typeof {
    name: FlowBindingId,
    ty: TypeId,
  },
}

impl SwitchDiscriminant {
  fn ty(&self) -> TypeId {
    match self {
      SwitchDiscriminant::Ident { ty, .. }
      | SwitchDiscriminant::Member { ty, .. }
      | SwitchDiscriminant::Typeof { ty, .. } => *ty,
    }
  }

  fn name(&self) -> FlowBindingId {
    match self {
      SwitchDiscriminant::Ident { name, .. }
      | SwitchDiscriminant::Member { name, .. }
      | SwitchDiscriminant::Typeof { name, .. } => *name,
    }
  }
}

#[derive(Default)]
struct BindingTable {
  expr_bindings: HashMap<ExprId, BindingKey>,
  pat_bindings: HashMap<PatId, BindingKey>,
  param_bindings: HashSet<BindingKey>,
  flow_ids: HashMap<BindingKey, FlowBindingId>,
  flow_to_binding: HashMap<FlowBindingId, BindingKey>,
  next_flow_id: u64,
}

impl BindingTable {
  fn binding_key_for_expr(&self, expr: ExprId) -> Option<BindingKey> {
    self.expr_bindings.get(&expr).copied()
  }

  fn binding_key_for_pat(&self, pat: PatId) -> Option<BindingKey> {
    self.pat_bindings.get(&pat).copied()
  }

  fn binding_for_expr(&self, expr: ExprId) -> Option<FlowBindingId> {
    self.flow_binding_for_expr(expr)
  }

  fn binding_for_pat(&self, pat: PatId) -> Option<FlowBindingId> {
    self.flow_binding_for_pat(pat)
  }

  fn set_flow_binding(&mut self, binding: BindingKey, id: FlowBindingId) -> FlowBindingId {
    if let Some(existing) = self.flow_ids.get(&binding) {
      if *existing == id {
        return id;
      }
      self.flow_to_binding.remove(existing);
    }
    if let Some(previous_binding) = self.flow_to_binding.insert(id, binding) {
      if previous_binding != binding {
        self.flow_ids.remove(&previous_binding);
      }
    }
    self.flow_ids.insert(binding, id);
    id
  }

  fn ensure_flow_binding(&mut self, binding: BindingKey) -> FlowBindingId {
    if let Some(existing) = self.flow_ids.get(&binding) {
      return *existing;
    }
    let mut id = SymbolId(self.next_flow_id);
    self.next_flow_id += 1;
    while self.flow_to_binding.contains_key(&id) {
      id = SymbolId(self.next_flow_id);
      self.next_flow_id += 1;
    }
    self.set_flow_binding(binding, id)
  }

  fn flow_binding_for_key(&self, binding: BindingKey) -> Option<FlowBindingId> {
    self.flow_ids.get(&binding).copied()
  }

  fn flow_binding_for_expr(&self, expr: ExprId) -> Option<FlowBindingId> {
    self
      .expr_bindings
      .get(&expr)
      .and_then(|b| self.flow_ids.get(b))
      .copied()
  }

  fn flow_binding_for_pat(&self, pat: PatId) -> Option<FlowBindingId> {
    self
      .pat_bindings
      .get(&pat)
      .and_then(|b| self.flow_ids.get(b))
      .copied()
  }

  fn binding_for_flow(&self, id: FlowBindingId) -> Option<BindingKey> {
    self.flow_to_binding.get(&id).copied()
  }

  fn flow_binding_for_external(&mut self, name: NameId) -> FlowBindingId {
    self.ensure_flow_binding(BindingKey::External(name))
  }
}

struct BindingCollector<'a> {
  body: &'a Body,
  scopes: Vec<HashMap<NameId, BindingKey>>,
  table: BindingTable,
  visited_stmts: HashSet<StmtId>,
  flow_bindings: Option<&'a FlowBindings>,
}

impl<'a> BindingCollector<'a> {
  fn collect(body: &'a Body, flow_bindings: Option<&'a FlowBindings>) -> BindingTable {
    let mut collector = BindingCollector {
      body,
      scopes: vec![HashMap::new()],
      table: BindingTable::default(),
      visited_stmts: HashSet::new(),
      flow_bindings,
    };
    collector.collect_params();
    let roots = if !body.root_stmts.is_empty() {
      body.root_stmts.clone()
    } else {
      (0..body.stmts.len() as u32).map(StmtId).collect()
    };
    for stmt in roots {
      collector.visit_stmt(stmt);
    }
    collector.table
  }

  fn collect_params(&mut self) {
    if let Some(function) = self.body.function.as_ref() {
      for param in function.params.iter() {
        self.declare_pat(param.pat, true, false);
        if let Some(default) = param.default {
          self.visit_expr(default);
        }
      }
    }
  }

  fn insert_binding(
    &mut self,
    name: NameId,
    pat: PatId,
    is_param: bool,
    hoist: bool,
    flow_binding: Option<FlowBindingId>,
  ) {
    let target_scope = if hoist {
      self
        .scopes
        .first_mut()
        .expect("binding collector always has a root scope")
    } else {
      self
        .scopes
        .last_mut()
        .expect("binding collector always has a scope")
    };
    // Hoisted `var` declarations share the function-scoped binding with
    // parameters and other `var`s. Reuse the existing binding if present so
    // flow facts accumulate on the same symbol.
    if let Some(existing) = target_scope.get(&name).copied() {
      self.table.pat_bindings.insert(pat, existing);
      if is_param {
        self.table.param_bindings.insert(existing);
      }
      if let Some(id) = flow_binding {
        self.table.set_flow_binding(existing, id);
      } else {
        self.table.ensure_flow_binding(existing);
      }
      return;
    }

    let key = BindingKey::Local { pat, name };
    self.table.pat_bindings.insert(pat, key);
    if is_param {
      self.table.param_bindings.insert(key);
    }
    if let Some(id) = flow_binding {
      self.table.set_flow_binding(key, id);
    } else {
      self.table.ensure_flow_binding(key);
    }
    target_scope.insert(name, key);
  }

  fn declare_pat(&mut self, pat_id: PatId, is_param: bool, hoist: bool) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => self.insert_binding(
        *name,
        pat_id,
        is_param,
        hoist,
        self
          .flow_bindings
          .and_then(|bindings| bindings.binding_for_pat(pat_id)),
      ),
      PatKind::Assign {
        target,
        default_value,
      } => {
        self.declare_pat(*target, is_param, hoist);
        self.visit_expr(*default_value);
      }
      PatKind::Rest(inner) => self.declare_pat(**inner, is_param, hoist),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.declare_pat(elem.pat, is_param, hoist);
          if let Some(default) = elem.default_value {
            self.visit_expr(default);
          }
        }
        if let Some(rest) = arr.rest {
          self.declare_pat(rest, is_param, hoist);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.declare_pat(prop.value, is_param, hoist);
          if let Some(default) = prop.default_value {
            self.visit_expr(default);
          }
          if let ObjectKey::Computed(expr) = &prop.key {
            self.visit_expr(*expr);
          }
        }
        if let Some(rest) = obj.rest {
          self.declare_pat(rest, is_param, hoist);
        }
      }
      PatKind::AssignTarget(expr) => self.visit_expr(*expr),
    }
  }

  fn resolve_binding(&mut self, name: NameId) -> BindingKey {
    for scope in self.scopes.iter().rev() {
      if let Some(binding) = scope.get(&name) {
        let binding = *binding;
        self.table.ensure_flow_binding(binding);
        return binding;
      }
    }
    let binding = BindingKey::External(name);
    self.table.ensure_flow_binding(binding);
    binding
  }

  fn visit_stmt(&mut self, stmt_id: StmtId) {
    if !self.visited_stmts.insert(stmt_id) {
      return;
    }
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    match &stmt.kind {
      StmtKind::Expr(expr) => self.visit_expr(*expr),
      StmtKind::Decl(_) => {}
      StmtKind::Return(expr) => {
        if let Some(expr) = expr {
          self.visit_expr(*expr);
        }
      }
      StmtKind::Block(stmts) => {
        self.push_scope();
        for stmt in stmts.iter() {
          self.visit_stmt(*stmt);
        }
        self.pop_scope();
      }
      StmtKind::If {
        test,
        consequent,
        alternate,
      } => {
        self.visit_expr(*test);
        self.push_scope();
        self.visit_stmt(*consequent);
        self.pop_scope();
        if let Some(alt) = alternate {
          self.push_scope();
          self.visit_stmt(*alt);
          self.pop_scope();
        }
      }
      StmtKind::While { test, body } => {
        self.visit_expr(*test);
        self.push_scope();
        self.visit_stmt(*body);
        self.pop_scope();
      }
      StmtKind::DoWhile { test, body } => {
        self.push_scope();
        self.visit_stmt(*body);
        self.pop_scope();
        self.visit_expr(*test);
      }
      StmtKind::For {
        init,
        test,
        update,
        body,
      } => {
        self.push_scope();
        if let Some(init) = init {
          match init {
            ForInit::Expr(expr) => self.visit_expr(*expr),
            ForInit::Var(var) => self.visit_var_decl(var),
          }
        }
        if let Some(test) = test {
          self.visit_expr(*test);
        }
        if let Some(update) = update {
          self.visit_expr(*update);
        }
        self.visit_stmt(*body);
        self.pop_scope();
      }
      StmtKind::ForIn {
        left, right, body, ..
      } => {
        self.push_scope();
        match left {
          ForHead::Pat(pat) => self.declare_pat(*pat, false, false),
          ForHead::Var(var) => self.visit_var_decl(var),
        }
        self.visit_expr(*right);
        self.visit_stmt(*body);
        self.pop_scope();
      }
      StmtKind::Switch {
        discriminant,
        cases,
        ..
      } => {
        self.visit_expr(*discriminant);
        self.push_scope();
        for case in cases.iter() {
          if let Some(test) = case.test {
            self.visit_expr(test);
          }
          for stmt in case.consequent.iter() {
            self.visit_stmt(*stmt);
          }
        }
        self.pop_scope();
      }
      StmtKind::Try {
        block,
        catch,
        finally_block,
      } => {
        self.push_scope();
        self.visit_stmt(*block);
        self.pop_scope();
        if let Some(catch) = catch {
          self.push_scope();
          if let Some(param) = catch.param {
            self.declare_pat(param, false, false);
          }
          self.visit_stmt(catch.body);
          self.pop_scope();
        }
        if let Some(finally_block) = finally_block {
          self.push_scope();
          self.visit_stmt(*finally_block);
          self.pop_scope();
        }
      }
      StmtKind::Throw(expr) => self.visit_expr(*expr),
      StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Empty => {}
      StmtKind::Var(decl) => self.visit_var_decl(decl),
      StmtKind::Labeled { body, .. } => self.visit_stmt(*body),
      StmtKind::With { object, body } => {
        self.visit_expr(*object);
        self.push_scope();
        self.visit_stmt(*body);
        self.pop_scope();
      }
    }
  }

  fn visit_var_decl(&mut self, decl: &HirVarDecl) {
    let hoist = matches!(decl.kind, hir_js::VarDeclKind::Var);
    for declarator in decl.declarators.iter() {
      self.declare_pat(declarator.pat, false, hoist);
      if let Some(init) = declarator.init {
        self.visit_expr(init);
      }
    }
  }

  fn visit_expr(&mut self, expr_id: ExprId) {
    let expr = &self.body.exprs[expr_id.0 as usize];
    match &expr.kind {
      ExprKind::Ident(name) => {
        let binding = self.resolve_binding(*name);
        self.table.expr_bindings.insert(expr_id, binding);
        if let Some(id) = self
          .flow_bindings
          .and_then(|bindings| bindings.binding_for_expr(expr_id))
        {
          self.table.set_flow_binding(binding, id);
        }
      }
      ExprKind::Unary { expr, .. } => self.visit_expr(*expr),
      ExprKind::Update { expr, .. } => self.visit_expr(*expr),
      ExprKind::Binary { left, right, .. } => {
        self.visit_expr(*left);
        self.visit_expr(*right);
      }
      ExprKind::Assignment { target, value, .. } => {
        self.visit_pat(*target);
        self.visit_expr(*value);
      }
      ExprKind::Call(call) => {
        self.visit_expr(call.callee);
        for arg in call.args.iter() {
          self.visit_expr(arg.expr);
        }
      }
      ExprKind::Member(mem) => {
        self.visit_expr(mem.object);
        if let ObjectKey::Computed(expr) = &mem.property {
          self.visit_expr(*expr);
        }
      }
      ExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => {
        self.visit_expr(*test);
        self.visit_expr(*consequent);
        self.visit_expr(*alternate);
      }
      ExprKind::Array(arr) => {
        for elem in arr.elements.iter() {
          match elem {
            ArrayElement::Expr(expr) | ArrayElement::Spread(expr) => self.visit_expr(*expr),
            ArrayElement::Empty => {}
          }
        }
      }
      ExprKind::Object(obj) => {
        for prop in obj.properties.iter() {
          match prop {
            ObjectProperty::KeyValue { key, value, .. } => {
              self.visit_expr(*value);
              if let ObjectKey::Computed(expr) = key {
                self.visit_expr(*expr);
              }
            }
            ObjectProperty::Getter { body, key } | ObjectProperty::Setter { body, key } => {
              if let ObjectKey::Computed(expr) = key {
                self.visit_expr(*expr);
              }
              self.visit_body(*body);
            }
            ObjectProperty::Spread(expr) => self.visit_expr(*expr),
          }
        }
      }
      ExprKind::Template(template) => {
        for span in template.spans.iter() {
          self.visit_expr(span.expr);
        }
      }
      ExprKind::TaggedTemplate { tag, template } => {
        self.visit_expr(*tag);
        for span in template.spans.iter() {
          self.visit_expr(span.expr);
        }
      }
      ExprKind::Await { expr } => self.visit_expr(*expr),
      ExprKind::Yield { expr, .. } => {
        if let Some(expr) = expr {
          self.visit_expr(*expr);
        }
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr, .. } => self.visit_expr(*expr),
      ExprKind::ImportCall {
        argument,
        attributes,
      } => {
        self.visit_expr(*argument);
        if let Some(attrs) = attributes {
          self.visit_expr(*attrs);
        }
      }
      ExprKind::Literal(_)
      | ExprKind::Missing
      | ExprKind::This
      | ExprKind::Super
      | ExprKind::FunctionExpr { .. }
      | ExprKind::ClassExpr { .. }
      | ExprKind::ImportMeta
      | ExprKind::NewTarget
      | ExprKind::Jsx(_) => {}
    }
  }

  fn visit_body(&mut self, _body_id: BodyId) {
    // Nested bodies are checked separately; nothing to do here.
  }

  fn visit_pat(&mut self, pat_id: PatId) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => {
        let binding = self.resolve_binding(*name);
        self.table.pat_bindings.entry(pat_id).or_insert(binding);
      }
      PatKind::Assign {
        target,
        default_value,
      } => {
        self.visit_pat(*target);
        self.visit_expr(*default_value);
      }
      PatKind::Rest(inner) => self.visit_pat(**inner),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.visit_pat(elem.pat);
          if let Some(default) = elem.default_value {
            self.visit_expr(default);
          }
        }
        if let Some(rest) = arr.rest {
          self.visit_pat(rest);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.visit_pat(prop.value);
          if let Some(default) = prop.default_value {
            self.visit_expr(default);
          }
          if let ObjectKey::Computed(expr) = &prop.key {
            self.visit_expr(*expr);
          }
        }
        if let Some(rest) = obj.rest {
          self.visit_pat(rest);
        }
      }
      PatKind::AssignTarget(expr) => self.visit_expr(*expr),
    }
  }

  fn push_scope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  fn pop_scope(&mut self) {
    self.scopes.pop();
  }
}

impl<'a> FlowBodyChecker<'a> {
  fn new(
    body_id: BodyId,
    body: &'a Body,
    names: &'a NameInterner,
    store: Arc<TypeStore>,
    file: FileId,
    initial: &HashMap<NameId, TypeId>,
    flow_bindings: Option<&'a FlowBindings>,
    relate: RelateCtx<'a>,
    ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
  ) -> Self {
    let prim = store.primitive_ids();
    let expr_types = vec![prim.unknown; body.exprs.len()];
    let mut pat_types = vec![prim.unknown; body.pats.len()];
    for (idx, pat) in body.pats.iter().enumerate() {
      if let PatKind::Ident(name) = pat.kind {
        if let Some(ty) = initial.get(&name) {
          pat_types[idx] = *ty;
        }
      }
    }
    let mut bindings = BindingCollector::collect(body, flow_bindings);
    let mut initial_flow = HashMap::new();
    for (name, ty) in initial.iter() {
      let id = bindings
        .param_bindings
        .iter()
        .find(|b| matches!(b, BindingKey::Local { name: n, .. } if *n == *name))
        .and_then(|b| bindings.flow_binding_for_key(*b))
        .unwrap_or_else(|| bindings.flow_binding_for_external(*name));
      initial_flow.insert(id, *ty);
    }

    let mut returns: Vec<(StmtId, u32)> = body
      .stmts
      .iter()
      .enumerate()
      .filter_map(|(idx, stmt)| {
        if matches!(stmt.kind, StmtKind::Return(_)) {
          Some((StmtId(idx as u32), stmt.span.start))
        } else {
          None
        }
      })
      .collect();
    returns.sort_by_key(|(_, start)| *start);
    let mut return_indices = HashMap::new();
    let mut return_types = Vec::new();
    for (idx, (stmt_id, _)) in returns.into_iter().enumerate() {
      return_indices.insert(stmt_id, idx);
      return_types.push(prim.unknown);
    }

    let expr_spans: Vec<TextRange> = body.exprs.iter().map(|e| e.span).collect();
    let pat_spans: Vec<TextRange> = body.pats.iter().map(|p| p.span).collect();
    Self {
      body_id,
      body,
      names,
      store,
      file,
      relate,
      expr_types,
      pat_types,
      expr_spans,
      pat_spans,
      diagnostics: Vec::new(),
      reported_unassigned: HashSet::new(),
      return_types,
      return_indices,
      widen_object_literals: true,
      ref_expander,
      initial: initial_flow,
      param_bindings: bindings.param_bindings.clone(),
      bindings,
    }
  }

  fn into_result(self) -> BodyCheckResult {
    BodyCheckResult {
      body: self.body_id,
      expr_types: self.expr_types,
      pat_types: self.pat_types,
      expr_spans: self.expr_spans,
      pat_spans: self.pat_spans,
      diagnostics: self.diagnostics,
      return_types: self.return_types,
    }
  }

  fn run(&mut self) {
    let cfg = ControlFlowGraph::from_body(self.body);
    let mut in_envs: Vec<Option<Env>> = vec![None; cfg.blocks.len()];
    let mut initial_env: Vec<(FlowBindingId, BindingKey, TypeId)> = Vec::new();
    for (id, ty) in self.initial.iter() {
      if let Some(key) = self.bindings.binding_for_flow(*id) {
        initial_env.push((*id, key, *ty));
      }
    }
    for binding in self.param_bindings.iter() {
      if let Some(id) = self.bindings.flow_binding_for_key(*binding) {
        initial_env.push((id, *binding, self.binding_type(*binding)));
      }
    }
    in_envs[cfg.entry.0] = Some(Env::with_initial(&initial_env));
    let mut worklist: VecDeque<BlockId> = VecDeque::new();
    worklist.push_back(cfg.entry);

    while let Some(block_id) = worklist.pop_front() {
      let env = match in_envs[block_id.0].clone() {
        Some(env) => env,
        None => continue,
      };
      let outgoing = self.process_block(block_id, env, &cfg);
      for (succ, out_env) in outgoing {
        if let Some(existing) = in_envs[succ.0].as_mut() {
          if existing.merge_from(&out_env, &self.store) {
            worklist.push_back(succ);
          }
        } else {
          in_envs[succ.0] = Some(out_env);
          worklist.push_back(succ);
        }
      }
    }
  }

  fn binding_type(&self, binding: BindingKey) -> TypeId {
    let prim = self.store.primitive_ids();
    match binding {
      BindingKey::Local { pat, .. } => self
        .pat_types
        .get(pat.0 as usize)
        .copied()
        .unwrap_or(prim.unknown),
      BindingKey::External(_) => self
        .bindings
        .flow_binding_for_key(binding)
        .and_then(|id| self.initial.get(&id).copied())
        .unwrap_or(prim.unknown),
    }
  }

  fn process_block(
    &mut self,
    block_id: BlockId,
    mut env: Env,
    cfg: &ControlFlowGraph,
  ) -> Vec<(BlockId, Env)> {
    let block = &cfg.blocks[block_id.0];

    match &block.kind {
      BlockKind::ForInit { init } => {
        if let Some(init) = init {
          match init {
            ForInit::Expr(expr_id) => {
              let (_, facts) = self.eval_expr(*expr_id, &mut env);
              env.apply_map(&facts.assertions);
            }
            ForInit::Var(var) => {
              let mode = match var.kind {
                hir_js::VarDeclKind::Const
                | hir_js::VarDeclKind::Using
                | hir_js::VarDeclKind::AwaitUsing => BindingMode::Declare,
                _ => BindingMode::Assign,
              };
              for declarator in var.declarators.iter() {
                let init_ty = declarator
                  .init
                  .map(|id| self.eval_expr(id, &mut env).0)
                  .unwrap_or_else(|| self.store.primitive_ids().unknown);
                self.bind_pat_with_mode(declarator.pat, init_ty, &mut env, mode);
                let state = if declarator.init.is_some() {
                  InitState::Assigned
                } else {
                  InitState::Unassigned
                };
                self.mark_pat_state(declarator.pat, &mut env, state);
              }
            }
          }
        }
        return block
          .successors
          .iter()
          .map(|succ| (*succ, env.clone()))
          .collect();
      }
      BlockKind::ForTest { test } => {
        let facts = test
          .map(|t| self.eval_expr(t, &mut env).1)
          .unwrap_or_default();
        let mut then_env = env.clone();
        then_env.apply_facts(&facts);
        let mut else_env = env.clone();
        else_env.apply_falsy(&facts);

        let mut outgoing = Vec::new();
        if let Some(succ) = block.successors.get(0) {
          outgoing.push((*succ, then_env));
        }
        if let Some(succ) = block.successors.get(1) {
          outgoing.push((*succ, else_env));
        }
        return outgoing;
      }
      BlockKind::ForUpdate { update } => {
        if let Some(expr_id) = update {
          let (_, facts) = self.eval_expr(*expr_id, &mut env);
          env.apply_map(&facts.assertions);
        }
        return block
          .successors
          .iter()
          .map(|succ| (*succ, env.clone()))
          .collect();
      }
      BlockKind::DoWhileTest { test } => {
        let facts = self.eval_expr(*test, &mut env).1;
        let mut body_env = env.clone();
        body_env.apply_facts(&facts);
        let mut after_env = env.clone();
        after_env.apply_falsy(&facts);
        let mut outgoing = Vec::new();
        if let Some(succ) = block.successors.get(0) {
          outgoing.push((*succ, body_env));
        }
        if let Some(succ) = block.successors.get(1) {
          outgoing.push((*succ, after_env));
        }
        return outgoing;
      }
      BlockKind::Normal => {}
    }

    if block.stmts.is_empty() {
      return block
        .successors
        .iter()
        .map(|succ| (*succ, env.clone()))
        .collect();
    }

    let mut outgoing = Vec::new();
    for stmt_id in block.stmts.iter() {
      let stmt = &self.body.stmts[stmt_id.0 as usize];
      match &stmt.kind {
        StmtKind::Expr(expr) => {
          let (_, facts) = self.eval_expr(*expr, &mut env);
          env.apply_map(&facts.assertions);
        }
        StmtKind::Return(expr) => {
          let ty = match expr {
            Some(id) => self.eval_expr(*id, &mut env).0,
            None => self.store.primitive_ids().undefined,
          };
          self.record_return(*stmt_id, ty);
          // return/throw terminate flow; no successors.
          return Vec::new();
        }
        StmtKind::Throw(expr) => {
          let _ = self.eval_expr(*expr, &mut env);
          return Vec::new();
        }
        StmtKind::Var(decl) => {
          let mode = match decl.kind {
            hir_js::VarDeclKind::Const
            | hir_js::VarDeclKind::Using
            | hir_js::VarDeclKind::AwaitUsing => BindingMode::Declare,
            _ => BindingMode::Assign,
          };
          for declarator in decl.declarators.iter() {
            let init_ty = declarator
              .init
              .map(|id| self.eval_expr(id, &mut env).0)
              .unwrap_or_else(|| self.store.primitive_ids().unknown);
            self.bind_pat_with_mode(declarator.pat, init_ty, &mut env, mode);
            let state = if declarator.init.is_some() {
              InitState::Assigned
            } else {
              InitState::Unassigned
            };
            self.mark_pat_state(declarator.pat, &mut env, state);
          }
        }
        StmtKind::If {
          test,
          consequent: _,
          alternate: _,
        } => {
          let facts = self.eval_expr(*test, &mut env).1;
          let mut then_env = env.clone();
          then_env.apply_facts(&facts);
          let mut else_env = env.clone();
          else_env.apply_falsy(&facts);

          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, then_env));
          }
          if let Some(succ) = block.successors.get(1) {
            outgoing.push((*succ, else_env));
          }
          return outgoing;
        }
        StmtKind::While { test, .. } => {
          let facts = self.eval_expr(*test, &mut env).1;
          let mut body_env = env.clone();
          body_env.apply_facts(&facts);
          let mut after_env = env.clone();
          after_env.apply_falsy(&facts);
          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, body_env));
          }
          if let Some(succ) = block.successors.get(1) {
            outgoing.push((*succ, after_env));
          }
          return outgoing;
        }
        StmtKind::DoWhile { .. } => {
          unreachable!("do...while statements are lowered into synthetic blocks");
        }
        StmtKind::For { .. } => {
          unreachable!("for statements are lowered into synthetic blocks");
        }
        StmtKind::ForIn {
          left,
          right,
          is_for_of,
          ..
        } => {
          let iter_ty = self.eval_expr(*right, &mut env).0;
          let right_ty = if *is_for_of {
            self.for_of_element_type(iter_ty)
          } else {
            self.store.primitive_ids().string
          };
          let mut loop_env = env.clone();
          match left {
            ForHead::Pat(pat) => self.assign_pat(*pat, right_ty, &mut loop_env),
            ForHead::Var(var) => {
              let mode = match var.kind {
                hir_js::VarDeclKind::Const
                | hir_js::VarDeclKind::Using
                | hir_js::VarDeclKind::AwaitUsing => BindingMode::Declare,
                _ => BindingMode::Assign,
              };
              for declarator in var.declarators.iter() {
                self.bind_pat_with_mode(declarator.pat, right_ty, &mut loop_env, mode);
                self.mark_pat_state(declarator.pat, &mut loop_env, InitState::Assigned);
              }
            }
          }
          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, loop_env.clone()));
          }
          if let Some(succ) = block.successors.get(1) {
            outgoing.push((*succ, env.clone()));
          }
          return outgoing;
        }
        StmtKind::Switch {
          discriminant,
          cases,
        } => {
          let discriminant_ty = self.eval_expr(*discriminant, &mut env).0;
          let target = self.switch_discriminant_target(*discriminant, discriminant_ty, &env);
          let default_remaining = target
            .as_ref()
            .and_then(|t| self.switch_default_remaining(t, cases));

          let mut case_envs = Vec::with_capacity(cases.len());
          for case in cases.iter() {
            let mut case_env = env.clone();
            if let Some(test) = case.test {
              let _ = self.eval_expr(test, &mut case_env);
              if let Some(target) = target.as_ref() {
                let _ = self.apply_switch_narrowing(target, test, &mut case_env);
              }
            } else if let (Some(target), Some(default_ty)) = (target.as_ref(), default_remaining) {
              self.apply_switch_result(target, default_ty, &mut case_env);
            }
            case_envs.push(case_env);
          }

          for (idx, case_env) in case_envs.iter().enumerate() {
            if let Some(succ) = block.successors.get(idx) {
              outgoing.push((*succ, case_env.clone()));
              if self.switch_case_falls_through(cases.get(idx)) {
                for later in (idx + 1)..cases.len() {
                  if let Some(later_succ) = block.successors.get(later) {
                    outgoing.push((*later_succ, case_env.clone()));
                  }
                }
              }
            }
          }
          // If there is an implicit default edge (no default case), use the final successor.
          if block.successors.len() > cases.len() {
            if let Some(succ) = block.successors.last() {
              let mut default_env = env.clone();
              if let (Some(target), Some(default_ty)) = (target.as_ref(), default_remaining) {
                self.apply_switch_result(target, default_ty, &mut default_env);
              }
              outgoing.push((*succ, default_env));
            }
          }
          return outgoing;
        }
        StmtKind::Try {
          block: _,
          catch,
          finally_block,
        } => {
          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, env.clone()));
          }
          if let Some((idx, catch_clause)) = catch.as_ref().map(|c| (1, c)) {
            let mut catch_env = env.clone();
            if let Some(param) = catch_clause.param {
              self.bind_pat(param, self.store.primitive_ids().unknown, &mut catch_env);
              self.mark_pat_state(param, &mut catch_env, InitState::Assigned);
            }
            if let Some(succ) = block.successors.get(idx) {
              outgoing.push((*succ, catch_env));
            }
          }
          if let Some(_) = finally_block {
            if let Some(pos) = catch.as_ref().map(|_| 2).or_else(|| Some(1)) {
              if let Some(succ) = block.successors.get(pos) {
                outgoing.push((*succ, env.clone()));
              }
            }
          }
          return outgoing;
        }
        _ => {}
      }
    }

    if outgoing.is_empty() {
      outgoing.extend(block.successors.iter().map(|succ| (*succ, env.clone())));
    }
    outgoing
  }

  fn record_return(&mut self, stmt: StmtId, ty: TypeId) {
    let prim = self.store.primitive_ids();
    if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
      eprintln!(
        "DEBUG record_return {:?} ty {}",
        stmt,
        TypeDisplay::new(&self.store, ty)
      );
    }
    let idx = *self.return_indices.entry(stmt).or_insert_with(|| {
      self.return_types.push(prim.unknown);
      self.return_types.len() - 1
    });
    let slot = self.return_types.get_mut(idx).unwrap();
    if *slot == prim.unknown {
      *slot = ty;
    } else {
      *slot = self.store.union(vec![*slot, ty]);
    }
  }

  fn eval_expr(&mut self, expr_id: ExprId, env: &mut Env) -> (TypeId, Facts) {
    self.eval_expr_inner(expr_id, env, false)
  }

  fn eval_expr_inner(
    &mut self,
    expr_id: ExprId,
    env: &mut Env,
    suppress_uninit: bool,
  ) -> (TypeId, Facts) {
    let prim = self.store.primitive_ids();
    let expr = &self.body.exprs[expr_id.0 as usize];
    let mut facts = Facts::default();
    let ty = match &expr.kind {
      ExprKind::Ident(name) => {
        let flow_binding = self.bindings.binding_for_expr(expr_id);
        let binding_key = self.bindings.binding_key_for_expr(expr_id);
        let ty = flow_binding
          .and_then(|id| env.get(id).or_else(|| self.initial.get(&id).copied()))
          .unwrap_or(prim.unknown);
        if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
          let name_text = self.hir_name(*name);
          eprintln!(
            "DEBUG ident {name_text} flow {:?} ty {} initial {:?}",
            flow_binding,
            TypeDisplay::new(&self.store, ty),
            flow_binding.and_then(
              |id| self
                .initial
                .get(&id)
                .copied()
                .map(|t| TypeDisplay::new(&self.store, t).to_string())
            )
          );
        }
        if let Some(binding) = binding_key {
          if !suppress_uninit && !self.param_bindings.contains(&binding) {
            let state = env.init_state(binding);
            if state != InitState::Assigned && self.reported_unassigned.insert(expr_id) {
              let span = Span {
                file: self.file,
                range: expr.span,
              };
              let name_text = self.hir_name(*name);
              self.diagnostics.push(
                codes::USE_BEFORE_ASSIGNMENT
                  .error(format!("{name_text} is used before being assigned"), span),
              );
            }
          }
        }
        let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
        if let Some(id) = flow_binding {
          let key = FlowKey::root(id);
          facts.truthy.insert(key.clone(), truthy);
          facts.falsy.insert(key, falsy);
        }
        ty
      }
      ExprKind::Literal(lit) => match lit {
        hir_js::Literal::Number(num) => self.store.intern_type(TypeKind::NumberLiteral(
          num.parse::<f64>().unwrap_or(0.0).into(),
        )),
        hir_js::Literal::String(s) => self
          .store
          .intern_type(TypeKind::StringLiteral(self.store.intern_name(s.clone()))),
        hir_js::Literal::Boolean(b) => self.store.intern_type(TypeKind::BooleanLiteral(*b)),
        hir_js::Literal::Null => prim.null,
        hir_js::Literal::Undefined => prim.undefined,
        hir_js::Literal::BigInt(v) => self.store.intern_type(TypeKind::BigIntLiteral(
          v.parse::<i128>().unwrap_or(0).into(),
        )),
        hir_js::Literal::Regex(_) => prim.string,
      },
      ExprKind::Unary { op, expr } => match op {
        UnaryOp::Not => {
          let (_, inner_facts) = self.eval_expr(*expr, env);
          facts.truthy = inner_facts.falsy;
          facts.falsy = inner_facts.truthy;
          facts.assertions = inner_facts.assertions;
          prim.boolean
        }
        UnaryOp::Typeof => {
          let _ = self.eval_expr_inner(*expr, env, true);
          prim.string
        }
        UnaryOp::Void => prim.undefined,
        UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => {
          let _ = self.eval_expr(*expr, env);
          prim.number
        }
        _ => prim.unknown,
      },
      ExprKind::Update { expr, .. } => {
        let operand_ty = self.eval_expr(*expr, env).0;
        let result_ty = if self.is_bigint_like(self.base_type(operand_ty)) {
          prim.bigint
        } else {
          prim.number
        };
        self.write_assign_target_expr(*expr, result_ty, env, BindingMode::Assign);
        self.mark_expr_state(*expr, env, InitState::Assigned);
        if let Some(root) = self.assignment_target_root_expr(*expr) {
          self.record_assignment_facts(Some(root), result_ty, &mut facts);
        }
        result_ty
      }
      ExprKind::Binary { op, left, right } => match op {
        BinaryOp::LogicalAnd | BinaryOp::LogicalOr | BinaryOp::NullishCoalescing => {
          self.eval_logical(*op, *left, *right, env, &mut facts)
        }
        BinaryOp::Equality
        | BinaryOp::Inequality
        | BinaryOp::StrictEquality
        | BinaryOp::StrictInequality => {
          self.eval_equality(*op, *left, *right, env, &mut facts);
          prim.boolean
        }
        BinaryOp::LessThan
        | BinaryOp::LessEqual
        | BinaryOp::GreaterThan
        | BinaryOp::GreaterEqual => {
          let _ = self.eval_expr(*left, env);
          let _ = self.eval_expr(*right, env);
          prim.boolean
        }
        BinaryOp::Add => {
          let (l_ty, _) = self.eval_expr(*left, env);
          let (r_ty, _) = self.eval_expr(*right, env);
          match (self.store.type_kind(l_ty), self.store.type_kind(r_ty)) {
            (TypeKind::String | TypeKind::StringLiteral(_), _)
            | (_, TypeKind::String | TypeKind::StringLiteral(_)) => prim.string,
            (
              TypeKind::Number | TypeKind::NumberLiteral(_),
              TypeKind::Number | TypeKind::NumberLiteral(_),
            ) => prim.number,
            _ => self.store.union(vec![l_ty, r_ty]),
          }
        }
        BinaryOp::Subtract
        | BinaryOp::Multiply
        | BinaryOp::Divide
        | BinaryOp::Remainder
        | BinaryOp::Exponent
        | BinaryOp::ShiftLeft
        | BinaryOp::ShiftRight
        | BinaryOp::ShiftRightUnsigned
        | BinaryOp::BitOr
        | BinaryOp::BitAnd
        | BinaryOp::BitXor => {
          let _ = self.eval_expr(*left, env);
          let _ = self.eval_expr(*right, env);
          prim.number
        }
        BinaryOp::Instanceof => {
          let left_expr = *left;
          let left_ty = self.eval_expr(left_expr, env).0;
          let _ = self.eval_expr(*right, env);
          if let Some(binding) = self.ident_binding(left_expr) {
            let (yes, no) = narrow_by_instanceof(left_ty, &self.store);
            let key = FlowKey::root(binding);
            facts.truthy.insert(key.clone(), yes);
            facts.falsy.insert(key, no);
          }
          prim.boolean
        }
        BinaryOp::In => {
          let _ = self.eval_expr(*left, env);
          let right_ty = self.eval_expr(*right, env).0;
          if let (Some(prop), Some(binding)) =
            (self.literal_prop(*left), self.ident_binding(*right))
          {
            let (yes, no) = narrow_by_in_check(right_ty, &prop, &self.store, self.ref_expander);
            let key = FlowKey::root(binding);
            facts.truthy.insert(key.clone(), yes);
            facts.falsy.insert(key, no);
          }
          prim.boolean
        }
        BinaryOp::Comma => {
          let _ = self.eval_expr(*left, env);
          self.eval_expr(*right, env).0
        }
      },
      ExprKind::Assignment { op, target, value } => {
        let (left_ty, root, _) = self.assignment_target_info(*target, env);
        match op {
          AssignOp::Assign => {
            let val_ty = self.eval_expr(*value, env).0;
            self.assign_pat(*target, val_ty, env);
            let assigned_ty = self.apply_binding_mode(val_ty, BindingMode::Assign);
            self.record_assignment_facts(root, assigned_ty, &mut facts);
            assigned_ty
          }
          AssignOp::AddAssign => {
            let val_ty = self.eval_expr(*value, env).0;
            let result_ty = self.add_assign_result(left_ty, val_ty);
            self.assign_pat(*target, result_ty, env);
            self.record_assignment_facts(root, result_ty, &mut facts);
            result_ty
          }
          AssignOp::LogicalAndAssign => {
            self.logical_and_assign(*target, left_ty, *value, root, env, &mut facts)
          }
          AssignOp::LogicalOrAssign => {
            self.logical_or_assign(*target, left_ty, *value, root, env, &mut facts)
          }
          AssignOp::NullishAssign => {
            self.nullish_assign(*target, left_ty, *value, root, env, &mut facts)
          }
          _ => {
            let val_ty = self.eval_expr(*value, env).0;
            let result_ty = self.numeric_assign_result(left_ty, val_ty);
            self.assign_pat(*target, result_ty, env);
            self.record_assignment_facts(root, result_ty, &mut facts);
            result_ty
          }
        }
      }
      ExprKind::Call(call) => {
        let ret_ty = self.eval_call(expr_id, call, env, &mut facts);
        if call.optional {
          if let Some(name) = self.optional_chain_root(call.callee) {
            let (non_nullish, _) =
              narrow_non_nullish(self.expr_types[call.callee.0 as usize], &self.store);
            if non_nullish != prim.never {
              facts.truthy.insert(FlowKey::root(name), non_nullish);
            }
          }
          self.store.union(vec![ret_ty, prim.undefined])
        } else {
          ret_ty
        }
      }
      ExprKind::Member(mem) => {
        let obj_ty = self.eval_expr(mem.object, env).0;
        let prop_ty = if let Some(binding) = self.ident_binding(mem.object) {
          let key = FlowKey::root(binding).with_segment(PathSegment::String(self.member_key(mem)));
          env
            .get_path(&key)
            .unwrap_or_else(|| self.member_type(obj_ty, &mem))
        } else {
          self.member_type(obj_ty, &mem)
        };
        if mem.optional {
          if let Some(name) = self.optional_chain_root(mem.object) {
            let (non_nullish, _) = narrow_non_nullish(obj_ty, &self.store);
            if non_nullish != prim.never {
              facts.truthy.insert(FlowKey::root(name), non_nullish);
            }
          }
          self.store.union(vec![prop_ty, prim.undefined])
        } else {
          prop_ty
        }
      }
      ExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => {
        let cond_facts = self.eval_expr(*test, env).1;
        let mut then_env = env.clone();
        then_env.apply_facts(&cond_facts);
        let mut else_env = env.clone();
        else_env.apply_falsy(&cond_facts);
        let then_ty = self.eval_expr(*consequent, &mut then_env).0;
        let else_ty = self.eval_expr(*alternate, &mut else_env).0;
        self.store.union(vec![then_ty, else_ty])
      }
      ExprKind::Array(arr) => {
        let mut elem_tys = Vec::new();
        for elem in arr.elements.iter() {
          match elem {
            ArrayElement::Expr(id) | ArrayElement::Spread(id) => {
              let elem_ty = self.eval_expr(*id, env).0;
              let widened = match self.store.type_kind(elem_ty) {
                TypeKind::NumberLiteral(_) => prim.number,
                TypeKind::StringLiteral(_) => prim.string,
                TypeKind::BooleanLiteral(_) => prim.boolean,
                _ => elem_ty,
              };
              elem_tys.push(widened);
            }
            ArrayElement::Empty => {}
          }
        }
        let elem_ty = if elem_tys.is_empty() {
          prim.any
        } else {
          self.store.union(elem_tys)
        };
        self.store.intern_type(TypeKind::Array {
          ty: elem_ty,
          readonly: false,
        })
      }
      ExprKind::Object(obj) => self.object_type(obj, env),
      ExprKind::FunctionExpr { .. } => prim.unknown,
      ExprKind::ClassExpr { .. } => prim.unknown,
      ExprKind::Template(_) => prim.string,
      ExprKind::TaggedTemplate { .. } => prim.unknown,
      ExprKind::Await { expr } => self.eval_expr(*expr, env).0,
      ExprKind::Yield { expr, .. } => expr
        .map(|id| self.eval_expr(id, env).0)
        .unwrap_or(prim.undefined),
      ExprKind::TypeAssertion { expr, .. } => self.eval_expr(*expr, env).0,
      ExprKind::NonNull { expr } => {
        let inner_ty = self.eval_expr(*expr, env).0;
        let (_, nonnull) = narrow_by_nullish_equality(
          inner_ty,
          BinaryOp::Equality,
          &LiteralValue::Null,
          &self.store,
        );
        nonnull
      }
      ExprKind::Satisfies { expr, .. } => {
        let prev = self.widen_object_literals;
        self.widen_object_literals = false;
        let ty = self.eval_expr(*expr, env).0;
        self.widen_object_literals = prev;
        ty
      }
      _ => prim.unknown,
    };

    let slot = &mut self.expr_types[expr_id.0 as usize];
    *slot = if *slot == prim.unknown {
      ty
    } else {
      self.store.union(vec![*slot, ty])
    };
    (ty, facts)
  }

  fn eval_logical(
    &mut self,
    op: BinaryOp,
    left: ExprId,
    right: ExprId,
    env: &mut Env,
    out: &mut Facts,
  ) -> TypeId {
    let (left_ty, left_facts) = self.eval_expr(left, env);
    match op {
      BinaryOp::LogicalAnd => {
        let mut right_env = env.clone();
        right_env.apply_facts(&left_facts);
        let (right_ty, right_facts) = self.eval_expr(right, &mut right_env);
        *out = and_facts(left_facts, right_facts, &self.store);
        self.store.union(vec![left_ty, right_ty])
      }
      BinaryOp::LogicalOr => {
        let mut right_env = env.clone();
        right_env.apply_falsy(&left_facts);
        let (right_ty, right_facts) = self.eval_expr(right, &mut right_env);
        let mut combined = or_facts(left_facts.clone(), right_facts, &self.store);
        for (key, ty) in combined.truthy.iter_mut() {
          if !left_facts.truthy.contains_key(key) {
            if let Some(orig) = env
              .get(key.root)
              .or_else(|| self.initial.get(&key.root).copied())
            {
              *ty = self.store.union(vec![*ty, orig]);
            }
          }
        }
        *out = combined;
        self.store.union(vec![left_ty, right_ty])
      }
      BinaryOp::NullishCoalescing => {
        let right_ty = self.eval_expr(right, env).0;
        let (nonnullish, _) = narrow_non_nullish(left_ty, &self.store);
        self.store.union(vec![nonnullish, right_ty])
      }
      _ => {
        let right_ty = self.eval_expr(right, env).0;
        self.store.union(vec![left_ty, right_ty])
      }
    }
  }

  fn eval_equality(
    &mut self,
    op: BinaryOp,
    left: ExprId,
    right: ExprId,
    env: &mut Env,
    out: &mut Facts,
  ) {
    let left_ty = self.eval_expr(left, env).0;
    let right_ty = self.eval_expr(right, env).0;
    let negate = matches!(op, BinaryOp::Inequality | BinaryOp::StrictInequality);

    fn apply_narrowing(
      out: &mut Facts,
      negate: bool,
      target: FlowBindingId,
      yes: TypeId,
      no: TypeId,
    ) {
      let key = FlowKey::root(target);
      if negate {
        out.truthy.insert(key.clone(), no);
        out.falsy.insert(key, yes);
      } else {
        out.truthy.insert(key.clone(), yes);
        out.falsy.insert(key, no);
      }
    }

    let mut apply_literal_narrow =
      |target: FlowBindingId, target_ty: TypeId, lit: &LiteralValue| {
        if matches!(lit, LiteralValue::Null | LiteralValue::Undefined) {
          let (yes, no) = narrow_by_nullish_equality(target_ty, op, lit, &self.store);
          apply_narrowing(out, negate, target, yes, no);
        } else {
          let (yes, no) = narrow_by_literal(target_ty, lit, &self.store);
          apply_narrowing(out, negate, target, yes, no);
        }
      };

    if let Some(target) = self.ident_binding(left) {
      if let Some(lit) = self.literal_value(right) {
        apply_literal_narrow(target, left_ty, &lit);
        return;
      }
    }
    if let Some(target) = self.ident_binding(right) {
      if let Some(lit) = self.literal_value(left) {
        apply_literal_narrow(target, right_ty, &lit);
        return;
      }
    }

    if let Some((target, prop, target_ty)) = self.discriminant_member(left) {
      if let Some(lit) = self.literal_value(right) {
        if let Some(prop_ty) = self.object_prop_type(target_ty, &prop) {
          let (prop_yes, prop_no) = match lit {
            LiteralValue::Null | LiteralValue::Undefined => {
              narrow_by_nullish_equality(prop_ty, op, &lit, &self.store)
            }
            _ => narrow_by_literal(prop_ty, &lit, &self.store),
          };
          let path = FlowKey::root(target).with_segment(PathSegment::String(prop.clone()));
          if negate {
            out.truthy.insert(path.clone(), prop_no);
            out.falsy.insert(path, prop_yes);
          } else {
            out.truthy.insert(path.clone(), prop_yes);
            out.falsy.insert(path, prop_no);
          }
        }
        match lit {
          LiteralValue::Null | LiteralValue::Undefined => {
            if let Some(prop_ty) = self.object_prop_type(target_ty, &prop) {
              let (yes_prop, no_prop) = narrow_by_nullish_equality(prop_ty, op, &lit, &self.store);
              let yes = self.narrow_object_by_prop_assignability(target_ty, &prop, yes_prop);
              let no = self.narrow_object_by_prop_assignability(target_ty, &prop, no_prop);
              apply_narrowing(out, negate, target, yes, no);
              return;
            }
          }
          _ => {
            let (yes, no) = narrow_by_discriminant(target_ty, &prop, &lit, &self.store);
            apply_narrowing(out, negate, target, yes, no);
            return;
          }
        }
      }
    }
    if let Some((target, prop, target_ty)) = self.discriminant_member(right) {
      if let Some(lit) = self.literal_value(left) {
        if let Some(prop_ty) = self.object_prop_type(target_ty, &prop) {
          let (prop_yes, prop_no) = match lit {
            LiteralValue::Null | LiteralValue::Undefined => {
              narrow_by_nullish_equality(prop_ty, op, &lit, &self.store)
            }
            _ => narrow_by_literal(prop_ty, &lit, &self.store),
          };
          let path = FlowKey::root(target).with_segment(PathSegment::String(prop.clone()));
          if negate {
            out.truthy.insert(path.clone(), prop_no);
            out.falsy.insert(path, prop_yes);
          } else {
            out.truthy.insert(path.clone(), prop_yes);
            out.falsy.insert(path, prop_no);
          }
        }
        match lit {
          LiteralValue::Null | LiteralValue::Undefined => {
            if let Some(prop_ty) = self.object_prop_type(target_ty, &prop) {
              let (yes_prop, no_prop) = narrow_by_nullish_equality(prop_ty, op, &lit, &self.store);
              let yes = self.narrow_object_by_prop_assignability(target_ty, &prop, yes_prop);
              let no = self.narrow_object_by_prop_assignability(target_ty, &prop, no_prop);
              apply_narrowing(out, negate, target, yes, no);
              return;
            }
          }
          _ => {
            let (yes, no) = narrow_by_discriminant(target_ty, &prop, &lit, &self.store);
            apply_narrowing(out, negate, target, yes, no);
            return;
          }
        }
      }
    }

    if !negate {
      if let (Some(left_ref), Some(right_ref)) = (
        self.reference_from_expr(left, left_ty),
        self.reference_from_expr(right, right_ty),
      ) {
        let left_yes = self.narrow_reference_against(&left_ref, right_ref.value_ty());
        let right_yes = self.narrow_reference_against(&right_ref, left_ref.value_ty());
        if left_ref.target() == right_ref.target() {
          let combined = self.store.intersection(vec![left_yes, right_yes]);
          apply_narrowing(
            out,
            negate,
            left_ref.target(),
            combined,
            left_ref.target_ty(),
          );
        } else {
          apply_narrowing(
            out,
            negate,
            left_ref.target(),
            left_yes,
            left_ref.target_ty(),
          );
          apply_narrowing(
            out,
            negate,
            right_ref.target(),
            right_yes,
            right_ref.target_ty(),
          );
        }
        return;
      }
    }

    if let Some((target, target_ty, lit)) = self.typeof_comparison(left, right) {
      let (yes, no) = narrow_by_typeof(target_ty, &lit, &self.store);
      apply_narrowing(out, negate, target, yes, no);
    }

    self.optional_chain_equality_facts(left, right_ty, negate, out);
    self.optional_chain_equality_facts(right, left_ty, negate, out);
  }

  fn eval_call(
    &mut self,
    expr_id: ExprId,
    call: &hir_js::CallExpr,
    env: &mut Env,
    out: &mut Facts,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let _ = self.eval_expr(call.callee, env);
    let callee_base = self.expand_ref(self.expr_types[call.callee.0 as usize]);
    self.expr_types[call.callee.0 as usize] = callee_base;
    let mut arg_bases = Vec::new();
    for arg in call.args.iter() {
      let _ = self.eval_expr(arg.expr, env);
      let expanded = self.expand_ref(self.expr_types[arg.expr.0 as usize]);
      self.expr_types[arg.expr.0 as usize] = expanded;
      arg_bases.push(expanded);
    }

    let this_arg = match &self.body.exprs[call.callee.0 as usize].kind {
      ExprKind::Member(MemberExpr { object, .. }) => Some(self.expr_types[object.0 as usize]),
      _ => None,
    };

    let span = Span::new(
      self.file,
      *self
        .expr_spans
        .get(expr_id.0 as usize)
        .unwrap_or(&TextRange::new(0, 0)),
    );
    let resolution = if call.is_new {
      resolve_construct(
        &self.store,
        &self.relate,
        callee_base,
        &arg_bases,
        None,
        None,
        span,
        self.ref_expander,
      )
    } else {
      resolve_call(
        &self.store,
        &self.relate,
        callee_base,
        &arg_bases,
        this_arg,
        None,
        span,
        self.ref_expander,
      )
    };
    if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
      eprintln!(
        "DEBUG call resolution sig {:?} ret {}",
        resolution.signature,
        TypeDisplay::new(&self.store, resolution.return_type)
      );
    }

    let mut ret_ty = resolution.return_type;
    if !call.is_new {
      if let Some(sig_id) = resolution.signature {
        let sig = self.store.signature(sig_id);
        if let TypeKind::Predicate {
          asserted,
          asserts,
          parameter,
        } = self.store.type_kind(sig.ret)
        {
          if let Some(asserted) = asserted {
            let target_idx = parameter
              .and_then(|param_name| sig.params.iter().position(|p| p.name == Some(param_name)))
              .unwrap_or(0);
            if let Some(arg_expr) = call.args.get(target_idx).map(|a| a.expr) {
              if let Some(binding) = self.ident_binding(arg_expr) {
                let arg_ty = arg_bases.get(target_idx).copied().unwrap_or(prim.unknown);
                let (yes, no) =
                  narrow_by_assignability(arg_ty, asserted, &self.store, &self.relate);
                if asserts {
                  if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
                    eprintln!(
                      "DEBUG asserts narrowing arg {} to {} (no {}) in file {:?}",
                      TypeDisplay::new(&self.store, arg_ty),
                      TypeDisplay::new(&self.store, yes),
                      TypeDisplay::new(&self.store, no),
                      self.file
                    );
                  }
                  env.set(binding, yes);
                  out.assertions.insert(FlowKey::root(binding), yes);
                } else {
                  let key = FlowKey::root(binding);
                  out.truthy.insert(key.clone(), yes);
                  out.falsy.insert(key, no);
                  if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
                    eprintln!(
                      "DEBUG predicate narrowing arg {} to {} (no {}) in file {:?}",
                      TypeDisplay::new(&self.store, arg_ty),
                      TypeDisplay::new(&self.store, yes),
                      TypeDisplay::new(&self.store, no),
                      self.file
                    );
                  }
                }
              }
            }
          }
          ret_ty = if asserts {
            prim.undefined
          } else {
            prim.boolean
          };
        } else {
          ret_ty = sig.ret;
        }
      }
    }

    ret_ty
  }

  fn optional_chain_equality_facts(
    &mut self,
    expr: ExprId,
    other_ty: TypeId,
    negate: bool,
    out: &mut Facts,
  ) {
    let prim = self.store.primitive_ids();
    let Some(info) = self.optional_chain_info(expr) else {
      return;
    };
    let (non_nullish_base, nullish_base) = narrow_non_nullish(info.base_ty, &self.store);
    if non_nullish_base == prim.never {
      return;
    }

    if self.excludes_nullish(other_ty) {
      let target = if negate {
        &mut out.falsy
      } else {
        &mut out.truthy
      };
      target.insert(FlowKey::root(info.base), non_nullish_base);
      return;
    }

    if self.is_nullish_only(other_ty) {
      if let Some(result_ty) = info.result_ty {
        let (_, result_nullish) = narrow_non_nullish(result_ty, &self.store);
        if result_nullish == prim.never && nullish_base != prim.never {
          let target = if negate {
            &mut out.falsy
          } else {
            &mut out.truthy
          };
          target.insert(FlowKey::root(info.base), nullish_base);
        }
      }
    }
  }

  fn optional_chain_info(&mut self, expr: ExprId) -> Option<OptionalChainInfo> {
    match &self.body.exprs[expr.0 as usize].kind {
      ExprKind::Member(mem) if mem.optional => {
        let base = self.optional_chain_root(mem.object)?;
        let base_ty = self.expr_types[mem.object.0 as usize];
        let result_ty = Some(self.member_type(base_ty, mem));
        Some(OptionalChainInfo {
          base,
          base_ty,
          result_ty,
        })
      }
      ExprKind::Call(call) if call.optional => {
        let base = self.optional_chain_root(call.callee)?;
        let base_ty = self.expr_types[call.callee.0 as usize];
        Some(OptionalChainInfo {
          base,
          base_ty,
          result_ty: None,
        })
      }
      _ => None,
    }
  }

  fn optional_chain_root(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.ident_binding(expr_id),
      ExprKind::Member(mem) => self.optional_chain_root(mem.object),
      ExprKind::Call(call) => self.optional_chain_root(call.callee),
      _ => None,
    }
  }

  fn excludes_nullish(&self, ty: TypeId) -> bool {
    let prim = self.store.primitive_ids();
    let (_, nullish) = narrow_non_nullish(ty, &self.store);
    nullish == prim.never
  }

  fn is_nullish_only(&self, ty: TypeId) -> bool {
    let prim = self.store.primitive_ids();
    let (non_nullish, nullish) = narrow_non_nullish(ty, &self.store);
    non_nullish == prim.never && nullish != prim.never
  }

  fn ident_binding(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    match self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.bindings.binding_for_expr(expr_id),
      _ => None,
    }
  }

  fn literal_value(&self, expr_id: ExprId) -> Option<LiteralValue> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) if self.hir_name(*name) == "undefined" => Some(LiteralValue::Undefined),
      ExprKind::Literal(lit) => match lit {
        hir_js::Literal::String(s) => Some(LiteralValue::String(s.clone())),
        hir_js::Literal::Number(n) => Some(LiteralValue::Number(n.clone())),
        hir_js::Literal::Boolean(b) => Some(LiteralValue::Boolean(*b)),
        hir_js::Literal::Null => Some(LiteralValue::Null),
        hir_js::Literal::Undefined => Some(LiteralValue::Undefined),
        _ => None,
      },
      _ => None,
    }
  }

  fn literal_prop(&self, expr_id: ExprId) -> Option<String> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Literal(hir_js::Literal::String(s)) => Some(s.clone()),
      _ => None,
    }
  }

  fn assignment_target_root_expr(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.ident_binding(expr_id),
      ExprKind::Member(mem) => self.assignment_target_root_expr(mem.object),
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Await { expr }
      | ExprKind::Yield {
        expr: Some(expr), ..
      } => self.assignment_target_root_expr(*expr),
      _ => None,
    }
  }

  fn record_assignment_facts(&self, root: Option<FlowBindingId>, ty: TypeId, facts: &mut Facts) {
    if let Some(binding) = root {
      let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
      let key = FlowKey::root(binding);
      facts.truthy.insert(key.clone(), truthy);
      facts.falsy.insert(key, falsy);
    }
  }

  fn apply_binding_mode(&self, ty: TypeId, mode: BindingMode) -> TypeId {
    match mode {
      BindingMode::Declare => ty,
      BindingMode::Assign => self.base_type(ty),
    }
  }

  fn expand_ref(&self, ty: TypeId) -> TypeId {
    let mut current = self.store.canon(ty);
    if let Some(expander) = self.ref_expander {
      let mut seen = HashSet::new();
      while seen.insert(current) {
        match self.store.type_kind(current) {
          TypeKind::Ref { def, args } => {
            if let Some(expanded) = expander.expand_ref(&self.store, def, &args) {
              current = self.store.canon(expanded);
              continue;
            }
          }
          _ => {}
        }
        break;
      }
    }
    current
  }

  fn base_type(&self, ty: TypeId) -> TypeId {
    match self.store.type_kind(ty) {
      TypeKind::BooleanLiteral(_) => self.store.primitive_ids().boolean,
      TypeKind::NumberLiteral(_) => self.store.primitive_ids().number,
      TypeKind::StringLiteral(_) => self.store.primitive_ids().string,
      TypeKind::BigIntLiteral(_) => self.store.primitive_ids().bigint,
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members.into_iter().map(|m| self.base_type(m)).collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members.into_iter().map(|m| self.base_type(m)).collect();
        self.store.intersection(mapped)
      }
      _ => ty,
    }
  }

  fn for_of_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => {
        let mut elems = Vec::new();
        for member in members {
          elems.push(self.for_of_element_type(member));
        }
        self.store.union(elems)
      }
      TypeKind::Intersection(members) => {
        let mut elems = Vec::new();
        for member in members {
          elems.push(self.for_of_element_type(member));
        }
        self.store.intersection(elems)
      }
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => {
        let mut members = Vec::new();
        for elem in elems {
          members.push(elem.ty);
        }
        self.store.union(members)
      }
      TypeKind::String | TypeKind::StringLiteral(_) => prim.string,
      _ => prim.unknown,
    }
  }

  fn is_bigint_like(&self, ty: TypeId) -> bool {
    match self.store.type_kind(ty) {
      TypeKind::BigInt | TypeKind::BigIntLiteral(_) => true,
      TypeKind::Union(members) => members.iter().all(|m| self.is_bigint_like(*m)),
      TypeKind::Intersection(members) => members.iter().all(|m| self.is_bigint_like(*m)),
      _ => false,
    }
  }

  fn maybe_string(&self, ty: TypeId) -> bool {
    match self.store.type_kind(ty) {
      TypeKind::String | TypeKind::StringLiteral(_) => true,
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        members.iter().any(|m| self.maybe_string(*m))
      }
      _ => false,
    }
  }

  fn split_nullish(&self, ty: TypeId) -> (TypeId, TypeId) {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => {
        let mut non_nullish = Vec::new();
        let mut nullish = Vec::new();
        for member in members {
          let (nonnull, nulls) = self.split_nullish(member);
          if nonnull != prim.never {
            non_nullish.push(nonnull);
          }
          if nulls != prim.never {
            nullish.push(nulls);
          }
        }
        (self.store.union(non_nullish), self.store.union(nullish))
      }
      TypeKind::Null | TypeKind::Undefined => (prim.never, ty),
      _ => (ty, prim.never),
    }
  }

  fn hir_name(&self, id: NameId) -> String {
    self
      .names
      .resolve(id)
      .map(|s| s.to_owned())
      .unwrap_or_default()
  }

  fn member_property_name(&self, property: &ObjectKey) -> Option<String> {
    match property {
      ObjectKey::Ident(id) => Some(self.hir_name(*id)),
      ObjectKey::String(s) => Some(s.clone()),
      ObjectKey::Number(n) => Some(n.clone()),
      ObjectKey::Computed(expr) => self.literal_value(*expr).and_then(|lit| match lit {
        LiteralValue::String(s) | LiteralValue::Number(s) => Some(s),
        _ => None,
      }),
    }
  }

  fn discriminant_member(&self, expr_id: ExprId) -> Option<(FlowBindingId, String, TypeId)> {
    if let ExprKind::Member(MemberExpr {
      object, property, ..
    }) = &self.body.exprs[expr_id.0 as usize].kind
    {
      if let Some(binding) = self.ident_binding(*object) {
        let prop = self.member_property_name(property)?;
        let obj_ty = self.expr_types[object.0 as usize];
        return Some((binding, prop, obj_ty));
      }
    }
    None
  }

  fn typeof_comparison(
    &self,
    left: ExprId,
    right: ExprId,
  ) -> Option<(FlowBindingId, TypeId, String)> {
    let left_expr = &self.body.exprs[left.0 as usize].kind;
    let right_expr = &self.body.exprs[right.0 as usize].kind;
    match (left_expr, right_expr) {
      (
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        },
        ExprKind::Literal(hir_js::Literal::String(s)),
      ) => {
        if let Some(binding) = self.ident_binding(*expr) {
          return Some((binding, self.expr_types[expr.0 as usize], s.clone()));
        }
      }
      (
        ExprKind::Literal(hir_js::Literal::String(s)),
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        },
      ) => {
        if let Some(binding) = self.ident_binding(*expr) {
          return Some((binding, self.expr_types[expr.0 as usize], s.clone()));
        }
      }
      _ => {}
    }
    None
  }
  fn assignment_expr_info(
    &mut self,
    expr_id: ExprId,
    env: &mut Env,
  ) -> (TypeId, Option<FlowBindingId>, bool) {
    let prim = self.store.primitive_ids();
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => {
        let binding = self.ident_binding(expr_id);
        let ty = binding
          .and_then(|id| env.get(id).or_else(|| self.initial.get(&id).copied()))
          .unwrap_or(prim.unknown);
        (ty, binding, false)
      }
      ExprKind::Member(mem) => {
        let obj_ty = self.eval_expr(mem.object, env).0;
        let prop_ty = match &mem.property {
          ObjectKey::Computed(prop) => {
            let _ = self.eval_expr(*prop, env);
            prim.unknown
          }
          _ => self.member_type(obj_ty, mem),
        };
        let root = self.assignment_target_root_expr(mem.object);
        (
          prop_ty,
          root,
          matches!(mem.property, ObjectKey::Computed(_)),
        )
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr, .. } => self.assignment_expr_info(*expr, env),
      _ => (prim.unknown, None, false),
    }
  }

  fn assignment_target_info(
    &mut self,
    pat_id: PatId,
    env: &mut Env,
  ) -> (TypeId, Option<FlowBindingId>, bool) {
    let pat = &self.body.pats[pat_id.0 as usize];
    let prim = self.store.primitive_ids();
    match &pat.kind {
      PatKind::Ident(_) => {
        let binding = self.bindings.binding_for_pat(pat_id);
        let ty = binding
          .and_then(|id| env.get(id).or_else(|| self.initial.get(&id).copied()))
          .unwrap_or(prim.unknown);
        (ty, binding, false)
      }
      PatKind::Assign { target, .. } => self.assignment_target_info(*target, env),
      PatKind::Rest(inner) => self.assignment_target_info(**inner, env),
      PatKind::AssignTarget(expr) => self.assignment_expr_info(*expr, env),
      _ => (prim.unknown, None, false),
    }
  }

  fn reference_from_expr(&self, expr_id: ExprId, expr_ty: TypeId) -> Option<Reference> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.ident_binding(expr_id).map(|id| Reference::Ident {
        name: id,
        ty: expr_ty,
      }),
      ExprKind::Member(mem) => {
        let base = self.ident_binding(mem.object)?;
        let prop = match &mem.property {
          ObjectKey::Ident(id) => self.hir_name(*id),
          ObjectKey::String(s) => s.clone(),
          ObjectKey::Number(n) => n.clone(),
          ObjectKey::Computed(_) => return None,
        };
        let base_ty = self.expr_types[mem.object.0 as usize];
        Some(Reference::Member {
          base,
          prop,
          base_ty,
          prop_ty: expr_ty,
        })
      }
      _ => None,
    }
  }

  fn narrow_reference_against(&self, reference: &Reference, other_value_ty: TypeId) -> TypeId {
    match reference {
      Reference::Ident { ty, .. } => {
        let (yes, _) = narrow_by_assignability(*ty, other_value_ty, &self.store, &self.relate);
        yes
      }
      Reference::Member { base_ty, prop, .. } => {
        self.narrow_object_by_prop_assignability(*base_ty, prop, other_value_ty)
      }
    }
  }

  fn narrow_object_by_prop_assignability(
    &self,
    obj_ty: TypeId,
    prop: &str,
    required_prop_ty: TypeId,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    if required_prop_ty == prim.never {
      return prim.never;
    }
    match self.store.type_kind(obj_ty) {
      TypeKind::Union(members) => {
        let mut narrowed = Vec::new();
        for member in members {
          let filtered = self.narrow_object_by_prop_assignability(member, prop, required_prop_ty);
          if filtered != prim.never {
            narrowed.push(filtered);
          }
        }
        self.store.union(narrowed)
      }
      _ => {
        if let Some(prop_ty) = self.object_prop_type(obj_ty, prop) {
          let (overlap, _) =
            narrow_by_assignability(prop_ty, required_prop_ty, &self.store, &self.relate);
          if overlap != prim.never {
            return obj_ty;
          }
          return prim.never;
        }
        obj_ty
      }
    }
  }

  fn numeric_assign_result(&self, left: TypeId, right: TypeId) -> TypeId {
    let left_base = self.base_type(left);
    let right_base = self.base_type(right);
    if self.is_bigint_like(left_base) && self.is_bigint_like(right_base) {
      self.store.primitive_ids().bigint
    } else {
      self.store.primitive_ids().number
    }
  }

  fn add_assign_result(&self, left: TypeId, right: TypeId) -> TypeId {
    let left_base = self.base_type(left);
    let right_base = self.base_type(right);
    let prim = self.store.primitive_ids();
    if self.is_bigint_like(left_base) && self.is_bigint_like(right_base) {
      return prim.bigint;
    }
    if self.maybe_string(left_base) || self.maybe_string(right_base) {
      self.store.union(vec![prim.string, prim.number])
    } else {
      prim.number
    }
  }

  fn logical_and_assign(
    &mut self,
    target: PatId,
    left: TypeId,
    value: ExprId,
    root: Option<FlowBindingId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (left_truthy, left_falsy) = truthy_falsy_types(left_base, &self.store);
    let mut right_env = env.clone();
    if let Some(binding) = root {
      right_env.set(binding, left_truthy);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self.store.union(vec![left_falsy, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  fn logical_or_assign(
    &mut self,
    target: PatId,
    left: TypeId,
    value: ExprId,
    root: Option<FlowBindingId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (left_truthy, left_falsy) = truthy_falsy_types(left_base, &self.store);
    let mut right_env = env.clone();
    if let Some(binding) = root {
      right_env.set(binding, left_falsy);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self
      .store
      .union(vec![left_truthy, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  fn nullish_assign(
    &mut self,
    target: PatId,
    left: TypeId,
    value: ExprId,
    root: Option<FlowBindingId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (nonnullish, nullish) = self.split_nullish(left_base);
    let mut right_env = env.clone();
    if let Some(binding) = root {
      right_env.set(binding, nullish);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self.store.union(vec![nonnullish, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  fn assign_pat(&mut self, pat_id: PatId, value_ty: TypeId, env: &mut Env) {
    self.bind_pat_with_mode(pat_id, value_ty, env, BindingMode::Assign);
    self.mark_pat_state(pat_id, env, InitState::Assigned);
  }

  fn bind_pat(&mut self, pat_id: PatId, value_ty: TypeId, env: &mut Env) {
    self.bind_pat_with_mode(pat_id, value_ty, env, BindingMode::Declare);
  }

  fn bind_pat_with_mode(
    &mut self,
    pat_id: PatId,
    value_ty: TypeId,
    env: &mut Env,
    mode: BindingMode,
  ) {
    let pat = &self.body.pats[pat_id.0 as usize];
    let prim = self.store.primitive_ids();
    let write_ty = self.apply_binding_mode(value_ty, mode);
    let slot = &mut self.pat_types[pat_id.0 as usize];
    *slot = if *slot == prim.unknown {
      write_ty
    } else {
      self.store.union(vec![*slot, write_ty])
    };
    match &pat.kind {
      PatKind::Ident(_) => {
        if let Some(id) = self.bindings.binding_for_pat(pat_id) {
          if matches!(mode, BindingMode::Assign) {
            env.invalidate(id);
          }
          env.set(id, write_ty);
        }
      }
      PatKind::Assign {
        target,
        default_value,
      } => {
        let default_eval = self.eval_expr(*default_value, env).0;
        let default_ty = self.apply_binding_mode(default_eval, mode);
        let combined = self.store.union(vec![write_ty, default_ty]);
        self.bind_pat_with_mode(*target, combined, env, mode);
      }
      PatKind::Rest(inner) => self.bind_pat_with_mode(**inner, write_ty, env, mode),
      PatKind::Array(arr) => {
        let element_ty = match self.store.type_kind(value_ty) {
          TypeKind::Array { ty, .. } => ty,
          TypeKind::Tuple(elems) => elems.first().map(|e| e.ty).unwrap_or(prim.unknown),
          _ => prim.unknown,
        };
        for (idx, elem) in arr.elements.iter().enumerate() {
          if let Some(elem) = elem {
            let mut ty = element_ty;
            if let TypeKind::Tuple(elems) = self.store.type_kind(value_ty) {
              if let Some(specific) = elems.get(idx) {
                ty = specific.ty;
              }
            }
            ty = self.apply_binding_mode(ty, mode);
            if let Some(default) = elem.default_value {
              let default_eval = self.eval_expr(default, env).0;
              let default_ty = self.apply_binding_mode(default_eval, mode);
              ty = self.store.union(vec![ty, default_ty]);
            }
            self.bind_pat_with_mode(elem.pat, ty, env, mode);
          }
        }
        if let Some(rest) = arr.rest {
          let rest_ty = self.apply_binding_mode(value_ty, mode);
          self.bind_pat_with_mode(rest, rest_ty, env, mode);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          let prop_name = match &prop.key {
            ObjectKey::Ident(id) => Some(self.hir_name(*id)),
            ObjectKey::String(s) => Some(s.clone()),
            ObjectKey::Number(n) => Some(n.clone()),
            _ => None,
          };
          let mut prop_ty = prim.unknown;
          if let Some(name) = prop_name {
            if let Some(found) = self.object_prop_type(value_ty, &name) {
              prop_ty = found;
            }
          }
          prop_ty = self.apply_binding_mode(prop_ty, mode);
          if let Some(default) = prop.default_value {
            let default_eval = self.eval_expr(default, env).0;
            let default_ty = self.apply_binding_mode(default_eval, mode);
            prop_ty = self.store.union(vec![prop_ty, default_ty]);
          }
          self.bind_pat_with_mode(prop.value, prop_ty, env, mode);
        }
        if let Some(rest) = obj.rest {
          let rest_ty = self.apply_binding_mode(value_ty, mode);
          self.bind_pat_with_mode(rest, rest_ty, env, mode);
        }
      }
      PatKind::AssignTarget(expr) => {
        self.write_assign_target_expr(*expr, write_ty, env, mode);
      }
    }
  }

  fn mark_expr_state(&self, expr_id: ExprId, env: &mut Env, state: InitState) {
    if let Some(binding) = self.bindings.binding_key_for_expr(expr_id) {
      env.set_init_state(binding, state);
    }
  }

  fn mark_pat_state(&self, pat_id: PatId, env: &mut Env, state: InitState) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(_) => {
        if let Some(binding) = self.bindings.binding_key_for_pat(pat_id) {
          env.set_init_state(binding, state);
        }
      }
      PatKind::Assign { target, .. } => self.mark_pat_state(*target, env, state),
      PatKind::Rest(inner) => self.mark_pat_state(**inner, env, state),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.mark_pat_state(elem.pat, env, state);
        }
        if let Some(rest) = arr.rest {
          self.mark_pat_state(rest, env, state);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.mark_pat_state(prop.value, env, state);
        }
        if let Some(rest) = obj.rest {
          self.mark_pat_state(rest, env, state);
        }
      }
      PatKind::AssignTarget(expr) => self.mark_expr_state(*expr, env, state),
    }
  }

  fn write_assign_target_expr(
    &mut self,
    expr_id: ExprId,
    value_ty: TypeId,
    env: &mut Env,
    mode: BindingMode,
  ) {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => {
        if let Some(id) = self.ident_binding(expr_id) {
          if matches!(mode, BindingMode::Assign) {
            env.invalidate(id);
          }
          env.set(id, value_ty);
        }
      }
      ExprKind::Member(mem) => {
        if let Some(root) = self.assignment_target_root_expr(mem.object) {
          let root_ty = env
            .get(root)
            .or_else(|| self.initial.get(&root).copied())
            .unwrap_or(self.store.primitive_ids().unknown);
          let widened = self.widen_object_prop(root_ty);
          env.invalidate(root);
          env.set(root, self.base_type(widened));
        } else if matches!(mem.property, ObjectKey::Computed(_)) {
          env.clear_all_properties();
        }
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr, .. } => {
        self.write_assign_target_expr(*expr, value_ty, env, mode);
      }
      _ => {}
    }
  }

  fn object_type(&mut self, obj: &ObjectLiteral, env: &mut Env) -> TypeId {
    let mut shape = Shape::new();
    for prop in obj.properties.iter() {
      match prop {
        ObjectProperty::KeyValue { key, value, .. } => {
          let prop_key = match key {
            ObjectKey::Ident(id) => PropKey::String(self.store.intern_name(self.hir_name(*id))),
            ObjectKey::String(s) => PropKey::String(self.store.intern_name(s.clone())),
            ObjectKey::Number(n) => PropKey::Number(n.parse::<i64>().unwrap_or(0)),
            ObjectKey::Computed(_) => continue,
          };
          let ty = self.eval_expr(*value, env).0;
          let ty = if self.widen_object_literals {
            self.widen_object_prop(ty)
          } else {
            ty
          };
          shape.properties.push(types_ts_interned::Property {
            key: prop_key,
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
        ObjectProperty::Getter { key, .. } | ObjectProperty::Setter { key, .. } => {
          let prop_key = match key {
            ObjectKey::Ident(id) => PropKey::String(self.store.intern_name(self.hir_name(*id))),
            ObjectKey::String(s) => PropKey::String(self.store.intern_name(s.clone())),
            ObjectKey::Number(n) => PropKey::Number(n.parse::<i64>().unwrap_or(0)),
            ObjectKey::Computed(_) => continue,
          };
          shape.properties.push(types_ts_interned::Property {
            key: prop_key,
            data: PropData {
              ty: self.store.primitive_ids().unknown,
              optional: false,
              readonly: false,
              accessibility: None,
              is_method: true,
              origin: None,
              declared_on: None,
            },
          });
        }
        ObjectProperty::Spread(expr) => {
          let _ = self.eval_expr(*expr, env);
        }
      }
    }
    let shape_id = self.store.intern_shape(shape);
    let obj_id = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj_id))
  }

  fn widen_object_prop(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::NumberLiteral(_) => prim.number,
      TypeKind::StringLiteral(_) => prim.string,
      TypeKind::BooleanLiteral(_) => prim.boolean,
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_prop(m))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_prop(m))
          .collect();
        self.store.intersection(mapped)
      }
      _ => ty,
    }
  }

  fn member_type(&mut self, obj: TypeId, mem: &MemberExpr) -> TypeId {
    let ty = match &mem.property {
      ObjectKey::Computed(expr) => {
        let _ = self.eval_expr(*expr, &mut Env::new());
        None
      }
      _ => {
        let key = self.member_key(mem);
        let ty = match self.store.type_kind(obj) {
          TypeKind::Ref { def, args } => {
            let expanded = self
              .ref_expander
              .and_then(|exp| exp.expand_ref(self.store.as_ref(), def, &args));
            if std::env::var("DEBUG_MEMBER").is_ok() {
              eprintln!(
                "DEBUG_MEMBER lookup {:?} expanded {:?}",
                def,
                expanded
                  .as_ref()
                  .map(|ty| self.store.type_kind(*ty).clone())
              );
            }
            expanded.and_then(|expanded| self.object_prop_type(expanded, &key))
          }
          _ => self.object_prop_type(obj, &key),
        };
        if ty.is_none() && std::env::var("DEBUG_MEMBER").is_ok() {
          eprintln!(
            "DEBUG_MEMBER missing property {} on {:?}",
            key,
            self.store.type_kind(obj)
          );
        }
        ty
      }
    };
    ty.unwrap_or_else(|| self.store.primitive_ids().unknown)
  }

  fn member_key(&self, mem: &MemberExpr) -> String {
    match &mem.property {
      ObjectKey::Ident(id) => self.hir_name(*id),
      ObjectKey::String(s) => s.clone(),
      ObjectKey::Number(n) => n.clone(),
      ObjectKey::Computed(_) => String::new(),
    }
  }

  fn object_prop_type(&self, obj: TypeId, key: &str) -> Option<TypeId> {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(obj) {
      TypeKind::Union(members) => {
        let mut tys = Vec::new();
        for member in members {
          if let Some(prop_ty) = self.object_prop_type(member, key) {
            tys.push(prop_ty);
          }
        }
        if tys.is_empty() {
          None
        } else {
          Some(self.store.union(tys))
        }
      }
      TypeKind::Intersection(members) => {
        let mut tys = Vec::new();
        for member in members {
          if let Some(prop_ty) = self.object_prop_type(member, key) {
            tys.push(prop_ty);
          }
        }
        if tys.is_empty() {
          None
        } else {
          Some(self.store.intersection(tys))
        }
      }
      TypeKind::Ref { def, args } => self
        .ref_expander
        .and_then(|exp| exp.expand_ref(self.store.as_ref(), def, &args))
        .and_then(|expanded| self.object_prop_type(expanded, key)),
      TypeKind::Callable { .. } => self.callable_prop_type(obj, key),
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in shape.properties.iter() {
          let matches = match prop.key {
            PropKey::String(name) => self.store.name(name) == key,
            PropKey::Number(num) => num.to_string() == key,
            _ => false,
          };
          if matches {
            return Some(prop.data.ty);
          }
        }
        if key == "call" && !shape.call_signatures.is_empty() {
          return Some(self.build_call_method_type(shape.call_signatures.clone()));
        }
        shape
          .indexers
          .first()
          .map(|idx| idx.value_type)
          .or(Some(prim.unknown))
      }
      TypeKind::Array { .. } if key == "length" => Some(prim.number),
      TypeKind::Array { ty, .. } => Some(ty),
      _ => None,
    }
  }

  fn callable_prop_type(&self, obj: TypeId, key: &str) -> Option<TypeId> {
    if key != "call" {
      return None;
    }
    let sigs = callable_signatures(&self.store, obj);
    if sigs.is_empty() {
      return None;
    }
    Some(self.build_call_method_type(sigs))
  }

  fn build_call_method_type(&self, sigs: Vec<SignatureId>) -> TypeId {
    let prim = self.store.primitive_ids();
    let mut overloads = Vec::new();
    for sig_id in sigs {
      let sig = self.store.signature(sig_id);
      let this_arg = sig.this_param.unwrap_or(prim.any);
      let mut params = Vec::with_capacity(sig.params.len() + 1);
      params.push(SigParam {
        name: None,
        ty: this_arg,
        optional: false,
        rest: false,
      });
      params.extend(sig.params.clone());
      let call_sig = Signature {
        params,
        ret: sig.ret,
        type_params: sig.type_params.clone(),
        this_param: None,
      };
      overloads.push(self.store.intern_signature(call_sig));
    }
    overloads.sort();
    overloads.dedup();
    self.store.intern_type(TypeKind::Callable { overloads })
  }

  fn switch_case_falls_through(&self, case: Option<&SwitchCase>) -> bool {
    let Some(case) = case else {
      return false;
    };
    match case.consequent.last() {
      None => true,
      Some(stmt) => match &self.body.stmts[stmt.0 as usize].kind {
        StmtKind::Return(_) | StmtKind::Throw(_) | StmtKind::Break(_) => false,
        _ => true,
      },
    }
  }

  fn apply_switch_narrowing(
    &mut self,
    target: &SwitchDiscriminant,
    test: ExprId,
    env: &mut Env,
  ) -> Option<(TypeId, TypeId)> {
    let (yes, no) = self.switch_case_narrowing_with_type(target, target.ty(), test)?;
    self.apply_switch_result(target, yes, env);
    Some((yes, no))
  }

  fn switch_default_remaining(
    &self,
    target: &SwitchDiscriminant,
    cases: &[SwitchCase],
  ) -> Option<TypeId> {
    let mut remaining = target.ty();
    for case in cases.iter() {
      if let Some(test) = case.test {
        let (_, no) = self.switch_case_narrowing_with_type(target, remaining, test)?;
        remaining = no;
      }
    }
    Some(remaining)
  }

  fn switch_case_narrowing_with_type(
    &self,
    target: &SwitchDiscriminant,
    ty: TypeId,
    test: ExprId,
  ) -> Option<(TypeId, TypeId)> {
    match target {
      SwitchDiscriminant::Ident { .. } => {
        let lit = self.literal_value(test)?;
        Some(narrow_by_literal(ty, &lit, &self.store))
      }
      SwitchDiscriminant::Member { prop, .. } => match self.literal_value(test) {
        Some(LiteralValue::String(value)) => {
          let lit = LiteralValue::String(value);
          Some(narrow_by_discriminant(ty, prop, &lit, &self.store))
        }
        _ => None,
      },
      SwitchDiscriminant::Typeof { .. } => match self.literal_value(test) {
        Some(LiteralValue::String(value)) => Some(narrow_by_typeof(ty, &value, &self.store)),
        _ => None,
      },
    }
  }

  fn switch_discriminant_target(
    &self,
    discriminant: ExprId,
    discriminant_ty: TypeId,
    env: &Env,
  ) -> Option<SwitchDiscriminant> {
    match &self.body.exprs[discriminant.0 as usize].kind {
      ExprKind::Unary {
        op: UnaryOp::Typeof,
        expr,
      } => {
        if let Some(binding) = self.ident_binding(*expr) {
          let operand_ty = env
            .get(binding)
            .unwrap_or_else(|| self.expr_types[expr.0 as usize]);
          return Some(SwitchDiscriminant::Typeof {
            name: binding,
            ty: operand_ty,
          });
        }
        None
      }
      ExprKind::Member(mem) => self.switch_member_target(mem, env),
      ExprKind::Ident(_) => {
        self
          .ident_binding(discriminant)
          .map(|binding| SwitchDiscriminant::Ident {
            name: binding,
            ty: env.get(binding).unwrap_or(discriminant_ty),
          })
      }
      _ => None,
    }
  }

  fn switch_member_target(&self, mem: &MemberExpr, env: &Env) -> Option<SwitchDiscriminant> {
    let binding = self.ident_binding(mem.object)?;
    let prop = self.member_property_name(&mem.property)?;
    let obj_ty = env
      .get(binding)
      .unwrap_or_else(|| self.expr_types[mem.object.0 as usize]);
    Some(SwitchDiscriminant::Member {
      name: binding,
      prop,
      ty: obj_ty,
    })
  }

  fn apply_switch_result(&mut self, target: &SwitchDiscriminant, narrowed: TypeId, env: &mut Env) {
    env.set(target.name(), narrowed);
  }
}
