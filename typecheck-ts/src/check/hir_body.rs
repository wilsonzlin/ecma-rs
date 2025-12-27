use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use bumpalo::Bump;
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  ArrayElement, AssignOp, BinaryOp, Body, BodyKind, ExprId, ExprKind, ForHead, ForInit, MemberExpr,
  NameId, NameInterner, ObjectKey, ObjectLiteral, ObjectProperty, PatId, PatKind, StmtId,
  StmtKind, UnaryOp,
};
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat as AstPat};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::{NamespaceBody, NamespaceDecl};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use types_ts_interned::{
  ExpandedType, ObjectType, Param as SigParam, PropData, PropKey, RelateCtx, Shape, Signature,
  TypeEvaluator, TypeExpander, TypeId, TypeKind, TypeStore,
};

use super::cfg::{BlockId, ControlFlowGraph};
use super::flow::{Env, FlowKey, PathSegment};
use super::flow_narrow::{
  and_facts, narrow_by_asserted, narrow_by_assignability, narrow_by_discriminant_path,
  narrow_by_in_check, narrow_by_instanceof, narrow_by_literal, narrow_by_nullish_equality,
  narrow_by_typeof, narrow_non_nullish, or_facts, split_nullish, truthy_falsy_types, Facts,
  LiteralValue,
};

use super::caches::BodyCaches;
use super::expr::resolve_call;
use super::infer::TypeParamDecl;
use super::overload::callable_signatures;
use super::type_expr::{TypeLowerer, TypeResolver};
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

#[derive(Clone, Copy, Default)]
struct ExprContext {
  contextual_type: Option<TypeId>,
  const_context: bool,
}

impl ExprContext {
  fn const_with_type(ty: TypeId) -> Self {
    Self {
      contextual_type: Some(ty),
      const_context: true,
    }
  }
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

#[derive(Default)]
struct AstIndex<'a> {
  stmts: HashMap<TextRange, &'a Node<Stmt>>,
  exprs: HashMap<TextRange, &'a Node<AstExpr>>,
  pats: HashMap<TextRange, &'a Node<AstPat>>,
  params: HashMap<TextRange, &'a Node<ParamDecl>>,
  vars: HashMap<TextRange, VarInfo<'a>>,
  functions: Vec<FunctionInfo<'a>>,
}

#[derive(Clone, Copy)]
struct VarInfo<'a> {
  decl: &'a Node<VarDecl>,
  initializer: Option<&'a Node<AstExpr>>,
  type_annotation: Option<&'a Node<parse_js::ast::type_expr::TypeExpr>>,
}

#[derive(Clone, Copy)]
struct FunctionInfo<'a> {
  func_span: TextRange,
  body_span: TextRange,
  func: &'a Node<Func>,
}

impl<'a> AstIndex<'a> {
  fn new() -> Self {
    Self::default()
  }

  fn index_top_level(&mut self, ast: &'a Node<parse_js::ast::stx::TopLevel>, file: FileId) {
    for stmt in ast.stx.body.iter() {
      self.index_stmt(stmt, file);
    }
  }

  fn index_stmt(&mut self, stmt: &'a Node<Stmt>, file: FileId) {
    let span = loc_to_range(file, stmt.loc);
    self.stmts.insert(span, stmt);
    match stmt.stx.as_ref() {
      Stmt::Expr(expr_stmt) => {
        self.index_expr(&expr_stmt.stx.expr, file);
      }
      Stmt::Return(ret) => {
        if let Some(value) = &ret.stx.value {
          self.index_expr(value, file);
        }
      }
      Stmt::Block(block) => self.index_stmt_list(&block.stx.body, file),
      Stmt::If(if_stmt) => {
        self.index_expr(&if_stmt.stx.test, file);
        self.index_stmt(&if_stmt.stx.consequent, file);
        if let Some(alt) = &if_stmt.stx.alternate {
          self.index_stmt(alt, file);
        }
      }
      Stmt::While(while_stmt) => {
        self.index_expr(&while_stmt.stx.condition, file);
        self.index_stmt(&while_stmt.stx.body, file);
      }
      Stmt::DoWhile(do_while) => {
        self.index_expr(&do_while.stx.condition, file);
        self.index_stmt(&do_while.stx.body, file);
      }
      Stmt::ForTriple(for_stmt) => {
        use parse_js::ast::stmt::ForTripleStmtInit;
        match &for_stmt.stx.init {
          ForTripleStmtInit::Expr(expr) => self.index_expr(expr, file),
          ForTripleStmtInit::Decl(decl) => self.index_var_decl(decl, file),
          ForTripleStmtInit::None => {}
        }
        if let Some(cond) = &for_stmt.stx.cond {
          self.index_expr(cond, file);
        }
        if let Some(post) = &for_stmt.stx.post {
          self.index_expr(post, file);
        }
        self.index_stmt_list(&for_stmt.stx.body.stx.body, file);
      }
      Stmt::ForIn(for_in) => {
        use parse_js::ast::stmt::ForInOfLhs;
        match &for_in.stx.lhs {
          ForInOfLhs::Assign(pat) => self.index_pat(pat, file),
          ForInOfLhs::Decl((_, pat_decl)) => self.index_pat(&pat_decl.stx.pat, file),
        }
        self.index_expr(&for_in.stx.rhs, file);
        self.index_stmt_list(&for_in.stx.body.stx.body, file);
      }
      Stmt::ForOf(for_of) => {
        use parse_js::ast::stmt::ForInOfLhs;
        match &for_of.stx.lhs {
          ForInOfLhs::Assign(pat) => self.index_pat(pat, file),
          ForInOfLhs::Decl((_, pat_decl)) => self.index_pat(&pat_decl.stx.pat, file),
        }
        self.index_expr(&for_of.stx.rhs, file);
        self.index_stmt_list(&for_of.stx.body.stx.body, file);
      }
      Stmt::Switch(sw) => {
        self.index_expr(&sw.stx.test, file);
        for branch in sw.stx.branches.iter() {
          if let Some(case) = &branch.stx.case {
            self.index_expr(case, file);
          }
          for stmt in branch.stx.body.iter() {
            self.index_stmt(stmt, file);
          }
        }
      }
      Stmt::Try(tr) => {
        self.index_stmt_list(&tr.stx.wrapped.stx.body, file);
        if let Some(catch) = &tr.stx.catch {
          if let Some(param) = &catch.stx.parameter {
            self.index_pat(&param.stx.pat, file);
          }
          self.index_stmt_list(&catch.stx.body, file);
        }
        if let Some(finally) = &tr.stx.finally {
          self.index_stmt_list(&finally.stx.body, file);
        }
      }
      Stmt::Throw(th) => self.index_expr(&th.stx.value, file),
      Stmt::Label(label) => self.index_stmt(&label.stx.statement, file),
      Stmt::With(w) => {
        self.index_expr(&w.stx.object, file);
        self.index_stmt(&w.stx.body, file);
      }
      Stmt::VarDecl(decl) => {
        self.index_var_decl(decl, file);
      }
      Stmt::FunctionDecl(func) => {
        self.index_function(&func.stx.function, file);
      }
      Stmt::NamespaceDecl(ns) => self.index_namespace(ns, file),
      Stmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          self.index_stmt_list(body, file);
        }
      }
      Stmt::GlobalDecl(global) => {
        self.index_stmt_list(&global.stx.body, file);
      }
      _ => {}
    }
  }

  fn index_stmt_list(&mut self, stmts: &'a [Node<Stmt>], file: FileId) {
    for stmt in stmts.iter() {
      self.index_stmt(stmt, file);
    }
  }

  fn index_namespace(&mut self, ns: &'a Node<NamespaceDecl>, file: FileId) {
    match &ns.stx.body {
      NamespaceBody::Block(stmts) => self.index_stmt_list(stmts, file),
      NamespaceBody::Namespace(inner) => self.index_namespace(inner, file),
    }
  }

  fn index_var_decl(&mut self, decl: &'a Node<VarDecl>, file: FileId) {
    for declarator in decl.stx.declarators.iter() {
      let pat_span = loc_to_range(file, declarator.pattern.loc);
      self.pats.insert(pat_span, &declarator.pattern.stx.pat);
      self.vars.insert(
        pat_span,
        VarInfo {
          decl,
          initializer: declarator.initializer.as_ref(),
          type_annotation: declarator.type_annotation.as_ref(),
        },
      );
      self.index_pat(&declarator.pattern.stx.pat, file);
      if let Some(init) = &declarator.initializer {
        self.index_expr(init, file);
      }
    }
  }

  fn index_function(&mut self, func: &'a Node<Func>, file: FileId) {
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
        func,
      });
    }

    for param in func.stx.parameters.iter() {
      let pat_span = loc_to_range(file, param.stx.pattern.loc);
      self.pats.insert(pat_span, &param.stx.pattern.stx.pat);
      self.params.insert(pat_span, param);
      self.index_pat(&param.stx.pattern.stx.pat, file);
      if let Some(default) = &param.stx.default_value {
        self.index_expr(default, file);
      }
    }

    if let Some(body) = &func.stx.body {
      match body {
        FuncBody::Block(block) => self.index_stmt_list(block, file),
        FuncBody::Expression(expr) => self.index_expr(expr, file),
      }
    }
  }

  fn index_expr(&mut self, expr: &'a Node<AstExpr>, file: FileId) {
    let span = loc_to_range(file, expr.loc);
    self.exprs.insert(span, expr);
    match expr.stx.as_ref() {
      AstExpr::Binary(bin) => {
        self.index_expr(&bin.stx.left, file);
        self.index_expr(&bin.stx.right, file);
      }
      AstExpr::Call(call) => {
        self.index_expr(&call.stx.callee, file);
        for arg in call.stx.arguments.iter() {
          self.index_expr(&arg.stx.value, file);
        }
      }
      AstExpr::Member(mem) => {
        self.index_expr(&mem.stx.left, file);
      }
      AstExpr::ComputedMember(mem) => {
        self.index_expr(&mem.stx.object, file);
        self.index_expr(&mem.stx.member, file);
      }
      AstExpr::Cond(cond) => {
        self.index_expr(&cond.stx.test, file);
        self.index_expr(&cond.stx.consequent, file);
        self.index_expr(&cond.stx.alternate, file);
      }
      AstExpr::Unary(un) => {
        self.index_expr(&un.stx.argument, file);
      }
      AstExpr::UnaryPostfix(post) => {
        self.index_expr(&post.stx.argument, file);
      }
      AstExpr::LitArr(arr) => {
        for elem in arr.stx.elements.iter() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(v)
            | parse_js::ast::expr::lit::LitArrElem::Rest(v) => self.index_expr(v, file),
            parse_js::ast::expr::lit::LitArrElem::Empty => {}
          }
        }
      }
      AstExpr::LitObj(obj) => {
        for member in obj.stx.members.iter() {
          match &member.stx.typ {
            ObjMemberType::Valued { val, .. } => match val {
              ClassOrObjVal::Prop(Some(expr)) => self.index_expr(expr, file),
              ClassOrObjVal::StaticBlock(block) => self.index_stmt_list(&block.stx.body, file),
              _ => {}
            },
            ObjMemberType::Rest { val } => self.index_expr(val, file),
            ObjMemberType::Shorthand { .. } => {}
          }
        }
      }
      AstExpr::Func(func) => self.index_function(&func.stx.func, file),
      AstExpr::ArrowFunc(func) => self.index_function(&func.stx.func, file),
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
      | AstExpr::NewTarget(..)
      | AstExpr::Class(..) => {}
    }
  }

  fn index_pat(&mut self, pat: &'a Node<AstPat>, file: FileId) {
    let span = loc_to_range(file, pat.loc);
    self.pats.insert(span, pat);
    match pat.stx.as_ref() {
      AstPat::Arr(arr) => {
        for elem in arr.stx.elements.iter().flatten() {
          self.index_pat(&elem.target, file);
          if let Some(default) = &elem.default_value {
            self.index_expr(default, file);
          }
        }
        if let Some(rest) = &arr.stx.rest {
          self.index_pat(rest, file);
        }
      }
      AstPat::Obj(obj) => {
        for prop in obj.stx.properties.iter() {
          self.index_pat(&prop.stx.target, file);
          if let Some(default) = &prop.stx.default_value {
            self.index_expr(default, file);
          }
        }
        if let Some(rest) = &obj.stx.rest {
          self.index_pat(rest, file);
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
  ast: &Node<parse_js::ast::stx::TopLevel>,
  store: Arc<TypeStore>,
  caches: &BodyCaches,
  bindings: &HashMap<String, TypeId>,
  resolver: Option<Arc<dyn TypeResolver>>,
) -> BodyCheckResult {
  check_body_with_expander(
    body_id, body, names, file, ast, store, caches, bindings, resolver, None,
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
  ast: &Node<parse_js::ast::stx::TopLevel>,
  store: Arc<TypeStore>,
  caches: &BodyCaches,
  bindings: &HashMap<String, TypeId>,
  resolver: Option<Arc<dyn TypeResolver>>,
  relate_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> BodyCheckResult {
  let prim = store.primitive_ids();
  let expr_types = vec![prim.unknown; body.exprs.len()];
  let pat_types = vec![prim.unknown; body.pats.len()];
  let expr_spans: Vec<TextRange> = body.exprs.iter().map(|e| e.span).collect();
  let pat_spans: Vec<TextRange> = body.pats.iter().map(|p| p.span).collect();

  let mut index = AstIndex::new();
  index.index_top_level(ast, file);

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
    expr_types,
    pat_types,
    expr_spans,
    pat_spans,
    expr_map,
    pat_map,
    diagnostics: Vec::new(),
    return_types: Vec::new(),
    index,
    scopes: vec![Scope::default()],
    function_type_params: HashMap::new(),
    expected_return: None,
    check_var_assignments: !synthetic_top_level,
    widen_object_literals: true,
    expr_context: ExprContext::default(),
    file,
    ref_expander: relate_expander,
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
      if !checker.check_enclosing_function(body_range) {
        checker.check_stmt_list(&ast.stx.body);
      }
    }
    BodyKind::Initializer => {
      if !checker.check_matching_initializer(body_range) {
        checker.check_stmt_list(&ast.stx.body);
      }
    }
    BodyKind::Class | BodyKind::Unknown => {
      checker.check_stmt_list(&ast.stx.body);
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

struct Checker<'a> {
  store: Arc<TypeStore>,
  relate: RelateCtx<'a>,
  lowerer: TypeLowerer,
  expr_types: Vec<TypeId>,
  pat_types: Vec<TypeId>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
  expr_map: HashMap<TextRange, ExprId>,
  pat_map: HashMap<TextRange, PatId>,
  diagnostics: Vec<Diagnostic>,
  return_types: Vec<TypeId>,
  index: AstIndex<'a>,
  scopes: Vec<Scope>,
  function_type_params: HashMap<TypeId, Vec<TypeParamDecl>>,
  expected_return: Option<TypeId>,
  check_var_assignments: bool,
  widen_object_literals: bool,
  expr_context: ExprContext,
  file: FileId,
  ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
  _names: &'a NameInterner,
  _bump: Bump,
}

impl<'a> Checker<'a> {
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
    let mut best: Option<FunctionInfo<'_>> = None;
    for func in self.index.functions.iter() {
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
        best = Some(*func);
      }
    }
    if let Some(func) = best {
      let prev_return = self.expected_return;
      let mut type_param_decls = Vec::new();
      let mut has_type_params = false;
      if let Some(params) = func.func.stx.type_parameters.as_ref() {
        self.lowerer.push_type_param_scope();
        has_type_params = true;
        type_param_decls = self.lower_type_params(params);
      }
      self.expected_return = func
        .func
        .stx
        .return_type
        .as_ref()
        .map(|ret| self.lowerer.lower_type_expr(ret));
      self.bind_params(func.func, &type_param_decls);
      self.check_function_body(func.func);
      if has_type_params {
        self.lowerer.pop_type_param_scope();
      }
      self.expected_return = prev_return;
      return true;
    }
    false
  }

  fn check_matching_initializer(&mut self, body_range: TextRange) -> bool {
    let mut best: Option<(TextRange, VarInfo<'_>)> = None;
    for (span, info) in self.index.vars.iter() {
      if let Some(init) = info.initializer {
        if contains_range(loc_to_range(self.file, init.loc), body_range) {
          let replace = match best {
            Some((existing_span, _)) => span.start < existing_span.start,
            None => true,
          };
          if replace {
            best = Some((*span, *info));
          }
        }
      }
    }
    if let Some((pat_span, info)) = best {
      if let Some(init) = info.initializer {
        let annotation = info
          .type_annotation
          .map(|ann| self.lowerer.lower_type_expr(ann));
        let init_ty = self.initializer_type(init, annotation);
        let mut ty = annotation.unwrap_or(init_ty);
        if annotation.is_none() {
          let init_is_satisfies = matches!(init.stx.as_ref(), AstExpr::SatisfiesExpr(_));
          ty = self.widen_inferred_binding_type(ty, info.decl.stx.mode, init_is_satisfies);
        }
        if let Some(pat) = self.index.pats.get(&pat_span) {
          self.bind_pattern(pat, ty);
        }
      }
      return true;
    }
    false
  }

  fn bind_params(&mut self, func: &Node<Func>, type_param_decls: &[TypeParamDecl]) {
    for param in func.stx.parameters.iter() {
      let pat_span = loc_to_range(self.file, param.stx.pattern.loc);
      let annotation = param
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| self.lowerer.lower_type_expr(ann));
      let default_ty = param.stx.default_value.as_ref().map(|d| self.check_expr(d));
      let mut ty = annotation.unwrap_or(self.store.primitive_ids().unknown);
      if let Some(default) = default_ty {
        ty = self.store.union(vec![ty, default]);
      }
      if let Some(pat) = self.index.pats.get(&pat_span) {
        self.bind_pattern_with_type_params(pat, ty, type_param_decls.to_vec());
      }
    }
  }

  fn lower_type_params(
    &mut self,
    params: &[Node<parse_js::ast::type_expr::TypeParameter>],
  ) -> Vec<TypeParamDecl> {
    let ids = self.lowerer.register_type_params(params);
    let mut decls = Vec::new();
    for (param, id) in params.iter().zip(ids.iter()) {
      let constraint = param
        .stx
        .constraint
        .as_ref()
        .map(|c| self.lowerer.lower_type_expr(c));
      let default = param
        .stx
        .default
        .as_ref()
        .map(|d| self.lowerer.lower_type_expr(d));
      decls.push(TypeParamDecl {
        id: *id,
        constraint,
        default,
      });
    }
    decls
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

  fn check_stmt_list(&mut self, stmts: &[Node<Stmt>]) {
    for stmt in stmts {
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
            if let Some(params) = self.function_type_params.get(&fn_ty).cloned() {
              self.function_type_params.entry(ty).or_insert(params);
            }
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
    let mode = decl.stx.mode;
    for declarator in decl.stx.declarators.iter() {
      let annot_ty = declarator
        .type_annotation
        .as_ref()
        .map(|ann| self.lowerer.lower_type_expr(ann));
      let init_is_satisfies = declarator
        .initializer
        .as_ref()
        .map(|init| matches!(init.stx.as_ref(), AstExpr::SatisfiesExpr(_)))
        .unwrap_or(false);
      let init_ty = if self.check_var_assignments {
        declarator
          .initializer
          .as_ref()
          .map(|i| self.initializer_type(i, annot_ty))
          .unwrap_or(prim.unknown)
      } else {
        prim.unknown
      };
      if self.check_var_assignments {
        if let (Some(ann), Some(init)) = (annot_ty, declarator.initializer.as_ref()) {
          self.check_assignable(init, init_ty, ann);
        }
      }
      let mut ty = annot_ty.unwrap_or(init_ty);
      if annot_ty.is_none() && self.check_var_assignments {
        ty = self.widen_inferred_binding_type(ty, mode, init_is_satisfies);
      }
      self.check_pat(&declarator.pattern.stx.pat, ty);
    }
  }

  fn initializer_type(
    &mut self,
    init: &Node<AstExpr>,
    annotation: Option<TypeId>,
  ) -> TypeId {
    let prev = self.widen_object_literals;
    if annotation.is_some() {
      self.widen_object_literals = false;
    }
    let init_ty = self.check_expr(init);
    self.widen_object_literals = prev;
    if let Some(expected) = annotation {
      let contextual = self.contextual_arg_type(init_ty, expected);
      if contextual != init_ty {
        self.record_expr_type(init.loc, contextual);
      }
      contextual
    } else {
      init_ty
    }
  }

  fn widen_inferred_binding_type(
    &self,
    ty: TypeId,
    mode: VarDeclMode,
    skip_containers: bool,
  ) -> TypeId {
    let mut widened = ty;
    if !skip_containers {
      widened = self.widen_array_elements(widened);
      widened = self.widen_object_literal(widened);
    }
    if !matches!(mode, VarDeclMode::Const) {
      widened = self.widen_literal(widened);
    }
    widened
  }

  fn widen_literal(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::NumberLiteral(_) => prim.number,
      TypeKind::StringLiteral(_) => prim.string,
      TypeKind::BooleanLiteral(_) => prim.boolean,
      _ => ty,
    }
  }

  fn widen_union_literals(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::NumberLiteral(_) => prim.number,
      TypeKind::StringLiteral(_) => prim.string,
      TypeKind::BooleanLiteral(_) => prim.boolean,
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_union_literals(m))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Array { ty, readonly } => {
        let widened = self.widen_union_literals(ty);
        self
          .store
          .intern_type(TypeKind::Array { ty: widened, readonly })
      }
      _ => ty,
    }
  }

  fn widen_array_elements(&self, ty: TypeId) -> TypeId {
    match self.store.type_kind(ty) {
      TypeKind::Array { ty, readonly } => {
        let widened = self.widen_union_literals(ty);
        self
          .store
          .intern_type(TypeKind::Array { ty: widened, readonly })
      }
      _ => ty,
    }
  }

  fn widen_object_literal(&self, ty: TypeId) -> TypeId {
    match self.store.type_kind(ty) {
      TypeKind::Object(obj_id) => {
        let obj = self.store.object(obj_id);
        let mut shape = self.store.shape(obj.shape);
        let mut changed = false;
        for prop in shape.properties.iter_mut() {
          if prop.data.readonly {
            continue;
          }
          let widened = self.widen_union_literals(prop.data.ty);
          if widened != prop.data.ty {
            prop.data.ty = widened;
            changed = true;
          }
        }
        for idx in shape.indexers.iter_mut() {
          if idx.readonly {
            continue;
          }
          let widened = self.widen_union_literals(idx.value_type);
          if widened != idx.value_type {
            idx.value_type = widened;
            changed = true;
          }
        }
        if changed {
          let shape_id = self.store.intern_shape(shape);
          let obj_id = self.store.intern_object(ObjectType { shape: shape_id });
          self.store.intern_type(TypeKind::Object(obj_id))
        } else {
          ty
        }
      }
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_literal(m))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_literal(m))
          .collect();
        self.store.intersection(mapped)
      }
      _ => ty,
    }
  }

  fn check_namespace(&mut self, ns: &Node<NamespaceDecl>) {
    match &ns.stx.body {
      NamespaceBody::Block(stmts) => self.check_stmt_list(stmts),
      NamespaceBody::Namespace(inner) => self.check_namespace(inner),
    }
  }

  fn check_pat(&mut self, pat: &Node<AstPat>, value_ty: TypeId) {
    self.bind_pattern(pat, value_ty);
  }

  fn with_expr_context<R>(&mut self, ctx: ExprContext, f: impl FnOnce(&mut Self) -> R) -> R {
    let prev_ctx = self.expr_context;
    let prev_widen = self.widen_object_literals;
    if ctx.const_context {
      self.widen_object_literals = false;
    }
    self.expr_context = ctx;
    let result = f(self);
    self.expr_context = prev_ctx;
    self.widen_object_literals = prev_widen;
    result
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
      AstExpr::Unary(un) => self.check_unary(un.stx.operator, &un.stx.argument),
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
        let (callee_ty, this_arg) = match call.stx.callee.stx.as_ref() {
          AstExpr::Member(mem) => {
            let obj_ty = self.check_expr(&mem.stx.left);
            let callee_ty = self.member_type(obj_ty, &mem.stx.right);
            self.record_expr_type(call.stx.callee.loc, callee_ty);
            (callee_ty, Some(obj_ty))
          }
          AstExpr::ComputedMember(mem) => {
            let obj_ty = self.check_expr(&mem.stx.object);
            let _ = self.check_expr(&mem.stx.member);
            let callee_ty = self.member_type(obj_ty, "<computed>");
            self.record_expr_type(call.stx.callee.loc, callee_ty);
            (callee_ty, Some(obj_ty))
          }
          _ => (self.check_expr(&call.stx.callee), None),
        };
        let arg_types: Vec<TypeId> = call
          .stx
          .arguments
          .iter()
          .map(|arg| self.check_expr(&arg.stx.value))
          .collect();
        let span = Span {
          file: self.file,
          range: loc_to_range(self.file, call.loc),
        };
        let type_params = self
          .function_type_params
          .get(&callee_ty)
          .cloned()
          .unwrap_or_default();
        let resolution = resolve_call(
          &self.store,
          &self.relate,
          callee_ty,
          &arg_types,
          this_arg,
          &type_params,
          None,
          span,
        );
        for diag in &resolution.diagnostics {
          self.diagnostics.push(diag.clone());
        }
        if resolution.diagnostics.is_empty() {
          if let Some(sig_id) = resolution.signature {
            let sig = self.store.signature(sig_id);
            let params = self.params_for_call(&sig);
            for (idx, arg) in call.stx.arguments.iter().enumerate() {
              if let Some(param) = params.get(idx) {
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
              let target = params
                .iter()
                .enumerate()
                .find(|(_, p)| p.name == Some(param_name))
                .or_else(|| params.get(0).map(|p| (0usize, p)));
              if let Some((idx, _)) = target {
                if let Some(arg) = call.stx.arguments.get(idx) {
                  if let AstExpr::Id(id) = arg.stx.value.stx.as_ref() {
                    self.insert_binding(id.stx.name.clone(), asserted.clone(), Vec::new());
                  }
                }
              }
            }
            let required = params.iter().filter(|p| !p.optional && !p.rest).count();
            let has_rest = params.iter().any(|p| p.rest);
            let max = if has_rest { None } else { Some(params.len()) };
            if arg_types.len() < required || max.map_or(false, |m| arg_types.len() > m) {
              self
                .diagnostics
                .push(codes::ARGUMENT_COUNT_MISMATCH.error("argument count mismatch", span));
            }
          }
        }
        let contextual_sig = resolution.signature.or_else(|| {
          callable_signatures(self.store.as_ref(), callee_ty)
            .into_iter()
            .next()
        });
        if let Some(sig_id) = contextual_sig {
          let sig = self.store.signature(sig_id);
          let params = self.params_for_call(&sig);
          for (idx, arg) in call.stx.arguments.iter().enumerate() {
            if let Some(param) = params.get(idx) {
              let arg_ty = arg_types
                .get(idx)
                .copied()
                .unwrap_or(self.store.primitive_ids().unknown);
              let contextual = self.contextual_arg_type(arg_ty, param.ty);
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
        let lhs_ty = self.with_expr_context(ExprContext::const_with_type(target_ty), |checker| {
          checker.check_expr(&expr.stx.expression)
        });
        self.check_assignable(&expr.stx.expression, lhs_ty, target_ty);
        lhs_ty
      }
      _ => self.store.primitive_ids().unknown,
    };
    self.record_expr_type(expr.loc, ty);
    ty
  }

  fn array_literal_type(&mut self, arr: &Node<parse_js::ast::expr::lit::LitArrExpr>) -> TypeId {
    let mut elems = Vec::new();
    for (idx, elem) in arr.stx.elements.iter().enumerate() {
      let elem_ctx = self.contextual_array_element_ctx(idx);
      match elem {
        parse_js::ast::expr::lit::LitArrElem::Single(v) => {
          elems.push(self.check_array_element(v, elem_ctx))
        }
        parse_js::ast::expr::lit::LitArrElem::Rest(v) => {
          elems.push(self.check_array_element(v, elem_ctx))
        }
        parse_js::ast::expr::lit::LitArrElem::Empty => {}
      }
    }
    let elem_ty = if elems.is_empty() {
      self.store.primitive_ids().unknown
    } else {
      self.store.union(elems)
    };
    self.store.intern_type(TypeKind::Array {
      ty: elem_ty,
      readonly: false,
    })
  }

  fn check_array_element(&mut self, expr: &Node<AstExpr>, ctx: Option<ExprContext>) -> TypeId {
    match ctx {
      Some(ctx) => self.with_expr_context(ctx, |checker| checker.check_expr(expr)),
      None => self.check_expr(expr),
    }
  }

  fn contextual_array_element_ctx(&self, index: usize) -> Option<ExprContext> {
    self
      .contextual_array_element_type(index)
      .map(|ty| ExprContext {
        contextual_type: Some(ty),
        const_context: self.expr_context.const_context,
      })
  }

  fn contextual_array_element_type(&self, index: usize) -> Option<TypeId> {
    let contextual = self.expr_context.contextual_type?;
    match self.store.type_kind(contextual) {
      TypeKind::Array { ty, .. } => Some(ty),
      TypeKind::Tuple(elems) => elems
        .get(index)
        .map(|elem| elem.ty)
        .or_else(|| elems.iter().find(|elem| elem.rest).map(|elem| elem.ty)),
      _ => None,
    }
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
    _op: OperatorName,
    left: &Node<AstExpr>,
    right: &Node<AstExpr>,
  ) -> TypeId {
    let value_ty = self.check_expr(right);
    match left.stx.as_ref() {
      AstExpr::Id(id) => {
        if let Some(binding) = self.lookup(&id.stx.name) {
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
        } else {
          self.insert_binding(id.stx.name.clone(), value_ty, Vec::new());
        }
      }
      AstExpr::ArrPat(arr) => {
        let span = loc_to_range(self.file, arr.loc);
        if let Some(pat) = self.index.pats.get(&span) {
          self.bind_pattern(pat, value_ty);
        }
      }
      AstExpr::ObjPat(obj) => {
        let span = loc_to_range(self.file, obj.loc);
        if let Some(pat) = self.index.pats.get(&span) {
          self.bind_pattern(pat, value_ty);
        }
      }
      _ => {}
    }
    value_ty
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
    let shape = match self.store.type_kind(value) {
      TypeKind::Object(obj_id) => Some(self.store.shape(self.store.object(obj_id).shape)),
      _ => None,
    };
    for prop in obj.stx.properties.iter() {
      let key_name = match &prop.stx.key {
        ClassOrObjKey::Direct(direct) => Some(direct.stx.key.clone()),
        ClassOrObjKey::Computed(_) => None,
      };
      let mut prop_ty = prim.unknown;
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

  fn function_type(&mut self, func: &Node<Func>) -> TypeId {
    let mut type_param_decls = Vec::new();
    let mut type_params_ids = Vec::new();
    let mut has_type_params = false;
    if let Some(params) = func.stx.type_parameters.as_ref() {
      self.lowerer.push_type_param_scope();
      has_type_params = true;
      type_param_decls = self.lower_type_params(params);
      type_params_ids = type_param_decls.iter().map(|d| d.id).collect();
    }
    let mut param_start = 0usize;
    let mut this_param = None;
    if let Some(first) = func.stx.parameters.first() {
      if let AstPat::Id(id) = first.stx.pattern.stx.pat.stx.as_ref() {
        if id.stx.name == "this" {
          if let Some(annotation) = first.stx.type_annotation.as_ref() {
            this_param = Some(self.lowerer.lower_type_expr(annotation));
            param_start = 1;
          }
        }
      }
    }
    let params = func
      .stx
      .parameters
      .iter()
      .skip(param_start)
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
    let sig = Signature {
      params,
      ret,
      type_params: type_params_ids,
      this_param,
    };
    let sig_id = self.store.intern_signature(sig);
    let ty = self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    });
    if !type_param_decls.is_empty() {
      self.function_type_params.insert(ty, type_param_decls);
    }
    if has_type_params {
      self.lowerer.pop_type_param_scope();
    }
    ty
  }

  fn params_for_call<'b>(&self, sig: &'b Signature) -> &'b [SigParam] {
    if sig.this_param.is_some() {
      if let Some(first) = sig.params.first() {
        if let Some(name) = first.name {
          if self.store.name(name) == "this" {
            return &sig.params[1..];
          }
        }
      }
    }
    sig.params.as_slice()
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
      // Fresh object literals only participate in excess property checking for
      // now; other assignability rules (e.g. structural compatibility) are
      // handled elsewhere in the type relation engine.
      return;
    }
    if self.relate.is_assignable(src, dst) {
      return;
    }
    self.diagnostics.push(codes::TYPE_MISMATCH.error(
      "type mismatch",
      Span {
        file: self.file,
        range: loc_to_range(self.file, expr.loc),
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
    TextRange::new(0, 0)
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
  _file: FileId,
  _source: &str,
  store: Arc<TypeStore>,
  initial: &HashMap<NameId, TypeId>,
) -> BodyCheckResult {
  let mut checker = FlowBodyChecker::new(body_id, body, names, Arc::clone(&store), initial);
  checker.run(initial);
  checker.into_result()
}

struct FlowBodyChecker<'a> {
  body_id: BodyId,
  body: &'a Body,
  names: &'a NameInterner,
  store: Arc<TypeStore>,
  relate: RelateCtx<'a>,
  expr_types: Vec<TypeId>,
  pat_types: Vec<TypeId>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
  diagnostics: Vec<Diagnostic>,
  return_types: Vec<TypeId>,
  return_indices: HashMap<StmtId, usize>,
  widen_object_literals: bool,
  initial: HashMap<NameId, TypeId>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BindingMode {
  Declare,
  Assign,
}

struct OptionalChainInfo {
  base: FlowKey,
  base_ty: TypeId,
  result_ty: Option<TypeId>,
}

#[derive(Clone)]
struct AccessPathInfo {
  path: FlowKey,
  optional: bool,
}

impl<'a> FlowBodyChecker<'a> {
  fn new(
    body_id: BodyId,
    body: &'a Body,
    names: &'a NameInterner,
    store: Arc<TypeStore>,
    initial: &HashMap<NameId, TypeId>,
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
    let relate = RelateCtx::with_hooks(Arc::clone(&store), store.options(), super::relate_hooks());

    Self {
      body_id,
      body,
      names,
      store,
      relate,
      expr_types,
      pat_types,
      expr_spans,
      pat_spans,
      diagnostics: Vec::new(),
      return_types,
      return_indices,
      widen_object_literals: true,
      initial: initial.clone(),
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

  fn access_path_info(&self, expr_id: ExprId) -> Option<AccessPathInfo> {
    let expr = &self.body.exprs[expr_id.0 as usize];
    match &expr.kind {
      ExprKind::Ident(name) => Some(AccessPathInfo {
        path: FlowKey::root(*name),
        optional: false,
      }),
      ExprKind::Member(mem) => {
        let base = self.access_path_info(mem.object)?;
        let segment = self.path_segment(&mem.property)?;
        Some(AccessPathInfo {
          path: base.path.with_segment(segment),
          optional: base.optional || mem.optional,
        })
      }
      _ => None,
    }
  }

  fn access_path_root(&self, expr_id: ExprId) -> Option<NameId> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => Some(*name),
      ExprKind::Member(mem) => self.access_path_root(mem.object),
      _ => None,
    }
  }

  fn ident_name(&self, expr_id: ExprId) -> Option<NameId> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => Some(*name),
      _ => None,
    }
  }

  fn path_segment(&self, key: &ObjectKey) -> Option<PathSegment> {
    match key {
      ObjectKey::Ident(id) => Some(PathSegment::String(self.hir_name(*id))),
      ObjectKey::String(s) => Some(PathSegment::String(s.clone())),
      ObjectKey::Number(n) => Some(PathSegment::Number(n.clone())),
      ObjectKey::Computed(expr) => self.literal_segment(*expr),
    }
  }

  fn literal_segment(&self, expr_id: ExprId) -> Option<PathSegment> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Literal(hir_js::Literal::String(s)) => Some(PathSegment::String(s.clone())),
      ExprKind::Literal(hir_js::Literal::Number(n)) => Some(PathSegment::Number(n.clone())),
      _ => None,
    }
  }

  fn invalidate_access_path(&mut self, expr_id: ExprId, env: &mut Env) {
    if let Some(path) = self.access_path_info(expr_id) {
      env.invalidate_prefix(&path.path);
    } else if let Some(root) = self.access_path_root(expr_id) {
      env.invalidate_prefix(&FlowKey::root(root));
    } else {
      env.invalidate_all();
    }
  }

  fn run(&mut self, initial: &HashMap<NameId, TypeId>) {
    let cfg = ControlFlowGraph::from_body(self.body);
    let mut in_envs: Vec<Option<Env>> = vec![None; cfg.blocks.len()];
    in_envs[cfg.entry.0] = Some(Env::with_initial(initial));
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

  fn process_block(
    &mut self,
    block_id: BlockId,
    mut env: Env,
    cfg: &ControlFlowGraph,
  ) -> Vec<(BlockId, Env)> {
    let block = &cfg.blocks[block_id.0];
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
          for declarator in decl.declarators.iter() {
            let init_ty = declarator
              .init
              .map(|id| self.eval_expr(id, &mut env).0)
              .unwrap_or_else(|| self.store.primitive_ids().unknown);
            self.bind_pat(declarator.pat, init_ty, &mut env);
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
        StmtKind::DoWhile { test, .. } => {
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
        StmtKind::For { init, test, .. } => {
          if let Some(init) = init {
            match init {
              ForInit::Expr(expr_id) => {
                let _ = self.eval_expr(*expr_id, &mut env);
              }
              ForInit::Var(var) => {
                for declarator in var.declarators.iter() {
                  let init_ty = declarator
                    .init
                    .map(|id| self.eval_expr(id, &mut env).0)
                    .unwrap_or_else(|| self.store.primitive_ids().unknown);
                  self.bind_pat(declarator.pat, init_ty, &mut env);
                }
              }
            }
          }
          let facts = test
            .map(|t| self.eval_expr(t, &mut env).1)
            .unwrap_or_default();
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
        StmtKind::ForIn {
          left,
          right,
          is_for_of,
          ..
        } => {
          let right_ty = self.eval_expr(*right, &mut env).0;
          let iter_ty = if *is_for_of {
            self.iterable_element_type(right_ty)
          } else {
            self.for_in_key_type(right_ty)
          };
          match left {
            ForHead::Pat(pat) => self.assign_pat(*pat, iter_ty, &mut env),
            ForHead::Var(var) => {
              for declarator in var.declarators.iter() {
                self.bind_pat(declarator.pat, iter_ty, &mut env);
              }
            }
          }
          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, env.clone()));
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
          for (idx, case) in cases.iter().enumerate() {
            if let Some(succ) = block.successors.get(idx) {
              let mut case_env = env.clone();
              if let Some(test) = case.test {
                let _ = self.eval_expr(test, &mut case_env);
                self.apply_switch_narrowing(*discriminant, discriminant_ty, test, &mut case_env);
              }
              outgoing.push((*succ, case_env));
            }
          }
          // If there is an implicit default edge (no default case), use the final successor.
          if block.successors.len() > cases.len() {
            if let Some(succ) = block.successors.last() {
              outgoing.push((*succ, env.clone()));
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

  fn iterable_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => {
        let elem_tys: Vec<_> = elems.into_iter().map(|e| e.ty).collect();
        if elem_tys.is_empty() {
          prim.unknown
        } else {
          self.store.union(elem_tys)
        }
      }
      TypeKind::Union(members) => {
        let elem_tys: Vec<_> = members
          .into_iter()
          .map(|member| self.iterable_element_type(member))
          .collect();
        if elem_tys.is_empty() {
          prim.unknown
        } else {
          self.store.union(elem_tys)
        }
      }
      _ => prim.unknown,
    }
  }

  fn for_in_key_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Array { .. } | TypeKind::Tuple(_) => {
        self.store.union(vec![prim.string, prim.number])
      }
      TypeKind::Union(members) => {
        let key_tys: Vec<_> = members
          .into_iter()
          .map(|member| self.for_in_key_type(member))
          .collect();
        if key_tys.is_empty() {
          prim.string
        } else {
          self.store.union(key_tys)
        }
      }
      _ => prim.string,
    }
  }

  fn record_return(&mut self, stmt: StmtId, ty: TypeId) {
    let prim = self.store.primitive_ids();
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
    let prim = self.store.primitive_ids();
    let expr = &self.body.exprs[expr_id.0 as usize];
    let mut facts = Facts::default();
    let ty = match &expr.kind {
      ExprKind::Ident(name) => {
        let key = FlowKey::root(*name);
        let ty = env.get_path(&key).unwrap_or(prim.unknown);
        let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
        facts.truthy.insert(key.clone(), truthy);
        facts.falsy.insert(key, falsy);
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
          let _ = self.eval_expr(*expr, env);
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
          if let Some(target) = self.access_path_info(left_expr) {
            let (yes, no) = narrow_by_instanceof(left_ty, &self.store);
            facts.truthy.insert(target.path.clone(), yes);
            facts.falsy.insert(target.path, no);
          }
          prim.boolean
        }
        BinaryOp::In => {
          let _ = self.eval_expr(*left, env);
          let right_ty = self.eval_expr(*right, env).0;
          if let (Some(prop), Some(target)) =
            (self.literal_prop(*left), self.access_path_info(*right))
          {
            let (yes, no) = narrow_by_in_check(right_ty, &prop, &self.store);
            facts.truthy.insert(target.path.clone(), yes);
            facts.falsy.insert(target.path, no);
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
        let ret_ty = self.eval_call(call, env, &mut facts);
        let mut ty = ret_ty;
        if call.optional {
          if let Some(base) = self.optional_chain_root(call.callee) {
            let base_ty = env
              .get_path(&base)
              .unwrap_or_else(|| self.expr_types[call.callee.0 as usize]);
            let (non_nullish, nullish) = split_nullish(base_ty, &self.store);
            if non_nullish != prim.never {
              facts.truthy.insert(base.clone(), non_nullish);
            }
            if nullish != prim.never {
              facts.falsy.insert(base, nullish);
            }
          }
          ty = self.store.union(vec![ty, prim.undefined]);
        }
        ty
      }
      ExprKind::Member(mem) => {
        let obj_ty = self.eval_expr(mem.object, env).0;
        let ty = self.member_type(obj_ty, &mem, env);
        if let Some(info) = self.access_path_info(expr_id) {
          let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
          facts.truthy.insert(info.path.clone(), truthy);
          facts.falsy.insert(info.path.clone(), falsy);
          if info.optional {
            let root = FlowKey::root(info.path.root);
            if let Some(root_ty) = env.get_path(&root) {
              let (non_nullish, nullish) = split_nullish(root_ty, &self.store);
              if non_nullish != prim.never {
                facts.truthy.insert(root.clone(), non_nullish);
              }
              if nullish != prim.never {
                facts.falsy.insert(root, nullish);
              }
            }
          }
        }
        ty
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
      ExprKind::TypeAssertion { expr } => self.eval_expr(*expr, env).0,
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
      ExprKind::Satisfies { expr } => {
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
        *out = or_facts(left_facts, right_facts, &self.store);
        self.store.union(vec![left_ty, right_ty])
      }
      BinaryOp::NullishCoalescing => {
        let prim = self.store.primitive_ids();
        let (non_nullish, nullish) = narrow_non_nullish(left_ty, &self.store);
        out.assertions = left_facts.assertions;
        if nullish == prim.never {
          return non_nullish;
        }

        let mut right_env = env.clone();
        if let Some(path) = self.access_path_info(left) {
          right_env.set_path(path.path, nullish);
        } else if let Some(root) = self.access_path_root(left) {
          right_env.set_var(root, nullish);
        }
        let right_ty = self.eval_expr(right, &mut right_env).0;
        self.store.union(vec![non_nullish, right_ty])
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

    let mut apply = |target: FlowKey, yes: TypeId, no: TypeId| {
      if negate {
        out.truthy.insert(target.clone(), no);
        out.falsy.insert(target, yes);
      } else {
        out.truthy.insert(target.clone(), yes);
        out.falsy.insert(target, no);
      }
    };

    let left_path = self.access_path_info(left);
    let right_path = self.access_path_info(right);

    if let (Some(target), Some(lit)) = (left_path.as_ref(), self.literal_value(right)) {
      let (yes, no) = if matches!(lit, LiteralValue::Null | LiteralValue::Undefined) {
        narrow_by_nullish_equality(left_ty, op, &lit, &self.store)
      } else {
        narrow_by_literal(left_ty, &lit, &self.store)
      };
      apply(target.path.clone(), yes, no);
      if let LiteralValue::String(value) = &lit {
        if !target.path.segments.is_empty() {
          let root = FlowKey::root(target.path.root);
          if let Some(root_ty) = env.get_path(&root) {
            let (yes_root, no_root) =
              narrow_by_discriminant_path(root_ty, &target.path.segments, value, &self.store);
            apply(root, yes_root, no_root);
          }
        }
      }
      return;
    }
    if let (Some(target), Some(lit)) = (right_path.as_ref(), self.literal_value(left)) {
      let (yes, no) = if matches!(lit, LiteralValue::Null | LiteralValue::Undefined) {
        narrow_by_nullish_equality(right_ty, op, &lit, &self.store)
      } else {
        narrow_by_literal(right_ty, &lit, &self.store)
      };
      apply(target.path.clone(), yes, no);
      if let LiteralValue::String(value) = &lit {
        if !target.path.segments.is_empty() {
          let root = FlowKey::root(target.path.root);
          if let Some(root_ty) = env.get_path(&root) {
            let (yes_root, no_root) =
              narrow_by_discriminant_path(root_ty, &target.path.segments, value, &self.store);
            apply(root, yes_root, no_root);
          }
        }
      }
      return;
    }

    if !negate {
      if let (Some((left_key, _)), Some((right_key, _))) =
        (self.reference_from_expr(left, left_ty), self.reference_from_expr(right, right_ty))
      {
        let (left_yes, _) = narrow_by_assignability(left_ty, right_ty, &self.store, &self.relate);
        let (right_yes, _) = narrow_by_assignability(right_ty, left_ty, &self.store, &self.relate);
        if left_key == right_key {
          let combined = self.store.intersection(vec![left_yes, right_yes]);
          apply(left_key, combined, left_ty);
        } else {
          apply(left_key, left_yes, left_ty);
          apply(right_key, right_yes, right_ty);
        }
        return;
      }
    }

    if let Some((target, target_ty, lit)) = self.typeof_comparison(left, right) {
      let (yes, no) = narrow_by_typeof(target_ty, &lit, &self.store);
      apply(target, yes, no);
    }

    self.optional_chain_equality_facts(left, right_ty, negate, env, out);
    self.optional_chain_equality_facts(right, left_ty, negate, env, out);
  }

  fn eval_call(&mut self, call: &hir_js::CallExpr, env: &mut Env, out: &mut Facts) -> TypeId {
    let prim = self.store.primitive_ids();
    let callee_ty = self.eval_expr(call.callee, env).0;
    let arg_tys: Vec<TypeId> = call
      .args
      .iter()
      .map(|arg| self.eval_expr(arg.expr, env).0)
      .collect();
    if let TypeKind::Callable { overloads } = self.store.type_kind(callee_ty) {
      if let Some(sig_id) = overloads.first() {
        let sig = self.store.signature(*sig_id);
        if let TypeKind::Predicate {
          asserted,
          asserts,
          parameter,
        } = self.store.type_kind(sig.ret)
        {
          if let Some(asserted) = asserted {
            let target_idx = parameter
              .and_then(|param_name| sig.params.iter().position(|p| p.name == Some(param_name)))
              .or(Some(0));
            if let Some(idx) = target_idx {
              if let Some(arg_expr) = call.args.get(idx).map(|a| a.expr) {
                if let Some(target) = self.access_path_info(arg_expr) {
                  let arg_ty = arg_tys.get(idx).copied().unwrap_or(prim.unknown);
                  let (yes, no) = narrow_by_asserted(arg_ty, asserted, &self.store);
                  if asserts {
                    out.assertions.insert(target.path, yes);
                  } else {
                    out.truthy.insert(target.path.clone(), yes);
                    out.falsy.insert(target.path, no);
                  }
                }
              }
            }
          }
          return if asserts {
            prim.undefined
          } else {
            prim.boolean
          };
        }
        return sig.ret;
      }
    }
    prim.unknown
  }

  fn optional_chain_equality_facts(
    &mut self,
    expr: ExprId,
    other_ty: TypeId,
    negate: bool,
    env: &mut Env,
    out: &mut Facts,
  ) {
    let prim = self.store.primitive_ids();
    let Some(info) = self.optional_chain_info(expr, env) else {
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
      target.insert(info.base.clone(), non_nullish_base);
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
          target.insert(info.base, nullish_base);
        }
      }
    }
  }

  fn optional_chain_info(&mut self, expr: ExprId, env: &mut Env) -> Option<OptionalChainInfo> {
    match &self.body.exprs[expr.0 as usize].kind {
      ExprKind::Member(mem) if mem.optional => {
        let base = self.optional_chain_root(mem.object)?;
        let base_ty = env
          .get_path(&base)
          .unwrap_or(self.expr_types[mem.object.0 as usize]);
        let result_ty = Some(self.member_type(base_ty, mem, env));
        Some(OptionalChainInfo {
          base,
          base_ty,
          result_ty,
        })
      }
      ExprKind::Call(call) if call.optional => {
        let base = self.optional_chain_root(call.callee)?;
        let base_ty = env
          .get_path(&base)
          .unwrap_or(self.expr_types[call.callee.0 as usize]);
        Some(OptionalChainInfo {
          base,
          base_ty,
          result_ty: None,
        })
      }
      _ => None,
    }
  }

  fn optional_chain_root(&self, expr_id: ExprId) -> Option<FlowKey> {
    match self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => Some(FlowKey::root(name)),
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
      ExprKind::Literal(hir_js::Literal::Number(n)) => Some(n.clone()),
      _ => None,
    }
  }

  fn reference_from_expr(&self, expr_id: ExprId, expr_ty: TypeId) -> Option<(FlowKey, TypeId)> {
    self
      .access_path_info(expr_id)
      .map(|info| (info.path, expr_ty))
  }

  fn assignment_target_root_expr(&self, expr_id: ExprId) -> Option<NameId> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => Some(*name),
      ExprKind::Member(mem) => self.assignment_target_root_expr(mem.object),
      ExprKind::TypeAssertion { expr }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr }
      | ExprKind::Await { expr }
      | ExprKind::Yield { expr: Some(expr), .. } => self.assignment_target_root_expr(*expr),
      _ => None,
    }
  }

  fn record_assignment_facts(&self, root: Option<NameId>, ty: TypeId, facts: &mut Facts) {
    if let Some(name) = root {
      let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
      let key = FlowKey::root(name);
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

  fn typeof_comparison(&self, left: ExprId, right: ExprId) -> Option<(FlowKey, TypeId, String)> {
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
        if let Some(path) = self.access_path_info(*expr) {
          return Some((path.path, self.expr_types[expr.0 as usize], s.clone()));
        }
      }
      (
        ExprKind::Literal(hir_js::Literal::String(s)),
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        },
      ) => {
        if let Some(path) = self.access_path_info(*expr) {
          return Some((path.path, self.expr_types[expr.0 as usize], s.clone()));
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
  ) -> (TypeId, Option<NameId>, bool) {
    let prim = self.store.primitive_ids();
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => (
        env.get_path(&FlowKey::root(*name)).unwrap_or(prim.unknown),
        Some(*name),
        false,
      ),
      ExprKind::Member(mem) => {
        let obj_ty = self.eval_expr(mem.object, env).0;
        let prop_ty = match &mem.property {
          ObjectKey::Computed(prop) => {
            let _ = self.eval_expr(*prop, env);
            prim.unknown
          }
          _ => self.member_type(obj_ty, mem, env),
        };
        let root = self.assignment_target_root_expr(mem.object);
        (prop_ty, root, matches!(mem.property, ObjectKey::Computed(_)))
      }
      ExprKind::TypeAssertion { expr }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr } => self.assignment_expr_info(*expr, env),
      _ => (prim.unknown, None, false),
    }
  }

  fn assignment_target_info(
    &mut self,
    pat_id: PatId,
    env: &mut Env,
  ) -> (TypeId, Option<NameId>, bool) {
    let pat = &self.body.pats[pat_id.0 as usize];
    let prim = self.store.primitive_ids();
    match &pat.kind {
      PatKind::Ident(name) => (
        env
          .get_path(&FlowKey::root(*name))
          .unwrap_or(prim.unknown),
        Some(*name),
        false,
      ),
      PatKind::Assign { target, .. } => self.assignment_target_info(*target, env),
      PatKind::Rest(inner) => self.assignment_target_info(**inner, env),
      PatKind::AssignTarget(expr) => self.assignment_expr_info(*expr, env),
      _ => (prim.unknown, None, false),
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
    root: Option<NameId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (left_truthy, left_falsy) = truthy_falsy_types(left_base, &self.store);
    let mut right_env = env.clone();
    if let Some(name) = root {
      right_env.set_var(name, left_truthy);
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
    root: Option<NameId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (left_truthy, left_falsy) = truthy_falsy_types(left_base, &self.store);
    let mut right_env = env.clone();
    if let Some(name) = root {
      right_env.set_var(name, left_falsy);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self.store.union(vec![left_truthy, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  fn nullish_assign(
    &mut self,
    target: PatId,
    left: TypeId,
    value: ExprId,
    root: Option<NameId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (nonnullish, nullish) = self.split_nullish(left_base);
    let mut right_env = env.clone();
    if let Some(name) = root {
      right_env.set_var(name, nullish);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self.store.union(vec![nonnullish, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  fn assign_pat(&mut self, pat_id: PatId, value_ty: TypeId, env: &mut Env) {
    self.bind_pat_with_mode(pat_id, value_ty, env, BindingMode::Assign);
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
      PatKind::Ident(name) => {
        env.set_var(*name, write_ty);
      }
      PatKind::Assign { target, default_value } => {
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
        if let Some(path) = self.access_path_info(*expr) {
          env.set_path(path.path, value_ty);
        } else if let Some(root) = self.access_path_root(*expr) {
          env.invalidate_prefix(&FlowKey::root(root));
        } else {
          env.invalidate_all();
        }
      }
    }
  }

  fn write_assign_target_expr(
    &mut self,
    expr_id: ExprId,
    value_ty: TypeId,
    env: &mut Env,
    _mode: BindingMode,
  ) {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => {
        env.set_var(*name, value_ty);
      }
      ExprKind::Member(_) => {
        if let Some(path) = self.access_path_info(expr_id) {
          env.set_path(path.path, value_ty);
        } else if let Some(root) = self.assignment_target_root_expr(expr_id) {
          env.invalidate_prefix(&FlowKey::root(root));
        } else {
          env.invalidate_all();
        }
      }
      ExprKind::TypeAssertion { expr }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr } => {
        self.write_assign_target_expr(*expr, value_ty, env, _mode);
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

  fn member_type(&mut self, obj: TypeId, mem: &MemberExpr, env: &mut Env) -> TypeId {
    let prim = self.store.primitive_ids();
    let path_info = self.access_path_info(mem.object).and_then(|base| {
      self.path_segment(&mem.property).map(|seg| AccessPathInfo {
        path: base.path.with_segment(seg),
        optional: base.optional || mem.optional,
      })
    });
    if let Some(info) = &path_info {
      if let Some(ty) = env.get_path(&info.path) {
        return ty;
      }
    }

    let mut obj_ty = obj;
    if let Some(base) = self.access_path_info(mem.object) {
      if let Some(ty) = env.get_path(&base.path) {
        obj_ty = ty;
      }
    }
    let (non_nullish_obj, nullish_obj) = split_nullish(obj_ty, &self.store);
    let lookup_obj = if mem.optional {
      non_nullish_obj
    } else {
      obj_ty
    };
    let mut ty = match &mem.property {
      ObjectKey::Computed(expr) => {
        let _ = self.eval_expr(*expr, &mut Env::new());
        None
      }
      _ => self.object_prop_type(lookup_obj, &self.member_key(mem)),
    }
    .unwrap_or(prim.unknown);
    if mem.optional && nullish_obj != prim.never {
      ty = self.store.union(vec![ty, prim.undefined]);
    }
    ty
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

  fn apply_switch_narrowing(
    &mut self,
    discriminant: ExprId,
    discriminant_ty: TypeId,
    test: ExprId,
    env: &mut Env,
  ) {
    if let Some(path) = self.access_path_info(discriminant) {
      if let Some(lit) = self.literal_value(test) {
        let (yes, _) = narrow_by_literal(discriminant_ty, &lit, &self.store);
        let mut map = HashMap::new();
        map.insert(path.path.clone(), yes);
        env.apply_map(&map);
        if let LiteralValue::String(value) = lit {
          if !path.path.segments.is_empty() {
            let root = FlowKey::root(path.path.root);
            if let Some(root_ty) = env.get_path(&root) {
              let (root_yes, _) =
                narrow_by_discriminant_path(root_ty, &path.path.segments, &value, &self.store);
              let mut root_map = HashMap::new();
              root_map.insert(root, root_yes);
              env.apply_map(&root_map);
            }
          }
        }
      }
    }
  }
}
