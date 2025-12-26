use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use bumpalo::Bump;
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  ArrayElement, BinaryOp, Body, BodyKind, ExprId, ExprKind, ForHead, ForInit, MemberExpr, NameId,
  NameInterner, ObjectKey, ObjectLiteral, ObjectProperty, PatId, PatKind, StmtId, StmtKind,
  UnaryOp,
};
use ordered_float::OrderedFloat;
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat as AstPat};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ParamDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::Stmt;
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::parse;
use types_ts_interned::{
  ExpandedType, ObjectType, Param as SigParam, PropData, PropKey, RelateCtx, Shape, Signature,
  TupleElem, TypeExpander, TypeId, TypeKind, TypeStore,
};

use super::cfg::{BlockId, ControlFlowGraph};
use super::flow::Env;
use super::flow_narrow::{
  narrow_by_asserted, narrow_by_discriminant, narrow_by_in_check, narrow_by_instanceof,
  narrow_by_literal, narrow_by_typeof, truthy_falsy_types, Facts, LiteralValue,
};

use super::expr::resolve_call;
use super::infer::{infer_type_arguments_from_contextual_signature, TypeParamDecl};
use super::instantiate::Substituter;
use super::object_literal;
use super::overload;
use super::relate_hooks;
use super::type_expr::TypeLowerer;
use crate::codes;

/// Result of checking a single HIR body produced by `hir-js`.
#[derive(Debug)]
pub struct BodyCheckResult {
  pub expr_types: Vec<TypeId>,
  pub pat_types: Vec<TypeId>,
  pub expr_spans: Vec<TextRange>,
  pub pat_spans: Vec<TextRange>,
  pub diagnostics: Vec<Diagnostic>,
  pub return_types: Vec<TypeId>,
}

struct NoopExpander;

impl TypeExpander for NoopExpander {
  fn expand(
    &self,
    _store: &TypeStore,
    _def: types_ts_interned::DefId,
    _args: &[TypeId],
  ) -> Option<ExpandedType> {
    None
  }
}

#[derive(Default, Clone)]
struct Scope {
  bindings: HashMap<String, Binding>,
}

#[derive(Clone)]
struct Binding {
  ty: TypeId,
  type_params: Vec<TypeParamDecl>,
}

#[derive(Clone, Copy)]
struct ExprContext {
  contextual_type: Option<TypeId>,
  const_context: bool,
  prefer_widening: bool,
}

impl ExprContext {
  fn base() -> Self {
    Self {
      contextual_type: None,
      const_context: false,
      prefer_widening: false,
    }
  }

  fn with_contextual_type(mut self, ty: Option<TypeId>) -> Self {
    self.contextual_type = ty;
    self
  }

  fn with_const_context(mut self) -> Self {
    self.const_context = true;
    self
  }

  fn with_prefer_widening(mut self) -> Self {
    self.prefer_widening = true;
    self
  }

  fn for_subexpression(self) -> Self {
    Self {
      contextual_type: None,
      const_context: self.const_context,
      prefer_widening: false,
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
  _decl: &'a Node<VarDecl>,
  initializer: Option<&'a Node<AstExpr>>,
  type_annotation: Option<&'a Node<parse_js::ast::type_expr::TypeExpr>>,
}

#[derive(Clone, Copy)]
struct FunctionInfo<'a> {
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
      _ => {}
    }
  }

  fn index_stmt_list(&mut self, stmts: &'a [Node<Stmt>], file: FileId) {
    for stmt in stmts.iter() {
      self.index_stmt(stmt, file);
    }
  }

  fn index_var_decl(&mut self, decl: &'a Node<VarDecl>, file: FileId) {
    for declarator in decl.stx.declarators.iter() {
      let pat_span = loc_to_range(file, declarator.pattern.loc);
      self.pats.insert(pat_span, &declarator.pattern.stx.pat);
      self.vars.insert(
        pat_span,
        VarInfo {
          _decl: decl,
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
    if let Some(body) = &func.stx.body {
      let body_span = match body {
        FuncBody::Block(block) => {
          span_for_stmt_list(&block, file).unwrap_or(loc_to_range(file, func.loc))
        }
        FuncBody::Expression(expr) => loc_to_range(file, expr.loc),
      };
      self.functions.push(FunctionInfo { body_span, func });
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
  body: &Body,
  names: &NameInterner,
  file: FileId,
  source: &str,
  store: Arc<TypeStore>,
) -> BodyCheckResult {
  let prim = store.primitive_ids();
  let expr_types = vec![prim.unknown; body.exprs.len()];
  let pat_types = vec![prim.unknown; body.pats.len()];
  let expr_spans: Vec<TextRange> = body.exprs.iter().map(|e| e.span).collect();
  let pat_spans: Vec<TextRange> = body.pats.iter().map(|p| p.span).collect();
  let mut diagnostics = Vec::new();
  let return_types = Vec::new();

  let parsed = match parse(source) {
    Ok(ast) => ast,
    Err(err) => {
      diagnostics.push(err.to_diagnostic(file));
      codes::normalize_diagnostics(&mut diagnostics);
      return BodyCheckResult {
        expr_types,
        pat_types,
        expr_spans,
        pat_spans,
        diagnostics,
        return_types,
      };
    }
  };

  let mut index = AstIndex::new();
  index.index_top_level(&parsed, file);

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
  let relate = RelateCtx::with_hooks(Arc::clone(&store), store.options(), relate_hooks());
  let mut lowerer = TypeLowerer::new(Arc::clone(&store));
  lowerer.set_file(file);
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
    file,
    _names: names,
    _bump: Bump::new(),
  };

  checker.seed_builtins();

  match body.kind {
    BodyKind::TopLevel => {
      checker.check_stmt_list(&parsed.stx.body);
    }
    BodyKind::Function => {
      if !checker.check_enclosing_function(body_range) {
        checker.check_stmt_list(&parsed.stx.body);
      }
    }
    BodyKind::Initializer => {
      if !checker.check_matching_initializer(body_range) {
        checker.check_stmt_list(&parsed.stx.body);
      }
    }
    BodyKind::Class | BodyKind::Unknown => {
      checker.check_stmt_list(&parsed.stx.body);
    }
  }

  checker
    .diagnostics
    .extend(checker.lowerer.take_diagnostics());
  codes::normalize_diagnostics(&mut checker.diagnostics);
  BodyCheckResult {
    expr_types: checker.expr_types,
    pat_types: checker.pat_types,
    expr_spans: checker.expr_spans,
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
  file: FileId,
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
      if ranges_overlap(func.body_span, body_range) {
        let len = func.body_span.end.saturating_sub(func.body_span.start);
        let replace = match best {
          Some(existing) => {
            let existing_len = existing
              .body_span
              .end
              .saturating_sub(existing.body_span.start);
            len < existing_len
          }
          None => true,
        };
        if replace {
          best = Some(*func);
        }
      }
    }
    if let Some(func) = best {
      self.bind_params(func.func);
      self.check_function_body(func.func);
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
        let mut expr_ctx = ExprContext::base().with_contextual_type(annotation);
        if annotation.is_none() {
          expr_ctx = expr_ctx.with_prefer_widening();
        }
        let init_ty = self.check_expr_with_ctx(init, expr_ctx);
        let ty = annotation.unwrap_or(init_ty);
        if let Some(pat) = self.index.pats.get(&pat_span) {
          self.bind_pattern(pat, ty);
        }
      }
      return true;
    }
    false
  }

  fn bind_params(&mut self, func: &Node<Func>) {
    let mut type_param_decls = Vec::new();
    if let Some(params) = func.stx.type_parameters.as_ref() {
      type_param_decls = self.lower_type_params(params);
    }
    for param in func.stx.parameters.iter() {
      let pat_span = loc_to_range(self.file, param.stx.pattern.loc);
      let is_this = matches!(
        param.stx.pattern.stx.pat.stx.as_ref(),
        AstPat::Id(id) if id.stx.name == "this"
      );
      let annotation = param
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| self.lowerer.lower_type_expr(ann));
      let mut default_ctx = ExprContext::base().with_contextual_type(annotation);
      if annotation.is_none() {
        default_ctx = default_ctx.with_prefer_widening();
      }
      let default_ty = param
        .stx
        .default_value
        .as_ref()
        .map(|d| self.check_expr_with_ctx(d, default_ctx));
      let mut ty = annotation.unwrap_or(self.store.primitive_ids().unknown);
      if let Some(default) = default_ty {
        ty = self.store.union(vec![ty, default]);
      }
      if is_this {
        self.insert_binding("this".to_string(), ty, type_param_decls.clone());
        continue;
      }
      if let Some(pat) = self.index.pats.get(&pat_span) {
        self.bind_pattern_with_type_params(pat, ty, type_param_decls.clone());
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
      Stmt::Return(ret) => {
        let ty = ret
          .stx
          .value
          .as_ref()
          .map(|v| self.check_expr(v))
          .unwrap_or(self.store.primitive_ids().undefined);
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
        // function declarations are handled by separate bodies; just bind the name if available
        if let Some(name) = func.stx.name.as_ref() {
          let name = name.stx.name.clone();
          let ty = self.function_type(&func.stx.function, None);
          self.insert_binding(name, ty, Vec::new());
        }
      }
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
      let mut expr_ctx = ExprContext::base().with_contextual_type(annot_ty);
      if matches!(decl.stx.mode, VarDeclMode::Let | VarDeclMode::Var) && annot_ty.is_none() {
        expr_ctx = expr_ctx.with_prefer_widening();
      }
      let init_ty = declarator
        .initializer
        .as_ref()
        .map(|i| self.check_expr_with_ctx(i, expr_ctx))
        .unwrap_or(prim.unknown);
      let final_ty = annot_ty.unwrap_or(init_ty);
      if let (Some(ann), Some(init)) = (annot_ty, declarator.initializer.as_ref()) {
        self.check_assignable(init, init_ty, ann);
      }
      self.check_pat(&declarator.pattern.stx.pat, final_ty);
    }
  }

  fn check_pat(&mut self, pat: &Node<AstPat>, value_ty: TypeId) {
    self.bind_pattern(pat, value_ty);
  }

  fn check_expr(&mut self, expr: &Node<AstExpr>) -> TypeId {
    self.check_expr_with_ctx(expr, ExprContext::base())
  }

  fn check_expr_with_ctx(&mut self, expr: &Node<AstExpr>, ctx: ExprContext) -> TypeId {
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
      AstExpr::This(_) => self
        .lookup("this")
        .map(|b| b.ty)
        .unwrap_or(self.store.primitive_ids().unknown),
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
        let sub_ctx = ctx.for_subexpression();
        let cons = self.check_expr_with_ctx(&cond.stx.consequent, sub_ctx);
        let alt = self.check_expr_with_ctx(&cond.stx.alternate, sub_ctx);
        self.store.union(vec![cons, alt])
      }
      AstExpr::Call(call) => {
        let sub_ctx = ctx.for_subexpression();
        let (callee_ty, this_arg, arg_contexts) = match call.stx.callee.stx.as_ref() {
          AstExpr::Member(mem) => {
            let obj_ty = self.check_expr_with_ctx(&mem.stx.left, sub_ctx);
            let prop_ty = self.member_type(obj_ty, &mem.stx.right);
            self.record_expr_type(call.stx.callee.loc, prop_ty);
            let contexts = self.contextual_argument_types(prop_ty, call.stx.arguments.len());
            (prop_ty, Some(obj_ty), contexts)
          }
          AstExpr::ComputedMember(mem) => {
            let obj_ty = self.check_expr_with_ctx(&mem.stx.object, sub_ctx);
            let _ = self.check_expr_with_ctx(&mem.stx.member, sub_ctx);
            let prop_ty = self.member_type(obj_ty, "<computed>");
            self.record_expr_type(call.stx.callee.loc, prop_ty);
            let contexts = self.contextual_argument_types(prop_ty, call.stx.arguments.len());
            (prop_ty, Some(obj_ty), contexts)
          }
          _ => {
            let callee_ty = self.check_expr_with_ctx(&call.stx.callee, sub_ctx);
            let arg_contexts = self.contextual_argument_types(callee_ty, call.stx.arguments.len());
            (callee_ty, None, arg_contexts)
          }
        };
        let arg_types: Vec<TypeId> = call
          .stx
          .arguments
          .iter()
          .enumerate()
          .map(|(idx, arg)| {
            let mut arg_ctx = ctx.for_subexpression();
            if let Some(contextual) = arg_contexts.get(idx).and_then(|c| *c) {
              arg_ctx = arg_ctx.with_contextual_type(Some(contextual));
            }
            self.check_expr_with_ctx(&arg.stx.value, arg_ctx)
          })
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
          ctx.contextual_type,
          span,
        );
        for diag in &resolution.diagnostics {
          self.diagnostics.push(diag.clone());
        }
        if resolution.diagnostics.is_empty() {
          if let Some(sig_id) = resolution.signature {
            let sig = self.store.signature(sig_id);
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
            let expander = NoopExpander;
            for (idx, arg) in call.stx.arguments.iter().enumerate() {
              if let Some(param_ty) = self.param_type_for_arg(&sig.params, idx) {
                let diags = object_literal::check_excess_properties(
                  &self.store,
                  &expander,
                  &arg.stx.value,
                  param_ty,
                  self.file,
                );
                self.diagnostics.extend(diags);
              }
            }
          }
        }
        resolution.return_type
      }
      AstExpr::Member(mem) => {
        let obj_ty = self.check_expr_with_ctx(&mem.stx.left, ctx.for_subexpression());
        self.member_type(obj_ty, &mem.stx.right)
      }
      AstExpr::ComputedMember(mem) => {
        let obj_ty = self.check_expr_with_ctx(&mem.stx.object, ctx.for_subexpression());
        let _ = self.check_expr_with_ctx(&mem.stx.member, ctx.for_subexpression());
        self.member_type(obj_ty, "<computed>")
      }
      AstExpr::LitArr(arr) => self.array_literal_type(arr, ctx),
      AstExpr::LitObj(obj) => self.object_literal_type(obj, ctx),
      AstExpr::Func(func) => self.function_type(&func.stx.func, ctx.contextual_type),
      AstExpr::ArrowFunc(func) => self.function_type(&func.stx.func, ctx.contextual_type),
      AstExpr::IdPat(_) | AstExpr::ArrPat(_) | AstExpr::ObjPat(_) => {
        self.store.primitive_ids().unknown
      }
      AstExpr::TypeAssertion(assert) if assert.stx.const_assertion => {
        let inner_ctx = ExprContext::base().with_const_context();
        let ty = self.check_expr_with_ctx(&assert.stx.expression, inner_ctx);
        let ty = self.apply_widening(ty, inner_ctx);
        self.record_expr_type(expr.loc, ty);
        return ty;
      }
      AstExpr::TypeAssertion(assert) => {
        self.check_expr_with_ctx(&assert.stx.expression, ctx.for_subexpression())
      }
      AstExpr::NonNullAssertion(assert) => {
        self.check_expr_with_ctx(&assert.stx.expression, ctx.for_subexpression())
      }
      AstExpr::SatisfiesExpr(expr) => {
        let target = self.lowerer.lower_type_expr(&expr.stx.type_annotation);
        let inner_ctx = ctx.for_subexpression().with_contextual_type(Some(target));
        let expr_ty = self.check_expr_with_ctx(&expr.stx.expression, inner_ctx);
        self.check_assignable(&expr.stx.expression, expr_ty, target);
        expr_ty
      }
      _ => self.store.primitive_ids().unknown,
    };
    let ty = self.apply_widening(ty, ctx);
    self.record_expr_type(expr.loc, ty);
    ty
  }

  fn param_type_for_arg(&self, params: &[SigParam], idx: usize) -> Option<TypeId> {
    if let Some(param) = params.get(idx) {
      return Some(self.unwrap_rest_type(param));
    }
    params.last().and_then(|param| {
      if param.rest {
        Some(self.unwrap_rest_type(param))
      } else {
        None
      }
    })
  }

  fn unwrap_rest_type(&self, param: &SigParam) -> TypeId {
    if !param.rest {
      return param.ty;
    }
    match self.store.type_kind(param.ty) {
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => elems.first().map(|e| e.ty).unwrap_or(param.ty),
      _ => param.ty,
    }
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
      TypeKind::Tuple(elems) => elems.get(0).map(|e| e.ty).unwrap_or(prim.unknown),
      _ => prim.unknown,
    }
  }

  fn array_literal_type(
    &mut self,
    arr: &Node<parse_js::ast::expr::lit::LitArrExpr>,
    ctx: ExprContext,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let tuple_context = ctx
      .contextual_type
      .and_then(|ty| match self.store.type_kind(ty) {
        TypeKind::Tuple(elems) => Some(elems),
        _ => None,
      });
    let array_context = ctx
      .contextual_type
      .and_then(|ty| match self.store.type_kind(ty) {
        TypeKind::Array { ty, readonly } => Some((ty, readonly)),
        _ => None,
      });
    let mut elem_types = Vec::new();
    let mut has_rest = false;
    let mut has_hole = false;
    for (idx, elem) in arr.stx.elements.iter().enumerate() {
      match elem {
        parse_js::ast::expr::lit::LitArrElem::Single(v) => {
          let mut elem_ctx = ctx.for_subexpression();
          if let Some(tuple) = tuple_context.as_ref().and_then(|t| t.get(idx)) {
            elem_ctx = elem_ctx.with_contextual_type(Some(tuple.ty));
            if tuple.readonly {
              elem_ctx.const_context = true;
            }
          } else if let Some((ty, readonly)) = array_context {
            elem_ctx = elem_ctx.with_contextual_type(Some(ty));
            if readonly {
              elem_ctx.const_context = true;
            }
          }
          let mut ty = self.check_expr_with_ctx(v, elem_ctx);
          if !self.prefers_literal_context(elem_ctx)
            && tuple_context.is_none()
            && !ctx.const_context
          {
            ty = self.widen_literal_type(ty);
          }
          elem_types.push(ty);
        }
        parse_js::ast::expr::lit::LitArrElem::Rest(v) => {
          has_rest = true;
          let rest_ctx = ctx.for_subexpression();
          let mut ty = self.check_expr_with_ctx(v, rest_ctx);
          if let TypeKind::Array { ty: inner, .. } = self.store.type_kind(ty) {
            ty = inner;
          }
          if !self.prefers_literal_context(rest_ctx) && !ctx.const_context {
            ty = self.widen_literal_type(ty);
          }
          elem_types.push(ty);
        }
        parse_js::ast::expr::lit::LitArrElem::Empty => {
          has_hole = true;
        }
      }
    }

    if ctx.const_context && !has_rest && !has_hole {
      let tuple_elems = elem_types
        .into_iter()
        .map(|ty| TupleElem {
          ty,
          optional: false,
          rest: false,
          readonly: true,
        })
        .collect();
      return self.store.intern_type(TypeKind::Tuple(tuple_elems));
    }

    if let Some(target_elems) = tuple_context.as_ref() {
      if !has_rest && !has_hole && target_elems.len() == elem_types.len() {
        let tuple_elems = elem_types
          .into_iter()
          .zip(target_elems.iter())
          .map(|(ty, target)| TupleElem {
            ty,
            optional: target.optional,
            rest: target.rest,
            readonly: target.readonly,
          })
          .collect();
        return self.store.intern_type(TypeKind::Tuple(tuple_elems));
      }
    }

    let elem_ty = if elem_types.is_empty() {
      prim.unknown
    } else {
      self.store.union(elem_types)
    };
    let mut readonly =
      ctx.const_context || array_context.map(|(_, readonly)| readonly).unwrap_or(false);
    if let Some(target_elems) = tuple_context.as_ref() {
      if target_elems.iter().all(|e| e.readonly) {
        readonly = true;
      }
    }
    self.store.intern_type(TypeKind::Array {
      ty: elem_ty,
      readonly,
    })
  }

  fn object_literal_type(
    &mut self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
    ctx: ExprContext,
  ) -> TypeId {
    let mut shape = Shape::new();
    let prefer_literal = self.prefers_literal_context(ctx);
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
            let contextual = ctx
              .contextual_type
              .and_then(|ty| self.contextual_property(ty, &prop_key));
            let mut value_ctx = ctx.for_subexpression();
            if let Some(prop) = contextual.as_ref() {
              value_ctx = value_ctx.with_contextual_type(Some(prop.ty));
              if prop.readonly {
                value_ctx.const_context = true;
              }
            }
            let mut ty = self.check_expr_with_ctx(expr, value_ctx);
            if !prefer_literal {
              ty = self.widen_literal_type(ty);
            }
            let readonly =
              ctx.const_context || contextual.as_ref().map(|p| p.readonly).unwrap_or(false);
            shape.properties.push(types_ts_interned::Property {
              key: prop_key,
              data: PropData {
                ty,
                optional: false,
                readonly,
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
          let mut ty = self
            .lookup(&id.stx.name)
            .map(|b| b.ty)
            .unwrap_or(self.store.primitive_ids().unknown);
          if !prefer_literal {
            ty = self.widen_literal_type(ty);
          }
          shape.properties.push(types_ts_interned::Property {
            key,
            data: PropData {
              ty,
              optional: false,
              readonly: ctx.const_context,
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          });
        }
        ObjMemberType::Rest { val } => {
          let _ = self.check_expr_with_ctx(val, ctx.for_subexpression());
        }
      }
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn apply_widening(&self, ty: TypeId, ctx: ExprContext) -> TypeId {
    if ctx.prefer_widening && !self.prefers_literal_context(ctx) {
      self.widen_literal_type(ty)
    } else {
      ty
    }
  }

  fn widen_literal_type(&self, ty: TypeId) -> TypeId {
    match self.store.type_kind(ty) {
      TypeKind::BooleanLiteral(_) => self.store.primitive_ids().boolean,
      TypeKind::NumberLiteral(_) => self.store.primitive_ids().number,
      TypeKind::StringLiteral(_) => self.store.primitive_ids().string,
      TypeKind::BigIntLiteral(_) => self.store.primitive_ids().bigint,
      TypeKind::UniqueSymbol => self.store.primitive_ids().symbol,
      TypeKind::Union(members) => {
        let widened: Vec<_> = members
          .into_iter()
          .map(|member| self.widen_literal_type(member))
          .collect();
        self.store.union(widened)
      }
      _ => ty,
    }
  }

  fn prefers_literal_context(&self, ctx: ExprContext) -> bool {
    if ctx.const_context {
      return true;
    }
    ctx
      .contextual_type
      .map(|ty| self.is_literal_context_type(ty))
      .unwrap_or(false)
  }

  fn is_literal_context_type(&self, ty: TypeId) -> bool {
    match self.store.type_kind(ty) {
      TypeKind::NumberLiteral(_)
      | TypeKind::StringLiteral(_)
      | TypeKind::BooleanLiteral(_)
      | TypeKind::BigIntLiteral(_)
      | TypeKind::UniqueSymbol => true,
      TypeKind::Array { ty, .. } => self.is_literal_context_type(ty),
      TypeKind::Tuple(_) => true,
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .into_iter()
        .any(|member| self.is_literal_context_type(member)),
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        shape
          .properties
          .iter()
          .any(|prop| self.is_literal_context_type(prop.data.ty))
      }
      _ => false,
    }
  }

  fn contextual_property(&self, contextual: TypeId, key: &PropKey) -> Option<PropData> {
    match self.store.type_kind(contextual) {
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in shape.properties.iter() {
          if prop.key == *key {
            return Some(prop.data.clone());
          }
        }
        None
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for member in members {
          if let Some(data) = self.contextual_property(member, key) {
            return Some(data);
          }
        }
        None
      }
      _ => None,
    }
  }

  fn resolve_ident(&mut self, name: &str, expr: &Node<AstExpr>) -> TypeId {
    if let Some(binding) = self.lookup(name) {
      return binding.ty;
    }
    self.diagnostics.push(codes::UNKNOWN_IDENTIFIER.error(
      format!("unknown identifier `{}`", name),
      Span {
        file: self.file,
        range: loc_to_range(self.file, expr.loc),
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
    let target_binding = match left.stx.as_ref() {
      AstExpr::Id(id) => self.lookup(&id.stx.name),
      _ => None,
    };
    let rhs_ctx =
      ExprContext::base().with_contextual_type(target_binding.as_ref().map(|binding| binding.ty));
    let value_ty = self.check_expr_with_ctx(right, rhs_ctx);
    match left.stx.as_ref() {
      AstExpr::Id(id) => {
        if let Some(binding) = target_binding {
          let expander = NoopExpander;
          let diags = object_literal::check_excess_properties(
            &self.store,
            &expander,
            right,
            binding.ty,
            self.file,
          );
          self.diagnostics.extend(diags);
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
          let default_ty = self.check_expr_with_ctx(
            default,
            ExprContext::base().with_contextual_type(Some(target_ty)),
          );
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
        let default_ty = self.check_expr_with_ctx(
          default,
          ExprContext::base().with_contextual_type(Some(prop_ty)),
        );
        prop_ty = self.store.union(vec![prop_ty, default_ty]);
      }
      self.bind_pattern(&prop.stx.target, prop_ty);
    }
    if let Some(rest) = &obj.stx.rest {
      self.bind_pattern_with_type_params(rest, value, type_params);
    }
  }

  fn function_type(&mut self, func: &Node<Func>, contextual: Option<TypeId>) -> TypeId {
    let prim = self.store.primitive_ids();
    let contextual_sig = self.contextual_signature(contextual);

    let mut type_param_decls = Vec::new();
    let mut type_param_ids = Vec::new();
    if let Some(params) = func.stx.type_parameters.as_ref() {
      let decls = self.lower_type_params(params);
      type_param_ids.extend(decls.iter().map(|d| d.id));
      type_param_decls.extend(decls);
    }
    if let Some(sig) = &contextual_sig {
      for tp in sig.type_params.iter() {
        if !type_param_ids.contains(tp) {
          type_param_ids.push(*tp);
          type_param_decls.push(TypeParamDecl::new(*tp));
        }
      }
    }

    self.scopes.push(Scope::default());

    let mut this_param = None;
    let mut params = Vec::new();
    for (idx, param) in func.stx.parameters.iter().enumerate() {
      let pat_span = loc_to_range(self.file, param.stx.pattern.loc);
      let annotation = param
        .stx
        .type_annotation
        .as_ref()
        .map(|t| self.lowerer.lower_type_expr(t));
      let contextual_param = contextual_sig
        .as_ref()
        .and_then(|sig| self.contextual_param_type(sig, idx));
      let mut ty = annotation.or(contextual_param).unwrap_or(prim.unknown);
      let mut default_ctx = ExprContext::base().with_contextual_type(Some(ty));
      if annotation.is_none() && contextual_param.is_none() {
        default_ctx = default_ctx.with_prefer_widening();
      }
      if let Some(default) = &param.stx.default_value {
        let default_ty = self.check_expr_with_ctx(default, default_ctx);
        ty = self.store.union(vec![ty, default_ty]);
      }
      let is_this = matches!(
        param.stx.pattern.stx.pat.stx.as_ref(),
        AstPat::Id(id) if id.stx.name == "this"
      );
      if is_this && this_param.is_none() {
        this_param = Some(ty);
        self.insert_binding("this".to_string(), ty, type_param_decls.clone());
        continue;
      }
      if let Some(pat) = self.index.pats.get(&pat_span) {
        self.bind_pattern_with_type_params(pat, ty, type_param_decls.clone());
      }
      params.push(SigParam {
        name: None,
        ty,
        optional: param.stx.optional,
        rest: param.stx.rest,
      });
    }

    let contextual_ret = contextual_sig.as_ref().map(|sig| sig.ret);
    let mut ret_ty = func
      .stx
      .return_type
      .as_ref()
      .map(|t| self.lowerer.lower_type_expr(t));
    if ret_ty.is_none() {
      ret_ty = Some(match &func.stx.body {
        Some(FuncBody::Expression(expr)) => {
          let mut ret_ctx = ExprContext::base().with_contextual_type(contextual_ret);
          if contextual_ret.is_none() {
            ret_ctx = ret_ctx.with_prefer_widening();
          }
          self.check_expr_with_ctx(expr, ret_ctx)
        }
        Some(FuncBody::Block(block)) => {
          let prev_returns = self.return_types.len();
          self.check_stmt_list(block);
          let returns = self.return_types.split_off(prev_returns);
          if returns.is_empty() {
            contextual_ret.unwrap_or(prim.void)
          } else {
            let ret = self.store.union(returns);
            if contextual_ret.is_none() {
              self.widen_literal_type(ret)
            } else {
              ret
            }
          }
        }
        None => contextual_ret.unwrap_or(prim.void),
      });
    }
    let ret_ty = ret_ty.unwrap_or(prim.unknown);

    let mut sig = Signature {
      params,
      ret: ret_ty,
      type_params: type_param_ids.clone(),
      this_param,
    };

    if let Some(ctx_sig) = contextual_sig.as_ref() {
      let inference = infer_type_arguments_from_contextual_signature(
        &self.store,
        ctx_sig,
        &type_param_decls,
        &sig,
      );
      if inference.diagnostics.is_empty() && !inference.substitutions.is_empty() {
        let mut substituter =
          Substituter::new(Arc::clone(&self.store), inference.substitutions.clone());
        let instantiated_id = substituter.substitute_signature(ctx_sig);
        let instantiated_sig = self.store.signature(instantiated_id);
        sig = instantiated_sig.clone();
        type_param_ids = instantiated_sig.type_params.clone();
        type_param_decls.retain(|decl| type_param_ids.contains(&decl.id));
      }
    }

    self.scopes.pop();

    let sig_id = self.store.intern_signature(sig);
    let ty = self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    });
    if !type_param_decls.is_empty() {
      self.function_type_params.insert(ty, type_param_decls);
    }
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

  fn check_assignable(&mut self, expr: &Node<AstExpr>, src: TypeId, dst: TypeId) {
    let expander = NoopExpander;
    let diags =
      object_literal::check_excess_properties(&self.store, &expander, expr, dst, self.file);
    self.diagnostics.extend(diags);
    if !self.relate.is_assignable(src, dst) {
      self.diagnostics.push(codes::TYPE_MISMATCH.error(
        "type mismatch",
        Span {
          file: self.file,
          range: loc_to_range(self.file, expr.loc),
        },
      ));
    }
  }

  fn contextual_signature(&self, contextual: Option<TypeId>) -> Option<Signature> {
    let ty = contextual?;
    let sigs = overload::callable_signatures(self.store.as_ref(), ty);
    sigs.first().map(|id| self.store.signature(*id))
  }

  fn contextual_param_type(&self, sig: &Signature, index: usize) -> Option<TypeId> {
    overload::expected_arg_type_at(self.store.as_ref(), sig, index)
  }

  fn contextual_argument_types(&self, callee: TypeId, arg_count: usize) -> Vec<Option<TypeId>> {
    let mut contexts = vec![None; arg_count];
    if arg_count == 0 {
      return contexts;
    }
    let sigs = overload::callable_signatures(self.store.as_ref(), callee);
    if sigs.is_empty() {
      return contexts;
    }
    for idx in 0..arg_count {
      let mut types = Vec::new();
      for sig_id in sigs.iter() {
        let sig = self.store.signature(*sig_id);
        if let Some(param_ty) = self.contextual_param_type(&sig, idx) {
          types.push(param_ty);
        }
      }
      if let Some(first) = types.first().copied() {
        let ctx_ty = if types.len() == 1 {
          first
        } else {
          self.store.union(types)
        };
        contexts[idx] = Some(ctx_ty);
      }
    }
    contexts
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
  body: &Body,
  names: &NameInterner,
  _file: FileId,
  _source: &str,
  store: Arc<TypeStore>,
  initial: &HashMap<NameId, TypeId>,
) -> BodyCheckResult {
  let mut checker = FlowBodyChecker::new(body, names, Arc::clone(&store), initial);
  checker.run(initial);
  checker.into_result()
}

struct FlowBodyChecker<'a> {
  body: &'a Body,
  names: &'a NameInterner,
  store: Arc<TypeStore>,
  expr_types: Vec<TypeId>,
  pat_types: Vec<TypeId>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
  diagnostics: Vec<Diagnostic>,
  return_types: Vec<TypeId>,
  return_indices: HashMap<StmtId, usize>,
}

impl<'a> FlowBodyChecker<'a> {
  fn new(
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

    Self {
      body,
      names,
      store,
      expr_types,
      pat_types,
      expr_spans,
      pat_spans,
      diagnostics: Vec::new(),
      return_types,
      return_indices,
    }
  }

  fn into_result(self) -> BodyCheckResult {
    BodyCheckResult {
      expr_types: self.expr_types,
      pat_types: self.pat_types,
      expr_spans: self.expr_spans,
      pat_spans: self.pat_spans,
      diagnostics: self.diagnostics,
      return_types: self.return_types,
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
        StmtKind::ForIn { left, right, .. } => {
          let right_ty = self.eval_expr(*right, &mut env).0;
          match left {
            ForHead::Pat(pat) => self.bind_pat(*pat, right_ty, &mut env),
            ForHead::Var(var) => {
              for declarator in var.declarators.iter() {
                self.bind_pat(declarator.pat, right_ty, &mut env);
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
        let ty = env.get(*name).unwrap_or(prim.unknown);
        let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
        facts.truthy.insert(*name, truthy);
        facts.falsy.insert(*name, falsy);
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
        let _ = self.eval_expr(*expr, env);
        prim.number
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
          if let Some(name) = self.ident_name(left_expr) {
            let (yes, no) = narrow_by_instanceof(left_ty, &self.store);
            facts.truthy.insert(name, yes);
            facts.falsy.insert(name, no);
          }
          prim.boolean
        }
        BinaryOp::In => {
          let _ = self.eval_expr(*left, env);
          let right_ty = self.eval_expr(*right, env).0;
          if let (Some(prop), Some(name)) = (self.literal_prop(*left), self.ident_name(*right)) {
            let (yes, no) = narrow_by_in_check(right_ty, &prop, &self.store);
            facts.truthy.insert(name, yes);
            facts.falsy.insert(name, no);
          }
          prim.boolean
        }
        BinaryOp::Comma => {
          let _ = self.eval_expr(*left, env);
          self.eval_expr(*right, env).0
        }
      },
      ExprKind::Assignment { target, value, .. } => {
        let val_ty = self.eval_expr(*value, env).0;
        self.bind_pat(*target, val_ty, env);
        val_ty
      }
      ExprKind::Call(call) => self.eval_call(call, env, &mut facts),
      ExprKind::Member(mem) => {
        let obj_ty = self.eval_expr(mem.object, env).0;
        self.member_type(obj_ty, &mem)
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
              elem_tys.push(self.eval_expr(*id, env).0);
            }
            ArrayElement::Empty => {}
          }
        }
        let elem_ty = if elem_tys.is_empty() {
          prim.unknown
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
      ExprKind::NonNull { expr } => self.eval_expr(*expr, env).0,
      ExprKind::Satisfies { expr } => self.eval_expr(*expr, env).0,
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
        out.merge(left_facts, &self.store);
        out.merge(right_facts, &self.store);
        self.store.union(vec![left_ty, right_ty])
      }
      BinaryOp::LogicalOr => {
        let mut right_env = env.clone();
        right_env.apply_falsy(&left_facts);
        let (right_ty, right_facts) = self.eval_expr(right, &mut right_env);
        out.merge(left_facts, &self.store);
        out.merge(right_facts, &self.store);
        self.store.union(vec![left_ty, right_ty])
      }
      BinaryOp::NullishCoalescing => {
        let right_ty = self.eval_expr(right, env).0;
        self.store.union(vec![left_ty, right_ty])
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

    let mut apply = |target: NameId, yes: TypeId, no: TypeId| {
      if negate {
        out.truthy.insert(target, no);
        out.falsy.insert(target, yes);
      } else {
        out.truthy.insert(target, yes);
        out.falsy.insert(target, no);
      }
    };

    if let Some(target) = self.ident_name(left) {
      if let Some(lit) = self.literal_value(right) {
        let (yes, no) = narrow_by_literal(left_ty, &lit, &self.store);
        apply(target, yes, no);
        return;
      }
    }
    if let Some(target) = self.ident_name(right) {
      if let Some(lit) = self.literal_value(left) {
        let (yes, no) = narrow_by_literal(right_ty, &lit, &self.store);
        apply(target, yes, no);
        return;
      }
    }

    if let Some((target, prop, target_ty)) = self.discriminant_member(left) {
      if let Some(LiteralValue::String(value)) = self.literal_value(right) {
        let (yes, no) = narrow_by_discriminant(target_ty, &prop, &value, &self.store);
        apply(target, yes, no);
        return;
      }
    }
    if let Some((target, prop, target_ty)) = self.discriminant_member(right) {
      if let Some(LiteralValue::String(value)) = self.literal_value(left) {
        let (yes, no) = narrow_by_discriminant(target_ty, &prop, &value, &self.store);
        apply(target, yes, no);
        return;
      }
    }

    if let Some((target, target_ty, lit)) = self.typeof_comparison(left, right) {
      let (yes, no) = narrow_by_typeof(target_ty, &lit, &self.store);
      apply(target, yes, no);
    }
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
          parameter,
          asserted,
          asserts,
        } = self.store.type_kind(sig.ret)
        {
          if let Some(asserted) = asserted {
            let target_idx = parameter
              .and_then(|param| {
                let param_name = self.store.name(param);
                sig.params.iter().position(|p| {
                  p.name
                    .map(|name| self.store.name(name) == param_name)
                    .unwrap_or(false)
                })
              })
              .or_else(|| {
                parameter.and_then(|param| {
                  let param_name = self.store.name(param);
                  call.args.iter().position(|arg| {
                    self
                      .ident_name(arg.expr)
                      .map(|name| self.hir_name(name) == param_name)
                      .unwrap_or(false)
                  })
                })
              })
              .unwrap_or(0);
            if let Some(arg) = call.args.get(target_idx) {
              if let Some(name) = self.ident_name(arg.expr) {
                let arg_ty = arg_tys.get(target_idx).copied().unwrap_or(prim.unknown);
                let (yes, no) = narrow_by_asserted(arg_ty, asserted, &self.store);
                if asserts {
                  out.assertions.insert(name, yes);
                } else {
                  out.truthy.insert(name, yes);
                  out.falsy.insert(name, no);
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

  fn ident_name(&self, expr_id: ExprId) -> Option<NameId> {
    match self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => Some(name),
      _ => None,
    }
  }

  fn literal_value(&self, expr_id: ExprId) -> Option<LiteralValue> {
    match &self.body.exprs[expr_id.0 as usize].kind {
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

  fn hir_name(&self, id: NameId) -> String {
    self
      .names
      .resolve(id)
      .map(|s| s.to_owned())
      .unwrap_or_default()
  }

  fn discriminant_member(&self, expr_id: ExprId) -> Option<(NameId, String, TypeId)> {
    if let ExprKind::Member(MemberExpr {
      object, property, ..
    }) = &self.body.exprs[expr_id.0 as usize].kind
    {
      if let Some(name) = self.ident_name(*object) {
        let prop = match property {
          ObjectKey::Ident(id) => Some(self.hir_name(*id)),
          ObjectKey::String(s) => Some(s.clone()),
          _ => None,
        }?;
        let obj_ty = self.expr_types[object.0 as usize];
        return Some((name, prop, obj_ty));
      }
    }
    None
  }

  fn typeof_comparison(&self, left: ExprId, right: ExprId) -> Option<(NameId, TypeId, String)> {
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
        if let Some(name) = self.ident_name(*expr) {
          return Some((name, self.expr_types[expr.0 as usize], s.clone()));
        }
      }
      (
        ExprKind::Literal(hir_js::Literal::String(s)),
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        },
      ) => {
        if let Some(name) = self.ident_name(*expr) {
          return Some((name, self.expr_types[expr.0 as usize], s.clone()));
        }
      }
      _ => {}
    }
    None
  }

  fn bind_pat(&mut self, pat_id: PatId, value_ty: TypeId, env: &mut Env) {
    let pat = &self.body.pats[pat_id.0 as usize];
    let prim = self.store.primitive_ids();
    let slot = &mut self.pat_types[pat_id.0 as usize];
    *slot = if *slot == prim.unknown {
      value_ty
    } else {
      self.store.union(vec![*slot, value_ty])
    };
    match &pat.kind {
      PatKind::Ident(name) => {
        env.set(*name, value_ty);
      }
      PatKind::Assign { target, .. } => {
        self.bind_pat(*target, value_ty, env);
      }
      PatKind::Rest(inner) => self.bind_pat(**inner, value_ty, env),
      PatKind::Array(arr) => {
        let element_ty = match self.store.type_kind(value_ty) {
          TypeKind::Array { ty, .. } => ty,
          TypeKind::Tuple(elems) => elems
            .first()
            .map(|e| e.ty)
            .unwrap_or(self.store.primitive_ids().unknown),
          _ => self.store.primitive_ids().unknown,
        };
        for (idx, elem) in arr.elements.iter().enumerate() {
          if let Some(elem) = elem {
            let mut ty = element_ty;
            if let TypeKind::Tuple(elems) = self.store.type_kind(value_ty) {
              if let Some(specific) = elems.get(idx) {
                ty = specific.ty;
              }
            }
            if let Some(default) = elem.default_value {
              let default_ty = self.eval_expr(default, env).0;
              ty = self.store.union(vec![ty, default_ty]);
            }
            self.bind_pat(elem.pat, ty, env);
          }
        }
        if let Some(rest) = arr.rest {
          self.bind_pat(rest, value_ty, env);
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
          let mut prop_ty = self.store.primitive_ids().unknown;
          if let Some(name) = prop_name {
            if let Some(found) = self.object_prop_type(value_ty, &name) {
              prop_ty = found;
            }
          }
          if let Some(default) = prop.default_value {
            let default_ty = self.eval_expr(default, env).0;
            prop_ty = self.store.union(vec![prop_ty, default_ty]);
          }
          self.bind_pat(prop.value, prop_ty, env);
        }
        if let Some(rest) = obj.rest {
          self.bind_pat(rest, value_ty, env);
        }
      }
      PatKind::AssignTarget(_) => {}
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

  fn member_type(&mut self, obj: TypeId, mem: &MemberExpr) -> TypeId {
    let ty = match &mem.property {
      ObjectKey::Computed(expr) => {
        let _ = self.eval_expr(*expr, &mut Env::new());
        None
      }
      _ => self.object_prop_type(obj, &self.member_key(mem)),
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
    if let Some((target, prop, obj_ty)) = self.discriminant_member(discriminant) {
      if let Some(LiteralValue::String(value)) = self.literal_value(test) {
        let (yes, _) = narrow_by_discriminant(obj_ty, &prop, &value, &self.store);
        env.set(target, yes);
      }
      return;
    }
    if let Some(name) = self.ident_name(discriminant) {
      if let Some(lit) = self.literal_value(test) {
        let (yes, _) = narrow_by_literal(discriminant_ty, &lit, &self.store);
        env.set(name, yes);
      }
    }
  }
}
