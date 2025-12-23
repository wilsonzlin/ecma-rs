use super::stmt::check_stmt;
use crate::db::Body;
use crate::db::BodyKind;
use crate::db::TypeDatabase;
use crate::diagnostic::Diagnostic;
use crate::ids::BodyId;
use crate::ids::ExprId;
use crate::ids::PatId;
use crate::types::TypeId;
use crate::types::TypeStore;
use bumpalo::Bump;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::loc::Loc;
use std::collections::HashMap;
use std::sync::Arc;

/// Per-body result including expression and pattern type side tables.
pub struct BodyCheckResult {
  pub expr_types: Vec<TypeId>,
  pub pat_types: Vec<TypeId>,
  pub diagnostics: Vec<Diagnostic>,
}

pub struct BodyChecker<'a> {
  pub store: &'a mut TypeStore,
  pub body_kind: &'a BodyKind,
  pub expr_types: Vec<TypeId>,
  pub pat_types: Vec<TypeId>,
  pub diagnostics: Vec<Diagnostic>,
  pub(crate) expr_map: HashMap<usize, ExprId>,
  pub(crate) pat_map: HashMap<usize, PatId>,
  pub(crate) expr_spans: &'a mut Vec<Loc>,
  pub(crate) pat_spans: &'a mut Vec<Loc>,
  pub scopes: Vec<HashMap<String, TypeId>>,
  pub expected_return: Option<TypeId>,
  pub arena: Bump,
}

impl<'a> BodyChecker<'a> {
  pub fn new(store: &'a mut TypeStore, body: &'a mut Body) -> Self {
    let Body {
      kind,
      expr_spans,
      pat_spans,
      ..
    } = body;
    expr_spans.clear();
    pat_spans.clear();

    BodyChecker {
      store,
      body_kind: kind,
      expr_types: Vec::new(),
      pat_types: Vec::new(),
      diagnostics: Vec::new(),
      expr_map: HashMap::new(),
      pat_map: HashMap::new(),
      expr_spans,
      pat_spans,
      scopes: Vec::new(),
      expected_return: None,
      arena: Bump::new(),
    }
  }

  pub fn assign_expr_id(&mut self, node: &Node<Expr>) -> ExprId {
    let key = node as *const _ as usize;
    if let Some(existing) = self.expr_map.get(&key) {
      return *existing;
    }
    let id = ExprId(self.expr_types.len());
    self.expr_types.push(self.store.unknown());
    self.expr_map.insert(key, id);
    self.expr_spans.push(node.loc);
    id
  }

  pub fn assign_pat_id(&mut self, node: &Node<parse_js::ast::expr::pat::Pat>) -> PatId {
    let key = node as *const _ as usize;
    if let Some(existing) = self.pat_map.get(&key) {
      return *existing;
    }
    let id = PatId(self.pat_types.len());
    self.pat_types.push(self.store.unknown());
    self.pat_map.insert(key, id);
    self.pat_spans.push(node.loc);
    id
  }

  pub fn push_scope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  pub fn pop_scope(&mut self) {
    self.scopes.pop();
  }

  pub fn define(&mut self, name: &str, ty: TypeId) {
    if let Some(scope) = self.scopes.last_mut() {
      scope.insert(name.to_string(), ty);
    }
  }

  pub fn resolve(&self, name: &str) -> Option<TypeId> {
    for scope in self.scopes.iter().rev() {
      if let Some(ty) = scope.get(name) {
        return Some(*ty);
      }
    }
    None
  }

  pub fn finish(self) -> BodyCheckResult {
    BodyCheckResult {
      expr_types: self.expr_types,
      pat_types: self.pat_types,
      diagnostics: self.diagnostics,
    }
  }
}

pub fn check_body(db: &mut TypeDatabase, body_id: BodyId) -> Arc<BodyCheckResult> {
  if let Some(existing) = db.results.get(body_id.index()).and_then(|r| r.clone()) {
    return existing;
  }

  let (store, bodies, results) = (&mut db.type_store, &mut db.bodies, &mut db.results);
  let body = bodies
    .get_mut(body_id.index())
    .expect("body id out of range");

  let mut checker = BodyChecker::new(store, body);
  checker.push_scope();

  match checker.body_kind {
    BodyKind::TopLevel(stmts) => {
      for stmt in stmts {
        check_stmt(&mut checker, stmt);
      }
    }
  }

  checker.pop_scope();
  let result = Arc::new(checker.finish());
  if let Some(slot) = results.get_mut(body_id.index()) {
    *slot = Some(result.clone());
  }
  result
}
