use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId, Span};
use hir_js::{
  Body, CallExpr, Expr, ExprId, ExprKind, Literal, NameInterner, PatId, PatKind, StmtId, StmtKind,
};
use ordered_float::OrderedFloat;
use types_ts_interned::{TypeId, TypeKind, TypeStore};

const CODE_UNKNOWN_IDENTIFIER: &str = "TC0005";
const CODE_TYPE_MISMATCH: &str = "TC0007";
const CODE_ARGUMENT_COUNT_MISMATCH: &str = "TC1006";

/// Result of checking a single HIR body produced by `hir-js`.
#[derive(Debug)]
pub struct BodyCheckResult {
  pub expr_types: Vec<TypeId>,
  pub pat_types: Vec<TypeId>,
  pub diagnostics: Vec<Diagnostic>,
  pub return_types: Vec<TypeId>,
}

#[derive(Clone)]
struct Scope {
  parent: Option<Box<Scope>>,
  bindings: HashMap<hir_js::NameId, TypeId>,
}

impl Scope {
  fn new(parent: Option<Scope>) -> Scope {
    Scope {
      parent: parent.map(Box::new),
      bindings: HashMap::new(),
    }
  }

  fn insert(&mut self, name: hir_js::NameId, ty: TypeId) {
    self.bindings.insert(name, ty);
  }

  fn get(&self, name: hir_js::NameId) -> Option<TypeId> {
    if let Some(ty) = self.bindings.get(&name) {
      Some(*ty)
    } else if let Some(parent) = &self.parent {
      parent.get(name)
    } else {
      None
    }
  }
}

/// Type-check a lowered HIR body, producing per-expression and per-pattern type tables.
///
/// This is intentionally lightweight and self-contained so it can be used in tests without
/// instantiating the full `Program` pipeline. It performs local inference only and does not
/// rely on prior binding; identifiers are resolved purely by lexical scopes within the body.
pub fn check_body(
  body: &Body,
  names: &NameInterner,
  file: FileId,
  source: &str,
  store: Arc<TypeStore>,
) -> BodyCheckResult {
  let prim = store.primitive_ids();
  let mut expr_types = vec![prim.unknown; body.exprs.len()];
  let mut pat_types = vec![prim.unknown; body.pats.len()];
  let mut diagnostics = Vec::new();
  let mut return_types = Vec::new();
  let mut scope = Scope::new(None);

  // Pre-bind all identifier patterns so parameters are available in scope.
  for (idx, pat) in body.pats.iter().enumerate() {
    if let PatKind::Ident(name) = pat.kind {
      scope.insert(name, prim.unknown);
      pat_types[idx] = prim.unknown;
    }
  }

  let mut checker = BodyChecker {
    body,
    names,
    file,
    source,
    store: Arc::clone(&store),
    expr_types: &mut expr_types,
    pat_types: &mut pat_types,
    diagnostics: &mut diagnostics,
    return_types: &mut return_types,
  };

  for stmt_id in 0..body.stmts.len() {
    checker.check_stmt(StmtId(stmt_id as u32), &mut scope);
  }

  BodyCheckResult {
    expr_types,
    pat_types,
    diagnostics,
    return_types,
  }
}

struct BodyChecker<'a> {
  body: &'a Body,
  names: &'a NameInterner,
  file: FileId,
  source: &'a str,
  store: Arc<TypeStore>,
  expr_types: &'a mut [TypeId],
  pat_types: &'a mut [TypeId],
  diagnostics: &'a mut Vec<Diagnostic>,
  return_types: &'a mut Vec<TypeId>,
}

impl<'a> BodyChecker<'a> {
  fn check_stmt(&mut self, id: StmtId, scope: &mut Scope) {
    let stmt = &self.body.stmts[id.0 as usize];
    match &stmt.kind {
      StmtKind::Expr(expr) => {
        let _ = self.check_expr(*expr, scope);
      }
      StmtKind::Return(expr) => {
        let ty = expr
          .map(|e| self.check_expr(e, scope))
          .unwrap_or(self.store.primitive_ids().undefined);
        self.return_types.push(ty);
      }
      StmtKind::Block(stmts) => {
        let mut inner = Scope::new(Some(scope.clone()));
        for stmt_id in stmts.iter() {
          self.check_stmt(*stmt_id, &mut inner);
        }
      }
      StmtKind::If {
        test,
        consequent,
        alternate,
      } => {
        let _ = self.check_expr(*test, scope);
        self.check_stmt(*consequent, scope);
        if let Some(alt) = alternate {
          self.check_stmt(*alt, scope);
        }
      }
      StmtKind::While { test, body } | StmtKind::DoWhile { test, body } => {
        let _ = self.check_expr(*test, scope);
        self.check_stmt(*body, scope);
      }
      StmtKind::For { init, test, update, body } => {
        if let Some(init) = init {
          match init {
            hir_js::ForInit::Expr(expr) => {
              let _ = self.check_expr(*expr, scope);
            }
            hir_js::ForInit::Var(var) => self.bind_var_decl(var, scope),
          }
        }
        if let Some(test) = test {
          let _ = self.check_expr(*test, scope);
        }
        if let Some(update) = update {
          let _ = self.check_expr(*update, scope);
        }
        self.check_stmt(*body, scope);
      }
      StmtKind::ForIn { left, right, body, .. } => {
        match left {
          hir_js::ForHead::Pat(pat) => {
            let value_ty = self.check_expr(*right, scope);
            self.bind_pat(*pat, value_ty, scope);
          }
          hir_js::ForHead::Var(var) => {
            let value_ty = self.check_expr(*right, scope);
            self.bind_var_decl_with_value(var, value_ty, scope);
          }
        }
        self.check_stmt(*body, scope);
      }
      StmtKind::Switch { discriminant, cases } => {
        let _ = self.check_expr(*discriminant, scope);
        for case in cases {
          if let Some(test) = case.test {
            let _ = self.check_expr(test, scope);
          }
          for stmt in &case.consequent {
            self.check_stmt(*stmt, scope);
          }
        }
      }
      StmtKind::Try {
        block,
        catch,
        finally_block,
      } => {
        self.check_stmt(*block, scope);
        if let Some(catch) = catch {
          if let Some(param) = catch.param {
            self.bind_pat(param, self.store.primitive_ids().unknown, scope);
          }
          self.check_stmt(catch.body, scope);
        }
        if let Some(finally_block) = finally_block {
          self.check_stmt(*finally_block, scope);
        }
      }
      StmtKind::Throw(expr) => {
        let _ = self.check_expr(*expr, scope);
      }
      StmtKind::Var(var) => self.bind_var_decl(var, scope),
      StmtKind::Decl(_) | StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Empty => {}
      StmtKind::Labeled { body, .. } | StmtKind::With { body, .. } => self.check_stmt(*body, scope),
    }
  }

  fn check_expr(&mut self, id: ExprId, scope: &mut Scope) -> TypeId {
    let expr = &self.body.exprs[id.0 as usize];
    let prim = self.store.primitive_ids();
    let ty = match &expr.kind {
      ExprKind::Missing => prim.unknown,
      ExprKind::Ident(name) => match scope.get(*name) {
        Some(ty) => ty,
        None => {
          self.diagnostics.push(Diagnostic::error(
            CODE_UNKNOWN_IDENTIFIER,
            format!(
              "unknown identifier `{}`",
              self.names.resolve(*name).unwrap_or("<unknown>")
            ),
            Span {
              file: self.file,
              range: expr.span,
            },
          ));
          prim.unknown
        }
      },
      ExprKind::Literal(lit) => self.infer_literal_value(lit),
      ExprKind::Binary { left, right, .. } => {
        let l = self.check_expr(*left, scope);
        let r = self.check_expr(*right, scope);
        self.infer_binary(expr, l, r)
      }
      ExprKind::Call(call) => self.check_call(expr, call, scope),
      ExprKind::Member(member) => {
        let _ = self.check_expr(member.object, scope);
        let _ = &member.property;
        prim.unknown
      }
      ExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => {
        let _ = self.check_expr(*test, scope);
        let cons = self.check_expr(*consequent, scope);
        let alt = self.check_expr(*alternate, scope);
        self.store.union(vec![cons, alt])
      }
      ExprKind::Assignment { target, value, .. } => {
        let value_ty = self.check_expr(*value, scope);
        self.bind_pat(*target, value_ty, scope);
        value_ty
      }
      ExprKind::Await { expr, .. } => {
        let _ = self.check_expr(*expr, scope);
        prim.unknown
      }
      ExprKind::Array(arr) => {
        for el in arr.elements.iter() {
          match el {
            hir_js::ArrayElement::Expr(e) | hir_js::ArrayElement::Spread(e) => {
              let _ = self.check_expr(*e, scope);
            }
            hir_js::ArrayElement::Empty => {}
          }
        }
        prim.unknown
      }
      ExprKind::Object(obj) => {
        for prop in obj.properties.iter() {
          match prop {
            hir_js::ObjectProperty::KeyValue { value, .. } => {
              let _ = self.check_expr(*value, scope);
            }
            hir_js::ObjectProperty::Getter { .. }
            | hir_js::ObjectProperty::Setter { .. } => {}
            hir_js::ObjectProperty::Spread(expr) => {
              let _ = self.check_expr(*expr, scope);
            }
          }
        }
        prim.unknown
      }
      _ => prim.unknown,
    };
    if let Some(slot) = self.expr_types.get_mut(id.0 as usize) {
      *slot = ty;
    }
    ty
  }

  fn bind_pat(&mut self, pat_id: PatId, value: TypeId, scope: &mut Scope) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => {
        scope.insert(*name, value);
        if let Some(slot) = self.pat_types.get_mut(pat_id.0 as usize) {
          *slot = value;
        }
      }
      PatKind::Array(array) => {
        for elem in array.elements.iter().flatten() {
          self.bind_pat(elem.pat, self.store.primitive_ids().unknown, scope);
          if let Some(default) = elem.default_value {
            let _ = self.check_expr(default, scope);
          }
        }
        if let Some(rest) = &array.rest {
          self.bind_pat(*rest, value, scope);
        }
        if let Some(slot) = self.pat_types.get_mut(pat_id.0 as usize) {
          *slot = value;
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.bind_pat(prop.value, self.store.primitive_ids().unknown, scope);
          if let Some(default) = prop.default_value {
            let _ = self.check_expr(default, scope);
          }
        }
        if let Some(rest) = &obj.rest {
          self.bind_pat(*rest, value, scope);
        }
        if let Some(slot) = self.pat_types.get_mut(pat_id.0 as usize) {
          *slot = value;
        }
      }
      PatKind::Rest(inner) => {
        self.bind_pat(**inner, value, scope);
        if let Some(slot) = self.pat_types.get_mut(pat_id.0 as usize) {
          *slot = value;
        }
      }
      PatKind::Assign {
        target,
        default_value,
      } => {
        let _ = self.check_expr(*default_value, scope);
        self.bind_pat(*target, value, scope);
        if let Some(slot) = self.pat_types.get_mut(pat_id.0 as usize) {
          *slot = value;
        }
      }
      PatKind::AssignTarget(expr) => {
        let target_ty = self.check_expr(*expr, scope);
        if self.store.type_kind(target_ty) != self.store.type_kind(value) {
          self.diagnostics.push(Diagnostic::error(
            CODE_TYPE_MISMATCH,
            "assignment type mismatch",
            Span {
              file: self.file,
              range: pat.span,
            },
          ));
        }
      }
    }
  }

  fn infer_literal_value(&self, lit: &Literal) -> TypeId {
    match lit {
      Literal::String(s) => {
        let name = self.store.intern_name(s.clone());
        self.store.intern_type(TypeKind::StringLiteral(name))
      }
      Literal::Number(n) => {
        if let Ok(parsed) = n.parse::<f64>() {
          self
            .store
            .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(parsed)))
        } else {
          self.store.primitive_ids().number
        }
      }
      Literal::Boolean(b) => self.store.intern_type(TypeKind::BooleanLiteral(*b)),
      Literal::Null => self.store.primitive_ids().null,
      Literal::Undefined => self.store.primitive_ids().undefined,
      Literal::BigInt(_) => self.store.primitive_ids().bigint,
      Literal::Regex(_) => self.store.primitive_ids().unknown,
    }
  }

  fn infer_binary(&self, expr: &Expr, left: TypeId, right: TypeId) -> TypeId {
    match expr.kind {
      ExprKind::Binary { .. } => {
        let left_kind = self.store.type_kind(left);
        let right_kind = self.store.type_kind(right);
        let prim = self.store.primitive_ids();
        if matches!(left_kind, TypeKind::String | TypeKind::StringLiteral(_))
          || matches!(right_kind, TypeKind::String | TypeKind::StringLiteral(_))
        {
          return prim.string;
        }
        if matches!(left_kind, TypeKind::Number | TypeKind::NumberLiteral(_))
          && matches!(right_kind, TypeKind::Number | TypeKind::NumberLiteral(_))
        {
          return prim.number;
        }
        prim.unknown
      }
      _ => self.store.primitive_ids().unknown,
    }
  }

  fn check_call(
    &mut self,
    expr: &Expr,
    call: &CallExpr,
    scope: &mut Scope,
  ) -> TypeId {
    let callee_ty = self.check_expr(call.callee, scope);
    let prim = self.store.primitive_ids();
    match self.store.type_kind(callee_ty) {
      TypeKind::Callable { overloads } => {
        if overloads.is_empty() {
          return prim.unknown;
        }
        let sig = self.store.signature(overloads[0]);
        if call.args.len() != sig.params.len() {
          self.diagnostics.push(Diagnostic::error(
            CODE_ARGUMENT_COUNT_MISMATCH,
            "argument count mismatch",
            Span {
              file: self.file,
              range: expr.span,
            },
          ));
        }
        for (idx, arg) in call.args.iter().enumerate() {
          let arg_ty = self.check_expr(arg.expr, scope);
          if let Some(param) = sig.params.get(idx) {
            if !self.assignable(arg_ty, param.ty) {
              self.diagnostics.push(Diagnostic::error(
                CODE_TYPE_MISMATCH,
                "argument type mismatch",
                Span {
                  file: self.file,
                  range: self.body.exprs[arg.expr.0 as usize].span,
                },
              ));
            }
          }
        }
        sig.ret
      }
      _ => prim.unknown,
    }
  }

  fn bind_var_decl(&mut self, var: &hir_js::VarDecl, scope: &mut Scope) {
    for decl in &var.declarators {
      let value_ty = decl
        .init
        .map(|init| self.check_expr(init, scope))
        .unwrap_or(self.store.primitive_ids().unknown);
      self.bind_pat(decl.pat, value_ty, scope);
    }
  }

  fn bind_var_decl_with_value(&mut self, var: &hir_js::VarDecl, value: TypeId, scope: &mut Scope) {
    for decl in &var.declarators {
      let value_ty = decl
        .init
        .map(|init| self.check_expr(init, scope))
        .unwrap_or(value);
      self.bind_pat(decl.pat, value_ty, scope);
    }
  }

  fn assignable(&self, src: TypeId, dst: TypeId) -> bool {
    if src == dst {
      return true;
    }
    let prim = self.store.primitive_ids();
    if dst == prim.any || dst == prim.unknown || src == prim.never || src == prim.any {
      return true;
    }
    match (self.store.type_kind(src), self.store.type_kind(dst)) {
      (TypeKind::NumberLiteral(_), TypeKind::Number)
      | (TypeKind::StringLiteral(_), TypeKind::String)
      | (TypeKind::BooleanLiteral(_), TypeKind::Boolean) => true,
      (TypeKind::Union(options), _) => options.iter().all(|m| self.assignable(*m, dst)),
      (_, TypeKind::Union(options)) => options.iter().any(|m| self.assignable(src, *m)),
      _ => false,
    }
  }
}
