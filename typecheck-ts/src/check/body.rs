use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{Body, Expr, ExprId, ExprKind, NameInterner, PatId, PatKind, StmtId, StmtKind};
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
      StmtKind::Decl(_) | StmtKind::Empty | StmtKind::Other => {}
    }
  }

  fn check_expr(&mut self, id: ExprId, scope: &mut Scope) -> TypeId {
    let expr = &self.body.exprs[id.0 as usize];
    let ty = match &expr.kind {
      ExprKind::Missing => self.store.primitive_ids().unknown,
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
          self.store.primitive_ids().unknown
        }
      },
      ExprKind::Literal => self.infer_literal(expr.span),
      ExprKind::Binary { left, right } => {
        let l = self.check_expr(*left, scope);
        let r = self.check_expr(*right, scope);
        self.infer_binary(expr, l, r)
      }
      ExprKind::Call { callee, args, .. } => self.check_call(expr, *callee, args, scope),
      ExprKind::Member {
        object, property, ..
      } => {
        let _ = self.check_expr(*object, scope);
        // Without full object typing, treat member access as unknown.
        let _ = property;
        self.store.primitive_ids().unknown
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
      ExprKind::Assignment { target, value } => {
        let value_ty = self.check_expr(*value, scope);
        self.bind_pat(*target, value_ty, scope);
        value_ty
      }
      ExprKind::FunctionExpr { .. }
      | ExprKind::ClassExpr { .. }
      | ExprKind::This
      | ExprKind::Super
      | ExprKind::Await { .. }
      | ExprKind::Object
      | ExprKind::Array
      | ExprKind::Other => self.store.primitive_ids().unknown,
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
      PatKind::Destructure(children) => {
        for child in children {
          self.bind_pat(*child, self.store.primitive_ids().unknown, scope);
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
      PatKind::Unknown => {}
    }
  }

  fn infer_literal(&self, span: TextRange) -> TypeId {
    let prim = self.store.primitive_ids();
    if span.end as usize <= self.source.len() && span.start as usize <= self.source.len() {
      let text = &self.source[span.start as usize..span.end as usize];
      let trimmed = text.trim();
      if trimmed.starts_with('"') || trimmed.starts_with('\'') || trimmed.starts_with('`') {
        let name = self
          .store
          .intern_name(trimmed.trim_matches(&['"', '\'', '`'][..]));
        return self.store.intern_type(TypeKind::StringLiteral(name));
      }
      if trimmed == "true" {
        return self.store.intern_type(TypeKind::BooleanLiteral(true));
      }
      if trimmed == "false" {
        return self.store.intern_type(TypeKind::BooleanLiteral(false));
      }
      if trimmed == "null" {
        return prim.null;
      }
      if trimmed == "undefined" {
        return prim.undefined;
      }
      if trimmed.parse::<f64>().is_ok() {
        return prim.number;
      }
    }
    prim.unknown
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
    callee: ExprId,
    args: &[ExprId],
    scope: &mut Scope,
  ) -> TypeId {
    let callee_ty = self.check_expr(callee, scope);
    let prim = self.store.primitive_ids();
    match self.store.type_kind(callee_ty) {
      TypeKind::Callable { overloads } => {
        if overloads.is_empty() {
          return prim.unknown;
        }
        let sig = self.store.signature(overloads[0]);
        if args.len() != sig.params.len() {
          self.diagnostics.push(Diagnostic::error(
            CODE_ARGUMENT_COUNT_MISMATCH,
            "argument count mismatch",
            Span {
              file: self.file,
              range: expr.span,
            },
          ));
        }
        for (idx, arg) in args.iter().enumerate() {
          let arg_ty = self.check_expr(*arg, scope);
          if let Some(param) = sig.params.get(idx) {
            if !self.assignable(arg_ty, param.ty) {
              self.diagnostics.push(Diagnostic::error(
                CODE_TYPE_MISMATCH,
                "argument type mismatch",
                Span {
                  file: self.file,
                  range: self.body.exprs[arg.0 as usize].span,
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
