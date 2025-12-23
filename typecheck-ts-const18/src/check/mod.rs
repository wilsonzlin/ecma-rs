use crate::diagnostic::Diagnostic;
use crate::expr::Expr;
use crate::expr::ObjectField;
use crate::types::Type;
use std::collections::HashMap;

pub mod literals;
pub mod object_literal;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarKind {
  Const,
  Let,
  Var,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InferOptions {
  pub widen_literals: bool,
  pub literalize: bool,
}

impl InferOptions {
  pub fn for_binding(kind: VarKind) -> Self {
    let widen_literals = !matches!(kind, VarKind::Const);
    InferOptions {
      widen_literals,
      literalize: false,
    }
  }

  pub fn literalize(self) -> Self {
    InferOptions {
      literalize: true,
      ..self
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Freshness {
  Fresh,
  Stale,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FreshContext {
  Direct,
  Nested,
}

#[derive(Debug, Clone)]
pub enum ExprOrigin {
  ObjectLiteral(Vec<ObjectField>),
}

#[derive(Debug, Clone)]
pub struct TypedExpr {
  pub ty: Type,
  pub freshness: Freshness,
  pub origin: Option<ExprOrigin>,
}

impl TypedExpr {
  pub fn stale(ty: Type) -> TypedExpr {
    TypedExpr {
      ty,
      freshness: Freshness::Stale,
      origin: None,
    }
  }
}

pub struct Checker {
  vars: HashMap<String, Type>,
  pub diagnostics: Vec<Diagnostic>,
}

impl Checker {
  pub fn new() -> Checker {
    Checker {
      vars: HashMap::new(),
      diagnostics: Vec::new(),
    }
  }

  pub fn declare(
    &mut self,
    name: impl Into<String>,
    kind: VarKind,
    expr: Expr,
    annotation: Option<Type>,
  ) -> Type {
    let name = name.into();
    let typed_expr = self.infer_expr(
      &expr,
      None,
      InferOptions::for_binding(kind),
      FreshContext::Direct,
    );
    let ty = if let Some(target) = annotation {
      self.check_assignable(&typed_expr, &target);
      target
    } else {
      typed_expr.ty
    };
    // stored vars are never fresh
    self.vars.insert(name, ty.clone());
    ty
  }

  pub fn infer_expr(
    &mut self,
    expr: &Expr,
    contextual: Option<&Type>,
    options: InferOptions,
    freshness: FreshContext,
  ) -> TypedExpr {
    use Expr::*;
    match expr {
      Number(n) => literals::infer_number_literal(*n, contextual, options),
      String(s) => literals::infer_string_literal(s, contextual, options),
      Boolean(b) => literals::infer_boolean_literal(*b, contextual, options),
      Identifier(name) => {
        let ty = self.vars.get(name).cloned().unwrap_or(Type::Any);
        TypedExpr::stale(ty)
      }
      TypeAssertion { expr, typ } => {
        let inner = self.infer_expr(expr, Some(typ), options, freshness);
        // assertions suppress excess property checks
        TypedExpr {
          ty: typ.clone(),
          freshness: Freshness::Stale,
          origin: inner.origin,
        }
      }
      ConstAssertion(expr) => {
        if !literals::is_valid_const_assertion(expr) {
          self
            .diagnostics
            .push(Diagnostic::const_assertion_not_literal());
        }
        let mut typed = self.infer_expr(
          expr,
          contextual,
          InferOptions {
            widen_literals: false,
            literalize: true,
          },
          freshness,
        );
        typed.ty = literals::apply_const_assertion(&typed.ty);
        typed.freshness = Freshness::Stale;
        typed
      }
      Object(fields) => {
        object_literal::infer_object_literal(self, fields, contextual, options, freshness)
      }
      Array(elems) => {
        object_literal::infer_array_literal(self, elems, contextual, options, freshness)
      }
      Satisfies { expr, typ } => {
        let inner = self.infer_expr(expr, Some(typ), options, freshness);
        self.check_assignable(&inner, typ);
        inner
      }
    }
  }

  pub fn check_assignable(&mut self, source: &TypedExpr, target: &Type) -> bool {
    object_literal::excess_property_check(self, source, target);
    if !is_assignable_type(&source.ty, target) {
      self.diagnostics.push(Diagnostic::not_assignable(
        source.ty.to_string(),
        target.to_string(),
      ));
      return false;
    }
    true
  }

  pub fn call(&mut self, params: &[Type], args: Vec<Expr>) {
    for (idx, arg) in args.iter().enumerate() {
      let param_ty = params.get(idx).unwrap_or(&Type::Any);
      let typed_arg = self.infer_expr(
        arg,
        Some(param_ty),
        InferOptions::for_binding(VarKind::Var),
        FreshContext::Direct,
      );
      self.check_assignable(&typed_arg, param_ty);
    }
  }
}

pub fn is_assignable_type(source: &Type, target: &Type) -> bool {
  match target {
    Type::Any => true,
    Type::Union(types) => types.iter().any(|t| is_assignable_type(source, t)),
    _ => match source {
      Type::Union(types) => types.iter().all(|s| is_assignable_type(s, target)),
      _ => assignable_non_union(source, target),
    },
  }
}

fn assignable_non_union(source: &Type, target: &Type) -> bool {
  use Type::*;
  match (source, target) {
    (_, Any) => true,
    (LiteralNumber(a), LiteralNumber(b)) => a == b,
    (LiteralString(a), LiteralString(b)) => a == b,
    (LiteralBoolean(a), LiteralBoolean(b)) => a == b,
    (LiteralNumber(_), Number) => true,
    (LiteralString(_), String) => true,
    (LiteralBoolean(_), Boolean) => true,
    (Number, Number) | (String, String) | (Boolean, Boolean) => true,
    (Never, _) => true,
    (Array(a), Array(b)) => is_assignable_type(a, b),
    (Tuple(a), Tuple(b)) => {
      if a.readonly && !b.readonly {
        return false;
      }
      if a.elements.len() != b.elements.len() {
        return false;
      }
      a.elements
        .iter()
        .zip(b.elements.iter())
        .all(|(s, t)| is_assignable_type(s, t))
    }
    (Tuple(a), Array(b)) => {
      if a.readonly {
        return false;
      }
      a.elements.iter().all(|el| is_assignable_type(el, b))
    }
    (Object(source_obj), Object(target_obj)) => {
      for target_prop in &target_obj.properties {
        let Some(source_prop) = source_obj.property(&target_prop.name) else {
          return false;
        };
        if !target_prop.readonly && source_prop.readonly {
          return false;
        }
        if !is_assignable_type(&source_prop.typ, &target_prop.typ) {
          return false;
        }
      }
      if let Some(idx) = &target_obj.index_signature {
        for prop in &source_obj.properties {
          if !is_assignable_type(&prop.typ, &idx.value) {
            return false;
          }
        }
      }
      true
    }
    _ => false,
  }
}
