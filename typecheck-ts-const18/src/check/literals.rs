use super::InferOptions;
use super::TypedExpr;
use crate::expr::Expr;
use crate::types::Type;

pub fn infer_number_literal(
  value: f64,
  contextual: Option<&Type>,
  options: InferOptions,
) -> TypedExpr {
  let value_int = value as i128;
  let ty = literal_type(
    Type::LiteralNumber(value_int),
    Type::Number,
    contextual,
    options,
  );
  TypedExpr::stale(ty)
}

pub fn infer_string_literal(
  value: &str,
  contextual: Option<&Type>,
  options: InferOptions,
) -> TypedExpr {
  let ty = literal_type(
    Type::LiteralString(value.to_string()),
    Type::String,
    contextual,
    options,
  );
  TypedExpr::stale(ty)
}

pub fn infer_boolean_literal(
  value: bool,
  contextual: Option<&Type>,
  options: InferOptions,
) -> TypedExpr {
  let ty = literal_type(
    Type::LiteralBoolean(value),
    Type::Boolean,
    contextual,
    options,
  );
  TypedExpr::stale(ty)
}

fn literal_type(
  lit: Type,
  primitive: Type,
  contextual: Option<&Type>,
  options: InferOptions,
) -> Type {
  if options.literalize {
    return lit;
  }
  if let Some(ctx) = contextual {
    if context_accepts_literal(ctx, &lit) {
      return lit;
    }
    return ctx.clone();
  }
  if options.widen_literals {
    primitive
  } else {
    lit
  }
}

fn context_accepts_literal(context: &Type, literal: &Type) -> bool {
  use Type::*;
  match context {
    LiteralNumber(_) | LiteralString(_) | LiteralBoolean(_) => context == literal,
    Union(types) => types.iter().any(|t| context_accepts_literal(t, literal)),
    _ => false,
  }
}

pub fn is_valid_const_assertion(expr: &Expr) -> bool {
  matches!(
    expr,
    Expr::Number(_) | Expr::String(_) | Expr::Boolean(_) | Expr::Object(_) | Expr::Array(_)
  )
}

pub fn apply_const_assertion(ty: &Type) -> Type {
  match ty {
    Type::Array(elem) => Type::Tuple(super::object_literal::tuple_from_array(elem, true)),
    Type::Tuple(tuple) => Type::Tuple(crate::types::TupleType {
      elements: tuple.elements.clone(),
      readonly: true,
    }),
    Type::Object(obj) => {
      let mut new_props = Vec::new();
      for prop in &obj.properties {
        let lit = apply_const_assertion(&prop.typ);
        new_props.push(crate::types::Property {
          name: prop.name.clone(),
          typ: lit,
          optional: prop.optional,
          readonly: true,
        });
      }
      Type::Object(Box::new(crate::types::ObjectType {
        properties: new_props,
        index_signature: obj.index_signature.clone(),
      }))
    }
    Type::LiteralNumber(_)
    | Type::LiteralString(_)
    | Type::LiteralBoolean(_)
    | Type::Number
    | Type::String
    | Type::Boolean
    | Type::Never
    | Type::Any => ty.clone(),
    Type::Union(types) => Type::Union(types.iter().map(apply_const_assertion).collect()),
  }
}
