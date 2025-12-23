use super::Freshness;
use super::InferOptions;
use super::TypedExpr;
use crate::check::Checker;
use crate::diagnostic::Diagnostic;
use crate::expr::Expr;
use crate::expr::ObjectField;
use crate::types::ObjectType;
use crate::types::Property;
use crate::types::TupleType;
use crate::types::Type;

pub fn infer_object_literal(
  checker: &mut Checker,
  fields: &[ObjectField],
  contextual: Option<&Type>,
  options: InferOptions,
  freshness: super::FreshContext,
) -> TypedExpr {
  let contextual_obj = contextual.and_then(as_object_type);
  let mut props = Vec::new();
  let mut origin_fields = Vec::new();
  for field in fields {
    let field_ctx = contextual_obj
      .and_then(|obj| obj.property(&field.name))
      .map(|p| &p.typ);
    let value_opts = if options.literalize {
      InferOptions {
        literalize: true,
        widen_literals: false,
      }
    } else if field_ctx.is_some() {
      InferOptions {
        literalize: false,
        widen_literals: false,
      }
    } else {
      InferOptions {
        literalize: false,
        widen_literals: options.widen_literals,
      }
    };
    let typed_value = checker.infer_expr(
      &field.value,
      field_ctx,
      value_opts,
      super::FreshContext::Nested,
    );
    props.push(Property {
      name: field.name.clone(),
      typ: typed_value.ty,
      optional: false,
      readonly: options.literalize,
    });
    origin_fields.push(field.clone());
  }
  let obj = ObjectType {
    properties: props,
    index_signature: None,
  };
  TypedExpr {
    ty: Type::Object(Box::new(obj)),
    freshness: match freshness {
      super::FreshContext::Direct => Freshness::Fresh,
      super::FreshContext::Nested => Freshness::Stale,
    },
    origin: Some(super::ExprOrigin::ObjectLiteral(origin_fields)),
  }
}

pub fn infer_array_literal(
  checker: &mut Checker,
  elems: &[Expr],
  contextual: Option<&Type>,
  options: InferOptions,
  _freshness: super::FreshContext,
) -> TypedExpr {
  let mut element_types = Vec::new();
  for (idx, elem) in elems.iter().enumerate() {
    let elem_ctx = contextual_element_type(contextual, idx);
    let widen_literals = if options.literalize {
      false
    } else if elem_ctx.is_some() {
      false
    } else {
      options.widen_literals
    };
    let elem_ty = checker
      .infer_expr(
        elem,
        elem_ctx,
        InferOptions {
          widen_literals,
          literalize: options.literalize,
        },
        super::FreshContext::Nested,
      )
      .ty;
    element_types.push(elem_ty);
  }
  if options.literalize {
    return TypedExpr {
      ty: Type::Tuple(TupleType {
        elements: element_types,
        readonly: true,
      }),
      freshness: Freshness::Stale,
      origin: None,
    };
  }

  if let Some(Type::Tuple(ctx_tuple)) = contextual {
    return TypedExpr {
      ty: Type::Tuple(TupleType {
        elements: element_types,
        readonly: ctx_tuple.readonly,
      }),
      freshness: Freshness::Stale,
      origin: None,
    };
  }
  let element_union = if element_types.is_empty() {
    Type::Any
  } else if element_types.len() == 1 {
    element_types.remove(0)
  } else {
    Type::union(element_types)
  };
  TypedExpr::stale(Type::Array(Box::new(element_union)))
}

fn contextual_element_type(contextual: Option<&Type>, index: usize) -> Option<&Type> {
  match contextual {
    Some(Type::Array(elem)) => Some(elem),
    Some(Type::Tuple(tuple)) => tuple.elements.get(index),
    _ => None,
  }
}

pub fn tuple_from_array(elem: &Type, readonly: bool) -> TupleType {
  TupleType {
    elements: vec![elem.clone()],
    readonly,
  }
}

pub fn excess_property_check(checker: &mut Checker, source: &TypedExpr, target: &Type) {
  let Type::Object(target_obj) = target else {
    return;
  };
  if target_obj.properties.is_empty() {
    return;
  }
  if target_obj.index_signature.is_some() {
    return;
  }
  if !matches!(source.freshness, Freshness::Fresh) {
    return;
  }
  let Some(origin) = &source.origin else {
    return;
  };
  let super::ExprOrigin::ObjectLiteral(fields) = origin;
  for field in fields {
    if !target_obj.has_property(&field.name) {
      checker
        .diagnostics
        .push(Diagnostic::excess_property(field.name.clone(), field.span));
    }
  }
}

fn as_object_type(ty: &Type) -> Option<&ObjectType> {
  match ty {
    Type::Object(obj) => Some(obj),
    _ => None,
  }
}
