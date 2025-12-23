use super::body::BodyChecker;
use super::expr::check_expr;
use crate::types::TypeId;
use parse_js::ast::expr::pat::ArrPat;
use parse_js::ast::expr::pat::ObjPat;
use parse_js::ast::expr::pat::ObjPatProp;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::node::Node;
use std::collections::BTreeMap;

pub(crate) fn check_pattern(
  ctx: &mut BodyChecker<'_>,
  pat: &Node<Pat>,
  expected: TypeId,
) -> TypeId {
  let id = ctx.assign_pat_id(pat);
  if let Some(slot) = ctx.pat_types.get_mut(id.index()) {
    *slot = expected;
  }

  match pat.stx.as_ref() {
    Pat::Id(id_pat) => {
      ctx.define(&id_pat.stx.name, expected);
      expected
    }
    Pat::Arr(arr) => check_array_pattern(ctx, arr, expected),
    Pat::Obj(obj) => check_object_pattern(ctx, obj, expected),
    Pat::AssignTarget(expr) => {
      check_expr(ctx, expr, Some(expected));
      expected
    }
  }
}

fn check_array_pattern(ctx: &mut BodyChecker<'_>, pat: &Node<ArrPat>, expected: TypeId) -> TypeId {
  let element_ty = match ctx.store.get(expected) {
    crate::types::Type::Array(elem) => *elem,
    _ => ctx.store.unknown(),
  };

  for elem in &pat.stx.elements {
    if let Some(elem) = elem {
      let target_ty = if let Some(default) = &elem.default_value {
        let default_ty = check_expr(ctx, default, Some(element_ty));
        ctx.store.union(vec![element_ty, default_ty])
      } else {
        element_ty
      };
      check_pattern(ctx, &elem.target, target_ty);
    }
  }

  if let Some(rest) = &pat.stx.rest {
    check_pattern(ctx, rest, expected);
  }

  expected
}

fn check_object_pattern(ctx: &mut BodyChecker<'_>, pat: &Node<ObjPat>, expected: TypeId) -> TypeId {
  let mut prop_types = BTreeMap::new();
  if let crate::types::Type::Object(props) = ctx.store.get(expected) {
    for (k, v) in props.iter() {
      prop_types.insert(k.clone(), *v);
    }
  }

  for prop in &pat.stx.properties {
    let ObjPatProp {
      key,
      target,
      default_value,
      ..
    } = prop.stx.as_ref();
    use parse_js::ast::class_or_object::ClassOrObjKey;
    let prop_ty = match key {
      ClassOrObjKey::Direct(key) => {
        let name = &key.stx.key;
        *prop_types.get(name).unwrap_or(&ctx.store.unknown())
      }
      ClassOrObjKey::Computed(expr) => {
        check_expr(ctx, expr, None);
        ctx.store.unknown()
      }
    };
    let prop_ty = if let Some(default) = default_value {
      let default_ty = check_expr(ctx, default, Some(prop_ty));
      ctx.store.union(vec![prop_ty, default_ty])
    } else {
      prop_ty
    };
    check_pattern(ctx, target, prop_ty);
  }

  if let Some(rest) = &pat.stx.rest {
    check_pattern(ctx, rest, expected);
  }

  expected
}
