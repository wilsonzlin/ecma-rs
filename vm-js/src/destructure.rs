use crate::exec::{eval_expr, RuntimeEnv};
use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Scope, Value, Vm, VmError};
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat};
use parse_js::ast::expr::{ComputedMemberExpr, Expr, MemberExpr};
use parse_js::ast::node::Node;

#[derive(Clone, Copy, Debug)]
pub(crate) enum BindingKind {
  Var,
  Let,
  Const,
  Assignment,
}

pub(crate) fn bind_pattern(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  pat: &Pat,
  value: Value,
  kind: BindingKind,
  strict: bool,
) -> Result<(), VmError> {
  // Keep temporary roots local to this binding operation.
  let mut scope = scope.reborrow();
  // Root the input value so destructuring can allocate without the RHS being collected.
  let value = scope.push_root(value);

  match pat {
    Pat::Id(id) => bind_identifier(env, &mut scope, &id.stx.name, value, kind, strict),
    Pat::Obj(obj) => bind_object_pattern(vm, &mut scope, env, &obj.stx, value, kind, strict),
    Pat::Arr(arr) => bind_array_pattern(vm, &mut scope, env, &arr.stx, value, kind, strict),
    Pat::AssignTarget(expr) => {
      if !matches!(kind, BindingKind::Assignment) {
        return Err(VmError::Unimplemented(
          "assignment target pattern in binding context",
        ));
      }
      bind_assignment_target(vm, &mut scope, env, expr, value, strict)
    }
  }
}

pub(crate) fn bind_assignment_target(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  target: &Node<Expr>,
  value: Value,
  strict: bool,
) -> Result<(), VmError> {
  // Keep temporary roots local to this binding operation.
  let mut scope = scope.reborrow();
  let value = scope.push_root(value);

  match &*target.stx {
    Expr::Id(id) => {
      bind_identifier(env, &mut scope, &id.stx.name, value, BindingKind::Assignment, strict)
    }
    Expr::IdPat(id) => {
      bind_identifier(env, &mut scope, &id.stx.name, value, BindingKind::Assignment, strict)
    }
    Expr::ObjPat(obj) => bind_object_pattern(
      vm,
      &mut scope,
      env,
      &obj.stx,
      value,
      BindingKind::Assignment,
      strict,
    ),
    Expr::ArrPat(arr) => bind_array_pattern(
      vm,
      &mut scope,
      env,
      &arr.stx,
      value,
      BindingKind::Assignment,
      strict,
    ),
    Expr::Member(member) => assign_to_member(vm, &mut scope, env, &member.stx, value, strict),
    Expr::ComputedMember(member) => {
      assign_to_computed_member(vm, &mut scope, env, &member.stx, value, strict)
    }
    _ => Err(VmError::Unimplemented("assignment target")),
  }
}

fn bind_identifier(
  env: &mut RuntimeEnv,
  scope: &mut Scope<'_>,
  name: &str,
  value: Value,
  kind: BindingKind,
  strict: bool,
) -> Result<(), VmError> {
  match kind {
    BindingKind::Var => env.set_var(scope, name, value),
    BindingKind::Let => {
      let env_rec = env.lexical_env();
      if !scope.heap().env_has_binding(env_rec, name)? {
        // Non-block statement contexts may not have performed lexical hoisting yet.
        scope.env_create_mutable_binding(env_rec, name)?;
      }
      scope.heap_mut().env_initialize_binding(env_rec, name, value)
    }
    BindingKind::Const => {
      let env_rec = env.lexical_env();
      if !scope.heap().env_has_binding(env_rec, name)? {
        // Non-block statement contexts may not have performed lexical hoisting yet.
        scope.env_create_immutable_binding(env_rec, name)?;
      }
      scope.heap_mut().env_initialize_binding(env_rec, name, value)
    }
    BindingKind::Assignment => env.set(scope, name, value, strict),
  }
}

fn bind_object_pattern(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  pat: &ObjPat,
  value: Value,
  kind: BindingKind,
  strict: bool,
) -> Result<(), VmError> {
  let Value::Object(obj) = value else {
    return Err(VmError::Unimplemented("object destructuring requires object"));
  };
  scope.push_root(Value::Object(obj));

  let mut excluded: Vec<PropertyKey> = Vec::with_capacity(pat.properties.len());

  for prop in &pat.properties {
    let key = resolve_obj_pat_key(vm, scope, env, &prop.stx.key)?;
    root_property_key(scope, key);
    excluded.push(key);

    let mut prop_value = scope.ordinary_get(vm, obj, key, Value::Object(obj))?;
    if matches!(prop_value, Value::Undefined) {
      if let Some(default_expr) = &prop.stx.default_value {
        prop_value = eval_expr(vm, env, scope, default_expr)?;
      }
    }

    bind_pattern(vm, scope, env, &prop.stx.target.stx, prop_value, kind, strict)?;
  }

  let Some(rest_pat) = &pat.rest else {
    return Ok(());
  };

  let rest_obj = scope.alloc_object()?;
  scope.push_root(Value::Object(rest_obj));

  let keys = scope.ordinary_own_property_keys(obj)?;
  for key in keys {
    if excluded
      .iter()
      .any(|excluded_key| scope.heap().property_key_eq(excluded_key, &key))
    {
      continue;
    }

    let Some(desc) = scope.ordinary_get_own_property(obj, key)? else {
      continue;
    };
    if !desc.enumerable {
      continue;
    }

    // `CopyDataProperties` uses `Get` even though we already have the descriptor.
    let v = scope.ordinary_get(vm, obj, key, Value::Object(obj))?;
    let _ = scope.create_data_property(rest_obj, key, v)?;
  }

  bind_pattern(vm, scope, env, &rest_pat.stx, Value::Object(rest_obj), kind, strict)
}

fn bind_array_pattern(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  pat: &ArrPat,
  value: Value,
  kind: BindingKind,
  strict: bool,
) -> Result<(), VmError> {
  let Value::Object(obj) = value else {
    return Err(VmError::Unimplemented("array destructuring requires object"));
  };
  scope.push_root(Value::Object(obj));

  let len = array_like_length(vm, scope, obj)?;
  let mut idx: u32 = 0;

  for elem in &pat.elements {
    let Some(elem) = elem else {
      idx = idx.saturating_add(1);
      continue;
    };

    let mut item = if idx < len {
      array_like_get(vm, scope, obj, idx)?
    } else {
      Value::Undefined
    };

    if matches!(item, Value::Undefined) {
      if let Some(default_expr) = &elem.default_value {
        item = eval_expr(vm, env, scope, default_expr)?;
      }
    }

    bind_pattern(vm, scope, env, &elem.target.stx, item, kind, strict)?;
    idx = idx.saturating_add(1);
  }

  let Some(rest_pat) = &pat.rest else {
    return Ok(());
  };

  let mut rest_values: Vec<Value> = Vec::new();
  while idx < len {
    rest_values.push(array_like_get(vm, scope, obj, idx)?);
    idx += 1;
  }

  let rest_arr = alloc_array_object(scope, &rest_values)?;
  bind_pattern(vm, scope, env, &rest_pat.stx, Value::Object(rest_arr), kind, strict)
}

fn resolve_obj_pat_key(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  key: &ClassOrObjKey,
) -> Result<PropertyKey, VmError> {
  match key {
    ClassOrObjKey::Direct(direct) => {
      let s = scope.alloc_string(&direct.stx.key)?;
      Ok(PropertyKey::from_string(s))
    }
    ClassOrObjKey::Computed(expr) => {
      let value = eval_expr(vm, env, scope, expr)?;
      // Root the computed value until `to_property_key` completes.
      let value = scope.push_root(value);
      let key = scope.heap_mut().to_property_key(value)?;
      Ok(key)
    }
  }
}

fn array_like_length(vm: &mut Vm, scope: &mut Scope<'_>, obj: GcObject) -> Result<u32, VmError> {
  let key_s = scope.alloc_string("length")?;
  let key = PropertyKey::from_string(key_s);
  let v = scope.ordinary_get(vm, obj, key, Value::Object(obj))?;
  match v {
    Value::Number(n) if n.is_finite() && n >= 0.0 => Ok(n as u32),
    Value::Undefined => Ok(0),
    _ => Err(VmError::Unimplemented("array-like length")),
  }
}

fn array_like_get(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  obj: GcObject,
  idx: u32,
) -> Result<Value, VmError> {
  let key_str = idx.to_string();
  let key_s = scope.alloc_string(&key_str)?;
  let key = PropertyKey::from_string(key_s);
  scope.ordinary_get(vm, obj, key, Value::Object(obj))
}

fn alloc_array_object(scope: &mut Scope<'_>, elems: &[Value]) -> Result<GcObject, VmError> {
  let arr = scope.alloc_object()?;
  scope.push_root(Value::Object(arr));

  for (i, &v) in elems.iter().enumerate() {
    let key_str = i.to_string();
    let key_s = scope.alloc_string(&key_str)?;
    let key = PropertyKey::from_string(key_s);
    let _ = scope.create_data_property(arr, key, v)?;
  }

  // Define `length` as non-enumerable to match real arrays closely enough for rest patterns.
  let length_s = scope.alloc_string("length")?;
  let length_key = PropertyKey::from_string(length_s);
  let length_desc = PropertyDescriptor {
    enumerable: false,
    configurable: true,
    kind: PropertyKind::Data {
      value: Value::Number(elems.len() as f64),
      writable: true,
    },
  };
  scope.define_property(arr, length_key, length_desc)?;

  Ok(arr)
}

fn assign_to_member(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  member: &MemberExpr,
  value: Value,
  strict: bool,
) -> Result<(), VmError> {
  if member.optional_chaining {
    return Err(VmError::Unimplemented("optional chaining assignment target"));
  }

  // Root the RHS across evaluation of the LHS object.
  let mut rhs_scope = scope.reborrow();
  rhs_scope.push_root(value);
  let obj_value = eval_expr(vm, env, &mut rhs_scope, &member.left)?;

  let Value::Object(obj) = obj_value else {
    return Err(VmError::Unimplemented("member assignment on non-object"));
  };

  let key_s = rhs_scope.alloc_string(&member.right)?;
  let key = PropertyKey::from_string(key_s);
  let ok = rhs_scope.ordinary_set(vm, obj, key, value, Value::Object(obj))?;
  if ok {
    Ok(())
  } else if strict {
    Err(VmError::Unimplemented(
      "strict mode assignment failed (needs TypeError)",
    ))
  } else {
    Ok(())
  }
}

fn assign_to_computed_member(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  member: &ComputedMemberExpr,
  value: Value,
  strict: bool,
) -> Result<(), VmError> {
  if member.optional_chaining {
    return Err(VmError::Unimplemented("optional chaining assignment target"));
  }

  // Root the RHS across evaluation of the LHS object/key.
  let mut rhs_scope = scope.reborrow();
  rhs_scope.push_root(value);

  let obj_value = eval_expr(vm, env, &mut rhs_scope, &member.object)?;
  let Value::Object(obj) = obj_value else {
    return Err(VmError::Unimplemented("computed member assignment on non-object"));
  };

  let key_value = eval_expr(vm, env, &mut rhs_scope, &member.member)?;
  let key_value = rhs_scope.push_root(key_value);
  let key = rhs_scope.heap_mut().to_property_key(key_value)?;

  let ok = rhs_scope.ordinary_set(vm, obj, key, value, Value::Object(obj))?;
  if ok {
    Ok(())
  } else if strict {
    Err(VmError::Unimplemented(
      "strict mode assignment failed (needs TypeError)",
    ))
  } else {
    Ok(())
  }
}

fn root_property_key(scope: &mut Scope<'_>, key: PropertyKey) {
  match key {
    PropertyKey::String(s) => {
      scope.push_root(Value::String(s));
    }
    PropertyKey::Symbol(s) => {
      scope.push_root(Value::Symbol(s));
    }
  }
}
