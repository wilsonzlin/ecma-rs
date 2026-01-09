use crate::exec::{eval_expr, InterpretedEcmaFunction, RuntimeEnv};
use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{new_type_error, GcObject, Realm, Scope, Value, Vm, VmError};
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat};
use parse_js::ast::expr::{ComputedMemberExpr, Expr, MemberExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use std::sync::Arc;

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
  realm: &Realm,
  ecma_functions: &mut Vec<InterpretedEcmaFunction>,
  pat: &Pat,
  value: Value,
  kind: BindingKind,
  strict: bool,
  this: Value,
  script: &Arc<Node<TopLevel>>,
) -> Result<(), VmError> {
  // Keep temporary roots local to this binding operation.
  let mut scope = scope.reborrow();
  // Root the input value so destructuring can allocate without the RHS being collected.
  let value = scope.push_root(value)?;

  match pat {
    Pat::Id(id) => bind_identifier(vm, env, realm, &mut scope, &id.stx.name, value, kind, strict),
    Pat::Obj(obj) => bind_object_pattern(
      vm,
      &mut scope,
      env,
      realm,
      ecma_functions,
      &obj.stx,
      value,
      kind,
      strict,
      this,
      script,
    ),
    Pat::Arr(arr) => bind_array_pattern(
      vm,
      &mut scope,
      env,
      realm,
      ecma_functions,
      &arr.stx,
      value,
      kind,
      strict,
      this,
      script,
    ),
    Pat::AssignTarget(expr) => {
      if !matches!(kind, BindingKind::Assignment) {
        return Err(VmError::Unimplemented(
          "assignment target pattern in binding context",
        ));
      }
      bind_assignment_target(
        vm,
        &mut scope,
        env,
        realm,
        ecma_functions,
        expr,
        value,
        strict,
        this,
        script,
      )
    }
  }
}

pub(crate) fn bind_assignment_target(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  realm: &Realm,
  ecma_functions: &mut Vec<InterpretedEcmaFunction>,
  target: &Node<Expr>,
  value: Value,
  strict: bool,
  this: Value,
  script: &Arc<Node<TopLevel>>,
) -> Result<(), VmError> {
  // Keep temporary roots local to this binding operation.
  let mut scope = scope.reborrow();
  let value = scope.push_root(value)?;

  match &*target.stx {
    Expr::Id(id) => bind_identifier(
      vm,
      env,
      realm,
      &mut scope,
      &id.stx.name,
      value,
      BindingKind::Assignment,
      strict,
    ),
    Expr::IdPat(id) => bind_identifier(
      vm,
      env,
      realm,
      &mut scope,
      &id.stx.name,
      value,
      BindingKind::Assignment,
      strict,
    ),
    Expr::ObjPat(obj) => bind_object_pattern(
      vm,
      &mut scope,
      env,
      realm,
      ecma_functions,
      &obj.stx,
      value,
      BindingKind::Assignment,
      strict,
      this,
      script,
    ),
    Expr::ArrPat(arr) => bind_array_pattern(
      vm,
      &mut scope,
      env,
      realm,
      ecma_functions,
      &arr.stx,
      value,
      BindingKind::Assignment,
      strict,
      this,
      script,
    ),
    Expr::Member(member) => assign_to_member(
      vm,
      &mut scope,
      env,
      realm,
      ecma_functions,
      &member.stx,
      value,
      strict,
      this,
      script,
    ),
    Expr::ComputedMember(member) => assign_to_computed_member(
      vm,
      &mut scope,
      env,
      realm,
      ecma_functions,
      &member.stx,
      value,
      strict,
      this,
      script,
    ),
    _ => Err(VmError::Unimplemented("assignment target")),
  }
}

fn bind_identifier(
  vm: &mut Vm,
  env: &mut RuntimeEnv,
  realm: &Realm,
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
    BindingKind::Assignment => env.set(vm, scope, realm, name, value, strict),
  }
}

fn bind_object_pattern(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  realm: &Realm,
  ecma_functions: &mut Vec<InterpretedEcmaFunction>,
  pat: &ObjPat,
  value: Value,
  kind: BindingKind,
  strict: bool,
  this: Value,
  script: &Arc<Node<TopLevel>>,
) -> Result<(), VmError> {
  let Value::Object(obj) = value else {
    return Err(new_type_error(scope, realm, "object destructuring requires object")?);
  };
  scope.push_root(Value::Object(obj))?;

  let mut excluded: Vec<PropertyKey> = Vec::new();
  excluded
    .try_reserve_exact(pat.properties.len())
    .map_err(|_| VmError::OutOfMemory)?;

  for prop in &pat.properties {
    let key = resolve_obj_pat_key(
      vm,
      scope,
      env,
      realm,
      ecma_functions,
      &prop.stx.key,
      strict,
      this,
      script,
    )?;
    root_property_key(scope, key)?;
    excluded.push(key);

    let mut prop_value = scope.ordinary_get(vm, obj, key, Value::Object(obj))?;
    if matches!(prop_value, Value::Undefined) {
      if let Some(default_expr) = &prop.stx.default_value {
        prop_value =
          eval_expr(vm, env, realm, ecma_functions, strict, this, script, scope, default_expr)?;
      }
    }

    bind_pattern(
      vm,
      scope,
      env,
      realm,
      ecma_functions,
      &prop.stx.target.stx,
      prop_value,
      kind,
      strict,
      this,
      script,
    )?;
  }

  let Some(rest_pat) = &pat.rest else {
    return Ok(());
  };

  let rest_obj = scope.alloc_object()?;
  scope.push_root(Value::Object(rest_obj))?;

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

  bind_pattern(
    vm,
    scope,
    env,
    realm,
    ecma_functions,
    &rest_pat.stx,
    Value::Object(rest_obj),
    kind,
    strict,
    this,
    script,
  )
}

fn bind_array_pattern(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  realm: &Realm,
  ecma_functions: &mut Vec<InterpretedEcmaFunction>,
  pat: &ArrPat,
  value: Value,
  kind: BindingKind,
  strict: bool,
  this: Value,
  script: &Arc<Node<TopLevel>>,
) -> Result<(), VmError> {
  let Value::Object(obj) = value else {
    return Err(new_type_error(scope, realm, "array destructuring requires object")?);
  };
  scope.push_root(Value::Object(obj))?;

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
        item = eval_expr(vm, env, realm, ecma_functions, strict, this, script, scope, default_expr)?;
      }
    }

    bind_pattern(
      vm,
      scope,
      env,
      realm,
      ecma_functions,
      &elem.target.stx,
      item,
      kind,
      strict,
      this,
      script,
    )?;
    idx = idx.saturating_add(1);
  }

  let Some(rest_pat) = &pat.rest else {
    return Ok(());
  };

  let rest_arr = scope.alloc_object()?;
  scope.push_root(Value::Object(rest_arr))?;

  let mut rest_idx: u32 = 0;
  while idx < len {
    let v = array_like_get(vm, scope, obj, idx)?;
    {
      // Root the element value while allocating the property key and defining the property:
      // `array_like_get` can invoke getters which may return newly-allocated objects that are not
      // reachable from `obj` itself.
      let mut elem_scope = scope.reborrow();
      let v = elem_scope.push_root(v)?;
      let key_str = rest_idx.to_string();
      let key_s = elem_scope.alloc_string(&key_str)?;
      let key = PropertyKey::from_string(key_s);
      let _ = elem_scope.create_data_property(rest_arr, key, v)?;
    }
    idx += 1;
    rest_idx += 1;
  }

  // Define `length` as non-enumerable to match real arrays closely enough for rest patterns.
  let length_s = scope.alloc_string("length")?;
  let length_key = PropertyKey::from_string(length_s);
  let length_desc = PropertyDescriptor {
    enumerable: false,
    configurable: true,
    kind: PropertyKind::Data {
      value: Value::Number(rest_idx as f64),
      writable: true,
    },
  };
  scope.define_property(rest_arr, length_key, length_desc)?;

  bind_pattern(
    vm,
    scope,
    env,
    realm,
    ecma_functions,
    &rest_pat.stx,
    Value::Object(rest_arr),
    kind,
    strict,
    this,
    script,
  )
}

fn resolve_obj_pat_key(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  realm: &Realm,
  ecma_functions: &mut Vec<InterpretedEcmaFunction>,
  key: &ClassOrObjKey,
  strict: bool,
  this: Value,
  script: &Arc<Node<TopLevel>>,
) -> Result<PropertyKey, VmError> {
  match key {
    ClassOrObjKey::Direct(direct) => {
      let s = scope.alloc_string(&direct.stx.key)?;
      Ok(PropertyKey::from_string(s))
    }
    ClassOrObjKey::Computed(expr) => {
      let value = eval_expr(vm, env, realm, ecma_functions, strict, this, script, scope, expr)?;
      // Root the computed value until `to_property_key` completes.
      let value = scope.push_root(value)?;
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

fn array_like_get(vm: &mut Vm, scope: &mut Scope<'_>, obj: GcObject, idx: u32) -> Result<Value, VmError> {
  let key_str = idx.to_string();
  let key_s = scope.alloc_string(&key_str)?;
  let key = PropertyKey::from_string(key_s);
  scope.ordinary_get(vm, obj, key, Value::Object(obj))
}

fn assign_to_member(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  realm: &Realm,
  ecma_functions: &mut Vec<InterpretedEcmaFunction>,
  member: &MemberExpr,
  value: Value,
  strict: bool,
  this: Value,
  script: &Arc<Node<TopLevel>>,
) -> Result<(), VmError> {
  if member.optional_chaining {
    return Err(VmError::Unimplemented("optional chaining assignment target"));
  }

  // Root the RHS across evaluation of the LHS object.
  let mut rhs_scope = scope.reborrow();
  rhs_scope.push_root(value)?;
  let obj_value = eval_expr(
    vm,
    env,
    realm,
    ecma_functions,
    strict,
    this,
    script,
    &mut rhs_scope,
    &member.left,
  )?;

  let Value::Object(obj) = obj_value else {
    return Err(new_type_error(&mut rhs_scope, realm, "member assignment on non-object")?);
  };

  let key_s = rhs_scope.alloc_string(&member.right)?;
  let key = PropertyKey::from_string(key_s);
  let ok = rhs_scope.ordinary_set(vm, obj, key, value, Value::Object(obj))?;
  if ok {
    Ok(())
  } else if strict {
    let msg = format!("Cannot assign to read only property '{}'", member.right);
    Err(new_type_error(&mut rhs_scope, realm, &msg)?)
  } else {
    Ok(())
  }
}

fn assign_to_computed_member(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  realm: &Realm,
  ecma_functions: &mut Vec<InterpretedEcmaFunction>,
  member: &ComputedMemberExpr,
  value: Value,
  strict: bool,
  this: Value,
  script: &Arc<Node<TopLevel>>,
) -> Result<(), VmError> {
  if member.optional_chaining {
    return Err(VmError::Unimplemented("optional chaining assignment target"));
  }

  // Root the RHS across evaluation of the LHS object/key.
  let mut rhs_scope = scope.reborrow();
  rhs_scope.push_root(value)?;

  let obj_value = eval_expr(
    vm,
    env,
    realm,
    ecma_functions,
    strict,
    this,
    script,
    &mut rhs_scope,
    &member.object,
  )?;
  let Value::Object(obj) = obj_value else {
    return Err(new_type_error(
      &mut rhs_scope,
      realm,
      "computed member assignment on non-object",
    )?);
  };

  let key_value = eval_expr(
    vm,
    env,
    realm,
    ecma_functions,
    strict,
    this,
    script,
    &mut rhs_scope,
    &member.member,
  )?;
  let key_value = rhs_scope.push_root(key_value)?;
  let key = rhs_scope.heap_mut().to_property_key(key_value)?;

  let ok = rhs_scope.ordinary_set(vm, obj, key, value, Value::Object(obj))?;
  if ok {
    Ok(())
  } else if strict {
    Err(new_type_error(
      &mut rhs_scope,
      realm,
      "strict mode assignment failed",
    )?)
  } else {
    Ok(())
  }
}

fn root_property_key(scope: &mut Scope<'_>, key: PropertyKey) -> Result<(), VmError> {
  match key {
    PropertyKey::String(s) => {
      scope.push_root(Value::String(s))?;
    }
    PropertyKey::Symbol(s) => {
      scope.push_root(Value::Symbol(s))?;
    }
  }
  Ok(())
}
