use crate::exec::{eval_class_expr_named, eval_expr, RuntimeEnv};
use crate::function_properties::set_function_name;
use crate::iterator::{
  get_iterator, iterator_close_with_completion, iterator_step_value, IteratorRecord,
};
use crate::property::PropertyKey;
use crate::{Scope, Value, Vm, VmError, VmHost, VmHostHooks};
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::{ArrPat, ObjPat, Pat};
use parse_js::ast::expr::{ComputedMemberExpr, Expr, MemberExpr};
use parse_js::ast::node::{literal_string_code_units, Node};
use parse_js::token::TT;

fn throw_type_error(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> Result<VmError, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let value =
    crate::error_object::new_error(scope, intr.type_error_prototype(), "TypeError", message)?;
  Ok(VmError::Throw(value))
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum BindingKind {
  Var,
  Let,
  Const,
  Assignment,
}

pub(crate) fn bind_pattern(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  pat: &Pat,
  value: Value,
  kind: BindingKind,
  strict: bool,
  this: Value,
) -> Result<(), VmError> {
  // Keep temporary roots local to this binding operation.
  let mut scope = scope.reborrow();
  // Root the input value so destructuring can allocate without the RHS being collected.
  let value = scope.push_root(value)?;

  match pat {
    Pat::Id(id) => bind_identifier(
      vm,
      host,
      hooks,
      env,
      &mut scope,
      &id.stx.name,
      value,
      kind,
      strict,
    ),
    Pat::Obj(obj) => bind_object_pattern(
      vm, host, hooks, &mut scope, env, &obj.stx, value, kind, strict, this,
    ),
    Pat::Arr(arr) => bind_array_pattern(
      vm, host, hooks, &mut scope, env, &arr.stx, value, kind, strict, this,
    ),
    Pat::AssignTarget(expr) => {
      if !matches!(kind, BindingKind::Assignment) {
        return Err(VmError::Unimplemented(
          "assignment target pattern in binding context",
        ));
      }
      bind_assignment_target(vm, host, hooks, &mut scope, env, expr, value, strict, this)
    }
  }
}

pub(crate) fn bind_assignment_target(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  target: &Node<Expr>,
  value: Value,
  strict: bool,
  this: Value,
) -> Result<(), VmError> {
  // Keep temporary roots local to this binding operation.
  let mut scope = scope.reborrow();
  let value = scope.push_root(value)?;

  match &*target.stx {
    Expr::Id(id) => bind_identifier(
      vm,
      host,
      hooks,
      env,
      &mut scope,
      &id.stx.name,
      value,
      BindingKind::Assignment,
      strict,
    ),
    Expr::IdPat(id) => bind_identifier(
      vm,
      host,
      hooks,
      env,
      &mut scope,
      &id.stx.name,
      value,
      BindingKind::Assignment,
      strict,
    ),
    Expr::ObjPat(obj) => bind_object_pattern(
      vm,
      host,
      hooks,
      &mut scope,
      env,
      &obj.stx,
      value,
      BindingKind::Assignment,
      strict,
      this,
    ),
    Expr::ArrPat(arr) => bind_array_pattern(
      vm,
      host,
      hooks,
      &mut scope,
      env,
      &arr.stx,
      value,
      BindingKind::Assignment,
      strict,
      this,
    ),
    Expr::Member(member) => assign_to_member(
      vm,
      host,
      hooks,
      &mut scope,
      env,
      &member.stx,
      value,
      strict,
      this,
    ),
    Expr::ComputedMember(member) => assign_to_computed_member(
      vm,
      host,
      hooks,
      &mut scope,
      env,
      &member.stx,
      value,
      strict,
      this,
    ),
    _ => Err(VmError::Unimplemented("assignment target")),
  }
}

fn bind_identifier(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  env: &mut RuntimeEnv,
  scope: &mut Scope<'_>,
  name: &str,
  value: Value,
  kind: BindingKind,
  strict: bool,
) -> Result<(), VmError> {
  match kind {
    BindingKind::Var => env.set_var(vm, scope, name, value, strict),
    BindingKind::Let => {
      let env_rec = env.lexical_env();
      if !scope.heap().env_has_binding(env_rec, name)? {
        // Non-block statement contexts may not have performed lexical hoisting yet.
        scope.env_create_mutable_binding(env_rec, name)?;
      }
      scope
        .heap_mut()
        .env_initialize_binding(env_rec, name, value)
    }
    BindingKind::Const => {
      let env_rec = env.lexical_env();
      if !scope.heap().env_has_binding(env_rec, name)? {
        // Non-block statement contexts may not have performed lexical hoisting yet.
        scope.env_create_immutable_binding(env_rec, name, true)?;
      }
      scope
        .heap_mut()
        .env_initialize_binding(env_rec, name, value)
    }
    BindingKind::Assignment => env.set(vm, host, hooks, scope, name, value, strict),
  }
}

fn bind_object_pattern(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  pat: &ObjPat,
  value: Value,
  kind: BindingKind,
  strict: bool,
  this: Value,
) -> Result<(), VmError> {
  let Value::Object(obj) = value else {
    return Err(throw_type_error(
      vm,
      scope,
      "object destructuring requires object",
    )?);
  };
  scope.push_root(Value::Object(obj))?;

  let mut excluded: Vec<PropertyKey> = Vec::new();
  excluded
    .try_reserve_exact(pat.properties.len())
    .map_err(|_| VmError::OutOfMemory)?;

  for prop in &pat.properties {
    let key = resolve_obj_pat_key(vm, host, hooks, scope, env, &prop.stx.key, strict, this)?;
    root_property_key(scope, key)?;
    excluded.push(key);

    let mut prop_value =
      scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, key, Value::Object(obj))?;
    if matches!(prop_value, Value::Undefined) {
      if let Some(default_expr) = &prop.stx.default_value {
        prop_value = eval_binding_default_initializer(
          vm,
          host,
          hooks,
          env,
          strict,
          this,
          scope,
          &prop.stx.target.stx,
          default_expr,
        )?;
      }
    }

    bind_pattern(
      vm,
      host,
      hooks,
      scope,
      env,
      &prop.stx.target.stx,
      prop_value,
      kind,
      strict,
      this,
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
    let v =
      scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, key, Value::Object(obj))?;
    let _ = scope.create_data_property(rest_obj, key, v)?;
  }

  bind_pattern(
    vm,
    host,
    hooks,
    scope,
    env,
    &rest_pat.stx,
    Value::Object(rest_obj),
    kind,
    strict,
    this,
  )
}

/// BindingInitialization for ArrayBindingPattern (§13.3.3.5): GetIterator + IteratorBindingInitialization
/// + IteratorClose when the iterator is not exhausted.
fn bind_array_pattern(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  pat: &ArrPat,
  value: Value,
  kind: BindingKind,
  strict: bool,
  this: Value,
) -> Result<(), VmError> {
  // GetIterator performs ToObject; null/undefined throw TypeError.
  if matches!(value, Value::Undefined | Value::Null) {
    return Err(throw_type_error(
      vm,
      scope,
      "array destructuring requires object",
    )?);
  }

  let mut iterator = get_iterator(vm, host, hooks, scope, value)?;
  scope.push_roots(&[iterator.iterator, iterator.next_method])?;

  let status = iterator_binding_initialization(
    vm,
    host,
    hooks,
    scope,
    env,
    pat,
    &mut iterator,
    kind,
    strict,
    this,
  );

  if iterator.done {
    return status;
  }
  iterator_close_with_completion(vm, host, hooks, scope, &iterator, status)
}

/// IteratorBindingInitialization for ArrayBindingPattern (§13.3.3.6).
fn iterator_binding_initialization(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  pat: &ArrPat,
  iterator: &mut IteratorRecord,
  kind: BindingKind,
  strict: bool,
  this: Value,
) -> Result<(), VmError> {
  for elem in &pat.elements {
    let Some(elem) = elem else {
      // Elision: IteratorStep (discard value).
      let _ = iterator_step_value(vm, host, hooks, scope, iterator)?;
      continue;
    };

    let mut item = match iterator_step_value(vm, host, hooks, scope, iterator)? {
      Some(v) => v,
      None => Value::Undefined,
    };

    if matches!(item, Value::Undefined) {
      if let Some(default_expr) = &elem.default_value {
        item = eval_binding_default_initializer(
          vm,
          host,
          hooks,
          env,
          strict,
          this,
          scope,
          &elem.target.stx,
          default_expr,
        )?;
      }
    }

    bind_pattern(
      vm,
      host,
      hooks,
      scope,
      env,
      &elem.target.stx,
      item,
      kind,
      strict,
      this,
    )?;
  }

  let Some(rest_pat) = &pat.rest else {
    return Ok(());
  };

  // BindingRestElement: ArrayCreate(0) then collect remaining IteratorStepValues.
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let rest_arr = scope.alloc_array(0)?;
  scope.push_root(Value::Object(rest_arr))?;
  scope
    .heap_mut()
    .object_set_prototype(rest_arr, Some(intr.array_prototype()))?;

  let mut rest_idx: u32 = 0;
  loop {
    let Some(v) = iterator_step_value(vm, host, hooks, scope, iterator)? else {
      break;
    };
    {
      let mut elem_scope = scope.reborrow();
      let v = elem_scope.push_root(v)?;
      let key_str = rest_idx.to_string();
      let key_s = elem_scope.alloc_string(&key_str)?;
      let key = PropertyKey::from_string(key_s);
      let _ = elem_scope.create_data_property(rest_arr, key, v)?;
    }
    rest_idx = rest_idx.saturating_add(1);
  }

  bind_pattern(
    vm,
    host,
    hooks,
    scope,
    env,
    &rest_pat.stx,
    Value::Object(rest_arr),
    kind,
    strict,
    this,
  )
}

/// `IsAnonymousFunctionDefinition` (ECMA-262), looking through cover/parentheses.
fn is_anonymous_function_definition(expr: &Node<Expr>) -> bool {
  // ParenthesizedExpr is recorded on the assoc of the covered expression node itself.
  match &*expr.stx {
    Expr::Func(f) => f.stx.name.is_none(),
    Expr::ArrowFunc(_) => true,
    Expr::Class(c) => c.stx.name.is_none(),
    _ => false,
  }
}

/// Evaluate a SingleNameBinding default with NamedEvaluation when applicable.
fn eval_binding_default_initializer(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  env: &mut RuntimeEnv,
  strict: bool,
  this: Value,
  scope: &mut Scope<'_>,
  target: &Pat,
  default_expr: &Node<Expr>,
) -> Result<Value, VmError> {
  if let Pat::Id(id) = target {
    if is_anonymous_function_definition(default_expr) {
      // Class NamedEvaluation must pass the name into ClassDefinitionEvaluation so
      // `static name()` (installed after SetFunctionName) can overwrite.
      if let Expr::Class(class) = &*default_expr.stx {
        return eval_class_expr_named(
          vm,
          host,
          hooks,
          env,
          strict,
          this,
          scope,
          class,
          &id.stx.name,
        );
      }
      let value = eval_expr(vm, host, hooks, env, strict, this, scope, default_expr)?;
      return maybe_set_function_name_from_binding(scope, target, default_expr, value);
    }
  }
  eval_expr(vm, host, hooks, env, strict, this, scope, default_expr)
}

/// NamedEvaluation / SetFunctionName for SingleNameBinding defaults (non-class).
fn maybe_set_function_name_from_binding(
  scope: &mut Scope<'_>,
  target: &Pat,
  default_expr: &Node<Expr>,
  value: Value,
) -> Result<Value, VmError> {
  let Pat::Id(id) = target else {
    return Ok(value);
  };
  if !is_anonymous_function_definition(default_expr) {
    return Ok(value);
  }
  // Cover grammar: `(function () {})` is still `Expr::Func` with `name: None` (anonymous).
  // `(0, function () {})` is a comma expression and fails `is_anonymous_function_definition`.
  let Value::Object(func) = value else {
    return Ok(value);
  };
  if !scope.heap().is_callable(value)? {
    return Ok(value);
  }

  let mut s = scope.reborrow();
  s.push_root(value)?;
  let name_s = s.alloc_string(&id.stx.name)?;
  set_function_name(&mut s, func, PropertyKey::from_string(name_s), None)?;
  Ok(value)
}

fn resolve_obj_pat_key(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  key: &ClassOrObjKey,
  strict: bool,
  this: Value,
) -> Result<PropertyKey, VmError> {
  match key {
    ClassOrObjKey::Direct(direct) => {
      let s = if let Some(units) = literal_string_code_units(&direct.assoc) {
        scope.alloc_string_from_code_units(units)?
      } else if direct.stx.tt == TT::LiteralNumber {
        let n = direct
          .stx
          .key
          .parse::<f64>()
          .map_err(|_| VmError::Unimplemented("numeric literal property name parse"))?;
        scope.heap_mut().to_string(Value::Number(n))?
      } else {
        scope.alloc_string(&direct.stx.key)?
      };
      Ok(PropertyKey::from_string(s))
    }
    ClassOrObjKey::Computed(expr) => {
      let value = eval_expr(vm, host, hooks, env, strict, this, scope, expr)?;
      // Root the computed value until `to_property_key` completes.
      let value = scope.push_root(value)?;
      let key = crate::spec_ops::to_property_key(vm, scope, value)?;
      Ok(key)
    }
  }
}

fn assign_to_member(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  member: &MemberExpr,
  value: Value,
  strict: bool,
  this: Value,
) -> Result<(), VmError> {
  if member.optional_chaining {
    return Err(VmError::Unimplemented(
      "optional chaining assignment target",
    ));
  }

  // Root the RHS across evaluation of the LHS object.
  let mut rhs_scope = scope.reborrow();
  rhs_scope.push_root(value)?;
  let obj_value = eval_expr(
    vm,
    host,
    hooks,
    env,
    strict,
    this,
    &mut rhs_scope,
    &member.left,
  )?;

  let Value::Object(obj) = obj_value else {
    return Err(throw_type_error(
      vm,
      &mut rhs_scope,
      "member assignment on non-object",
    )?);
  };

  let key_s = rhs_scope.alloc_string(&member.right)?;
  let key = PropertyKey::from_string(key_s);
  let ok = rhs_scope.ordinary_set_with_host_and_hooks(
    vm,
    host,
    hooks,
    obj,
    key,
    value,
    Value::Object(obj),
  )?;
  if ok {
    Ok(())
  } else if strict {
    let msg = format!("Cannot assign to read only property '{}'", member.right);
    Err(throw_type_error(vm, &mut rhs_scope, &msg)?)
  } else {
    Ok(())
  }
}

fn assign_to_computed_member(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  member: &ComputedMemberExpr,
  value: Value,
  strict: bool,
  this: Value,
) -> Result<(), VmError> {
  if member.optional_chaining {
    return Err(VmError::Unimplemented(
      "optional chaining assignment target",
    ));
  }

  // Root the RHS across evaluation of the LHS object/key.
  let mut rhs_scope = scope.reborrow();
  rhs_scope.push_root(value)?;

  let obj_value = eval_expr(
    vm,
    host,
    hooks,
    env,
    strict,
    this,
    &mut rhs_scope,
    &member.object,
  )?;
  let Value::Object(obj) = obj_value else {
    return Err(throw_type_error(
      vm,
      &mut rhs_scope,
      "computed member assignment on non-object",
    )?);
  };

  let key_value = eval_expr(
    vm,
    host,
    hooks,
    env,
    strict,
    this,
    &mut rhs_scope,
    &member.member,
  )?;
  let key_value = rhs_scope.push_root(key_value)?;
  let key = crate::spec_ops::to_property_key(vm, &mut rhs_scope, key_value)?;

  let ok = rhs_scope.ordinary_set_with_host_and_hooks(
    vm,
    host,
    hooks,
    obj,
    key,
    value,
    Value::Object(obj),
  )?;
  if ok {
    Ok(())
  } else if strict {
    Err(throw_type_error(
      vm,
      &mut rhs_scope,
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
