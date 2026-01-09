use std::cell::Cell;

use vm_js::{
  GcObject, Heap, HeapLimits, PropertyKey, Realm, Scope, Value, Vm, VmError, VmHost, VmHostHooks,
  VmOptions,
};

thread_local! {
  static LAST_PROMISE: Cell<Option<GcObject>> = const { Cell::new(None) };
  static LAST_RESOLVE: Cell<Option<GcObject>> = const { Cell::new(None) };
  static LAST_REJECT: Cell<Option<GcObject>> = const { Cell::new(None) };
  static RESOLVE_CALLS: Cell<u32> = const { Cell::new(0) };
  static REJECT_CALLS: Cell<u32> = const { Cell::new(0) };
}

fn reset_thread_locals() {
  LAST_PROMISE.with(|c| c.set(None));
  LAST_RESOLVE.with(|c| c.set(None));
  LAST_REJECT.with(|c| c.set(None));
  RESOLVE_CALLS.with(|c| c.set(0));
  REJECT_CALLS.with(|c| c.set(0));
}

fn get_own_data_property(
  heap: &mut Heap,
  obj: GcObject,
  name: &str,
) -> Result<Option<Value>, VmError> {
  let mut scope = heap.scope();
  let key = PropertyKey::from_string(scope.alloc_string(name)?);
  scope.heap().object_get_own_data_property_value(obj, &key)
}

fn get_own_data_function(heap: &mut Heap, obj: GcObject, name: &str) -> Result<GcObject, VmError> {
  let Some(Value::Object(func)) = get_own_data_property(heap, obj, name)? else {
    return Err(VmError::Unimplemented("missing intrinsic function"));
  };
  Ok(func)
}

fn noop_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

fn record_resolver_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let resolve = LAST_RESOLVE.with(|c| c.get());
  let reject = LAST_REJECT.with(|c| c.get());

  if Some(callee) == resolve {
    RESOLVE_CALLS.with(|c| c.set(c.get() + 1));
  } else if Some(callee) == reject {
    REJECT_CALLS.with(|c| c.set(c.get() + 1));
  } else {
    return Err(VmError::Unimplemented("unexpected resolver callee"));
  }

  Ok(Value::Undefined)
}

fn promise_like_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "promise_like_construct requires intrinsics (create a Realm first)",
  ))?;

  let executor = args.get(0).copied().unwrap_or(Value::Undefined);

  let call_id = vm.register_native_call(record_resolver_call)?;

  let resolve_name = scope.alloc_string("resolve")?;
  let resolve = scope.alloc_native_function(call_id, None, resolve_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(resolve, Some(intr.function_prototype()))?;
  scope.push_root(Value::Object(resolve))?;

  let reject_name = scope.alloc_string("reject")?;
  let reject = scope.alloc_native_function(call_id, None, reject_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(reject, Some(intr.function_prototype()))?;
  scope.push_root(Value::Object(reject))?;

  let promise = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(promise, Some(intr.object_prototype()))?;
  scope.push_root(Value::Object(promise))?;

  LAST_PROMISE.with(|c| c.set(Some(promise)));
  LAST_RESOLVE.with(|c| c.set(Some(resolve)));
  LAST_REJECT.with(|c| c.set(Some(reject)));

  let _ = vm.call_with_host(
    scope,
    hooks,
    executor,
    Value::Undefined,
    &[Value::Object(resolve), Value::Object(reject)],
  )?;

  Ok(Value::Object(promise))
}

fn executor_double_call_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "executor_double_call_construct requires intrinsics (create a Realm first)",
  ))?;

  let executor = args.get(0).copied().unwrap_or(Value::Undefined);

  let call_id = vm.register_native_call(record_resolver_call)?;
  let resolve_name = scope.alloc_string("resolve")?;
  let resolve = scope.alloc_native_function(call_id, None, resolve_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(resolve, Some(intr.function_prototype()))?;
  scope.push_root(Value::Object(resolve))?;

  let reject_name = scope.alloc_string("reject")?;
  let reject = scope.alloc_native_function(call_id, None, reject_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(reject, Some(intr.function_prototype()))?;
  scope.push_root(Value::Object(reject))?;

  let _ = vm.call_with_host(
    scope,
    hooks,
    executor,
    Value::Undefined,
    &[Value::Object(resolve), Value::Object(reject)],
  )?;
  // Second call: must throw TypeError.
  vm.call_with_host(
    scope,
    hooks,
    executor,
    Value::Undefined,
    &[Value::Object(resolve), Value::Object(reject)],
  )?;

  Ok(Value::Undefined)
}

fn non_callable_resolvers_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "non_callable_resolvers_construct requires intrinsics (create a Realm first)",
  ))?;

  let executor = args.get(0).copied().unwrap_or(Value::Undefined);

  let promise = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(promise, Some(intr.object_prototype()))?;

  // Store non-callable values into the resolvingFunctions record.
  let _ = vm.call_with_host(
    scope,
    hooks,
    executor,
    Value::Undefined,
    &[Value::Number(1.0), Value::Bool(false)],
  )?;

  Ok(Value::Object(promise))
}

#[test]
fn promise_resolve_and_reject_use_new_promise_capability_for_custom_constructors() -> Result<(), VmError>
{
  reset_thread_locals();

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_resolve = get_own_data_function(&mut heap, promise, "resolve")?;
  let promise_reject = get_own_data_function(&mut heap, promise, "reject")?;

  let call_id = vm.register_native_call(noop_call)?;
  let construct_id = vm.register_native_construct(promise_like_construct)?;
  let c = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("C")?;
    scope.alloc_native_function(call_id, Some(construct_id), name, 1)?
  };

  // Promise.resolve.call(C, 1)
  {
    let mut scope = heap.scope();
    let v = vm.call_without_host(
      &mut scope,
      Value::Object(promise_resolve),
      Value::Object(c),
      &[Value::Number(1.0)],
    )?;
    let promise_obj = LAST_PROMISE.with(|c| c.get()).expect("constructor should set LAST_PROMISE");
    assert_eq!(v, Value::Object(promise_obj));
    assert_eq!(RESOLVE_CALLS.with(|c| c.get()), 1);
    assert_eq!(REJECT_CALLS.with(|c| c.get()), 0);
  }

  reset_thread_locals();

  // Promise.reject.call(C, 2)
  {
    let mut scope = heap.scope();
    let v = vm.call_without_host(
      &mut scope,
      Value::Object(promise_reject),
      Value::Object(c),
      &[Value::Number(2.0)],
    )?;
    let promise_obj = LAST_PROMISE.with(|c| c.get()).expect("constructor should set LAST_PROMISE");
    assert_eq!(v, Value::Object(promise_obj));
    assert_eq!(RESOLVE_CALLS.with(|c| c.get()), 0);
    assert_eq!(REJECT_CALLS.with(|c| c.get()), 1);
  }

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn new_promise_capability_executor_double_call_throws_type_error() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_resolve = get_own_data_function(&mut heap, promise, "resolve")?;

  let call_id = vm.register_native_call(noop_call)?;
  let construct_id = vm.register_native_construct(executor_double_call_construct)?;
  let c = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("C")?;
    scope.alloc_native_function(call_id, Some(construct_id), name, 1)?
  };

  let err = {
    let mut scope = heap.scope();
    vm.call_without_host(
      &mut scope,
      Value::Object(promise_resolve),
      Value::Object(c),
      &[Value::Number(1.0)],
    )
    .unwrap_err()
  };

  let thrown = match err {
    VmError::Throw(v) | VmError::ThrowWithStack { value: v, .. } => v,
    other => panic!("expected throw, got {other:?}"),
  };

  let Value::Object(obj) = thrown else {
    panic!("expected thrown object, got {thrown:?}");
  };
  assert_eq!(
    heap.object_prototype(obj)?,
    Some(realm.intrinsics().type_error_prototype())
  );

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn new_promise_capability_non_callable_resolve_reject_throws_type_error() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_resolve = get_own_data_function(&mut heap, promise, "resolve")?;

  let call_id = vm.register_native_call(noop_call)?;
  let construct_id = vm.register_native_construct(non_callable_resolvers_construct)?;
  let c = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("C")?;
    scope.alloc_native_function(call_id, Some(construct_id), name, 1)?
  };

  let err = {
    let mut scope = heap.scope();
    vm.call_without_host(
      &mut scope,
      Value::Object(promise_resolve),
      Value::Object(c),
      &[Value::Number(1.0)],
    )
    .unwrap_err()
  };

  let thrown = match err {
    VmError::Throw(v) | VmError::ThrowWithStack { value: v, .. } => v,
    other => panic!("expected throw, got {other:?}"),
  };

  let Value::Object(obj) = thrown else {
    panic!("expected thrown object, got {thrown:?}");
  };
  assert_eq!(
    heap.object_prototype(obj)?,
    Some(realm.intrinsics().type_error_prototype())
  );

  realm.teardown(&mut heap);
  Ok(())
}

