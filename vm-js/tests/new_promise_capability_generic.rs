use std::cell::Cell;

use vm_js::{
  new_promise_capability_with_constructor, GcObject, Heap, HeapLimits, Realm, Scope, Value, Vm,
  VmError, VmHost, VmHostHooks, VmOptions,
};

thread_local! {
  static LAST_PROMISE: Cell<Option<GcObject>> = const { Cell::new(None) };
  static LAST_RESOLVE: Cell<Option<GcObject>> = const { Cell::new(None) };
  static LAST_REJECT: Cell<Option<GcObject>> = const { Cell::new(None) };
}

fn reset_thread_locals() {
  LAST_PROMISE.with(|c| c.set(None));
  LAST_RESOLVE.with(|c| c.set(None));
  LAST_REJECT.with(|c| c.set(None));
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

  // Create fresh resolve/reject functions and pass them to the executor.
  let call_id = vm.register_native_call(noop_call)?;

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

  let _ = vm.call_with_host(
    scope,
    hooks,
    executor,
    Value::Undefined,
    &[Value::Object(resolve), Value::Object(reject)],
  )?;

  LAST_PROMISE.with(|c| c.set(Some(promise)));
  LAST_RESOLVE.with(|c| c.set(Some(resolve)));
  LAST_REJECT.with(|c| c.set(Some(reject)));

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

  let call_id = vm.register_native_call(noop_call)?;
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

  // First call: stores resolve/reject.
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

  // Unreachable: executor should have thrown on the second call.
  let promise = scope.alloc_object()?;
  Ok(Value::Object(promise))
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
fn new_promise_capability_calls_constructor_and_captures_resolve_reject() -> Result<(), VmError> {
  reset_thread_locals();

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;
  let mut hooks = vm_js::MicrotaskQueue::new();

  let call_id = vm.register_native_call(noop_call)?;
  let construct_id = vm.register_native_construct(promise_like_construct)?;

  let c = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("C")?;
    scope.alloc_native_function(call_id, Some(construct_id), name, 1)?
  };

  let cap = {
    let mut scope = heap.scope();
    new_promise_capability_with_constructor(&mut vm, &mut scope, &mut hooks, Value::Object(c))?
  };

  let promise = LAST_PROMISE.with(|c| c.get()).expect("constructor should have set LAST_PROMISE");
  let resolve = LAST_RESOLVE.with(|c| c.get()).expect("constructor should have set LAST_RESOLVE");
  let reject = LAST_REJECT.with(|c| c.get()).expect("constructor should have set LAST_REJECT");

  assert_eq!(cap.promise, Value::Object(promise));
  assert_eq!(cap.resolve, Value::Object(resolve));
  assert_eq!(cap.reject, Value::Object(reject));

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn new_promise_capability_executor_double_call_throws_type_error() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;
  let mut hooks = vm_js::MicrotaskQueue::new();

  let call_id = vm.register_native_call(noop_call)?;
  let construct_id = vm.register_native_construct(executor_double_call_construct)?;

  let c = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("C")?;
    scope.alloc_native_function(call_id, Some(construct_id), name, 1)?
  };

  let err = {
    let mut scope = heap.scope();
    new_promise_capability_with_constructor(&mut vm, &mut scope, &mut hooks, Value::Object(c))
      .unwrap_err()
  };

  let thrown = match err {
    VmError::Throw(v) => v,
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
  let mut hooks = vm_js::MicrotaskQueue::new();

  let call_id = vm.register_native_call(noop_call)?;
  let construct_id = vm.register_native_construct(non_callable_resolvers_construct)?;

  let c = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("C")?;
    scope.alloc_native_function(call_id, Some(construct_id), name, 1)?
  };

  let err = {
    let mut scope = heap.scope();
    new_promise_capability_with_constructor(&mut vm, &mut scope, &mut hooks, Value::Object(c))
      .unwrap_err()
  };

  let thrown = match err {
    VmError::Throw(v) => v,
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

