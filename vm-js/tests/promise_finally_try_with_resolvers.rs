use std::cell::Cell;

use vm_js::{GcObject, Heap, HeapLimits, PromiseState, PropertyKey, Realm, Scope, Value, Vm, VmError, VmOptions};

thread_local! {
  static FINALLY_CALLS: Cell<u32> = Cell::new(0);
}

fn reset_thread_locals() {
  FINALLY_CALLS.with(|c| c.set(0));
}

fn get_own_data_property(heap: &mut Heap, obj: GcObject, name: &str) -> Result<Option<Value>, VmError> {
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

fn on_finally_increments(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  FINALLY_CALLS.with(|c| c.set(c.get() + 1));
  Ok(Value::Undefined)
}

fn try_returns_value(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  assert_eq!(args.get(0).copied().unwrap_or(Value::Undefined), Value::Number(1.0));
  assert_eq!(args.get(1).copied().unwrap_or(Value::Undefined), Value::Number(2.0));
  Ok(Value::Number(42.0))
}

fn try_throws(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::Throw(Value::Number(9.0)))
}

#[test]
fn promise_finally_on_fulfill_runs_callback_and_preserves_value() -> Result<(), VmError> {
  reset_thread_locals();

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_prototype = realm.intrinsics().promise_prototype();
  let promise_resolve = get_own_data_function(&mut heap, promise, "resolve")?;
  let promise_finally = get_own_data_function(&mut heap, promise_prototype, "finally")?;

  // Promise.resolve(1)
  let p = {
    let mut scope = heap.scope();
    let v = vm.call(
      &mut scope,
      Value::Object(promise_resolve),
      Value::Object(promise),
      &[Value::Number(1.0)],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected Promise object, got {v:?}");
    };
    obj
  };

  // p.finally(onFinally)
  let q = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(on_finally_increments)?;
    let name = scope.alloc_string("onFinally")?;
    let on_finally = scope.alloc_native_function(call_id, None, name, 0)?;

    let v = vm.call(
      &mut scope,
      Value::Object(promise_finally),
      Value::Object(p),
      &[Value::Object(on_finally)],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected Promise object, got {v:?}");
    };
    obj
  };

  assert_eq!(FINALLY_CALLS.with(|c| c.get()), 0);
  assert!(vm.microtask_queue().len() > 0, "expected finally() to enqueue a microtask");

  vm.perform_microtask_checkpoint(&mut heap)?;

  assert_eq!(FINALLY_CALLS.with(|c| c.get()), 1);
  assert_eq!(heap.promise_state(q)?, PromiseState::Fulfilled);
  assert_eq!(heap.promise_result(q)?, Some(Value::Number(1.0)));

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn promise_finally_on_reject_runs_callback_and_preserves_reason() -> Result<(), VmError> {
  reset_thread_locals();

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_prototype = realm.intrinsics().promise_prototype();
  let promise_reject = get_own_data_function(&mut heap, promise, "reject")?;
  let promise_finally = get_own_data_function(&mut heap, promise_prototype, "finally")?;

  // Promise.reject(1)
  let p = {
    let mut scope = heap.scope();
    let v = vm.call(
      &mut scope,
      Value::Object(promise_reject),
      Value::Object(promise),
      &[Value::Number(1.0)],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected Promise object, got {v:?}");
    };
    obj
  };

  // p.finally(onFinally)
  let q = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(on_finally_increments)?;
    let name = scope.alloc_string("onFinally")?;
    let on_finally = scope.alloc_native_function(call_id, None, name, 0)?;

    let v = vm.call(
      &mut scope,
      Value::Object(promise_finally),
      Value::Object(p),
      &[Value::Object(on_finally)],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected Promise object, got {v:?}");
    };
    obj
  };

  assert_eq!(FINALLY_CALLS.with(|c| c.get()), 0);
  assert!(vm.microtask_queue().len() > 0, "expected finally() to enqueue a microtask");

  vm.perform_microtask_checkpoint(&mut heap)?;

  assert_eq!(FINALLY_CALLS.with(|c| c.get()), 1);
  assert_eq!(heap.promise_state(q)?, PromiseState::Rejected);
  assert_eq!(heap.promise_result(q)?, Some(Value::Number(1.0)));

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn promise_try_resolves_or_rejects_based_on_callback_completion() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_try = get_own_data_function(&mut heap, promise, "try")?;

  // Promise.try(() => 42, 1, 2)
  let p_ok = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(try_returns_value)?;
    let name = scope.alloc_string("tryReturnsValue")?;
    let cb = scope.alloc_native_function(call_id, None, name, 0)?;

    let v = vm.call(
      &mut scope,
      Value::Object(promise_try),
      Value::Object(promise),
      &[Value::Object(cb), Value::Number(1.0), Value::Number(2.0)],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected Promise object, got {v:?}");
    };
    obj
  };
  assert_eq!(heap.promise_state(p_ok)?, PromiseState::Fulfilled);
  assert_eq!(heap.promise_result(p_ok)?, Some(Value::Number(42.0)));

  // Promise.try(() => { throw 9; })
  let p_err = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(try_throws)?;
    let name = scope.alloc_string("tryThrows")?;
    let cb = scope.alloc_native_function(call_id, None, name, 0)?;

    let v = vm.call(
      &mut scope,
      Value::Object(promise_try),
      Value::Object(promise),
      &[Value::Object(cb)],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected Promise object, got {v:?}");
    };
    obj
  };
  assert_eq!(heap.promise_state(p_err)?, PromiseState::Rejected);
  assert_eq!(heap.promise_result(p_err)?, Some(Value::Number(9.0)));

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn promise_with_resolvers_returns_object_with_callable_resolve_reject() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let with_resolvers = get_own_data_function(&mut heap, promise, "withResolvers")?;

  let record = {
    let mut scope = heap.scope();
    let v = vm.call(
      &mut scope,
      Value::Object(with_resolvers),
      Value::Object(promise),
      &[],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected object, got {v:?}");
    };
    obj
  };

  let record_promise = match get_own_data_property(&mut heap, record, "promise")? {
    Some(Value::Object(p)) => p,
    other => panic!("expected record.promise to be object, got {other:?}"),
  };
  let record_resolve = match get_own_data_property(&mut heap, record, "resolve")? {
    Some(Value::Object(f)) => f,
    other => panic!("expected record.resolve to be function object, got {other:?}"),
  };
  let record_reject = match get_own_data_property(&mut heap, record, "reject")? {
    Some(Value::Object(f)) => f,
    other => panic!("expected record.reject to be function object, got {other:?}"),
  };

  assert!(heap.is_promise_object(record_promise));
  assert!(heap.is_callable(Value::Object(record_resolve))?);
  assert!(heap.is_callable(Value::Object(record_reject))?);

  // resolve(1) fulfills promise.
  {
    let mut scope = heap.scope();
    let _ = vm.call(
      &mut scope,
      Value::Object(record_resolve),
      Value::Undefined,
      &[Value::Number(1.0)],
    )?;
  }
  assert_eq!(heap.promise_state(record_promise)?, PromiseState::Fulfilled);
  assert_eq!(heap.promise_result(record_promise)?, Some(Value::Number(1.0)));

  realm.teardown(&mut heap);
  Ok(())
}

