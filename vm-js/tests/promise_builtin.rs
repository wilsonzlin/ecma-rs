use std::cell::Cell;

use vm_js::{
  GcObject, Heap, HeapLimits, PromiseState, PropertyKey, Realm, RootId, Scope, Value, Vm, VmError,
  VmHost, VmHostHooks, VmOptions,
};

thread_local! {
  static EXECUTOR_CALLS: Cell<u32> = Cell::new(0);
  static THEN1_CALLS: Cell<u32> = Cell::new(0);
  static THEN2_ARG: Cell<Option<f64>> = Cell::new(None);
}

fn reset_thread_locals() {
  EXECUTOR_CALLS.with(|c| c.set(0));
  THEN1_CALLS.with(|c| c.set(0));
  THEN2_ARG.with(|c| c.set(None));
}

fn executor_calls_and_resolves(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  EXECUTOR_CALLS.with(|c| c.set(c.get() + 1));
  let resolve = args.get(0).copied().unwrap_or(Value::Undefined);
  vm.call_with_host(scope, hooks, resolve, Value::Undefined, &[Value::Number(1.0)])?;
  Ok(Value::Undefined)
}

fn then1_handler(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  THEN1_CALLS.with(|c| c.set(c.get() + 1));
  assert_eq!(args.get(0).copied().unwrap_or(Value::Undefined), Value::Number(1.0));
  Ok(Value::Number(2.0))
}

fn then2_handler(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let arg = args.get(0).copied().unwrap_or(Value::Undefined);
  let Value::Number(n) = arg else {
    panic!("expected number argument, got {arg:?}");
  };
  THEN2_ARG.with(|c| c.set(Some(n)));
  Ok(Value::Undefined)
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

#[test]
fn promise_is_installed_on_global_and_constructable() -> Result<(), VmError> {
  reset_thread_locals();

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_prototype = realm.intrinsics().promise_prototype();

  // Global binding.
  let global_promise = get_own_data_property(&mut heap, realm.global_object(), "Promise")?
    .expect("global Promise binding");
  assert_eq!(global_promise, Value::Object(promise));

  // Prototype wiring.
  assert_eq!(
    heap.object_prototype(promise)?,
    Some(realm.intrinsics().function_prototype())
  );
  assert_eq!(
    heap.object_prototype(promise_prototype)?,
    Some(realm.intrinsics().object_prototype())
  );

  // new Promise(executor) calls executor and returns a Promise instance.
    let promise_instance = {
      let mut scope = heap.scope();
      let call_id = vm.register_native_call(executor_calls_and_resolves)?;
      let executor_name = scope.alloc_string("executor")?;
      let executor = scope.alloc_native_function(call_id, None, executor_name, 1)?;

    let value = vm.construct(
      &mut scope,
      Value::Object(promise),
      &[Value::Object(executor)],
      Value::Object(promise),
    )?;
    let Value::Object(obj) = value else {
      panic!("expected object, got {value:?}");
    };
    obj
  };

  assert_eq!(EXECUTOR_CALLS.with(|c| c.get()), 1);
  assert_eq!(heap.object_prototype(promise_instance)?, Some(promise_prototype));

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn promise_resolve_and_then_schedule_microtasks() -> Result<(), VmError> {
  reset_thread_locals();

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();
  let promise_prototype = realm.intrinsics().promise_prototype();
  let promise_resolve = get_own_data_function(&mut heap, promise, "resolve")?;
  let promise_then = get_own_data_function(&mut heap, promise_prototype, "then")?;

  // Promise.resolve(1) returns a fulfilled promise.
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

  // Promise.resolve(p) returns `p` if it's already a promise of the same constructor.
  {
    let mut scope = heap.scope();
    let v = vm.call(
      &mut scope,
      Value::Object(promise_resolve),
      Value::Object(promise),
      &[Value::Object(p)],
    )?;
    assert_eq!(v, Value::Object(p));
  }

  // p.then(then1) schedules a reaction microtask and returns a derived promise.
  let derived = {
    let mut scope = heap.scope();
    let then1_call_id = vm.register_native_call(then1_handler)?;
    let then1_name = scope.alloc_string("then1")?;
    let then1 = scope.alloc_native_function(then1_call_id, None, then1_name, 1)?;

    let v = vm.call(
      &mut scope,
      Value::Object(promise_then),
      Value::Object(p),
      &[Value::Object(then1)],
    )?;
    let Value::Object(obj) = v else {
      panic!("expected Promise object, got {v:?}");
    };
    obj
  };

  assert!(
    vm.microtask_queue().len() > 0,
    "expected then() to enqueue a microtask"
  );

  // Attach another handler to the derived promise before running microtasks so we also test
  // reaction scheduling for pending promises.
  {
    let mut scope = heap.scope();
    let then2_call_id = vm.register_native_call(then2_handler)?;
    let then2_name = scope.alloc_string("then2")?;
    let then2 = scope.alloc_native_function(then2_call_id, None, then2_name, 1)?;

    let _ = vm.call(
      &mut scope,
      Value::Object(promise_then),
      Value::Object(derived),
      &[Value::Object(then2)],
    )?;
  }

  // Drain the microtask queue: should run then1, resolve `derived` with 2, then run then2.
  vm.perform_microtask_checkpoint(&mut heap)?;

  assert_eq!(vm.microtask_queue().len(), 0);
  assert_eq!(THEN1_CALLS.with(|c| c.get()), 1);
  assert_eq!(THEN2_ARG.with(|c| c.get()), Some(2.0));

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn promise_constructor_throws_type_error_when_executor_not_callable() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise = realm.intrinsics().promise();

  {
    let mut scope = heap.scope();
    let err = vm.construct(
      &mut scope,
      Value::Object(promise),
      &[Value::Number(1.0)],
      Value::Object(promise),
    );
 
    let thrown = match err {
      Ok(v) => panic!("expected Promise constructor to throw, got {v:?}"),
      Err(VmError::Throw(v)) => v,
      Err(e) => return Err(e),
    };
 
    let Value::Object(obj) = thrown else {
      panic!("expected thrown object, got {thrown:?}");
    };
 
    assert_eq!(
      scope.heap().object_prototype(obj)?,
      Some(realm.intrinsics().type_error_prototype())
    );
  }

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn promise_self_resolution_rejects_with_type_error_object() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_with_resolvers = get_own_data_function(&mut heap, promise_ctor, "withResolvers")?;

  let (promise_obj, promise_root): (GcObject, RootId) = {
    let mut scope = heap.scope();

    // Promise.withResolvers()
    let res = vm.call(
      &mut scope,
      Value::Object(promise_with_resolvers),
      Value::Object(promise_ctor),
      &[],
    )?;
    let Value::Object(res_obj) = res else {
      panic!("expected withResolvers result object, got {res:?}");
    };

    // Root the result record while extracting its fields.
    scope.push_root(res)?;

    let promise_key = PropertyKey::from_string(scope.alloc_string("promise")?);
    let resolve_key = PropertyKey::from_string(scope.alloc_string("resolve")?);

    let promise_val = scope
      .heap()
      .object_get_own_data_property_value(res_obj, &promise_key)?
      .expect("withResolvers result missing promise property");
    let resolve_val = scope
      .heap()
      .object_get_own_data_property_value(res_obj, &resolve_key)?
      .expect("withResolvers result missing resolve property");

    let Value::Object(promise_obj) = promise_val else {
      panic!("expected promise object, got {promise_val:?}");
    };

    // Resolve the promise with itself.
    vm.call(
      &mut scope,
      resolve_val,
      Value::Undefined,
      &[Value::Object(promise_obj)],
    )?;

    // Keep the promise alive across the microtask checkpoint.
    let root = scope.heap_mut().add_root(Value::Object(promise_obj))?;

    (promise_obj, root)
  };

  // Drain jobs (should be a no-op for self-resolution, but exercise the microtask checkpoint).
  vm.perform_microtask_checkpoint(&mut heap)?;

  assert_eq!(heap.promise_state(promise_obj)?, PromiseState::Rejected);
  let reason = heap
    .promise_result(promise_obj)?
    .expect("rejected promise missing result");
  let Value::Object(reason_obj) = reason else {
    panic!("expected rejection reason object, got {reason:?}");
  };
  assert_eq!(
    heap.object_prototype(reason_obj)?,
    Some(realm.intrinsics().type_error_prototype())
  );

  heap.remove_root(promise_root);

  realm.teardown(&mut heap);
  Ok(())
}
