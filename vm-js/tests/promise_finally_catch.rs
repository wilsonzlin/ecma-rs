use std::cell::Cell;
use std::collections::VecDeque;

use vm_js::{
  GcObject, Heap, HeapLimits, Job, PromiseHandle, PromiseRejectionOperation, PromiseState, PropertyKey,
  PropertyDescriptor, PropertyKind, Realm, RealmId, RootId, Scope, Value, Vm, VmError, VmHost,
  VmHostHooks, VmJobContext, VmOptions,
};

thread_local! {
  static CATCH_CALLS: Cell<u32> = Cell::new(0);
  static BORROWED_THEN_CALLS: Cell<u32> = Cell::new(0);
  static FINALLY_CALLS: Cell<u32> = Cell::new(0);
  static THEN_ARG: Cell<Option<f64>> = Cell::new(None);
  static FINALLY_RETURN_PROMISE: Cell<Option<GcObject>> = Cell::new(None);
}

fn reset_thread_locals() {
  CATCH_CALLS.with(|c| c.set(0));
  BORROWED_THEN_CALLS.with(|c| c.set(0));
  FINALLY_CALLS.with(|c| c.set(0));
  THEN_ARG.with(|c| c.set(None));
  FINALLY_RETURN_PROMISE.with(|c| c.set(None));
}

#[derive(Default)]
struct TestHost {
  queue: VecDeque<Job>,
  rejection_tracker: Vec<(PromiseHandle, PromiseRejectionOperation)>,
}

impl VmHostHooks for TestHost {
  fn host_enqueue_promise_job(&mut self, job: Job, _realm: Option<RealmId>) {
    self.queue.push_back(job);
  }

  fn host_promise_rejection_tracker(&mut self, promise: PromiseHandle, operation: PromiseRejectionOperation) {
    self.rejection_tracker.push((promise, operation));
  }
}

struct TestContext {
  vm: Vm,
  heap: Heap,
}

impl TestContext {
  fn new() -> Self {
    Self {
      vm: Vm::new(VmOptions::default()),
      heap: Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024)),
    }
  }

  fn run_jobs(&mut self, host: &mut TestHost) -> Result<(), VmError> {
    // Keep draining even if a job fails so we don't drop queued jobs with leaked persistent roots.
    let mut first_err: Option<VmError> = None;
    while let Some(job) = host.queue.pop_front() {
      let result = job.run(self, host);
      if first_err.is_none() {
        if let Err(e) = result {
          first_err = Some(e);
        }
      }
    }
    match first_err {
      None => Ok(()),
      Some(e) => Err(e),
    }
  }
}

impl VmJobContext for TestContext {
  fn call(
    &mut self,
    host: &mut dyn VmHostHooks,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let mut scope = self.heap.scope();
    self.vm.call_with_host(&mut scope, host, callee, this, args)
  }

  fn construct(
    &mut self,
    host: &mut dyn VmHostHooks,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let mut scope = self.heap.scope();
    self
      .vm
      .construct_with_host(&mut scope, host, callee, args, new_target)
  }

  fn add_root(&mut self, value: Value) -> Result<RootId, VmError> {
    self.heap.add_root(value)
  }

  fn remove_root(&mut self, id: RootId) {
    self.heap.remove_root(id)
  }
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

fn on_rejected_returns_42(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  CATCH_CALLS.with(|c| c.set(c.get() + 1));
  assert_eq!(args.get(0).copied().unwrap_or(Value::Undefined), Value::Number(1.0));
  Ok(Value::Number(42.0))
}

fn borrowed_then_returns_123(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  BORROWED_THEN_CALLS.with(|c| c.set(c.get() + 1));
  assert_eq!(this, Value::Number(1.0));
  assert_eq!(args.get(0).copied().unwrap_or(Value::Undefined), Value::Undefined);
  assert_eq!(args.get(1).copied().unwrap_or(Value::Undefined), Value::Number(99.0));
  Ok(Value::Number(123.0))
}

fn borrowed_then_should_not_be_called(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  BORROWED_THEN_CALLS.with(|c| c.set(c.get() + 1));
  Ok(Value::Number(123.0))
}

fn on_finally_increments(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  FINALLY_CALLS.with(|c| c.set(c.get() + 1));
  Ok(Value::Undefined)
}

fn on_finally_returns_promise(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  FINALLY_CALLS.with(|c| c.set(c.get() + 1));
  let promise = FINALLY_RETURN_PROMISE.with(|c| c.get()).expect("missing finally return promise");
  Ok(Value::Object(promise))
}

fn then_records_value(
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
    return Err(VmError::Unimplemented("expected number arg"));
  };
  THEN_ARG.with(|c| c.set(Some(n)));
  Ok(Value::Undefined)
}

#[test]
fn promise_catch_transforms_rejection_into_fulfillment() -> Result<(), VmError> {
  reset_thread_locals();

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_reject = get_own_data_function(&mut ctx.heap, promise_ctor, "reject")?;
  let promise_catch = get_own_data_function(&mut ctx.heap, promise_proto, "catch")?;

  let (p, q) = {
    let mut scope = ctx.heap.scope();

    // p = Promise.reject(1)
    let Value::Object(p) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_reject),
      Value::Object(promise_ctor),
      &[Value::Number(1.0)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.reject returned non-object"));
    };

    let call_id = ctx.vm.register_native_call(on_rejected_returns_42)?;
    let name = scope.alloc_string("onRejected")?;
    let on_rejected = scope.alloc_native_function(call_id, None, name, 1)?;

    // q = p.catch(onRejected)
    let Value::Object(q) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_catch),
      Value::Object(p),
      &[Value::Object(on_rejected)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.catch returned non-object"));
    };

    (p, q)
  };

  assert_eq!(
    host.rejection_tracker,
    vec![
      (PromiseHandle(p), PromiseRejectionOperation::Reject),
      (PromiseHandle(p), PromiseRejectionOperation::Handle),
    ]
  );

  ctx.run_jobs(&mut host)?;

  assert_eq!(CATCH_CALLS.with(|c| c.get()), 1);
  assert_eq!(ctx.heap.promise_state(q)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(q)?, Some(Value::Number(42.0)));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn promise_catch_is_borrowable_and_boxes_primitives_for_then_lookup() -> Result<(), VmError> {
  reset_thread_locals();

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_catch = get_own_data_function(&mut ctx.heap, promise_proto, "catch")?;
  let number_proto = realm.intrinsics().number_prototype();

  let result = {
    let mut scope = ctx.heap.scope();
    scope.push_root(Value::Object(number_proto))?;

    // Number.prototype.then = borrowed_then_returns_123
    let call_id = ctx.vm.register_native_call(borrowed_then_returns_123)?;
    let name = scope.alloc_string("then")?;
    let then_fn = scope.alloc_native_function(call_id, None, name, 2)?;
    scope.push_root(Value::Object(then_fn))?;

    let key_s = scope.alloc_string("then")?;
    scope.push_root(Value::String(key_s))?;
    let key = PropertyKey::from_string(key_s);
    scope.define_property(
      number_proto,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Object(then_fn),
          writable: true,
        },
      },
    )?;

    // Promise.prototype.catch.call(1, 99) => Number.prototype.then(undefined, 99)
    ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_catch),
      Value::Number(1.0),
      &[Value::Number(99.0)],
    )?
  };

  assert_eq!(result, Value::Number(123.0));
  assert_eq!(BORROWED_THEN_CALLS.with(|c| c.get()), 1);

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn promise_finally_throws_on_non_object_receiver_even_if_then_exists() -> Result<(), VmError> {
  reset_thread_locals();

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_finally = get_own_data_function(&mut ctx.heap, promise_proto, "finally")?;
  let number_proto = realm.intrinsics().number_prototype();

  let result = {
    let mut scope = ctx.heap.scope();
    scope.push_root(Value::Object(number_proto))?;

    // Number.prototype.then is callable, but `Promise.prototype.finally` should still throw because
    // it requires an Object receiver (ECMA-262).
    let call_id = ctx.vm.register_native_call(borrowed_then_should_not_be_called)?;
    let name = scope.alloc_string("then")?;
    let then_fn = scope.alloc_native_function(call_id, None, name, 2)?;
    scope.push_root(Value::Object(then_fn))?;

    let key_s = scope.alloc_string("then")?;
    scope.push_root(Value::String(key_s))?;
    let key = PropertyKey::from_string(key_s);
    scope.define_property(
      number_proto,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Object(then_fn),
          writable: true,
        },
      },
    )?;

    ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_finally),
      Value::Number(1.0),
      &[Value::Undefined],
    )
  };

  if !matches!(result, Err(VmError::Throw(_)) | Err(VmError::ThrowWithStack { .. })) {
    return Err(VmError::Unimplemented(
      "expected Promise.prototype.finally to throw on non-object receiver",
    ));
  }

  assert_eq!(BORROWED_THEN_CALLS.with(|c| c.get()), 0);

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn promise_finally_on_fulfill_runs_callback_and_preserves_value() -> Result<(), VmError> {
  reset_thread_locals();

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_resolve = get_own_data_function(&mut ctx.heap, promise_ctor, "resolve")?;
  let promise_finally = get_own_data_function(&mut ctx.heap, promise_proto, "finally")?;

  let q = {
    let mut scope = ctx.heap.scope();

    // p = Promise.resolve(1)
    let Value::Object(p) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_resolve),
      Value::Object(promise_ctor),
      &[Value::Number(1.0)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.resolve returned non-object"));
    };

    let call_id = ctx.vm.register_native_call(on_finally_increments)?;
    let name = scope.alloc_string("onFinally")?;
    let on_finally = scope.alloc_native_function(call_id, None, name, 0)?;

    // q = p.finally(onFinally)
    let Value::Object(q) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_finally),
      Value::Object(p),
      &[Value::Object(on_finally)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.finally returned non-object"));
    };

    q
  };

  ctx.run_jobs(&mut host)?;

  assert_eq!(FINALLY_CALLS.with(|c| c.get()), 1);
  assert_eq!(ctx.heap.promise_state(q)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(q)?, Some(Value::Number(1.0)));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn promise_finally_on_reject_runs_callback_and_preserves_reason() -> Result<(), VmError> {
  reset_thread_locals();

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_reject = get_own_data_function(&mut ctx.heap, promise_ctor, "reject")?;
  let promise_finally = get_own_data_function(&mut ctx.heap, promise_proto, "finally")?;

  let q = {
    let mut scope = ctx.heap.scope();

    // p = Promise.reject(1)
    let Value::Object(p) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_reject),
      Value::Object(promise_ctor),
      &[Value::Number(1.0)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.reject returned non-object"));
    };

    let call_id = ctx.vm.register_native_call(on_finally_increments)?;
    let name = scope.alloc_string("onFinally")?;
    let on_finally = scope.alloc_native_function(call_id, None, name, 0)?;

    // q = p.finally(onFinally)
    let Value::Object(q) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_finally),
      Value::Object(p),
      &[Value::Object(on_finally)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.finally returned non-object"));
    };

    q
  };

  ctx.run_jobs(&mut host)?;

  assert_eq!(FINALLY_CALLS.with(|c| c.get()), 1);
  assert_eq!(ctx.heap.promise_state(q)?, PromiseState::Rejected);
  assert_eq!(ctx.heap.promise_result(q)?, Some(Value::Number(1.0)));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn promise_finally_waits_for_returned_promise_before_continuing() -> Result<(), VmError> {
  reset_thread_locals();

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_resolve = get_own_data_function(&mut ctx.heap, promise_ctor, "resolve")?;
  let with_resolvers = get_own_data_function(&mut ctx.heap, promise_ctor, "withResolvers")?;
  let promise_finally = get_own_data_function(&mut ctx.heap, promise_proto, "finally")?;
  let promise_then = get_own_data_function(&mut ctx.heap, promise_proto, "then")?;

  let (gate_promise, gate_resolve, q) = {
    let mut scope = ctx.heap.scope();

    // p = Promise.resolve(1)
    let Value::Object(p) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_resolve),
      Value::Object(promise_ctor),
      &[Value::Number(1.0)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.resolve returned non-object"));
    };

    // gate = Promise.withResolvers()
    let Value::Object(record) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(with_resolvers),
      Value::Object(promise_ctor),
      &[],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.withResolvers returned non-object"));
    };

    // Root `record` while allocating property keys (which may trigger GC).
    scope.push_root(Value::Object(record))?;

    let promise_key = PropertyKey::from_string(scope.alloc_string("promise")?);
    let gate_promise = match scope.heap().object_get_own_data_property_value(record, &promise_key)? {
      Some(Value::Object(p)) => p,
      _ => return Err(VmError::Unimplemented("record.promise missing or not object")),
    };

    let resolve_key = PropertyKey::from_string(scope.alloc_string("resolve")?);
    let gate_resolve = match scope.heap().object_get_own_data_property_value(record, &resolve_key)? {
      Some(Value::Object(f)) => f,
      _ => return Err(VmError::Unimplemented("record.resolve missing or not object")),
    };

    FINALLY_RETURN_PROMISE.with(|c| c.set(Some(gate_promise)));

    let finally_call = ctx.vm.register_native_call(on_finally_returns_promise)?;
    let finally_name = scope.alloc_string("onFinally")?;
    let on_finally = scope.alloc_native_function(finally_call, None, finally_name, 0)?;

    // q = p.finally(() => gate.promise)
    let Value::Object(q) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_finally),
      Value::Object(p),
      &[Value::Object(on_finally)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.finally returned non-object"));
    };

    // Attach a handler to q before running jobs.
    let then_call = ctx.vm.register_native_call(then_records_value)?;
    let then_name = scope.alloc_string("thenRecords")?;
    let then_cb = scope.alloc_native_function(then_call, None, then_name, 1)?;

    let _ = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(q),
      &[Value::Object(then_cb)],
    )?;

    (gate_promise, gate_resolve, q)
  };

  // Keep the gate + result promises alive across job execution (jobs may allocate/GC).
  let gate_promise_root = ctx.heap.add_root(Value::Object(gate_promise))?;
  let gate_resolve_root = ctx.heap.add_root(Value::Object(gate_resolve))?;
  let q_root = ctx.heap.add_root(Value::Object(q))?;

  // Drain the queued jobs. `onFinally` should run, but `q` must remain pending until we resolve
  // `gate_promise`.
  ctx.run_jobs(&mut host)?;

  assert_eq!(FINALLY_CALLS.with(|c| c.get()), 1);
  assert_eq!(THEN_ARG.with(|c| c.get()), None);
  assert_eq!(ctx.heap.promise_state(q)?, PromiseState::Pending);
  assert!(host.queue.is_empty());

  // Resolve `gate_promise` and drain jobs again: this should allow the `finally` chain to continue.
  {
    let mut scope = ctx.heap.scope();
    let _ = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(gate_resolve),
      Value::Undefined,
      &[Value::Number(999.0)],
    )?;
  }

  ctx.run_jobs(&mut host)?;

  assert_eq!(ctx.heap.promise_state(gate_promise)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_state(q)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(q)?, Some(Value::Number(1.0)));
  assert_eq!(THEN_ARG.with(|c| c.get()), Some(1.0));

  ctx.heap.remove_root(gate_promise_root);
  ctx.heap.remove_root(gate_resolve_root);
  ctx.heap.remove_root(q_root);

  realm.teardown(&mut ctx.heap);
  Ok(())
}
