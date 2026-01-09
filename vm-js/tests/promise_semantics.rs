use std::cell::{Cell, RefCell};
use std::collections::VecDeque;

use vm_js::{
  GcObject, Heap, HeapLimits, Job, JobCallback, PromiseHandle, PromiseRejectionOperation,
  PromiseState, PropertyDescriptor, PropertyKey, PropertyKind, Realm, RealmId, RootId, Scope,
  Value, Vm, VmError, VmHostHooks, VmJobContext, VmOptions,
};

thread_local! {
  static STORED_RESOLVE_ROOT: Cell<Option<RootId>> = Cell::new(None);
  static THEN2_ARG: Cell<Option<f64>> = Cell::new(None);
  static CALL_LOG: RefCell<Vec<u8>> = RefCell::new(Vec::new());
  static THEN_GETTER_CALLS: Cell<u32> = Cell::new(0);
  static THEN_GETTER_EXPECTED_THIS: Cell<Option<GcObject>> = Cell::new(None);
  static THEN_GETTER_RETURN: Cell<Option<GcObject>> = Cell::new(None);
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

  fn host_call_job_callback(
    &mut self,
    ctx: &mut dyn VmJobContext,
    callback: &JobCallback,
    this_argument: Value,
    arguments: &[Value],
  ) -> Result<Value, VmError> {
    ctx.call(
      self,
      Value::Object(callback.callback_object()),
      this_argument,
      arguments,
    )
  }

  fn host_promise_rejection_tracker(
    &mut self,
    promise: PromiseHandle,
    operation: PromiseRejectionOperation,
  ) {
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
    while let Some(job) = host.queue.pop_front() {
      job.run(self, host)?;
    }
    Ok(())
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

fn data_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
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

fn executor_resolve_one(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let resolve = args.get(0).copied().unwrap_or(Value::Undefined);
  let _ = vm.call_with_host(scope, host, resolve, Value::Undefined, &[Value::Number(1.0)])?;
  Ok(Value::Undefined)
}

fn executor_reject_one(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let reject = args.get(1).copied().unwrap_or(Value::Undefined);
  let _ = vm.call_with_host(scope, host, reject, Value::Undefined, &[Value::Number(1.0)])?;
  Ok(Value::Undefined)
}

fn executor_store_resolve(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let resolve = args.get(0).copied().unwrap_or(Value::Undefined);
  let root = scope.heap_mut().add_root(resolve)?;
  STORED_RESOLVE_ROOT.with(|c| c.set(Some(root)));
  Ok(Value::Undefined)
}

fn add_one(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Value::Number(n) = args.get(0).copied().unwrap_or(Value::Undefined) else {
    return Err(VmError::Unimplemented("expected number"));
  };
  Ok(Value::Number(n + 1.0))
}

fn return_99(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(99.0))
}

fn record_then2_arg(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Value::Number(n) = args.get(0).copied().unwrap_or(Value::Undefined) else {
    return Err(VmError::Unimplemented("expected number"));
  };
  THEN2_ARG.with(|c| c.set(Some(n)));
  Ok(Value::Undefined)
}

fn log_1(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  CALL_LOG.with(|l| l.borrow_mut().push(1));
  Ok(Value::Undefined)
}

fn log_2(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  CALL_LOG.with(|l| l.borrow_mut().push(2));
  Ok(Value::Undefined)
}

fn thenable_then_resolve_42(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let resolve = args.get(0).copied().unwrap_or(Value::Undefined);
  let _ = vm.call_with_host(scope, host, resolve, Value::Undefined, &[Value::Number(42.0)])?;
  Ok(Value::Undefined)
}

fn thenable_then_getter_returns_then_fn(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  THEN_GETTER_CALLS.with(|c| c.set(c.get() + 1));

  let expected = THEN_GETTER_EXPECTED_THIS
    .with(|c| c.get())
    .expect("THEN_GETTER_EXPECTED_THIS should be set");
  assert_eq!(this, Value::Object(expected));

  // Stress rooting: `resolve_promise` must keep the receiver + getter return value live across GC.
  scope.heap_mut().collect_garbage();

  let then_fn = THEN_GETTER_RETURN
    .with(|c| c.get())
    .expect("THEN_GETTER_RETURN should be set");
  Ok(Value::Object(then_fn))
}

fn executor_resolve_thenable_then_resolve_again(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let resolve = args.get(0).copied().unwrap_or(Value::Undefined);

  // Create thenable object with a callable `.then` data property.
  let thenable = scope.alloc_object()?;
  scope.push_root(Value::Object(thenable))?;

  let then_call_id = vm.register_native_call(thenable_then_resolve_42)?;
  let then_name = scope.alloc_string("then")?;
  let then_fn = scope.alloc_native_function(then_call_id, None, then_name, 2)?;
  scope.push_root(Value::Object(then_fn))?;

  let then_key_s = scope.alloc_string("then")?;
  scope.push_root(Value::String(then_key_s))?;
  let then_key = PropertyKey::from_string(then_key_s);
  scope.define_property(thenable, then_key, data_desc(Value::Object(then_fn)))?;

  // First resolve schedules the thenable job. The second resolve must be ignored due to the shared
  // alreadyResolved record.
  let _ = vm.call_with_host(
    scope,
    host,
    resolve,
    Value::Undefined,
    &[Value::Object(thenable)],
  )?;
  let _ = vm.call_with_host(scope, host, resolve, Value::Undefined, &[Value::Number(1.0)])?;

  Ok(Value::Undefined)
}

fn executor_resolve_thenable_accessor_then(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  THEN_GETTER_CALLS.with(|c| c.set(0));
  THEN_GETTER_EXPECTED_THIS.with(|c| c.set(None));
  THEN_GETTER_RETURN.with(|c| c.set(None));

  let resolve = args.get(0).copied().unwrap_or(Value::Undefined);

  let thenable = scope.alloc_object()?;
  scope.push_root(Value::Object(thenable))?;

  let then_call_id = vm.register_native_call(thenable_then_resolve_42)?;
  let then_name = scope.alloc_string("then")?;
  let then_fn = scope.alloc_native_function(then_call_id, None, then_name, 2)?;
  scope.push_root(Value::Object(then_fn))?;

  let getter_call_id = vm.register_native_call(thenable_then_getter_returns_then_fn)?;
  let getter_name = scope.alloc_string("get_then")?;
  let getter_fn = scope.alloc_native_function(getter_call_id, None, getter_name, 0)?;
  scope.push_root(Value::Object(getter_fn))?;

  THEN_GETTER_EXPECTED_THIS.with(|c| c.set(Some(thenable)));
  THEN_GETTER_RETURN.with(|c| c.set(Some(then_fn)));

  let then_key_s = scope.alloc_string("then")?;
  scope.push_root(Value::String(then_key_s))?;
  let then_key = PropertyKey::from_string(then_key_s);
  scope.define_property(
    thenable,
    then_key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Accessor {
        get: Value::Object(getter_fn),
        set: Value::Undefined,
      },
    },
  )?;

  let _ = vm.call_with_host(
    scope,
    host,
    resolve,
    Value::Undefined,
    &[Value::Object(thenable)],
  )?;
  Ok(Value::Undefined)
}

#[test]
fn basic_fulfillment_then_schedules_microtask_and_fulfills_derived() -> Result<(), VmError> {
  THEN2_ARG.with(|c| c.set(None));

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_then = get_own_data_function(&mut ctx.heap, promise_proto, "then")?;

  let (promise_obj, derived_obj) = {
    let mut scope = ctx.heap.scope();

    let exec_id = ctx.vm.register_native_call(executor_resolve_one)?;
    let exec_name = scope.alloc_string("executor")?;
    let executor = scope.alloc_native_function(exec_id, None, exec_name, 2)?;

    let Value::Object(promise_obj) = ctx.vm.construct_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_ctor),
      &[Value::Object(executor)],
      Value::Object(promise_ctor),
    )?
    else {
      return Err(VmError::Unimplemented("Promise constructor returned non-object"));
    };

    let add_one_id = ctx.vm.register_native_call(add_one)?;
    let add_one_name = scope.alloc_string("add_one")?;
    let add_one_fn = scope.alloc_native_function(add_one_id, None, add_one_name, 1)?;

    let Value::Object(derived_obj) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(promise_obj),
      &[Value::Object(add_one_fn)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.then returned non-object"));
    };

    // Attach another handler to the derived promise before running jobs (pending-then path).
    let then2_id = ctx.vm.register_native_call(record_then2_arg)?;
    let then2_name = scope.alloc_string("then2")?;
    let then2_fn = scope.alloc_native_function(then2_id, None, then2_name, 1)?;
    let _ = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(derived_obj),
      &[Value::Object(then2_fn)],
    )?;

    (promise_obj, derived_obj)
  };

  assert_eq!(ctx.heap.promise_state(promise_obj)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_state(derived_obj)?, PromiseState::Pending);
  assert_eq!(host.queue.len(), 1, "then() should enqueue exactly one job");
  assert_eq!(ctx.vm.microtask_queue().len(), 0, "custom host should be used");

  ctx.run_jobs(&mut host)?;

  assert_eq!(ctx.heap.promise_state(derived_obj)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(derived_obj)?, Some(Value::Number(2.0)));
  assert_eq!(THEN2_ARG.with(|c| c.get()), Some(2.0));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn rejection_tracker_reports_reject_then_handle() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_then = get_own_data_function(&mut ctx.heap, promise_proto, "then")?;

  let (promise_obj, derived_obj) = {
    let mut scope = ctx.heap.scope();

    let exec_id = ctx.vm.register_native_call(executor_reject_one)?;
    let exec_name = scope.alloc_string("executor")?;
    let executor = scope.alloc_native_function(exec_id, None, exec_name, 2)?;

    let Value::Object(promise_obj) = ctx.vm.construct_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_ctor),
      &[Value::Object(executor)],
      Value::Object(promise_ctor),
    )?
    else {
      return Err(VmError::Unimplemented("Promise constructor returned non-object"));
    };

    assert_eq!(
      host.rejection_tracker,
      vec![(PromiseHandle(promise_obj), PromiseRejectionOperation::Reject)]
    );

    let on_rejected_id = ctx.vm.register_native_call(return_99)?;
    let on_rejected_name = scope.alloc_string("return_99")?;
    let on_rejected = scope.alloc_native_function(on_rejected_id, None, on_rejected_name, 1)?;

    let Value::Object(derived_obj) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(promise_obj),
      &[Value::Undefined, Value::Object(on_rejected)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.then returned non-object"));
    };

    (promise_obj, derived_obj)
  };

  assert_eq!(
    host.rejection_tracker,
    vec![
      (PromiseHandle(promise_obj), PromiseRejectionOperation::Reject),
      (PromiseHandle(promise_obj), PromiseRejectionOperation::Handle),
    ]
  );
  assert_eq!(host.queue.len(), 1);

  ctx.run_jobs(&mut host)?;

  assert_eq!(ctx.heap.promise_state(derived_obj)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(derived_obj)?, Some(Value::Number(99.0)));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn pending_then_resolve_later_triggers_reaction_job() -> Result<(), VmError> {
  STORED_RESOLVE_ROOT.with(|c| c.set(None));

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_then = get_own_data_function(&mut ctx.heap, promise_proto, "then")?;

  let (promise_obj, derived_obj) = {
    let mut scope = ctx.heap.scope();

    let exec_id = ctx.vm.register_native_call(executor_store_resolve)?;
    let exec_name = scope.alloc_string("executor")?;
    let executor = scope.alloc_native_function(exec_id, None, exec_name, 2)?;

    let Value::Object(promise_obj) = ctx.vm.construct_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_ctor),
      &[Value::Object(executor)],
      Value::Object(promise_ctor),
    )?
    else {
      return Err(VmError::Unimplemented("Promise constructor returned non-object"));
    };

    let add_one_id = ctx.vm.register_native_call(add_one)?;
    let add_one_name = scope.alloc_string("add_one")?;
    let add_one_fn = scope.alloc_native_function(add_one_id, None, add_one_name, 1)?;

    let Value::Object(derived_obj) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(promise_obj),
      &[Value::Object(add_one_fn)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.then returned non-object"));
    };

    (promise_obj, derived_obj)
  };

  assert_eq!(ctx.heap.promise_state(promise_obj)?, PromiseState::Pending);
  assert_eq!(host.queue.len(), 0);

  // Resolve later.
  let resolve_root = STORED_RESOLVE_ROOT.with(|c| c.take()).expect("resolve root should be set");
  let resolve = ctx
    .heap
    .get_root(resolve_root)
    .expect("resolve root should be valid");
  {
    let mut scope = ctx.heap.scope();
    let _ = ctx
      .vm
      .call_with_host(&mut scope, &mut host, resolve, Value::Undefined, &[Value::Number(1.0)])?;
  }
  ctx.heap.remove_root(resolve_root);

  assert_eq!(host.queue.len(), 1);
  ctx.run_jobs(&mut host)?;

  assert_eq!(ctx.heap.promise_state(derived_obj)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(derived_obj)?, Some(Value::Number(2.0)));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn fulfill_reactions_run_in_registration_order() -> Result<(), VmError> {
  CALL_LOG.with(|l| l.borrow_mut().clear());
  STORED_RESOLVE_ROOT.with(|c| c.set(None));

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_then = get_own_data_function(&mut ctx.heap, promise_proto, "then")?;

  let promise_obj = {
    let mut scope = ctx.heap.scope();

    let exec_id = ctx.vm.register_native_call(executor_store_resolve)?;
    let exec_name = scope.alloc_string("executor")?;
    let executor = scope.alloc_native_function(exec_id, None, exec_name, 2)?;

    let Value::Object(promise_obj) = ctx.vm.construct_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_ctor),
      &[Value::Object(executor)],
      Value::Object(promise_ctor),
    )?
    else {
      return Err(VmError::Unimplemented("Promise constructor returned non-object"));
    };

    let log1_id = ctx.vm.register_native_call(log_1)?;
    let log1_name = scope.alloc_string("log1")?;
    let log1_fn = scope.alloc_native_function(log1_id, None, log1_name, 1)?;

    let log2_id = ctx.vm.register_native_call(log_2)?;
    let log2_name = scope.alloc_string("log2")?;
    let log2_fn = scope.alloc_native_function(log2_id, None, log2_name, 1)?;

    // Attach two fulfill handlers in order.
    let _ = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(promise_obj),
      &[Value::Object(log1_fn)],
    )?;
    let _ = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(promise_obj),
      &[Value::Object(log2_fn)],
    )?;

    promise_obj
  };

  assert_eq!(host.queue.len(), 0);

  // Resolve later, then run jobs.
  let resolve_root = STORED_RESOLVE_ROOT.with(|c| c.take()).expect("resolve root should be set");
  let resolve = ctx
    .heap
    .get_root(resolve_root)
    .expect("resolve root should be valid");
  {
    let mut scope = ctx.heap.scope();
    let _ =
      ctx.vm
        .call_with_host(&mut scope, &mut host, resolve, Value::Undefined, &[Value::Undefined])?;
  }
  ctx.heap.remove_root(resolve_root);

  assert_eq!(host.queue.len(), 2);
  ctx.run_jobs(&mut host)?;

  assert_eq!(CALL_LOG.with(|l| l.borrow().clone()), vec![1, 2]);

  // Keep `promise_obj` used so the test exercises the promise API.
  assert_eq!(ctx.heap.promise_state(promise_obj)?, PromiseState::Fulfilled);

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn thenable_assimilation_and_already_resolved_record() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();

  let promise_obj = {
    let mut scope = ctx.heap.scope();

    let exec_id = ctx
      .vm
      .register_native_call(executor_resolve_thenable_then_resolve_again)?;
    let exec_name = scope.alloc_string("executor")?;
    let executor = scope.alloc_native_function(exec_id, None, exec_name, 2)?;

    let Value::Object(promise_obj) = ctx.vm.construct_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_ctor),
      &[Value::Object(executor)],
      Value::Object(promise_ctor),
    )?
    else {
      return Err(VmError::Unimplemented("Promise constructor returned non-object"));
    };
    promise_obj
  };

  // The thenable should enqueue a resolve-thenable job and keep the promise pending until it runs.
  assert_eq!(ctx.heap.promise_state(promise_obj)?, PromiseState::Pending);
  assert_eq!(host.queue.len(), 1);

  ctx.run_jobs(&mut host)?;

  assert_eq!(ctx.heap.promise_state(promise_obj)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(promise_obj)?, Some(Value::Number(42.0)));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn thenable_assimilation_supports_accessor_then_property() -> Result<(), VmError> {
  THEN_GETTER_CALLS.with(|c| c.set(0));

  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();

  let promise_obj = {
    let mut scope = ctx.heap.scope();

    let exec_id = ctx
      .vm
      .register_native_call(executor_resolve_thenable_accessor_then)?;
    let exec_name = scope.alloc_string("executor")?;
    let executor = scope.alloc_native_function(exec_id, None, exec_name, 2)?;

    let Value::Object(promise_obj) = ctx.vm.construct_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_ctor),
      &[Value::Object(executor)],
      Value::Object(promise_ctor),
    )?
    else {
      return Err(VmError::Unimplemented("Promise constructor returned non-object"));
    };
    promise_obj
  };

  assert_eq!(THEN_GETTER_CALLS.with(|c| c.get()), 1);
  assert_eq!(ctx.heap.promise_state(promise_obj)?, PromiseState::Pending);
  assert_eq!(host.queue.len(), 1);

  ctx.run_jobs(&mut host)?;

  assert_eq!(ctx.heap.promise_state(promise_obj)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(promise_obj)?, Some(Value::Number(42.0)));

  realm.teardown(&mut ctx.heap);
  Ok(())
}

#[test]
fn jobs_root_captures_across_gc() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut host = TestHost::default();
  let mut realm = Realm::new(&mut ctx.vm, &mut ctx.heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let promise_proto = realm.intrinsics().promise_prototype();
  let promise_then = get_own_data_function(&mut ctx.heap, promise_proto, "then")?;
  let promise_resolve = get_own_data_function(&mut ctx.heap, promise_ctor, "resolve")?;

  let (derived_obj, thenable_promise_obj) = {
    let mut scope = ctx.heap.scope();

    // --- Reaction job rooting ---
    let exec_id = ctx.vm.register_native_call(executor_resolve_one)?;
    let exec_name = scope.alloc_string("executor")?;
    let executor = scope.alloc_native_function(exec_id, None, exec_name, 2)?;
    let Value::Object(p) = ctx.vm.construct_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_ctor),
      &[Value::Object(executor)],
      Value::Object(promise_ctor),
    )?
    else {
      return Err(VmError::Unimplemented("Promise constructor returned non-object"));
    };

    let add_one_id = ctx.vm.register_native_call(add_one)?;
    let add_one_name = scope.alloc_string("add_one")?;
    let add_one_fn = scope.alloc_native_function(add_one_id, None, add_one_name, 1)?;
    let Value::Object(derived_obj) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_then),
      Value::Object(p),
      &[Value::Object(add_one_fn)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.prototype.then returned non-object"));
    };

    // --- Thenable job rooting (Promise.resolve(thenable)) ---
    let thenable = scope.alloc_object()?;
    scope.push_root(Value::Object(thenable))?;

    let then_id = ctx.vm.register_native_call(thenable_then_resolve_42)?;
    let then_name = scope.alloc_string("then")?;
    let then_fn = scope.alloc_native_function(then_id, None, then_name, 2)?;
    scope.push_root(Value::Object(then_fn))?;
    let then_key_s = scope.alloc_string("then")?;
    scope.push_root(Value::String(then_key_s))?;
    let then_key = PropertyKey::from_string(then_key_s);
    scope.define_property(thenable, then_key, data_desc(Value::Object(then_fn)))?;

    let Value::Object(thenable_promise_obj) = ctx.vm.call_with_host(
      &mut scope,
      &mut host,
      Value::Object(promise_resolve),
      Value::Object(promise_ctor),
      &[Value::Object(thenable)],
    )?
    else {
      return Err(VmError::Unimplemented("Promise.resolve returned non-object"));
    };

    assert_eq!(host.queue.len(), 2, "expected one reaction job and one thenable job");
    (derived_obj, thenable_promise_obj)
  };

  // Force a GC cycle while jobs are still queued. If jobs do not root their captured GC objects
  // correctly, executing them would observe stale handles (invalid objects / not-callable).
  ctx.heap.collect_garbage();

  assert!(ctx.heap.is_valid_object(derived_obj));
  assert!(ctx.heap.is_valid_object(thenable_promise_obj));

  ctx.run_jobs(&mut host)?;

  assert_eq!(ctx.heap.promise_state(derived_obj)?, PromiseState::Fulfilled);
  assert_eq!(ctx.heap.promise_result(derived_obj)?, Some(Value::Number(2.0)));

  assert_eq!(
    ctx.heap.promise_state(thenable_promise_obj)?,
    PromiseState::Fulfilled
  );
  assert_eq!(
    ctx.heap.promise_result(thenable_promise_obj)?,
    Some(Value::Number(42.0))
  );

  realm.teardown(&mut ctx.heap);
  Ok(())
}
