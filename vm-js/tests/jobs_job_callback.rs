use vm_js::Budget;
use vm_js::GcObject;
use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::Job;
use vm_js::RealmId;
use vm_js::RootId;
use vm_js::Scope;
use vm_js::TerminationReason;
use vm_js::Value;
use vm_js::Vm;
use vm_js::VmError;
use vm_js::VmHostHooks;
use vm_js::VmJobContext;
use vm_js::VmOptions;

#[derive(Default)]
struct TestHost;

impl VmHostHooks for TestHost {
  fn host_enqueue_promise_job(&mut self, _job: Job, _realm: Option<RealmId>) {
    // Not needed for these tests.
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

fn return_123(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(123.0))
}

fn add_this_and_first_arg(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Value::Number(this_n) = this else {
    return Ok(Value::Undefined);
  };
  let Some(Value::Number(arg0)) = args.first().copied() else {
    return Ok(Value::Undefined);
  };
  Ok(Value::Number(this_n + arg0))
}

fn should_not_be_called(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  panic!("callback should not have been executed when out of fuel");
}

fn alloc_native_callback(
  ctx: &mut TestContext,
  handler: fn(
    &mut Vm,
    &mut Scope<'_>,
    &mut dyn VmHostHooks,
    GcObject,
    Value,
    &[Value],
  ) -> Result<Value, VmError>,
  length: u32,
) -> Result<GcObject, VmError> {
  let call_id = ctx.vm.register_native_call(handler)?;
  let mut scope = ctx.heap.scope();
  let name = scope.alloc_string("cb")?;
  scope.alloc_native_function(call_id, None, name, length)
}

#[test]
fn host_make_job_callback_can_be_rooted_across_gc() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut host = TestHost::default();

  let callback = alloc_native_callback(&mut ctx, return_123, 0)?;
  let job_callback = host.host_make_job_callback(callback);

  // Root the callback through the JobCallback record so the host can safely store it in
  // out-of-heap state (timers, tasks, etc.).
  let _root = job_callback.ensure_rooted(&mut ctx)?;

  ctx.heap.collect_garbage();
  assert!(
    ctx.heap.is_valid_object(callback),
    "callback should remain live while rooted"
  );

  job_callback.teardown(&mut ctx);
  ctx.heap.collect_garbage();
  assert!(
    !ctx.heap.is_valid_object(callback),
    "callback should become collectable after teardown"
  );

  Ok(())
}

#[test]
fn host_call_job_callback_invokes_and_returns_result() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut host = TestHost::default();

  let callback = alloc_native_callback(&mut ctx, add_this_and_first_arg, 1)?;
  let job_callback = host.host_make_job_callback(callback);

  let result = host.host_call_job_callback(
    &mut ctx,
    &job_callback,
    Value::Number(1.0),
    &[Value::Number(2.0)],
  )?;

  assert_eq!(result, Value::Number(3.0));
  Ok(())
}

#[test]
fn host_call_job_callback_observes_budget() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut host = TestHost::default();

  // Configure an empty fuel budget so the next host-initiated call terminates immediately.
  ctx.vm.set_budget(Budget {
    fuel: Some(0),
    deadline: None,
    check_time_every: 1,
  });

  let callback = alloc_native_callback(&mut ctx, should_not_be_called, 0)?;
  let job_callback = host.host_make_job_callback(callback);

  let err = host
    .host_call_job_callback(&mut ctx, &job_callback, Value::Undefined, &[])
    .expect_err("callback should not run when out of fuel");

  assert!(
    matches!(&err, VmError::Termination(t) if t.reason == TerminationReason::OutOfFuel),
    "expected out-of-fuel termination, got: {err:?}"
  );

  Ok(())
}
