use vm_js::create_promise_resolve_thenable_job;
use vm_js::new_promise_reaction_job;
use vm_js::perform_promise_then;
use vm_js::GcObject;
use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::Job;
use vm_js::JobCallback;
use vm_js::RootId;
use vm_js::Scope;
use vm_js::Value;
use vm_js::Vm;
use vm_js::VmError;
use vm_js::VmHostHooks;
use vm_js::VmJobContext;
use vm_js::VmOptions;

fn noop(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TestJobCallbackData {
  id: u32,
}

#[derive(Debug)]
struct ExpectedCall {
  callback: GcObject,
  this_argument: Value,
  arguments: Vec<Value>,
}

#[derive(Default)]
struct TestHost {
  made: Vec<GcObject>,
  expected: Option<ExpectedCall>,
  calls: usize,
}

impl VmHostHooks for TestHost {
  fn host_enqueue_promise_job(&mut self, _job: Job, _realm: Option<vm_js::RealmId>) {
    // Not used by these tests; we run jobs directly.
  }

  fn host_make_job_callback(&mut self, callback: GcObject) -> JobCallback {
    let id = u32::try_from(self.made.len()).expect("too many callbacks for test");
    self.made.push(callback);
    JobCallback::new_with_data(callback, TestJobCallbackData { id })
  }

  fn host_call_job_callback(
    &mut self,
    _ctx: &mut dyn VmJobContext,
    callback: &JobCallback,
    this_argument: Value,
    arguments: &[Value],
  ) -> Result<Value, VmError> {
    let data = callback
      .downcast_ref::<TestJobCallbackData>()
      .expect("job callback should have been created by TestHost::host_make_job_callback");
    let callback_obj = callback.callback();
    assert_eq!(
      self.made[data.id as usize], callback_obj,
      "JobCallback metadata should remain consistent"
    );

    let expected = self
      .expected
      .take()
      .expect("unexpected HostCallJobCallback invocation");

    assert_eq!(callback_obj, expected.callback);
    assert_eq!(this_argument, expected.this_argument);
    assert_eq!(arguments, expected.arguments.as_slice());

    self.calls += 1;
    Ok(Value::Undefined)
  }
}

struct RootingContext<'a> {
  heap: &'a mut Heap,
}

impl VmJobContext for RootingContext<'_> {
  fn call(&mut self, _callee: Value, _this: Value, _args: &[Value]) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("RootingContext::call"))
  }

  fn construct(
    &mut self,
    _callee: Value,
    _args: &[Value],
    _new_target: Value,
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("RootingContext::construct"))
  }

  fn add_root(&mut self, value: Value) -> RootId {
    self.heap.add_root(value)
  }

  fn remove_root(&mut self, id: RootId) {
    self.heap.remove_root(id)
  }
}

#[test]
fn promise_reaction_job_uses_host_call_job_callback() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();
  let call_id = vm.register_native_call(noop)?;
  let name = scope.alloc_string("onFulfilled")?;
  let on_fulfilled = scope.alloc_native_function(call_id, None, name, 1)?;
  let non_callable = scope.alloc_object()?;

  let mut host = TestHost::default();
  let (fulfill_reaction, reject_reaction) = perform_promise_then(
    &mut host,
    scope.heap(),
    Value::Object(on_fulfilled),
    Value::Object(non_callable),
  )?;
  assert!(fulfill_reaction.handler.is_some());
  assert!(reject_reaction.handler.is_none());
  assert_eq!(host.made, vec![on_fulfilled]);

  // Use heap objects so we can validate GC safety for job captures.
  let argument_obj = scope.alloc_object()?;
  let argument = Value::Object(argument_obj);
  let job = new_promise_reaction_job(scope.heap_mut(), fulfill_reaction, argument);
  host.expected = Some(ExpectedCall {
    callback: on_fulfilled,
    this_argument: Value::Undefined,
    arguments: vec![argument],
  });

  drop(scope);

  // The job should keep both the callback and argument alive until it runs.
  heap.collect_garbage();
  assert!(heap.is_valid_object(on_fulfilled));
  assert!(heap.is_valid_object(argument_obj));

  let mut ctx = RootingContext { heap: &mut heap };
  job.run(&mut ctx, &mut host)?;
  assert_eq!(host.calls, 1);

  // After job execution, the persistent roots should be removed.
  ctx.heap.collect_garbage();
  assert!(!ctx.heap.is_valid_object(on_fulfilled));
  assert!(!ctx.heap.is_valid_object(argument_obj));
  Ok(())
}

#[test]
fn promise_resolve_thenable_job_uses_host_call_job_callback() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();
  let call_id = vm.register_native_call(noop)?;
  let name = scope.alloc_string("then")?;
  let then_action = scope.alloc_native_function(call_id, None, name, 2)?;

  let thenable = scope.alloc_object()?;
  let resolve = scope.alloc_object()?;
  let reject = scope.alloc_object()?;

  let mut host = TestHost::default();
  let job = create_promise_resolve_thenable_job(
    &mut host,
    scope.heap_mut(),
    Value::Object(thenable),
    Value::Object(then_action),
    Value::Object(resolve),
    Value::Object(reject),
  )?
  .expect("then_action is callable");
  assert_eq!(host.made, vec![then_action]);

  host.expected = Some(ExpectedCall {
    callback: then_action,
    this_argument: Value::Object(thenable),
    arguments: vec![Value::Object(resolve), Value::Object(reject)],
  });

  drop(scope);

  // The job should keep all captured values alive until it runs.
  heap.collect_garbage();
  assert!(heap.is_valid_object(then_action));
  assert!(heap.is_valid_object(thenable));
  assert!(heap.is_valid_object(resolve));
  assert!(heap.is_valid_object(reject));

  let mut ctx = RootingContext { heap: &mut heap };
  job.run(&mut ctx, &mut host)?;
  assert_eq!(host.calls, 1);

  // After execution, the job roots should be removed.
  ctx.heap.collect_garbage();
  assert!(!ctx.heap.is_valid_object(then_action));
  assert!(!ctx.heap.is_valid_object(thenable));
  assert!(!ctx.heap.is_valid_object(resolve));
  assert!(!ctx.heap.is_valid_object(reject));
  Ok(())
}
