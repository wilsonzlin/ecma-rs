use std::collections::VecDeque;

use vm_js::await_value;
use vm_js::Awaitable;
use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::Job;
use vm_js::JobCallback;
use vm_js::Promise;
use vm_js::PromiseHandle;
use vm_js::PromiseRejectionOperation;
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
  _callee: vm_js::GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

#[derive(Default)]
struct RecordingHost {
  queue: VecDeque<Job>,
  tracker_calls: Vec<(PromiseHandle, PromiseRejectionOperation)>,
  calls: Vec<(vm_js::GcObject, Value, Vec<Value>)>,
}

impl VmHostHooks for RecordingHost {
  fn host_enqueue_promise_job(&mut self, job: Job, _realm: Option<vm_js::RealmId>) {
    self.queue.push_back(job);
  }

  fn host_make_job_callback(&mut self, callback: vm_js::GcObject) -> JobCallback {
    JobCallback::new(callback)
  }

  fn host_call_job_callback(
    &mut self,
    _ctx: &mut dyn VmJobContext,
    callback: &JobCallback,
    this_argument: Value,
    arguments: &[Value],
  ) -> Result<Value, VmError> {
    self
      .calls
      .push((callback.callback(), this_argument, arguments.to_vec()));
    Ok(Value::Undefined)
  }

  fn host_promise_rejection_tracker(
    &mut self,
    promise: PromiseHandle,
    operation: PromiseRejectionOperation,
  ) {
    self.tracker_calls.push((promise, operation));
  }
}

#[derive(Default)]
struct TestContext;

impl VmJobContext for TestContext {
  fn call(&mut self, _callee: Value, _this: Value, _args: &[Value]) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("TestContext::call"))
  }

  fn construct(
    &mut self,
    _callee: Value,
    _args: &[Value],
    _new_target: Value,
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("TestContext::construct"))
  }

  fn add_root(&mut self, _value: Value) -> RootId {
    panic!("TestContext::add_root should not be called in this test")
  }

  fn remove_root(&mut self, _id: RootId) {
    panic!("TestContext::remove_root should not be called in this test")
  }
}

#[test]
fn await_non_promise_value_queues_microtask() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let (on_fulfilled, on_rejected) = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(noop);
    let name = scope.alloc_string("onFulfilled").unwrap();
    let on_fulfilled = scope.alloc_native_function(call_id, None, name, 1).unwrap();
    let name = scope.alloc_string("onRejected").unwrap();
    let on_rejected = scope.alloc_native_function(call_id, None, name, 1).unwrap();
    (on_fulfilled, on_rejected)
  };

  let mut host = RecordingHost::default();
  await_value(
    &mut host,
    &heap,
    Awaitable::from(Value::Number(123.0)),
    Value::Object(on_fulfilled),
    Value::Object(on_rejected),
  )
  .unwrap();

  // Must not run synchronously.
  assert!(host.calls.is_empty());
  assert_eq!(host.queue.len(), 1);

  let mut ctx = TestContext::default();
  while let Some(job) = host.queue.pop_front() {
    job.run(&mut ctx, &mut host).unwrap();
  }

  assert_eq!(
    host.calls,
    vec![(
      on_fulfilled,
      Value::Undefined,
      vec![Value::Number(123.0)]
    )]
  );
}

#[test]
fn await_rejected_promise_calls_on_rejected() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let (promise_handle, boom, on_fulfilled, on_rejected) = {
    let mut scope = heap.scope();
    let promise_handle = PromiseHandle::from(scope.alloc_object().unwrap());
    let boom = Value::String(scope.alloc_string("boom").unwrap());

    let call_id = vm.register_native_call(noop);
    let name = scope.alloc_string("onFulfilled").unwrap();
    let on_fulfilled = scope.alloc_native_function(call_id, None, name, 1).unwrap();
    let name = scope.alloc_string("onRejected").unwrap();
    let on_rejected = scope.alloc_native_function(call_id, None, name, 1).unwrap();

    (promise_handle, boom, on_fulfilled, on_rejected)
  };

  let promise = Promise::pending(Some(promise_handle));

  let mut host = RecordingHost::default();

  // Reject with no handlers attached: should be tracked as unhandled.
  promise.reject(&mut host, boom).unwrap();
  assert_eq!(
    host.tracker_calls,
    vec![(promise_handle, PromiseRejectionOperation::Reject)]
  );
  assert!(host.queue.is_empty());

  await_value(
    &mut host,
    &heap,
    Awaitable::from(promise.clone()),
    Value::Object(on_fulfilled),
    Value::Object(on_rejected),
  )
  .unwrap();

  // Attaching a rejection handler to an already-rejected promise must transition it to "handled".
  assert_eq!(
    host.tracker_calls,
    vec![
      (promise_handle, PromiseRejectionOperation::Reject),
      (promise_handle, PromiseRejectionOperation::Handle),
    ]
  );

  // Must not run synchronously.
  assert!(host.calls.is_empty());
  assert_eq!(host.queue.len(), 1);

  let mut ctx = TestContext::default();
  while let Some(job) = host.queue.pop_front() {
    job.run(&mut ctx, &mut host).unwrap();
  }

  assert_eq!(
    host.calls,
    vec![(on_rejected, Value::Undefined, vec![boom])]
  );
}
