use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::Mutex;

use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::Job;
use vm_js::JobCallback;
use vm_js::JobKind;
use vm_js::RootId;
use vm_js::Value;
use vm_js::VmError;
use vm_js::VmHostHooks;
use vm_js::VmJobContext;
use vm_js::WeakGcObject;

#[derive(Default)]
struct TestHost {
  queue: VecDeque<Job>,
}

impl VmHostHooks for TestHost {
  fn host_enqueue_promise_job(&mut self, job: Job, _realm: Option<vm_js::RealmId>) {
    self.queue.push_back(job);
  }
}

#[derive(Default)]
struct TestContext;

impl VmJobContext for TestContext {
  fn call(
    &mut self,
    _host: &mut dyn VmHostHooks,
    _callee: Value,
    _this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("TestContext::call"))
  }

  fn construct(
    &mut self,
    _host: &mut dyn VmHostHooks,
    _callee: Value,
    _args: &[Value],
    _new_target: Value,
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("TestContext::construct"))
  }

  fn add_root(&mut self, _value: Value) -> Result<RootId, VmError> {
    panic!("TestContext::add_root should not be called in this test")
  }

  fn remove_root(&mut self, _id: RootId) {
    panic!("TestContext::remove_root should not be called in this test")
  }
}

struct RootingContext {
  heap: Heap,
}

impl Default for RootingContext {
  fn default() -> Self {
    Self {
      heap: Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024)),
    }
  }
}

impl VmJobContext for RootingContext {
  fn call(
    &mut self,
    _host: &mut dyn VmHostHooks,
    _callee: Value,
    _this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("RootingContext::call"))
  }

  fn construct(
    &mut self,
    _host: &mut dyn VmHostHooks,
    _callee: Value,
    _args: &[Value],
    _new_target: Value,
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("RootingContext::construct"))
  }

  fn add_root(&mut self, value: Value) -> Result<RootId, VmError> {
    self.heap.add_root(value)
  }

  fn remove_root(&mut self, id: RootId) {
    self.heap.remove_root(id)
  }
}

fn enqueue_three_jobs(host: &mut dyn VmHostHooks, sink: Arc<Mutex<Vec<u8>>>) {
  for i in 1..=3u8 {
    let sink = sink.clone();
    host.host_enqueue_promise_job(
      Job::new(JobKind::Promise, move |_ctx, _host| {
        sink.lock().unwrap().push(i);
        Ok(())
      }),
      None,
    );
  }
}

#[test]
fn promise_jobs_can_be_run_in_fifo_order() {
  let sink = Arc::new(Mutex::new(Vec::new()));

  // Ensure the host hook API is object-safe and ergonomic by exercising it behind a trait object.
  let mut host = TestHost::default();
  enqueue_three_jobs(&mut host, sink.clone());

  let mut ctx = TestContext::default();
  while let Some(job) = host.queue.pop_front() {
    job.run(&mut ctx, &mut host).unwrap();
  }

  assert_eq!(&*sink.lock().unwrap(), &[1, 2, 3]);
}

#[test]
fn unrooted_job_captures_can_be_collected_before_run() -> Result<(), VmError> {
  let mut ctx = RootingContext::default();
  let mut host = TestHost::default();

  let obj;
  {
    let mut scope = ctx.heap.scope();
    obj = scope.alloc_object()?;
    host.host_enqueue_promise_job(
      Job::new(JobKind::Promise, move |_ctx, _host| {
        // If this job attempted to use `obj` after a GC, it could observe a stale handle.
        let _ = obj;
        Ok(())
      }),
      None,
    );
  }

  ctx.heap.collect_garbage();
  assert!(
    !ctx.heap.is_valid_object(obj),
    "captured values are not traced by the GC; unrooted jobs can observe stale handles"
  );

  Ok(())
}

#[test]
fn rooted_job_keeps_values_alive_until_run_and_then_allows_collection() -> Result<(), VmError> {
  let mut ctx = RootingContext::default();
  let mut host = TestHost::default();

  let obj;
  {
    let mut scope = ctx.heap.scope();
    obj = scope.alloc_object()?;
  }
  let mut job = Job::new(JobKind::Promise, move |_ctx, _host| Ok(()));
  job.add_root(&mut ctx, Value::Object(obj))?;
  host.host_enqueue_promise_job(job, None);

  ctx.heap.collect_garbage();
  assert!(ctx.heap.is_valid_object(obj));

  let job = host.queue.pop_front().expect("job should be enqueued");
  job.run(&mut ctx, &mut host)?;

  ctx.heap.collect_garbage();
  assert!(
    !ctx.heap.is_valid_object(obj),
    "Job::run should remove persistent roots"
  );

  Ok(())
}

#[test]
fn job_discard_removes_roots_without_running() -> Result<(), VmError> {
  let mut ctx = RootingContext::default();
  let mut host = TestHost::default();

  let obj;
  {
    let mut scope = ctx.heap.scope();
    obj = scope.alloc_object()?;
  }
  let mut job = Job::new(JobKind::Promise, move |_ctx, _host| Ok(()));
  job.add_root(&mut ctx, Value::Object(obj))?;
  host.host_enqueue_promise_job(job, None);

  ctx.heap.collect_garbage();
  assert!(ctx.heap.is_valid_object(obj));

  let job = host.queue.pop_front().expect("job should be enqueued");
  job.discard(&mut ctx);

  ctx.heap.collect_garbage();
  assert!(
    !ctx.heap.is_valid_object(obj),
    "Job::discard should remove persistent roots"
  );

  Ok(())
}

#[test]
fn job_run_removes_roots_even_on_error() -> Result<(), VmError> {
  let mut ctx = RootingContext::default();
  let mut host = TestHost::default();

  let obj;
  {
    let mut scope = ctx.heap.scope();
    obj = scope.alloc_object()?;
  }
  let mut job =
    Job::new(JobKind::Promise, move |_ctx, _host| Err(VmError::Unimplemented("job failed")));
  job.add_root(&mut ctx, Value::Object(obj))?;
  host.host_enqueue_promise_job(job, None);

  ctx.heap.collect_garbage();
  assert!(ctx.heap.is_valid_object(obj));

  let job = host.queue.pop_front().expect("job should be enqueued");
  assert!(matches!(
    job.run(&mut ctx, &mut host),
    Err(VmError::Unimplemented("job failed"))
  ));

  ctx.heap.collect_garbage();
  assert!(
    !ctx.heap.is_valid_object(obj),
    "Job::run should remove persistent roots even when it returns an error"
  );

  Ok(())
}

#[test]
fn host_call_job_callback_default_delegates_to_ctx_call() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let callback_obj = {
    let mut scope = heap.scope();
    scope.alloc_object()?
  };

  let mut host = TestHost::default();
  let mut ctx = TestContext::default();
  let callback = JobCallback::new(callback_obj);

  // Not implementing `host_call_job_callback` should still compile; the default impl is a stub.
  let err = (&mut host as &mut dyn VmHostHooks).host_call_job_callback(
    &mut ctx,
    &callback,
    Value::Undefined,
    &[],
  );
  assert!(matches!(
    err,
    Err(VmError::Unimplemented("TestContext::call"))
  ));
  Ok(())
}

#[test]
fn job_callback_exposes_callback_object() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let callback_obj;
  {
    let mut scope = heap.scope();
    callback_obj = scope.alloc_object()?;
  }

  let cb = JobCallback::new(callback_obj);
  assert_eq!(cb.callback(), callback_obj);
  Ok(())
}

#[test]
fn job_callback_downcast_ref_exposes_host_data() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let callback_obj;
  {
    let mut scope = heap.scope();
    callback_obj = scope.alloc_object()?;
  }

  let cb = JobCallback::new_with_data(callback_obj, 42u32);
  assert_eq!(cb.callback(), callback_obj);
  assert_eq!(cb.downcast_ref::<u32>(), Some(&42u32));
  assert_eq!(cb.downcast_ref::<u64>(), None);
  Ok(())
}

#[test]
fn job_callback_does_not_implicitly_root_callback() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let obj;
  let cb;
  let weak;
  {
    let mut scope = heap.scope();
    obj = scope.alloc_object()?;
    cb = JobCallback::new(obj);
    weak = WeakGcObject::from(obj);
  }

  // Holding onto the `JobCallback` record must not keep the callback alive by itself.
  assert_eq!(cb.callback(), obj);
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);
  Ok(())
}

#[test]
fn job_callback_callback_can_be_rooted_by_host() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let obj;
  let cb;
  let weak;
  {
    let mut scope = heap.scope();
    obj = scope.alloc_object()?;
    cb = JobCallback::new(obj);
    weak = WeakGcObject::from(obj);
  }

  let root = heap.add_root(Value::Object(cb.callback()))?;
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), Some(obj));

  heap.remove_root(root);
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);

  Ok(())
}

#[derive(Default)]
struct CallbackRecordingHost {
  queue: VecDeque<Job>,
  calls: Vec<(u32, Value, Vec<Value>)>,
}

impl VmHostHooks for CallbackRecordingHost {
  fn host_enqueue_promise_job(&mut self, job: Job, _realm: Option<vm_js::RealmId>) {
    self.queue.push_back(job);
  }

  fn host_call_job_callback(
    &mut self,
    _ctx: &mut dyn VmJobContext,
    callback: &JobCallback,
    this_argument: Value,
    arguments: &[Value],
  ) -> Result<Value, VmError> {
    let callback_id = *callback
      .downcast_ref::<u32>()
      .expect("unexpected JobCallback payload type");
    self
      .calls
      .push((callback_id, this_argument, arguments.to_vec()));
    Ok(Value::Undefined)
  }
}

#[test]
fn job_can_invoke_host_call_job_callback() -> Result<(), VmError> {
  let mut ctx = RootingContext::default();
  let callback_obj = {
    let mut scope = ctx.heap.scope();
    scope.alloc_object()?
  };
  let callback = JobCallback::new_with_data(callback_obj, 42u32);
  let this_argument = Value::Null;
  let arguments = vec![Value::Bool(true), Value::Number(1.0)];
  let expected_arguments = arguments.clone();

  let mut job = Job::new(JobKind::Promise, move |ctx, host| {
    host.host_call_job_callback(ctx, &callback, this_argument, &arguments)?;
    Ok(())
  });
  // Ensure the callback stays live until the job runs.
  job.add_root(&mut ctx, Value::Object(callback_obj))?;

  let mut host = CallbackRecordingHost::default();
  host.host_enqueue_promise_job(job, None);

  while let Some(job) = host.queue.pop_front() {
    job.run(&mut ctx, &mut host)?;
  }

  assert_eq!(host.calls, vec![(42, this_argument, expected_arguments)]);
  Ok(())
}
