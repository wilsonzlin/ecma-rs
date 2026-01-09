use std::sync::Arc;
use std::sync::Mutex;

use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::Job;
use vm_js::JobKind;
use vm_js::MicrotaskQueue;
use vm_js::RootId;
use vm_js::Value;
use vm_js::VmError;
use vm_js::VmHostHooks;
use vm_js::VmJobContext;
use vm_js::WeakGcObject;

struct TestContext {
  heap: Heap,
}

impl TestContext {
  fn new() -> Self {
    Self {
      heap: Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024)),
    }
  }
}

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

  fn add_root(&mut self, value: Value) -> Result<RootId, VmError> {
    self.heap.add_root(value)
  }

  fn remove_root(&mut self, id: RootId) {
    self.heap.remove_root(id);
  }
}

#[test]
fn fifo_ordering_is_preserved() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut queue = MicrotaskQueue::new();

  let sink: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));
  for i in 1..=3u8 {
    let sink = sink.clone();
    queue.enqueue_promise_job(
      Job::new(JobKind::Promise, move |_ctx, _host| {
        sink.lock().unwrap().push(i);
        Ok(())
      }),
      None,
    );
  }

  let errors = queue.perform_microtask_checkpoint(&mut ctx);
  assert!(errors.is_empty());
  assert_eq!(&*sink.lock().unwrap(), &[1, 2, 3]);
  Ok(())
}

#[test]
fn microtasks_queued_by_microtasks_run_in_the_same_checkpoint() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut queue = MicrotaskQueue::new();

  let sink: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));
  let sink_for_job1 = sink.clone();

  queue.enqueue_promise_job(
    Job::new(JobKind::Promise, move |_ctx, host| {
      sink_for_job1.lock().unwrap().push(1);

      let sink_for_job2 = sink_for_job1.clone();
      host.host_enqueue_promise_job(
        Job::new(JobKind::Promise, move |_ctx, _host| {
          sink_for_job2.lock().unwrap().push(2);
          Ok(())
        }),
        None,
      );

      Ok(())
    }),
    None,
  );

  let errors = queue.perform_microtask_checkpoint(&mut ctx);
  assert!(errors.is_empty());
  assert_eq!(&*sink.lock().unwrap(), &[1, 2]);
  Ok(())
}

#[test]
fn microtask_checkpoint_reentrancy_guard_prevents_recursion() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut queue = MicrotaskQueue::new();

  let log: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));
  let log_for_job1 = log.clone();
  let log_for_job2 = log.clone();

  let job2 = Job::new(JobKind::Promise, move |_ctx, _host| {
    log_for_job2.lock().unwrap().push("job2");
    Ok(())
  });

  queue.enqueue_promise_job(
    Job::new(JobKind::Promise, move |ctx, host| {
      log_for_job1.lock().unwrap().push("job1");

      host.host_enqueue_promise_job(job2, None);

      // Attempt to recurse into another microtask checkpoint while already in one. The nested
      // checkpoint must be a no-op: `job2` should run only after `job1` finishes.
      let Some(any) = host.as_any_mut() else {
        return Err(VmError::Unimplemented("VmHostHooks::as_any_mut"));
      };
      let queue = any
        .downcast_mut::<MicrotaskQueue>()
        .ok_or(VmError::Unimplemented("downcast MicrotaskQueue"))?;
      let errors = queue.perform_microtask_checkpoint(ctx);
      assert!(errors.is_empty());

      log_for_job1.lock().unwrap().push("job1_after");
      Ok(())
    }),
    None,
  );

  let errors = queue.perform_microtask_checkpoint(&mut ctx);
  assert!(errors.is_empty());

  assert_eq!(
    &*log.lock().unwrap(),
    // If the reentrancy guard is working, `job2` runs only after `job1` returns.
    &["job1", "job1_after", "job2"],
  );
  Ok(())
}

#[test]
fn jobs_keep_values_alive_until_run_when_rooted() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut queue = MicrotaskQueue::new();

  let obj = {
    let mut scope = ctx.heap.scope();
    scope.alloc_object()?
  };
  let weak = WeakGcObject::from(obj);

  let mut job = Job::new(JobKind::Promise, |_ctx, _host| Ok(()));
  job.add_root(&mut ctx, Value::Object(obj))?;

  queue.enqueue_promise_job(job, None);

  // The queued job holds a persistent root, so a GC cycle should not collect the object.
  ctx.heap.collect_garbage();
  assert_eq!(weak.upgrade(&ctx.heap), Some(obj));

  let errors = queue.perform_microtask_checkpoint(&mut ctx);
  assert!(errors.is_empty());

  // After the job runs its roots are removed, so the object becomes collectible.
  ctx.heap.collect_garbage();
  assert_eq!(weak.upgrade(&ctx.heap), None);

  Ok(())
}

#[test]
fn checkpoint_continues_after_errors_and_collects_them() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut queue = MicrotaskQueue::new();

  let log: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));
  let log_for_ok = log.clone();

  queue.enqueue_promise_job(
    Job::new(JobKind::Promise, |_ctx, _host| Err(VmError::Unimplemented("job1 failed"))),
    None,
  );

  queue.enqueue_promise_job(
    Job::new(JobKind::Promise, move |_ctx, _host| {
      log_for_ok.lock().unwrap().push("job2");
      Ok(())
    }),
    None,
  );

  queue.enqueue_promise_job(
    Job::new(JobKind::Promise, |_ctx, _host| Err(VmError::Unimplemented("job3 failed"))),
    None,
  );

  let errors = queue.perform_microtask_checkpoint(&mut ctx);
  assert_eq!(errors.len(), 2);
  assert!(matches!(errors[0], VmError::Unimplemented("job1 failed")));
  assert!(matches!(errors[1], VmError::Unimplemented("job3 failed")));
  assert_eq!(&*log.lock().unwrap(), &["job2"]);
  Ok(())
}

#[test]
fn cancel_all_discards_jobs_and_unregisters_roots() -> Result<(), VmError> {
  let mut ctx = TestContext::new();
  let mut queue = MicrotaskQueue::new();

  let obj = {
    let mut scope = ctx.heap.scope();
    scope.alloc_object()?
  };
  let weak = WeakGcObject::from(obj);

  let mut job = Job::new(JobKind::Promise, |_ctx, _host| Ok(()));
  job.add_root(&mut ctx, Value::Object(obj))?;
  queue.enqueue_promise_job(job, None);

  // The job's persistent root keeps the object alive while the job is pending.
  ctx.heap.collect_garbage();
  assert_eq!(weak.upgrade(&ctx.heap), Some(obj));

  queue.cancel_all(&mut ctx);
  assert!(queue.is_empty());

  ctx.heap.collect_garbage();
  assert_eq!(weak.upgrade(&ctx.heap), None);
  Ok(())
}
