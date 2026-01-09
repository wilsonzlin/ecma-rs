use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::Mutex;

use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::Job;
use vm_js::JobCallback;
use vm_js::JobKind;
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

impl VmJobContext for TestContext {}

fn enqueue_three_jobs(host: &mut dyn VmHostHooks, sink: Arc<Mutex<Vec<u8>>>) {
  for i in 1..=3u8 {
    let sink = sink.clone();
    host.host_enqueue_promise_job(
      Job::new(JobKind::Promise, move |_ctx| {
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
    job.run(&mut ctx).unwrap();
  }

  assert_eq!(&*sink.lock().unwrap(), &[1, 2, 3]);
}

#[test]
fn host_call_job_callback_stub_is_present_and_object_safe() -> Result<(), VmError> {
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
    Err(VmError::Unimplemented("HostCallJobCallback"))
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

  let root = heap.add_root(Value::Object(cb.callback()));
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), Some(obj));

  heap.remove_root(root);
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);

  Ok(())
}
