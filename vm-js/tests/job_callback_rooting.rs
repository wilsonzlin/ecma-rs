use vm_js::{
  GcObject, Heap, HeapLimits, Job, JobKind, JobResult, RootId, Value, VmError, VmHostHooks,
  VmJobContext,
};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Default)]
struct TestHost;

impl VmHostHooks for TestHost {
  fn host_enqueue_promise_job(&mut self, _job: Job, _realm: Option<vm_js::RealmId>) {
    // Not needed for these tests.
  }
}

struct HeapBackedContext {
  heap: Rc<RefCell<Heap>>,
}

impl VmJobContext for HeapBackedContext {
  fn call(&mut self, _callee: Value, _this: Value, _args: &[Value]) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("HeapBackedContext::call"))
  }

  fn construct(
    &mut self,
    _callee: Value,
    _args: &[Value],
    _new_target: Value,
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("HeapBackedContext::construct"))
  }

  fn add_root(&mut self, value: Value) -> RootId {
    self.heap.borrow_mut().add_root(value)
  }

  fn remove_root(&mut self, id: RootId) {
    self.heap.borrow_mut().remove_root(id)
  }
}

#[test]
fn job_callback_payload_is_not_a_gc_root() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut host = TestHost::default();

  let callback_obj: GcObject = {
    let mut scope = heap.scope();
    scope.alloc_object()?
  };

  // The default `host_make_job_callback` stores a raw `GcObject` inside a `JobCallback`, but this is
  // host-owned data and is not traced by GC.
  let job_callback = host.host_make_job_callback(callback_obj);

  // With no other roots, a GC cycle should reclaim the object even though the `JobCallback` still
  // holds a handle to it.
  heap.collect_garbage();
  assert!(!heap.is_valid_object(callback_obj));

  // The record still contains the stale handle (demonstrating the pitfall).
  let stored = job_callback.callback();
  assert_eq!(stored, callback_obj);
  assert!(!heap.is_valid_object(stored));

  Ok(())
}

#[test]
fn job_roots_callback_until_run_then_releases() -> Result<(), VmError> {
  let heap = Rc::new(RefCell::new(Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024))));
  let mut host = TestHost::default();
  let mut ctx = HeapBackedContext { heap: heap.clone() };

  let callback_obj = {
    let mut heap_mut = heap.borrow_mut();
    let mut scope = heap_mut.scope();
    scope.alloc_object()?
  };
  let job_callback = host.host_make_job_callback(callback_obj);

  // Create a job that captures the JobCallback (and therefore the raw callback handle).
  let mut job = Job::new(
    JobKind::Generic,
    move |_ctx: &mut dyn VmJobContext, _host: &mut dyn VmHostHooks| -> JobResult {
      // We don't actually call the callback here; the test is about rooting/handle validity.
      let stored = job_callback.callback();
      let _ = stored;
      Ok(())
    },
  );

  // Correct pattern: when queueing work that will later observe/call the callback, root the
  // callback object for the lifetime of the queued job.
  job.add_root(&mut ctx, Value::Object(callback_obj));

  heap.borrow_mut().collect_garbage();
  assert!(
    heap.borrow().is_valid_object(callback_obj),
    "callback object should stay alive while the job is queued"
  );

  job.run(&mut ctx, &mut host)?;

  heap.borrow_mut().collect_garbage();
  assert!(
    !heap.borrow().is_valid_object(callback_obj),
    "callback object should become collectable after the queued job runs and releases its roots"
  );

  Ok(())
}
