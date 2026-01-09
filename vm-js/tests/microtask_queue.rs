use std::sync::Arc;
use std::sync::Mutex;

use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::JobKind;
use vm_js::MicrotaskQueue;
use vm_js::RootedJob;
use vm_js::Value;
use vm_js::VmError;
use vm_js::VmJobContext;

#[derive(Default)]
struct TestContext;

impl VmJobContext for TestContext {}

#[test]
fn microtask_queue_runs_promise_jobs_in_fifo_order() {
  let sink: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));

  let mut queue: MicrotaskQueue<RootedJob> = MicrotaskQueue::new();
  for i in 1..=3u8 {
    let sink = sink.clone();
    queue.enqueue(RootedJob::new(JobKind::Promise, move |_ctx, _host| {
      sink.lock().unwrap().push(i);
      Ok(())
    }));
  }

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut ctx = TestContext::default();

  let errors = queue.perform_microtask_checkpoint(&mut heap, &mut ctx);
  assert!(errors.is_empty());
  assert!(queue.is_empty());
  assert_eq!(&*sink.lock().unwrap(), &[1, 2, 3]);
}

#[test]
fn microtask_queue_drains_until_empty_including_nested_enqueues() {
  let sink: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));

  let mut queue: MicrotaskQueue<RootedJob> = MicrotaskQueue::new();
  {
    let sink = sink.clone();
    queue.enqueue(RootedJob::new(JobKind::Promise, move |_ctx, host| {
      sink.lock().unwrap().push(1);

      let sink = sink.clone();
      host.host_enqueue_promise_job(
        RootedJob::new(JobKind::Promise, move |_ctx, _host| {
          sink.lock().unwrap().push(2);
          Ok(())
        }),
        None,
      );

      Ok(())
    }));
  }

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut ctx = TestContext::default();

  let errors = queue.perform_microtask_checkpoint(&mut heap, &mut ctx);
  assert!(errors.is_empty());
  assert!(queue.is_empty());
  assert_eq!(&*sink.lock().unwrap(), &[1, 2]);
}

#[test]
fn microtask_checkpoint_continues_after_errors() {
  let sink: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));

  let mut queue: MicrotaskQueue<RootedJob> = MicrotaskQueue::new();
  queue.enqueue(RootedJob::new(JobKind::Promise, |_ctx, _host| {
    Err(VmError::Unimplemented("microtask failure"))
  }));
  {
    let sink = sink.clone();
    queue.enqueue(RootedJob::new(JobKind::Promise, move |_ctx, _host| {
      sink.lock().unwrap().push(1);
      Ok(())
    }));
  }

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut ctx = TestContext::default();

  let errors = queue.perform_microtask_checkpoint(&mut heap, &mut ctx);
  assert_eq!(errors.len(), 1);
  assert!(queue.is_empty());
  assert_eq!(&*sink.lock().unwrap(), &[1]);
}

#[test]
fn drain_and_cancel_removes_persistent_roots() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));

  let obj = {
    let mut scope = heap.scope();
    scope.alloc_object().unwrap()
  };

  let mut queue: MicrotaskQueue<RootedJob> = MicrotaskQueue::new();
  queue.enqueue(RootedJob::new_rooted(
    &mut heap,
    [Value::Object(obj)],
    JobKind::Promise,
    |_ctx, _host| Ok(()),
  ));

  // The queued microtask's persistent root keeps the object alive across GC.
  heap.collect_garbage();
  assert!(heap.is_valid_object(obj));

  queue.drain_and_cancel(&mut heap);
  assert!(queue.is_empty());

  // After cancellation + GC, the object should be collectable.
  heap.collect_garbage();
  assert!(!heap.is_valid_object(obj));
}

