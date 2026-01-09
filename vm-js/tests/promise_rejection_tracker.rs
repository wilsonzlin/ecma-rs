use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::JobQueue;
use vm_js::PromiseHandle;
use vm_js::PromiseRejectionOperation;
use vm_js::RootedMicrotaskJob;

#[derive(Default)]
struct RecordingHost {
  calls: Vec<(PromiseHandle, PromiseRejectionOperation)>,
}

impl JobQueue<()> for RecordingHost {
  fn enqueue_microtask(&mut self, _job: RootedMicrotaskJob<()>) {
    // Not needed for this test.
  }

  fn host_promise_rejection_tracker(
    &mut self,
    promise: PromiseHandle,
    operation: PromiseRejectionOperation,
  ) {
    self.calls.push((promise, operation));
  }
}

#[test]
fn promise_rejection_tracker_api_surface_is_usable() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut scope = heap.scope();

  let p1 = PromiseHandle::from(scope.alloc_object().unwrap());
  let p2 = PromiseHandle::from(scope.alloc_object().unwrap());

  let mut host = RecordingHost::default();

  host.host_promise_rejection_tracker(p1, PromiseRejectionOperation::Reject);
  host.host_promise_rejection_tracker(p2, PromiseRejectionOperation::Reject);
  host.host_promise_rejection_tracker(p1, PromiseRejectionOperation::Handle);

  assert_eq!(
    host.calls,
    vec![
      (p1, PromiseRejectionOperation::Reject),
      (p2, PromiseRejectionOperation::Reject),
      (p1, PromiseRejectionOperation::Handle),
    ]
  );
}
