use vm_js::{
  AboutToBeNotifiedBatch, Heap, HeapLimits, PromiseHandle, PromiseRejectionHandleAction,
  PromiseRejectionTracker, WeakGcObject,
};

fn new_test_heap() -> Heap {
  Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024))
}

#[test]
fn about_to_be_notified_roots_until_batch_teardown() {
  let mut heap = new_test_heap();

  let promise: PromiseHandle;
  let weak: WeakGcObject;
  {
    let mut scope = heap.scope();
    let obj = scope.alloc_object().unwrap();
    promise = PromiseHandle::from(obj);
    weak = WeakGcObject::from(obj);
  }

  let mut tracker = PromiseRejectionTracker::new();
  tracker.on_reject(&mut heap, promise);

  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), Some(promise.into()));

  let batch = tracker.drain_about_to_be_notified(&mut heap);
  assert_eq!(batch.promises(), &[promise]);

  // The drained batch must keep the promise alive until teardown.
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), Some(promise.into()));

  batch.teardown(&mut heap);

  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);
}

#[test]
fn on_handle_removes_from_about_to_be_notified_without_queueing_rejectionhandled() {
  let mut heap = new_test_heap();

  let promise: PromiseHandle;
  let weak: WeakGcObject;
  {
    let mut scope = heap.scope();
    let obj = scope.alloc_object().unwrap();
    promise = PromiseHandle::from(obj);
    weak = WeakGcObject::from(obj);
  }

  let mut tracker = PromiseRejectionTracker::new();
  tracker.on_reject(&mut heap, promise);

  let action = tracker.on_handle(&mut heap, promise);
  assert_eq!(action, PromiseRejectionHandleAction::None);

  let batch: AboutToBeNotifiedBatch = tracker.drain_about_to_be_notified(&mut heap);
  assert!(batch.promises().is_empty());
  batch.teardown(&mut heap);

  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);
}

#[test]
fn outstanding_rejected_promises_is_weak_and_drives_rejectionhandled_queueing() {
  let mut heap = new_test_heap();

  let promise: PromiseHandle;
  let weak: WeakGcObject;
  {
    let mut scope = heap.scope();
    let obj = scope.alloc_object().unwrap();
    promise = PromiseHandle::from(obj);
    weak = WeakGcObject::from(obj);
  }

  let mut tracker = PromiseRejectionTracker::new();

  tracker.after_unhandledrejection_dispatch(promise, false);

  // A handled signal should request queueing `rejectionhandled` and remove it from outstanding.
  let action = tracker.on_handle(&mut heap, promise);
  assert_eq!(
    action,
    PromiseRejectionHandleAction::QueueRejectionHandled { promise }
  );

  // If it's handled again, nothing happens (it was removed from the outstanding set).
  assert_eq!(
    tracker.on_handle(&mut heap, promise),
    PromiseRejectionHandleAction::None
  );

  // The outstanding weak set must not keep promises alive.
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);
}

