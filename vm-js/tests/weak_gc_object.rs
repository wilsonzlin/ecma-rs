use vm_js::{Heap, HeapLimits, Value, VmError, WeakGcObject};

#[test]
fn weak_gc_object_upgrade_reflects_liveness() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let weak: WeakGcObject;
  {
    let mut scope = heap.scope();
    let obj = scope.alloc_object()?;
    scope.push_root(Value::Object(obj))?;

    weak = WeakGcObject::from(obj);
    assert!(weak.upgrade(scope.heap()).is_some());

    scope.heap_mut().collect_garbage();
    assert!(weak.upgrade(scope.heap()).is_some());
  }

  // Once the stack roots are popped, a GC cycle should collect the wrapper.
  heap.collect_garbage();
  assert!(weak.upgrade(&heap).is_none());

  // Stale weak handles stay stale even if the slot is later reused.
  let _reused = {
    let mut scope = heap.scope();
    scope.alloc_object()?
  };
  assert!(weak.upgrade(&heap).is_none());

  Ok(())
}
