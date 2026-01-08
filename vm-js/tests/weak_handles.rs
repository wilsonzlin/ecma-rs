use vm_js::{Heap, HeapLimits, Value, VmError, WeakGcObject};

#[test]
fn weak_handle_does_not_keep_object_live() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let weak;
  {
    let mut scope = heap.scope();
    let obj = scope.alloc_object()?;
    weak = WeakGcObject::from(obj);
    // `obj` is not rooted. Keeping a `WeakGcObject` must not keep it alive.
  }

  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);
  Ok(())
}

#[test]
fn weak_handle_upgrades_while_object_is_rooted() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let obj;
  let weak;
  let root;
  {
    let mut scope = heap.scope();
    obj = scope.alloc_object()?;
    weak = WeakGcObject::from(obj);
    root = scope.heap_mut().add_root(Value::Object(obj));
  }

  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), Some(obj));

  heap.remove_root(root);
  heap.collect_garbage();
  assert_eq!(weak.upgrade(&heap), None);

  Ok(())
}

