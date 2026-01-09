use vm_js::{Heap, HeapLimits, HostSlots, VmError};

#[test]
fn set_and_get_host_slots_on_live_object() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let mut scope = heap.scope();
  let obj = scope.alloc_object()?;

  let slots = HostSlots { a: 1, b: 2 };
  scope.heap_mut().object_set_host_slots(obj, slots)?;
  assert_eq!(scope.heap().object_host_slots(obj)?, Some(slots));

  Ok(())
}

#[test]
fn host_slots_cleared_on_gc_and_reuse() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let old_obj = {
    let mut scope = heap.scope();
    let obj = scope.alloc_object()?;
    scope
      .heap_mut()
      .object_set_host_slots(obj, HostSlots { a: 123, b: 456 })?;
    obj
  };

  let old_index = old_obj.index();
  let old_generation = old_obj.generation();

  // `old_obj` is not rooted; it should be collected.
  heap.collect_garbage();
  assert!(
    !heap.is_valid_object(old_obj),
    "expected old object to be collected"
  );

  // Allocate until we observe the old slot index being reused.
  let mut new_obj = None;
  {
    let mut scope = heap.scope();
    for _ in 0..32 {
      let obj = scope.alloc_object()?;
      if obj.index() == old_index {
        new_obj = Some(obj);
        break;
      }
    }
  }

  let new_obj = new_obj.expect(
    "expected allocator to eventually reuse freed slot index; \
     if this fails, allocator behaviour may have changed",
  );

  assert_ne!(
    new_obj.generation(),
    old_generation,
    "expected slot generation to change on reuse"
  );
  assert_eq!(heap.object_host_slots(new_obj)?, None);

  Ok(())
}

