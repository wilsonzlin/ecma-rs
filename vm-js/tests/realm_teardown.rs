use vm_js::{Heap, HeapLimits, Realm, VmError};

#[test]
fn realm_teardown_unregisters_persistent_roots() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut heap)?;

  let global = realm.global_object();
  let object_proto = realm.intrinsics().object_prototype();
  let array_proto = realm.intrinsics().array_prototype();

  // Before teardown, the realm's persistent roots keep the allocations alive across GCs.
  heap.collect_garbage();
  assert!(heap.is_valid_object(global));
  assert!(heap.is_valid_object(object_proto));
  assert!(heap.is_valid_object(array_proto));

  realm.teardown(&mut heap);
  // Teardown is idempotent.
  realm.teardown(&mut heap);

  heap.collect_garbage();
  assert!(!heap.is_valid_object(global));
  assert!(!heap.is_valid_object(object_proto));
  assert!(!heap.is_valid_object(array_proto));

  Ok(())
}

