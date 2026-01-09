use vm_js::{
  Heap, HeapLimits, PropertyDescriptorPatch, PropertyKey, PropertyKind, Value, Vm, VmError,
  VmOptions,
};

#[test]
fn ordinary_define_own_property_rejects_new_property_under_gc_without_panic() -> Result<(), VmError> {
  // Stress rooting: force a GC before each allocation.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  // Keep `obj` alive while allocating `key`.
  let obj_root = scope.heap_mut().add_root(Value::Object(obj))?;
  scope.object_prevent_extensions(obj)?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.heap_mut().remove_root(obj_root);

  let ok = scope.ordinary_define_own_property(obj, key, PropertyDescriptorPatch::default())?;
  assert!(!ok);
  Ok(())
}

#[test]
fn ordinary_set_roots_value_under_gc_without_panic() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  // Stress rooting: force a GC before each allocation.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  // Keep `obj` alive while allocating `key`/`value`.
  let obj_root = scope.heap_mut().add_root(Value::Object(obj))?;

  let key_s = scope.alloc_string("x")?;
  let key = PropertyKey::from_string(key_s);
  // Keep `key` alive so this test focuses on the rooting of `value`.
  let key_root = scope.heap_mut().add_root(Value::String(key_s))?;

  let value_s = scope.alloc_string("value")?;
  scope.heap_mut().remove_root(obj_root);

  let ok = scope.ordinary_set(&mut vm, obj, key, Value::String(value_s), Value::Object(obj))?;
  assert!(ok);

  let desc = scope
    .ordinary_get_own_property(obj, key)?
    .expect("property should exist");
  match desc.kind {
    PropertyKind::Data { value, .. } => assert_eq!(value, Value::String(value_s)),
    _ => panic!("expected data property"),
  }

  scope.heap_mut().remove_root(key_root);
  Ok(())
}

#[test]
fn ordinary_delete_missing_property_under_gc_without_panic() -> Result<(), VmError> {
  // Stress rooting: force a GC before each allocation.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  // Keep `obj` alive while allocating `key`.
  let obj_root = scope.heap_mut().add_root(Value::Object(obj))?;

  let key = PropertyKey::from_string(scope.alloc_string("missing")?);
  scope.heap_mut().remove_root(obj_root);

  let ok = scope.ordinary_delete(obj, key)?;
  assert!(ok);
  Ok(())
}

#[test]
fn array_define_own_property_roots_descriptor_value_under_gc_without_panic() -> Result<(), VmError> {
  // Stress rooting: force a GC before each allocation.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut scope = heap.scope();

  let array = scope.alloc_array(0)?;
  // Keep `array` alive while allocating `key`/`value`.
  let array_root = scope.heap_mut().add_root(Value::Object(array))?;

  let key_s = scope.alloc_string("0")?;
  let key = PropertyKey::from_string(key_s);
  // Keep `key` alive so this test focuses on the rooting of descriptor values.
  let key_root = scope.heap_mut().add_root(Value::String(key_s))?;

  let value_s = scope.alloc_string("value")?;
  scope.heap_mut().remove_root(array_root);

  let ok = scope.define_own_property(
    array,
    key,
    PropertyDescriptorPatch {
      value: Some(Value::String(value_s)),
      writable: Some(true),
      enumerable: Some(true),
      configurable: Some(true),
      ..Default::default()
    },
  )?;
  assert!(ok);

  let desc = scope
    .ordinary_get_own_property(array, key)?
    .expect("property should exist");
  match desc.kind {
    PropertyKind::Data { value, .. } => assert_eq!(value, Value::String(value_s)),
    _ => panic!("expected data property"),
  }

  scope.heap_mut().remove_root(key_root);
  Ok(())
}
