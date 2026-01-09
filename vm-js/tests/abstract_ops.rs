use vm_js::{
  create_data_property_or_throw, define_property_or_throw, delete_property_or_throw, get_method,
  Heap, HeapLimits, PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind, Value,
  Vm, VmError, VmOptions,
};

#[test]
fn create_data_property_or_throw_throws_on_non_extensible_object() -> Result<(), VmError> {
  // Stress rooting: force a GC before each allocation.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope.object_prevent_extensions(obj)?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  let err = create_data_property_or_throw(&mut scope, obj, key, Value::Number(1.0)).unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));
  Ok(())
}

#[test]
fn delete_property_or_throw_throws_on_non_configurable_property() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(
    obj,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: false,
      kind: PropertyKind::Data {
        value: Value::Null,
        writable: true,
      },
    },
  )?;

  let err = delete_property_or_throw(&mut scope, obj, key).unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));
  Ok(())
}

#[test]
fn define_property_or_throw_throws_on_non_extensible_object_under_gc() -> Result<(), VmError> {
  // Stress rooting: force a GC before each allocation.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope.object_prevent_extensions(obj)?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  let err = define_property_or_throw(&mut scope, obj, key, PropertyDescriptorPatch::default()).unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));
  Ok(())
}

#[test]
fn delete_property_or_throw_succeeds_for_missing_property_under_gc() -> Result<(), VmError> {
  // Stress rooting: force a GC before each allocation.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  let key = PropertyKey::from_string(scope.alloc_string("missing")?);
  delete_property_or_throw(&mut scope, obj, key)?;
  Ok(())
}

#[test]
fn get_method_returns_none_for_undefined() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  let key = PropertyKey::from_string(scope.alloc_string("m")?);
  let got = get_method(&mut vm, &mut scope, Value::Object(obj), key)?;
  assert_eq!(got, None);
  Ok(())
}

#[test]
fn get_method_throws_type_error_for_non_callable() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  let key = PropertyKey::from_string(scope.alloc_string("m")?);
  scope.define_property(
    obj,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(1.0),
        writable: true,
      },
    },
  )?;

  let err = get_method(&mut vm, &mut scope, Value::Object(obj), key).unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));
  Ok(())
}

#[test]
fn get_method_on_non_object_is_unimplemented_for_now() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let key = PropertyKey::from_string(scope.alloc_string("m")?);
  let err = get_method(&mut vm, &mut scope, Value::Number(1.0), key).unwrap_err();
  assert!(matches!(
    err,
    VmError::Unimplemented("GetMethod on non-object")
  ));
  Ok(())
}
