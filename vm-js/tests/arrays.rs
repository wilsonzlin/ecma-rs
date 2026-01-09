use vm_js::{GcObject, Heap, HeapLimits, PropertyDescriptorPatch, PropertyKey, Value, VmError};

fn data_patch(value: Value) -> PropertyDescriptorPatch {
  PropertyDescriptorPatch {
    value: Some(value),
    writable: Some(true),
    enumerable: Some(true),
    configurable: Some(true),
    ..Default::default()
  }
}

fn length_key(scope: &mut vm_js::Scope<'_>) -> Result<PropertyKey, VmError> {
  Ok(PropertyKey::from_string(scope.alloc_string("length")?))
}

fn get_length(scope: &vm_js::Scope<'_>, array: GcObject, key: PropertyKey) -> Result<Value, VmError> {
  Ok(
    scope
      .heap()
      .object_get_own_data_property_value(array, &key)?
      .expect("array should have a length data property"),
  )
}

#[test]
fn defining_indices_updates_length() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let array = scope.alloc_array(0)?;
  scope.push_root(Value::Object(array))?;

  let k0 = PropertyKey::from_string(scope.alloc_string("0")?);
  assert!(scope.define_own_property(array, k0, data_patch(Value::Null))?);

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(1.0));

  let k10 = PropertyKey::from_string(scope.alloc_string("10")?);
  assert!(scope.define_own_property(array, k10, data_patch(Value::Bool(true)))?);

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(11.0));
  Ok(())
}

#[test]
fn shrinking_length_deletes_elements() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let array = scope.alloc_array(0)?;
  scope.push_root(Value::Object(array))?;

  for i in 0..5u32 {
    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    let ok = scope.create_data_property(array, key, Value::Number(i as f64))?;
    assert!(ok);
  }

  let len_key = length_key(&mut scope)?;
  let ok = scope.define_own_property(
    array,
    len_key,
    PropertyDescriptorPatch {
      value: Some(Value::Number(2.0)),
      ..Default::default()
    },
  )?;
  assert!(ok);

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(2.0));

  for i in 2..5u32 {
    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    assert!(scope.heap().object_get_own_property(array, &key)?.is_none());
  }

  Ok(())
}

#[test]
fn shrinking_length_fails_if_non_configurable_element_blocks_deletion() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let array = scope.alloc_array(0)?;
  scope.push_root(Value::Object(array))?;

  // Create a non-configurable element at index 3 (so old length becomes 4).
  for i in 0..3u32 {
    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    let ok = scope.create_data_property(array, key, Value::Number(i as f64))?;
    assert!(ok);
  }
  let k3 = PropertyKey::from_string(scope.alloc_string("3")?);
  let ok = scope.define_own_property(
    array,
    k3,
    PropertyDescriptorPatch {
      value: Some(Value::Null),
      writable: Some(true),
      enumerable: Some(true),
      configurable: Some(false),
      ..Default::default()
    },
  )?;
  assert!(ok);

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(4.0));

  // Attempt to shrink length below the non-configurable element: should fail and keep length.
  let len_key = length_key(&mut scope)?;
  let ok = scope.define_own_property(
    array,
    len_key,
    PropertyDescriptorPatch {
      value: Some(Value::Number(2.0)),
      ..Default::default()
    },
  )?;
  assert!(!ok);

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(4.0));

  let k3 = PropertyKey::from_string(scope.alloc_string("3")?);
  assert!(scope.heap().object_get_own_property(array, &k3)?.is_some());

  Ok(())
}

#[test]
fn non_writable_length_blocks_extension() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let array = scope.alloc_array(0)?;
  scope.push_root(Value::Object(array))?;

  for i in 0..2u32 {
    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    let ok = scope.create_data_property(array, key, Value::Bool(true))?;
    assert!(ok);
  }

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(2.0));

  // Make length non-writable.
  let len_key = length_key(&mut scope)?;
  let ok = scope.define_own_property(
    array,
    len_key,
    PropertyDescriptorPatch {
      writable: Some(false),
      ..Default::default()
    },
  )?;
  assert!(ok);

  // Defining an index >= length must fail.
  let k2 = PropertyKey::from_string(scope.alloc_string("2")?);
  let ok = scope.define_own_property(array, k2, data_patch(Value::Null))?;
  assert!(!ok);

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(2.0));

  let k2 = PropertyKey::from_string(scope.alloc_string("2")?);
  assert!(scope.heap().object_get_own_property(array, &k2)?.is_none());

  Ok(())
}

#[test]
fn invalid_length_value_is_rejected() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let array = scope.alloc_array(0)?;
  scope.push_root(Value::Object(array))?;

  let len_key = length_key(&mut scope)?;
  let ok = scope.define_own_property(
    array,
    len_key,
    PropertyDescriptorPatch {
      value: Some(Value::Number(3.5)),
      ..Default::default()
    },
  )?;
  assert!(!ok);

  let len_key = length_key(&mut scope)?;
  assert_eq!(get_length(&scope, array, len_key)?, Value::Number(0.0));
  Ok(())
}
