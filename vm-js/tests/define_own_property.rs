use vm_js::{
  Heap, HeapLimits, PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind, Value,
  VmError,
};

#[test]
fn non_configurable_property_cannot_flip_enumerable_or_configurable() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let (obj, key) = {
    let mut scope = heap.scope();
    let obj = scope.alloc_object()?;
    let key = PropertyKey::from_string(scope.alloc_string("x")?);
    scope.define_property(
      obj,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: false,
        kind: PropertyKind::Data {
          value: Value::Undefined,
          writable: true,
        },
      },
    )?;
    (obj, key)
  };

  assert!(!heap.define_own_property(
    obj,
    key,
    PropertyDescriptorPatch {
      configurable: Some(true),
      ..Default::default()
    },
  )?);
  assert!(!heap.define_own_property(
    obj,
    key,
    PropertyDescriptorPatch {
      enumerable: Some(false),
      ..Default::default()
    },
  )?);

  let desc = heap
    .object_get_own_property(obj, &key)?
    .expect("property should still exist");
  assert!(!desc.configurable);
  assert!(desc.enumerable);

  Ok(())
}

#[test]
fn non_writable_data_property_rejects_value_changes_and_writable_true() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let (obj, key) = {
    let mut scope = heap.scope();
    let obj = scope.alloc_object()?;
    let key = PropertyKey::from_string(scope.alloc_string("x")?);
    scope.define_property(
      obj,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: false,
        kind: PropertyKind::Data {
          value: Value::Number(1.0),
          writable: false,
        },
      },
    )?;
    (obj, key)
  };

  assert!(!heap.define_own_property(
    obj,
    key,
    PropertyDescriptorPatch {
      value: Some(Value::Number(2.0)),
      ..Default::default()
    },
  )?);
  assert!(!heap.define_own_property(
    obj,
    key,
    PropertyDescriptorPatch {
      writable: Some(true),
      ..Default::default()
    },
  )?);

  assert!(heap.define_own_property(
    obj,
    key,
    PropertyDescriptorPatch {
      value: Some(Value::Number(1.0)),
      ..Default::default()
    },
  )?);

  Ok(())
}

#[test]
fn non_configurable_accessor_rejects_getter_setter_changes() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let (obj, key, get1, get2) = {
    let mut scope = heap.scope();

    let get1 = scope.alloc_object()?;
    let get2 = scope.alloc_object()?;

    let obj = scope.alloc_object()?;
    let key = PropertyKey::from_string(scope.alloc_string("x")?);

    scope.define_property(
      obj,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: false,
        kind: PropertyKind::Accessor {
          get: Value::Object(get1),
          set: Value::Undefined,
        },
      },
    )?;

    (obj, key, get1, get2)
  };

  assert!(!heap.define_own_property(
    obj,
    key,
    PropertyDescriptorPatch {
      get: Some(Value::Object(get2)),
      ..Default::default()
    },
  )?);

  assert!(heap.define_own_property(
    obj,
    key,
    PropertyDescriptorPatch {
      get: Some(Value::Object(get1)),
      ..Default::default()
    },
  )?);

  Ok(())
}

#[test]
fn non_extensible_object_cannot_add_new_property() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let (obj, key) = {
    let mut scope = heap.scope();

    let obj = scope.alloc_object()?;
    scope.object_prevent_extensions(obj)?;

    let key = PropertyKey::from_string(scope.alloc_string("x")?);
    (obj, key)
  };

  assert!(!heap.define_own_property(obj, key, PropertyDescriptorPatch::default())?);
  assert!(heap.object_get_own_property(obj, &key)?.is_none());

  Ok(())
}

#[test]
fn defining_new_property_with_empty_patch_creates_default_data_descriptor() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let (obj, key) = {
    let mut scope = heap.scope();
    let obj = scope.alloc_object()?;
    let key = PropertyKey::from_string(scope.alloc_string("x")?);
    (obj, key)
  };

  assert!(heap.define_own_property(obj, key, PropertyDescriptorPatch::default())?);

  let desc = heap
    .object_get_own_property(obj, &key)?
    .expect("property should exist");

  assert!(!desc.enumerable);
  assert!(!desc.configurable);
  match desc.kind {
    PropertyKind::Data { value, writable } => {
      assert!(matches!(value, Value::Undefined));
      assert!(!writable);
    }
    PropertyKind::Accessor { .. } => panic!("expected a data property"),
  }

  Ok(())
}

#[test]
fn define_property_or_throw_throws_type_error_on_rejection() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let (obj, key) = {
    let mut scope = heap.scope();

    let obj = scope.alloc_object()?;
    scope.object_prevent_extensions(obj)?;

    let key = PropertyKey::from_string(scope.alloc_string("x")?);
    (obj, key)
  };

  let err = heap
    .define_property_or_throw(obj, key, PropertyDescriptorPatch::default())
    .unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));

  Ok(())
}
