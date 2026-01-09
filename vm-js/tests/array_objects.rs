use vm_js::{
  Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Value, VmError,
};

fn data_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

#[test]
fn array_length_updates_on_index_definitions() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let a = scope.alloc_array(0)?;
  scope.push_root(Value::Object(a));

  let length_key = PropertyKey::from_string(scope.alloc_string("length")?);
  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(a, &length_key)?
      .expect("array should have a length data property"),
    Value::Number(0.0)
  );

  // a[0]
  let k0 = PropertyKey::from_string(scope.alloc_string("0")?);
  scope.define_property(a, k0, data_desc(Value::Null))?;
  let length_key = PropertyKey::from_string(scope.alloc_string("length")?);
  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(a, &length_key)?
      .expect("array length should exist"),
    Value::Number(1.0)
  );

  // a[5]
  let k5 = PropertyKey::from_string(scope.alloc_string("5")?);
  scope.define_property(a, k5, data_desc(Value::Bool(true)))?;
  let length_key = PropertyKey::from_string(scope.alloc_string("length")?);
  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(a, &length_key)?
      .expect("array length should exist"),
    Value::Number(6.0)
  );

  Ok(())
}

#[test]
fn own_property_keys_orders_array_indices_first() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let a = scope.alloc_array(0)?;
  scope.push_root(Value::Object(a));

  // Define out of order; `own_property_keys` should sort indices.
  let k5 = PropertyKey::from_string(scope.alloc_string("5")?);
  scope.define_property(a, k5, data_desc(Value::Null))?;
  let k0 = PropertyKey::from_string(scope.alloc_string("0")?);
  scope.define_property(a, k0, data_desc(Value::Null))?;

  let keys = scope.heap().own_property_keys(a)?;
  let mut names = Vec::new();
  for k in keys {
    match k {
      PropertyKey::String(s) => names.push(scope.heap().get_string(s)?.to_utf8_lossy()),
      PropertyKey::Symbol(_) => names.push("<symbol>".to_string()),
    }
  }

  assert_eq!(names, vec!["0", "5", "length"]);
  Ok(())
}

