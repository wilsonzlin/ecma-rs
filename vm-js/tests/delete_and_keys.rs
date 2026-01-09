use vm_js::{
  Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Value, VmError,
};

fn enumerable_configurable_data(value: Value) -> PropertyDescriptor {
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
fn ordinary_delete_configurable_removes_property_and_updates_used_bytes() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(obj, key, enumerable_configurable_data(Value::Null))?;

  let used_bytes_before_delete = scope.heap().used_bytes();
  assert!(scope.heap_mut().ordinary_delete(obj, key)?);
  let used_bytes_after_delete = scope.heap().used_bytes();

  assert!(
    used_bytes_after_delete < used_bytes_before_delete,
    "expected heap.used_bytes to decrease after deleting a configurable property (before={used_bytes_before_delete}, after={used_bytes_after_delete})"
  );

  assert!(scope.heap().get_own_property(obj, key)?.is_none());
  Ok(())
}

#[test]
fn ordinary_delete_non_configurable_returns_false_and_keeps_property() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));

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

  assert!(!scope.heap_mut().ordinary_delete(obj, key)?);
  assert!(scope.heap().get_own_property(obj, key)?.is_some());
  Ok(())
}

#[test]
fn ordinary_own_property_keys_orders_indices_strings_and_symbols() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));

  let k_2 = PropertyKey::from_string(scope.alloc_string("2")?);
  let k_1 = PropertyKey::from_string(scope.alloc_string("1")?);
  let k_b = PropertyKey::from_string(scope.alloc_string("b")?);
  let sym_a = scope.alloc_symbol(Some("symA"))?;
  let k_sym_a = PropertyKey::from_symbol(sym_a);
  let k_a = PropertyKey::from_string(scope.alloc_string("a")?);
  let sym_b = scope.alloc_symbol(Some("symB"))?;
  let k_sym_b = PropertyKey::from_symbol(sym_b);

  // Define properties in order: ["2", "1", "b", symA, "a", symB]
  scope.define_property(obj, k_2, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_1, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_b, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_sym_a, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_a, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_sym_b, enumerable_configurable_data(Value::Null))?;

  let keys = scope.heap().ordinary_own_property_keys(obj)?;
  assert_eq!(keys, vec![k_1, k_2, k_b, k_a, k_sym_a, k_sym_b]);
  Ok(())
}

#[test]
fn ordinary_own_property_keys_array_index_edge_cases() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));

  let k_00 = PropertyKey::from_string(scope.alloc_string("00")?);
  let k_max_minus_1 = PropertyKey::from_string(scope.alloc_string("4294967294")?);
  let k_max = PropertyKey::from_string(scope.alloc_string("4294967295")?);
  let k_0 = PropertyKey::from_string(scope.alloc_string("0")?);

  // Define in order: ["00", "4294967294", "4294967295", "0"].
  scope.define_property(obj, k_00, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_max_minus_1, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_max, enumerable_configurable_data(Value::Null))?;
  scope.define_property(obj, k_0, enumerable_configurable_data(Value::Null))?;

  // Array indices: "0" and "4294967294"; others are non-index strings.
  let keys = scope.heap().ordinary_own_property_keys(obj)?;
  assert_eq!(keys, vec![k_0, k_max_minus_1, k_00, k_max]);
  Ok(())
}

