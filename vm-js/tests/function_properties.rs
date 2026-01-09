use vm_js::{
  Heap, HeapLimits, NativeFunctionId, PropertyDescriptor, PropertyKey, PropertyKind, Value, VmError,
};

#[test]
fn native_function_objects_support_own_properties() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let func;
  let child;
  let dead;
  let key_string;
  let key;
  {
    let mut scope = heap.scope();

    let name = scope.alloc_string("f")?;
    func = scope.alloc_native_function(NativeFunctionId(1), None, name, 0)?;
    scope.push_root(Value::Object(func));

    child = scope.alloc_object()?;
    dead = scope.alloc_object()?;

    key_string = scope.alloc_string("x")?;
    key = PropertyKey::from_string(key_string);

    scope.define_property(
      func,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Object(child),
          writable: true,
        },
      },
    )?;

    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_object(func));
    assert!(
      scope.heap().is_valid_object(child),
      "child should survive via function property"
    );
    assert!(!scope.heap().is_valid_object(dead), "dead should be collected");

    assert_eq!(scope.heap().get_string(key_string)?.to_utf8_lossy(), "x");
    assert_eq!(
      scope
        .heap()
        .object_get_own_data_property_value(func, &key)?,
      Some(Value::Object(child))
    );
  }

  Ok(())
}

