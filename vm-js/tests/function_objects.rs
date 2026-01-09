use vm_js::{
  Heap, HeapLimits, NativeFunctionId, PropertyDescriptor, PropertyKey, PropertyKind, Value, Vm,
  VmError, VmOptions,
};

#[test]
fn function_objects_support_prototype_and_properties() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let name = scope.alloc_string("f")?;
  let func = scope.alloc_native_function(NativeFunctionId(1), None, name, 0)?;
  scope.push_root(Value::Object(func));

  let proto = scope.alloc_object()?;
  scope.push_root(Value::Object(proto));

  scope
    .heap_mut()
    .object_set_prototype(func, Some(proto))?;
  assert_eq!(scope.heap().object_prototype(func)?, Some(proto));

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(
    func,
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

  assert_eq!(
    scope.heap().object_get_own_data_property_value(func, &key)?,
    Some(Value::Number(1.0))
  );
  Ok(())
}

#[test]
fn function_property_lookups_traverse_prototype_chain() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();
  let mut vm = Vm::new(VmOptions::default());

  let name = scope.alloc_string("f")?;
  let func = scope.alloc_native_function(NativeFunctionId(1), None, name, 0)?;
  scope.push_root(Value::Object(func));

  let proto = scope.alloc_object()?;
  scope.push_root(Value::Object(proto));

  scope
    .heap_mut()
    .object_set_prototype(func, Some(proto))?;

  let key = PropertyKey::from_string(scope.alloc_string("y")?);
  scope.define_property(
    proto,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(42.0),
        writable: true,
      },
    },
  )?;

  let found = scope.ordinary_get(&mut vm, func, key, Value::Object(func))?;
  assert_eq!(found, Value::Number(42.0));
  Ok(())
}
