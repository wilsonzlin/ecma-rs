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
  scope.push_root(Value::Object(func))?;

  let proto = scope.alloc_object()?;
  scope.push_root(Value::Object(proto))?;

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

  let Some(desc) = scope.heap().get_property(func, &key)? else {
    panic!("expected get_property to find function's own property");
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => assert_eq!(value, Value::Number(1.0)),
    PropertyKind::Accessor { .. } => panic!("expected data property"),
  }

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
  scope.push_root(Value::Object(func))?;

  let proto = scope.alloc_object()?;
  scope.push_root(Value::Object(proto))?;

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

  let Some(desc) = scope.heap().get_property(func, &key)? else {
    panic!("expected get_property to traverse function prototype chain");
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => assert_eq!(value, Value::Number(42.0)),
    PropertyKind::Accessor { .. } => panic!("expected data property"),
  }

  let found = scope.ordinary_get(&mut vm, func, key, Value::Object(func))?;
  assert_eq!(found, Value::Number(42.0));
  Ok(())
}

#[test]
fn function_prototype_chain_can_include_function_objects() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let proto_name = scope.alloc_string("proto")?;
  let proto = scope.alloc_native_function(NativeFunctionId(1), None, proto_name, 0)?;
  scope.push_root(Value::Object(proto))?;

  let func_name = scope.alloc_string("f")?;
  let func = scope.alloc_native_function(NativeFunctionId(1), None, func_name, 0)?;
  scope.push_root(Value::Object(func))?;

  scope.heap_mut().object_set_prototype(func, Some(proto))?;

  let key = PropertyKey::from_string(scope.alloc_string("z")?);
  scope.define_property(
    proto,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Bool(true),
        writable: true,
      },
    },
  )?;

  let Some(desc) = scope.heap().get_property(func, &key)? else {
    panic!("expected get_property to traverse function->function prototype chain");
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => assert_eq!(value, Value::Bool(true)),
    PropertyKind::Accessor { .. } => panic!("expected data property"),
  }
  Ok(())
}

#[test]
fn objects_can_inherit_from_function_objects() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let proto_name = scope.alloc_string("proto")?;
  let proto = scope.alloc_native_function(NativeFunctionId(1), None, proto_name, 0)?;
  scope.push_root(Value::Object(proto))?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope.heap_mut().object_set_prototype(obj, Some(proto))?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(
    proto,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(123.0),
        writable: true,
      },
    },
  )?;

  let Some(desc) = scope.heap().get_property(obj, &key)? else {
    panic!("expected get_property to traverse object->function prototype chain");
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => assert_eq!(value, Value::Number(123.0)),
    PropertyKind::Accessor { .. } => panic!("expected data property"),
  }
  Ok(())
}

#[test]
fn set_existing_data_property_value_works_on_functions() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let name = scope.alloc_string("f")?;
  let func = scope.alloc_native_function(NativeFunctionId(1), None, name, 0)?;
  scope.push_root(Value::Object(func))?;

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

  scope
    .heap_mut()
    .object_set_existing_data_property_value(func, &key, Value::Number(2.0))?;

  assert_eq!(
    scope.heap().object_get_own_data_property_value(func, &key)?,
    Some(Value::Number(2.0))
  );
  Ok(())
}
