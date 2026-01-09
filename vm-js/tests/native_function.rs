use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Scope, Value, Vm,
  VmError, VmHost, VmHostHooks, VmOptions,
};

fn return_42(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(42.0))
}

#[test]
fn native_function_can_be_allocated_and_called() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let func: GcObject = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(return_42)?;
    let name = scope.alloc_string("return_42")?;
    scope.alloc_native_function(call_id, None, name, 0)?
  };

  assert!(heap.is_callable(Value::Object(func))?);

  let result = heap.call(&mut vm, Value::Object(func), Value::Undefined, &[])?;
  assert_eq!(result, Value::Number(42.0));
  Ok(())
}

#[test]
fn calling_collected_native_function_returns_invalid_handle() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let func: GcObject = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(return_42)?;
    let name = scope.alloc_string("return_42")?;
    scope.alloc_native_function(call_id, None, name, 0)?
  };

  // The function is unreachable once the scope ends; a GC cycle should free it.
  heap.collect_garbage();

  let err = heap
    .call(&mut vm, Value::Object(func), Value::Undefined, &[])
    .unwrap_err();
  assert!(matches!(err, VmError::InvalidHandle));
  Ok(())
}

#[test]
fn property_descriptor_tracing_keeps_native_functions_alive() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let func_alive: GcObject;
  let func_dead: GcObject;
  let owner;
  let owner_root;
  {
    let mut scope = heap.scope();

    let call_id = vm.register_native_call(return_42)?;

    // Referenced through a property descriptor.
    let name = scope.alloc_string("return_42")?;
    func_alive = scope.alloc_native_function(call_id, None, name, 0)?;

    // Unreferenced: should be collected.
    let name = scope.alloc_string("return_42")?;
    func_dead = scope.alloc_native_function(call_id, None, name, 0)?;

    owner = scope.alloc_object()?;
    let key = scope.alloc_string("f")?;

    let desc = PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Object(func_alive),
        writable: true,
      },
    };
    scope.define_property(owner, PropertyKey::from_string(key), desc)?;
    owner_root = scope.heap_mut().add_root(Value::Object(owner))?;
  }

  heap.collect_garbage();

  assert!(heap.is_valid_object(owner));
  assert!(heap.is_valid_object(func_alive));
  assert!(!heap.is_valid_object(func_dead));
  assert!(heap.is_callable(Value::Object(func_alive))?);

  let result = heap.call(&mut vm, Value::Object(func_alive), Value::Undefined, &[])?;
  assert_eq!(result, Value::Number(42.0));

  let err = heap
    .call(&mut vm, Value::Object(func_dead), Value::Undefined, &[])
    .unwrap_err();
  assert!(matches!(err, VmError::InvalidHandle));

  heap.remove_root(owner_root);
  Ok(())
}
