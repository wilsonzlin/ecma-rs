use vm_js::{GcObject, Heap, HeapLimits, Scope, Value, Vm, VmError, VmHost, VmHostHooks, VmOptions};

fn alloc_and_return_object(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let obj = scope.alloc_object()?;
  Ok(Value::Object(obj))
}

fn dummy_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

fn alloc_and_return_object_construct(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  let obj = scope.alloc_object()?;
  Ok(Value::Object(obj))
}

#[test]
fn call_return_value_is_not_rooted_by_default() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let returned_obj;
  {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(alloc_and_return_object)?;
    let name = scope.alloc_string("f")?;
    let callee = scope.alloc_native_function(call_id, None, name, 0)?;

    let result = vm.call_without_host(&mut scope, Value::Object(callee), Value::Undefined, &[])?;
    let Value::Object(obj) = result else {
      panic!("native function should return an object");
    };
    returned_obj = obj;

    // `returned_obj` is not rooted: a GC cycle should reclaim it.
    scope.heap_mut().collect_garbage();
    assert!(!scope.heap().is_valid_object(returned_obj));
  }

  Ok(())
}

#[test]
fn call_return_value_survives_when_rooted_by_caller() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let returned_obj;
  {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(alloc_and_return_object)?;
    let name = scope.alloc_string("f")?;
    let callee = scope.alloc_native_function(call_id, None, name, 0)?;

    let result = vm.call_without_host(&mut scope, Value::Object(callee), Value::Undefined, &[])?;
    let Value::Object(obj) = result else {
      panic!("native function should return an object");
    };
    returned_obj = obj;

    // Root the object before any further allocations/GC.
    scope.push_root(Value::Object(returned_obj))?;

    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_object(returned_obj));
  }

  Ok(())
}

#[test]
fn construct_return_value_is_not_rooted_by_default() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let returned_obj;
  {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(dummy_call)?;
    let construct_id = vm.register_native_construct(alloc_and_return_object_construct)?;
    let name = scope.alloc_string("F")?;
    let callee = scope.alloc_native_function(call_id, Some(construct_id), name, 0)?;

    let result =
      vm.construct_without_host(&mut scope, Value::Object(callee), &[], Value::Object(callee))?;
    let Value::Object(obj) = result else {
      panic!("native constructor should return an object");
    };
    returned_obj = obj;

    // `returned_obj` is not rooted: a GC cycle should reclaim it.
    scope.heap_mut().collect_garbage();
    assert!(!scope.heap().is_valid_object(returned_obj));
  }

  Ok(())
}

#[test]
fn construct_return_value_survives_when_rooted_by_caller() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let returned_obj;
  {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(dummy_call)?;
    let construct_id = vm.register_native_construct(alloc_and_return_object_construct)?;
    let name = scope.alloc_string("F")?;
    let callee = scope.alloc_native_function(call_id, Some(construct_id), name, 0)?;

    let result =
      vm.construct_without_host(&mut scope, Value::Object(callee), &[], Value::Object(callee))?;
    let Value::Object(obj) = result else {
      panic!("native constructor should return an object");
    };
    returned_obj = obj;

    // Root the object before any further allocations/GC.
    scope.push_root(Value::Object(returned_obj))?;

    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_object(returned_obj));
  }

  Ok(())
}
