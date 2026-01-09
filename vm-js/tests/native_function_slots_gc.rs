use vm_js::{
  GcObject, Heap, HeapLimits, NativeFunctionId, Scope, Value, Vm, VmError, VmHostHooks, VmOptions,
  VmHost,
};

fn return_first_native_slot(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let slots = scope.heap().get_function_native_slots(callee)?;
  Ok(slots.first().copied().unwrap_or(Value::Undefined))
}

#[test]
fn native_function_slots_are_traced_by_gc() -> Result<(), VmError> {
  // Use a tiny GC threshold to force GC during root-stack growth inside
  // `alloc_native_function_with_slots`. This ensures the allocator treats `slots` as extra roots
  // while rooting its own inputs.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));

  let captured;
  let func;
  {
    let mut scope = heap.scope();
    let name = scope.alloc_string("f")?;
    // Root `name` across the allocation of `captured` so forced GC does not reclaim it.
    scope.push_root(Value::String(name))?;

    captured = scope.alloc_object()?;
    func = scope.alloc_native_function_with_slots(
      NativeFunctionId(1),
      None,
      name,
      0,
      &[Value::Object(captured)],
    )?;

    // Root only the function object. The captured object must remain alive via `native_slots`.
    scope.push_root(Value::Object(func))?;
    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_object(func));
    assert!(scope.heap().is_valid_object(captured));
  }

  // Stack roots were removed when the scope was dropped: both objects should now be collectable.
  heap.collect_garbage();
  assert!(!heap.is_valid_object(func));
  assert!(!heap.is_valid_object(captured));
  assert_eq!(heap.used_bytes(), 0);
  Ok(())
}

#[test]
fn native_handler_can_read_its_own_slots_via_callee_handle() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();

  let call_id = vm.register_native_call(return_first_native_slot)?;
  let captured = scope.alloc_object()?;
  let name = scope.alloc_string("f")?;
  let func = scope.alloc_native_function_with_slots(
    call_id,
    None,
    name,
    0,
    &[Value::Object(captured)],
  )?;

  let result = vm.call(&mut scope, Value::Object(func), Value::Undefined, &[])?;
  assert_eq!(result, Value::Object(captured));
  Ok(())
}
