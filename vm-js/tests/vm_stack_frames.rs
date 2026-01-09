use vm_js::{
  GcObject, Heap, HeapLimits, Scope, TerminationReason, Value, Vm, VmError, VmHost, VmHostHooks,
  VmOptions,
};

fn native_error(
  vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let stack = vm.capture_stack();
  assert_eq!(stack.len(), 1);
  assert_eq!(stack[0].function.as_deref(), Some("f"));
  assert_eq!(stack[0].source.as_ref(), "<native>");
  Err(VmError::Unimplemented("x"))
}

#[test]
fn vm_call_pushes_and_pops_stack_frame_even_on_error() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();
  let call_id = vm.register_native_call(native_error)?;
  let name = scope.alloc_string("f")?;
  let callee = scope.alloc_native_function(call_id, None, name, 0)?;

  let err = vm
    .call(&mut scope, Value::Object(callee), Value::Undefined, &[])
    .unwrap_err();
  assert!(matches!(err, VmError::Unimplemented("x")));

  assert!(vm.capture_stack().is_empty());
  Ok(())
}

fn recursive(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let callee = args.get(0).copied().unwrap_or(Value::Undefined);
  vm.call_with_host(scope, hooks, callee, Value::Undefined, args)
}

#[test]
fn vm_stack_overflow_on_deep_manual_frames() -> Result<(), VmError> {
  let max_stack_depth = 4;

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut opts = VmOptions::default();
  opts.max_stack_depth = max_stack_depth;
  let mut vm = Vm::new(opts);

  let mut scope = heap.scope();
  let call_id = vm.register_native_call(recursive)?;
  let name = scope.alloc_string("recurse")?;
  let callee = scope.alloc_native_function(call_id, None, name, 1)?;

  let args = [Value::Object(callee)];
  let err = vm
    .call(&mut scope, Value::Object(callee), Value::Undefined, &args)
    .unwrap_err();

  let VmError::Termination(term) = err else {
    panic!("expected termination, got: {err:?}");
  };
  assert_eq!(term.reason, TerminationReason::StackOverflow);
  assert_eq!(term.stack.len(), max_stack_depth);
  for frame in &term.stack {
    assert_eq!(frame.source.as_ref(), "<native>");
    assert_eq!(frame.function.as_deref(), Some("recurse"));
    assert_eq!(frame.line, 0);
    assert_eq!(frame.col, 0);
  }

  assert!(vm.capture_stack().is_empty());
  Ok(())
}
