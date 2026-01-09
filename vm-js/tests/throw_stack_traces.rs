use vm_js::{
  GcObject, Heap, HeapLimits, JsRuntime, Scope, Value, Vm, VmError, VmHost, VmHostHooks, VmOptions,
};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn inner_throw(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::Throw(Value::Undefined))
}

fn call_single_arg(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let callee = args.get(0).copied().unwrap_or(Value::Undefined);
  vm.call_with_host(scope, hooks, callee, Value::Undefined, &[])
}

fn call_two_args(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let callee = args.get(0).copied().unwrap_or(Value::Undefined);
  let arg0 = args.get(1).copied().unwrap_or(Value::Undefined);
  vm.call_with_host(scope, hooks, callee, Value::Undefined, &[arg0])
}

#[test]
fn thrown_exceptions_capture_nested_native_call_stack() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();

  let inner_id = vm.register_native_call(inner_throw)?;
  let middle_id = vm.register_native_call(call_single_arg)?;
  let outer_id = vm.register_native_call(call_two_args)?;

  let inner_name = scope.alloc_string("inner")?;
  let middle_name = scope.alloc_string("middle")?;
  let outer_name = scope.alloc_string("outer")?;

  let inner = scope.alloc_native_function(inner_id, None, inner_name, 0)?;
  let middle = scope.alloc_native_function(middle_id, None, middle_name, 1)?;
  let outer = scope.alloc_native_function(outer_id, None, outer_name, 2)?;

  let err = vm
    .call(
      &mut scope,
      Value::Object(outer),
      Value::Undefined,
      &[Value::Object(middle), Value::Object(inner)],
    )
    .unwrap_err();

  let VmError::ThrowWithStack { stack, .. } = err else {
    return Err(err);
  };

  let names: Vec<&str> = stack
    .iter()
    .filter_map(|frame| frame.function.as_deref())
    .collect();
  assert_eq!(names, vec!["inner", "middle", "outer"]);
  Ok(())
}

#[test]
fn thrown_exceptions_include_top_level_source_location() -> Result<(), VmError> {
  let mut rt = new_runtime();

  // Throw starts at line 2, column 1.
  let err = rt.exec_script("1;\nthrow \"x\";").unwrap_err();
  let VmError::ThrowWithStack { stack, .. } = err else {
    panic!("expected ThrowWithStack, got {err:?}");
  };

  assert_eq!(stack.len(), 1);
  let frame = &stack[0];
  assert_eq!(frame.function, None);
  assert_eq!(frame.source.as_ref(), "<inline>");
  assert_eq!((frame.line, frame.col), (2, 1));
  Ok(())
}
