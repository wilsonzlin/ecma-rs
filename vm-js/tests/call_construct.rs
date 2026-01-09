use vm_js::{
  Budget, GcObject, Heap, HeapLimits, Scope, TerminationReason, Value, Vm, VmError, VmOptions,
  VmHost, VmHostHooks,
};

fn return_123(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(123.0))
}

fn noop_constructor(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

#[test]
fn call_native_function_returns_value() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 32,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });
  vm.set_budget(Budget::unlimited(1));

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let call_id = vm.register_native_call(return_123)?;
  let construct_id = vm.register_native_construct(noop_constructor)?;

  let func = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("return_123")?;
    scope.alloc_native_function(call_id, Some(construct_id), name, 0)?
  };

  let mut scope = heap.scope();
  let out = vm.call(&mut scope, Value::Object(func), Value::Undefined, &[])?;
  assert_eq!(out, Value::Number(123.0));
  Ok(())
}

#[test]
fn call_non_callable_returns_type_error_placeholder() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 32,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });
  vm.set_budget(Budget::unlimited(1));

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let obj = {
    let mut scope = heap.scope();
    scope.alloc_object()?
  };

  let err = {
    let mut scope = heap.scope();
    vm.call(&mut scope, Value::Object(obj), Value::Undefined, &[])
      .unwrap_err()
  };

  match err {
    VmError::Throw(_) => {}
    VmError::NotCallable => {}
    VmError::Unimplemented(msg) => assert!(msg.contains("TypeError") || msg.contains("call")),
    other => panic!("expected throw or TypeError placeholder, got {other:?}"),
  }

  Ok(())
}

#[test]
fn call_ticks_budget_and_reports_stack_on_termination() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 32,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });
  vm.set_budget(Budget {
    fuel: Some(0),
    deadline: None,
    check_time_every: 1,
  });

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let call_id = vm.register_native_call(return_123)?;

  let func = {
    let mut scope = heap.scope();
    let name = scope.alloc_string("out_of_fuel")?;
    scope.alloc_native_function(call_id, None, name, 0)?
  };

  let err = {
    let mut scope = heap.scope();
    vm.call(&mut scope, Value::Object(func), Value::Undefined, &[])
      .unwrap_err()
  };

  match err {
    VmError::Termination(term) => {
      assert_eq!(term.reason, TerminationReason::OutOfFuel);
      assert!(
        term
          .stack
          .iter()
          .any(|f| f.function.as_deref() == Some("out_of_fuel") && f.source.as_ref() == "<native>"),
        "termination stack should include native call frame"
      );
    }
    other => panic!("expected termination, got {other:?}"),
  }

  Ok(())
}
