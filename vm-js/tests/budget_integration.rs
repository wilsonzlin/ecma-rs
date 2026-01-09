use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use vm_js::{
  Budget, GcObject, Heap, HeapLimits, JsRuntime, Scope, TerminationReason, Value, Vm, VmError,
  VmHostHooks, VmOptions,
};

fn new_runtime_with_vm(vm: Vm) -> JsRuntime {
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn assert_termination_reason(err: VmError, expected: TerminationReason) {
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, expected),
    other => panic!("expected VmError::Termination({expected:?}), got {other:?}"),
  }
}

#[test]
fn fuel_stops_infinite_loop() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);

  rt.vm.set_budget(Budget {
    fuel: Some(10),
    deadline: None,
    check_time_every: 1,
  });

  let err = rt.exec_script("for(;;){}").unwrap_err();
  assert_termination_reason(err, TerminationReason::OutOfFuel);
}

#[test]
fn interrupt_stops_execution() {
  let interrupt_flag = Arc::new(AtomicBool::new(false));
  let vm = Vm::new(VmOptions {
    interrupt_flag: Some(interrupt_flag.clone()),
    ..VmOptions::default()
  });
  let mut rt = new_runtime_with_vm(vm);
  rt.vm.set_budget(Budget::unlimited(1));

  interrupt_flag.store(true, Ordering::Relaxed);

  let err = rt.exec_script("var x = 1; x = 2; x").unwrap_err();
  assert_termination_reason(err, TerminationReason::Interrupted);
}

#[test]
fn expression_evaluation_consumes_fuel() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);

  // The expression evaluator should tick at expression-granularity, so a small fuel budget should
  // be exhausted even if the script consists of a single expression statement.
  rt.vm.set_budget(Budget {
    fuel: Some(2),
    deadline: None,
    check_time_every: 1,
  });

  let err = rt.exec_script("1 === 1").unwrap_err();
  assert_termination_reason(err, TerminationReason::OutOfFuel);
}

fn native_noop(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

#[test]
fn native_call_consumes_tick() {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let native_id = vm.register_native_call(native_noop).unwrap();
  let mut scope = heap.scope();
  let name = scope.alloc_string("f").unwrap();
  let callee = scope
    .alloc_native_function(native_id, None, name, 0)
    .unwrap();

  vm.set_budget(Budget {
    fuel: Some(0),
    deadline: None,
    check_time_every: 1,
  });

  let err = vm
    .call(&mut scope, Value::Object(callee), Value::Undefined, &[])
    .unwrap_err();
  assert_termination_reason(err, TerminationReason::OutOfFuel);
}
