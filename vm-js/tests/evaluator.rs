use vm_js::{
  Budget, Heap, HeapLimits, JsRuntime, TerminationReason, Value, Vm, VmError, VmOptions,
};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn as_utf8_lossy(rt: &JsRuntime, value: Value) -> String {
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };
  rt.heap().get_string(s).unwrap().to_utf8_lossy()
}

#[test]
fn function_declaration_call_and_closure_capture() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
        function makeAdder(x) {
          return function(y) { return x + y; };
        }
        var add5 = makeAdder(5);
        add5(3)
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(8.0));
}

#[test]
fn new_and_prototype_lookup() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
        function C() { this.x = 1; }
        C.prototype.y = 2;
        var o = new C();
        o.y
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn try_catch_with_thrown_object() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
        try { throw { x: 1 }; } catch (e) { e.x }
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn typeof_primitives_and_functions() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"typeof undefined + "," + typeof null + "," + typeof function() {}"#)
    .unwrap();
  assert_eq!(as_utf8_lossy(&rt, value), "undefined,object,function");
}

#[test]
fn budget_termination_in_tight_loop() {
  let mut vm = Vm::new(VmOptions::default());
  vm.set_budget(Budget {
    fuel: Some(50),
    deadline: None,
    check_time_every: 1,
  });
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut rt = JsRuntime::new(vm, heap).unwrap();

  let err = rt.exec_script("while (true) {}").unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::OutOfFuel),
    other => panic!("expected termination, got {other:?}"),
  }
}
