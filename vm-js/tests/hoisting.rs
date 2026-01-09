use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn function_declarations_are_hoisted() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("f(); function f() { return 1; }")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn var_declarations_are_hoisted_to_undefined() {
  let mut rt = new_runtime();

  let value = rt.exec_script("x === undefined; var x = 1;").unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script("x").unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn lexical_declarations_have_tdz() {
  let mut rt = new_runtime();
  let err = rt.exec_script("{ x; let x = 1; }").unwrap_err();
  match err {
    VmError::Throw(_) | VmError::ThrowWithStack { .. } => {}
    other => panic!("expected ReferenceError/TDZ throw, got {other:?}"),
  }
}

