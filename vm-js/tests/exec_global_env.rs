use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn var_binding_resolves_as_identifier() {
  let mut rt = new_runtime();
  let value = rt.exec_script("var x = 1; x").unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn var_binding_is_global_object_property() {
  let mut rt = new_runtime();
  let value = rt.exec_script("var x = 1; globalThis.x === 1").unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn let_binding_is_not_global_object_property() {
  let mut rt = new_runtime();
  let value = rt.exec_script("let y = 2; globalThis.y").unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn sloppy_assignment_to_undeclared_creates_global_property() {
  let mut rt = new_runtime();
  let value = rt.exec_script("z = 3; globalThis.z === 3").unwrap();
  assert_eq!(value, Value::Bool(true));
}

