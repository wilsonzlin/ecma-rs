use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn typeof_unbound_identifier_returns_undefined_string() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"typeof notDefined === "undefined""#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn void_evaluates_argument_for_side_effects() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var x = 0; void (x = 1); x === 1"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn delete_removes_configurable_property() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o = {x: 1}; delete o.x; o.x === undefined"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn delete_identifier_strict_mode_throws() {
  let mut rt = new_runtime();
  let err = rt.exec_script(r#""use strict"; var x = 1; delete x;"#).unwrap_err();
  match err {
    VmError::Throw(_) | VmError::ThrowWithStack { .. } | VmError::Syntax(_) => {}
    other => panic!("expected throw or syntax error, got {other:?}"),
  }
}
