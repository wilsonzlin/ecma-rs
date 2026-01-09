use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).expect("JsRuntime::new should succeed for unit tests")
}

fn assert_value_is_utf8(rt: &JsRuntime, value: Value, expected: &str) {
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };
  let actual = rt.heap().get_string(s).unwrap().to_utf8_lossy();
  assert_eq!(actual, expected);
}

#[test]
fn let_shadows_var_in_block() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var x = 1; { let x = 2; } x"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn tdz_throws_on_access_before_initialization() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script(r#"let x = 1; { x; let x = 2; }"#)
    .unwrap_err();
  assert!(matches!(err, VmError::Throw(_) | VmError::ThrowWithStack { .. }));
}

#[test]
fn const_assignment_throws() {
  let mut rt = new_runtime();
  let err = rt.exec_script(r#"const x = 1; x = 2;"#).unwrap_err();
  assert!(matches!(err, VmError::Throw(_) | VmError::ThrowWithStack { .. }));
}

#[test]
fn env_records_keep_values_alive_across_gc() {
  let mut rt = new_runtime();

  let value = rt.exec_script(r#"let x = "alive"; x"#).unwrap();
  assert_value_is_utf8(&rt, value, "alive");

  // `value` is not rooted; it should survive this GC only because it is referenced
  // from the environment record.
  rt.heap_mut().collect_garbage();
  assert_value_is_utf8(&rt, value, "alive");
}
