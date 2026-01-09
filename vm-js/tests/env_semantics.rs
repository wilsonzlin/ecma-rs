use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn assert_value_is_utf8(rt: &JsRuntime, value: Value, expected: &str) {
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };
  let actual = rt.heap().get_string(s).unwrap().to_utf8_lossy();
  assert_eq!(actual, expected);
}

#[test]
fn var_hoists_across_blocks() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"if (true) { var x = 1; } x"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn let_does_not_leak_out_of_blocks() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"{ let x = 1; } try { x; } catch(e) { "ok" }"#)
    .unwrap();
  assert_value_is_utf8(&rt, value, "ok");
}

#[test]
fn tdz_for_lexical_bindings() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"try { x; let x = 1; } catch(e) { "ok" }"#)
    .unwrap();
  assert_value_is_utf8(&rt, value, "ok");
}

#[test]
fn let_initializes_to_undefined_when_no_initializer() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"let x; x"#).unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn const_assignment_throws() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"try { const x = 1; x = 2; } catch(e) { "ok" }"#)
    .unwrap();
  assert_value_is_utf8(&rt, value, "ok");
}
