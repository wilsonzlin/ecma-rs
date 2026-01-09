use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn object_literal_member_get_set() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o = {a: 1}; o.a === 1; o.a = 2; o.a"#)
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn computed_member_get_set() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var o = {}; o["x"] = 3; o.x"#).unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn array_literal_index_get() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var a = [1,2]; (a[0] === 1) && (a[1] === 2)"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn arithmetic_precedence() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"1 + 2 * 3 === 7"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn logical_ops() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"true && false"#).unwrap();
  assert_eq!(value, Value::Bool(false));

  let value = rt.exec_script(r#"false || true"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"null ?? 5"#).unwrap();
  assert_eq!(value, Value::Number(5.0));
}

#[test]
fn cond_operator() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"true ? 1 : 2"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}
