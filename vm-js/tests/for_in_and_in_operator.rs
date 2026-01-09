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
fn for_in_over_own_enumerable_props() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o={a:1,b:2}; var s=''; for (var k in o) { s = s + k; } s"#)
    .unwrap();
  assert_value_is_utf8(&rt, value, "ab");
}

#[test]
fn for_in_includes_prototype_enumerable_props() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"var p={x:1}; var o=Object.create(p); o.y=2; var s=''; for (var k in o) { s = s + k; } s"#,
    )
    .unwrap();
  assert_value_is_utf8(&rt, value, "yx");
}

#[test]
fn in_operator_walks_prototype_chain() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var p={x:1}; var o=Object.create(p); o.y=2; ('x' in o) && !('z' in o)"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

