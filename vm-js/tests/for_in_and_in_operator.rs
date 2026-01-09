use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

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

#[test]
fn for_in_restores_lexical_env_on_uncatchable_error() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script(r#"for (let k in {a:1}) { debugger; }"#)
    .unwrap_err();
  assert!(matches!(err, VmError::Unimplemented(_)));

  // If the loop's per-iteration lexical environment is not restored when the body returns an
  // uncatchable error, the loop variable binding would leak into subsequent script executions.
  let value = rt
    .exec_script(r#"try { k; "leaked" } catch(e) { "ok" }"#)
    .unwrap();
  assert_value_is_utf8(&rt, value, "ok");
}
