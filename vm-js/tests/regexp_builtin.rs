//! Minimal `%RegExp%` global: typeof/identity and constructable stub (no regex engine).

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn typeof_regexp_is_function() {
  let mut rt = new_runtime();
  let v = rt.exec_script("typeof RegExp").unwrap();
  match v {
    Value::String(s) => {
      assert_eq!(rt.heap().get_string(s).unwrap().to_utf8_lossy(), "function")
    }
    other => panic!("expected string, got {other:?}"),
  }
}

#[test]
fn regexp_call_and_construct_return_objects() {
  let mut rt = new_runtime();
  let v = rt
    .exec_script(
      r#"
        var a = RegExp("a");
        var b = new RegExp("b", "i");
        (typeof a === "object") && (typeof b === "object")
          && a.constructor === RegExp && b.constructor === RegExp
          ? 1 : 0
      "#,
    )
    .unwrap();
  assert_eq!(v, Value::Number(1.0));
}

#[test]
fn typeof_new_function_and_regexp_match_native_call_shape() {
  // Shape of language/expressions/typeof/native-call.js residual checks.
  let mut rt = new_runtime();
  let v = rt
    .exec_script(
      r#"
        (typeof new Function() === "function")
          && (typeof Function() === "function")
          && (typeof RegExp === "function")
          && (typeof Date === "function")
          ? 1 : 0
      "#,
    )
    .unwrap();
  assert_eq!(v, Value::Number(1.0));
}
