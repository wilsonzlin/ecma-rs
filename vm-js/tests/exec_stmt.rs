use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap)
}

fn assert_value_is_utf8(rt: &JsRuntime, value: Value, expected: &str) {
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };
  let actual = rt.heap().get_string(s).unwrap().to_utf8_lossy();
  assert_eq!(actual, expected);
}

#[test]
fn try_catch_binds_param_and_returns_value() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"try { throw "x"; } catch(e){ e }"#).unwrap();
  assert_value_is_utf8(&rt, value, "x");
}

#[test]
fn try_finally_preserves_throw_if_finally_is_normal() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script(r#"try { throw "x"; } finally { }"#)
    .unwrap_err();
  let VmError::Throw(value) = err else {
    panic!("expected VmError::Throw, got {err:?}");
  };
  assert_value_is_utf8(&rt, value, "x");
}

#[test]
fn try_catch_throw_overrides_prior_throw() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script(r#"try { throw "x"; } catch(e){ throw "y"; }"#)
    .unwrap_err();
  let VmError::Throw(value) = err else {
    panic!("expected VmError::Throw, got {err:?}");
  };
  assert_value_is_utf8(&rt, value, "y");
}

#[test]
fn var_decl_and_if_statement_execute() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var x = 1; if (x === 1) { x = 2; } x"#)
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn try_finally_updates_empty_completion_value() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"try { } finally { 1 }"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn var_initializer_assigns_to_var_env_even_when_catch_param_shadows() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var e = 1; try { throw 2; } catch(e){ var e = 3; } e"#)
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
}
