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
  let value = err
    .thrown_value()
    .unwrap_or_else(|| panic!("expected thrown exception, got {err:?}"));
  assert_value_is_utf8(&rt, value, "x");
}

#[test]
fn try_catch_throw_overrides_prior_throw() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script(r#"try { throw "x"; } catch(e){ throw "y"; }"#)
    .unwrap_err();
  let value = err
    .thrown_value()
    .unwrap_or_else(|| panic!("expected thrown exception, got {err:?}"));
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
fn try_statement_update_empty_to_undefined_finally_only() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"1; try { } finally { }"#).unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn try_statement_update_empty_to_undefined_catch_only() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"1; try { } catch { }"#).unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn try_statement_update_empty_to_undefined_catch_and_finally() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"1; try { } catch { } finally { }"#).unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn try_finally_preserves_non_empty_value() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"try { 1 } finally { }"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn while_try_break_finally_returns_undefined() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"while(true){ 1; try{ break; } finally {} }"#)
    .unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn var_initializer_assigns_to_var_env_even_when_catch_param_shadows() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var e = 1; try { throw 2; } catch(e){ var e = 3; } e"#)
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn labelled_block_break_consumes_break() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"a: { 1; break a; }"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn nested_labels_break_outer() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"a: b: { 1; break a; 2; }"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn labelled_break_with_empty_value_does_not_clobber_prior_statement_list_value() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"1; a: { break a; }"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn while_not_entered_returns_undefined() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"1; while(false) {}"#).unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn while_empty_statement_does_not_clobber_later_value() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"while(false) {} 1"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn while_break_propagates_value() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"while(true) { 1; break; }"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn labelled_continue_targets_outer_loop() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
        var x = 0;
        outer: while (x === 0) {
          while (true) {
            x = 1;
            continue outer;
          }
        }
        x
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn call_expression_invokes_user_function() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"function f(a){ return a; } f(5)"#).unwrap();
  assert_eq!(value, Value::Number(5.0));
}

#[test]
fn new_target_is_undefined_for_plain_call() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function C(){ return new.target; } C()"#)
    .unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn new_target_is_constructor_for_new_expression() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function C(){ return new.target; } var x = new C(); x === C"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}
