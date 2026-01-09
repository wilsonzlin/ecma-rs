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
fn switch_empty_case_block_returns_undefined() {
  let mut rt = new_runtime();
  let value = rt.exec_script("switch (0) {}").unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn switch_matching_case_returns_last_statement_value() {
  let mut rt = new_runtime();
  let value = rt.exec_script("switch (0) { case 0: 1; }").unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn switch_default_clause_executes_when_no_cases_match() {
  let mut rt = new_runtime();
  let value = rt.exec_script("switch (0) { case 1: 1; default: 2; }").unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn switch_fallthrough_updates_value_with_last_executed_clause() {
  let mut rt = new_runtime();
  let value = rt.exec_script("switch (0) { case 0: 1; case 1: 2; }").unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn switch_break_exits_switch_and_preserves_last_value() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("switch (0) { case 0: 1; break; case 1: 2; }")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn switch_does_not_evaluate_case_selectors_after_match_is_found() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("var x = 0; switch (0) { case 0: 1; break; case (x = 1): 2; } x")
    .unwrap();
  assert_eq!(value, Value::Number(0.0));
}

#[test]
fn switch_default_before_matching_case_is_skipped() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("var y = 0; switch (1) { default: y = 1; case 1: 2; } y")
    .unwrap();
  assert_eq!(value, Value::Number(0.0));
}

#[test]
fn switch_match_before_default_falls_through_to_default() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("var y = 0; switch (0) { case 0: y = 1; default: y = 2; } y")
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn switch_default_falls_through_to_after_default_clauses() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("var y = 0; switch (0) { default: 0; case 1: y = 1; } y")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn switch_after_default_case_selector_is_evaluated_once_when_no_match() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("var x = 0; switch (0) { default: 0; case (++x): 0; } x")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn switch_after_default_case_selector_is_not_evaluated_when_match_before_default() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("var x = 0; switch (0) { case 0: 0; default: 0; case (++x): 0; } x")
    .unwrap();
  assert_eq!(value, Value::Number(0.0));
}

#[test]
fn switch_var_is_hoisted_out_of_case_clauses() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("switch (0) { case 0: break; case 1: var x = 1; } x")
    .unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn switch_let_is_not_visible_outside_case_block() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"try { switch (0) { case 0: let x = 1; } x } catch(e) { e.name }"#)
    .unwrap();
  assert_value_is_utf8(&rt, value, "ReferenceError");
}

#[test]
fn switch_let_tdz_applies_across_case_clauses() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"try { switch (0) { case 0: x; break; case 1: let x = 1; } } catch(e) { e.name }"#)
    .unwrap();
  assert_value_is_utf8(&rt, value, "ReferenceError");
}

#[test]
fn switch_let_initialized_is_visible_in_same_clause() {
  let mut rt = new_runtime();
  let value = rt.exec_script("switch (0) { case 0: let x = 1; x }").unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn switch_let_initialized_fallthrough_is_visible_in_later_clause() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("switch (0) { case 0: let x = 1; case 1: x }")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}
