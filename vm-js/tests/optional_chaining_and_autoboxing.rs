//! Regression tests for optional-chain short-circuit propagation (ECMA-262 §13.3.9) and primitive
//! autoboxing / `GetV` on primitive bases (§7.3.2 / §13.3.3).

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn eval(src: &str) -> Result<Value, VmError> {
  new_runtime().exec_script(src)
}

fn eval_num(src: &str) -> f64 {
  match eval(src).unwrap() {
    Value::Number(n) => n,
    other => panic!("expected number, got {other:?}"),
  }
}

fn eval_bool(src: &str) -> bool {
  match eval(src).unwrap() {
    Value::Bool(b) => b,
    other => panic!("expected bool, got {other:?}"),
  }
}

/// Whether a `VmError` is a JS exception (either stack-captured or not).
fn is_js_throw(err: &VmError) -> bool {
  matches!(err, VmError::Throw(_) | VmError::ThrowWithStack { .. })
}

// --- Optional chaining short-circuit (§13.3.9) ---

#[test]
fn optional_member_then_member_short_circuits() {
  // `a?.b.c` with nullish `a` yields `undefined`, not a throw.
  assert_eq!(eval("var a = null; a?.b.c").unwrap(), Value::Undefined);
  assert_eq!(eval("var a = undefined; a?.b.c").unwrap(), Value::Undefined);
}

#[test]
fn optional_member_then_computed_short_circuits() {
  assert_eq!(eval("var a = null; a?.b[c]").unwrap(), Value::Undefined);
}

#[test]
fn optional_member_then_call_short_circuits() {
  assert_eq!(eval("var a = null; a?.b()").unwrap(), Value::Undefined);
  // A call further down the chain also short-circuits.
  assert_eq!(eval("var a = null; a?.b.c()").unwrap(), Value::Undefined);
}

#[test]
fn optional_call_then_member_short_circuits() {
  assert_eq!(eval("var a = null; a?.().x").unwrap(), Value::Undefined);
}

#[test]
fn parenthesized_chain_resets_boundary_and_throws() {
  // `(a?.b).c` throws when `a` is nullish: the parens end the chain, so `.c` runs on `undefined`.
  let err = eval("var a = null; (a?.b).c").unwrap_err();
  assert!(is_js_throw(&err), "expected TypeError throw, got {err:?}");
}

#[test]
fn optional_chain_truthy_path_matches_non_optional() {
  // Truthy-path equivalence with the non-optional chain.
  assert_eq!(eval_num("var a = {b: {c: 42}}; a?.b.c"), 42.0);
  assert_eq!(eval_num("var a = {b: {c: 42}}; a.b.c"), 42.0);
  assert_eq!(eval_num("var a = {b: [10, 20]}; a?.b[1]"), 20.0);
}

#[test]
fn optional_chain_after_call() {
  assert_eq!(
    eval_num("var o = {f: function() { return {x: 7}; }}; o.f()?.x"),
    7.0
  );
  assert_eq!(
    eval("var o = {f: function() { return null; }}; o.f()?.x").unwrap(),
    Value::Undefined
  );
}

#[test]
fn optional_chain_method_this_binding() {
  // `this` inside the called method must be the object left of `?.`.
  assert_eq!(
    eval_num("var o = {n: 5, get: function() { return this.n; }}; o?.get()"),
    5.0
  );
}

#[test]
fn delete_optional_chain_short_circuits() {
  // `delete a?.b` is `true` when `a` is nullish (no throw).
  assert_eq!(
    eval("var a = null; delete a?.b").unwrap(),
    Value::Bool(true)
  );
  // And actually deletes when present.
  assert_eq!(
    eval_bool("var a = {b: 1}; var r = delete a?.b; r && !('b' in a)"),
    true
  );
}

// --- Primitive autoboxing / GetV (§7.3.2, §13.3.3) ---

#[test]
fn string_length_and_index() {
  assert_eq!(eval_num("'abc'.length"), 3.0);
  assert!(eval_bool("'abc'[0] === 'a'"));
  assert!(eval_bool("'abc'[1] === 'b'"));
  assert!(eval_bool("'abc'[5] === undefined"));
}

#[test]
fn string_methods() {
  assert!(eval_bool("'abc'.charAt(1) === 'b'"));
  assert_eq!(eval_num("'abc'.charCodeAt(0)"), 97.0);
  assert_eq!(eval_num("'abcabc'.indexOf('c')"), 2.0);
  assert!(eval_bool("'Hello'.toUpperCase() === 'HELLO'"));
  assert!(eval_bool("'Hello'.toLowerCase() === 'hello'"));
  assert!(eval_bool("'abcdef'.slice(1, 3) === 'bc'"));
  assert!(eval_bool("'abc'.includes('b')"));
}

#[test]
fn number_methods() {
  assert!(eval_bool("(5).toFixed(2) === '5.00'"));
  assert!(eval_bool("(255).toString(16) === 'ff'"));
  assert!(eval_bool("(42).toString() === '42'"));
  assert_eq!(eval_num("(3.7).valueOf()"), 3.7);
}

#[test]
fn boolean_methods() {
  assert!(eval_bool("true.toString() === 'true'"));
  assert!(eval_bool("false.toString() === 'false'"));
  assert_eq!(eval("true.valueOf()").unwrap(), Value::Bool(true));
}

#[test]
fn member_access_on_nullish_throws_typeerror() {
  let err = eval("var a = null; a.b").unwrap_err();
  assert!(is_js_throw(&err), "expected TypeError throw, got {err:?}");
  let err = eval("undefined.x").unwrap_err();
  assert!(is_js_throw(&err), "expected TypeError throw, got {err:?}");
}
