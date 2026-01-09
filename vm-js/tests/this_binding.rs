use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn method_call_binds_this_to_base_object() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function f(){ return this; } var o = {}; o.f = f; o.f() === o"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn unqualified_call_sloppy_binds_this_to_global_object() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function f(){ return this === globalThis; } f()"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn unqualified_call_strict_binds_this_to_undefined() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#""use strict"; function f(){ return this === undefined; } f()"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn optional_chaining_short_circuits_call() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o = null; (o?.f?.()) === undefined"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}
