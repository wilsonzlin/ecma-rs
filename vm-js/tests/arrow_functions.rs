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
fn arrow_function_captures_lexical_this() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o={x:1,f:function(){ return (()=>this.x)(); }}; o.f() === 1"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn arrow_function_top_level_this_sloppy_is_global_object() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"(() => this).call({}) === globalThis"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn arrow_function_top_level_this_strict_is_undefined() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#""use strict"; (() => this).call(globalThis) === undefined"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn arrow_function_captures_lexical_new_target_in_constructor() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
        function C() {
          this.ok = (() => new.target === C)();
        }
        var o = new C();
        o.ok === true
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn arrow_function_captures_lexical_new_target_in_plain_call() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
        function f() {
          return (() => new.target)();
        }
        f() === undefined
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn arrow_function_is_not_constructable() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
        var f = () => {};
        try { new f(); "no error"; } catch(e) { e.name }
      "#,
    )
    .unwrap();
  assert_value_is_utf8(&rt, value, "TypeError");
}
