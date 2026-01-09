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

