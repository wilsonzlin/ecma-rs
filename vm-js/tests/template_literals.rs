use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn untagged_template_literal_interpolates_substitutions() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var x=1; `a${x}b` === "a1b""#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn tagged_template_literal_calls_tag_with_template_object() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function tag(a){ return a[0]; } tag`hi` === "hi""#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

