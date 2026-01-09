use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap)
}

fn assert_string_code_units(rt: &JsRuntime, value: Value, expected: &[u16]) {
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };
  let actual = rt.heap().get_string(s).unwrap().as_code_units();
  assert_eq!(actual, expected);
}

#[test]
fn lone_surrogate_escape_preserves_code_unit() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#""\uD800""#).unwrap();
  assert_string_code_units(&rt, value, &[0xD800]);
}

#[test]
fn mixed_string_bmp_astral_and_lone_surrogate_preserves_all_code_units() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#""A\u2603\u{1F600}\uD800B""#).unwrap();
  assert_string_code_units(
    &rt,
    value,
    &[0x0041, 0x2603, 0xD83D, 0xDE00, 0xD800, 0x0042],
  );
}

