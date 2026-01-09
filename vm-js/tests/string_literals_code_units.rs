use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn string_literal_preserves_unpaired_surrogate_code_units() -> Result<(), VmError> {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#""\uD800""#)?;
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };

  let js = rt.heap().get_string(s)?;
  assert_eq!(js.as_code_units(), &[0xD800]);
  Ok(())
}

#[test]
fn string_literal_preserves_surrogate_and_bmp_ordering() -> Result<(), VmError> {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#""a\uD800b""#)?;
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };

  let js = rt.heap().get_string(s)?;
  assert_eq!(js.as_code_units(), &[0x0061, 0xD800, 0x0062]);
  Ok(())
}
