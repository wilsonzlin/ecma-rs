use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn plus_operator_concatenates_when_either_side_is_string() {
  let mut rt = new_runtime();

  let value = rt.exec_script(r#""1" + 2 === "12""#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"1 + "2" === "12""#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn numeric_operators_use_tonumber_for_strings() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#""5" - 2 === 3"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn abstract_equality_matches_ecmascript_primitives() {
  let mut rt = new_runtime();

  let value = rt.exec_script(r#"null == undefined"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"false == 0"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"true == 1"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#""0" == 0"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn tonumber_rejects_signed_radix_prefixes() {
  let mut rt = new_runtime();

  // ECMA-262 `StringToNumber` does not accept signed 0x/0b/0o prefixes.
  // Assert NaN via self-inequality to avoid depending on NaN bit patterns.
  let value = rt.exec_script(r#"+'+0x10' !== +'+0x10'"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"+'-0x10' !== +'-0x10'"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"+'+0b10' !== +'+0b10'"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"+'-0b10' !== +'-0b10'"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"+'+0o10' !== +'+0o10'"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"+'-0o10' !== +'-0o10'"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}
