use vm_js::{Heap, HeapLimits, Value, Vm, VmError, VmOptions};
use webidl::{InterfaceId, JsRuntime, PropertyKey, WebIdlHooks, WebIdlLimits};
use webidl_vm_js::VmJsWebIdlCx;

struct NoHooks;

impl WebIdlHooks<Value> for NoHooks {
  fn is_platform_object(&self, _value: Value) -> bool {
    false
  }

  fn implements_interface(&self, _value: Value, _interface: InterfaceId) -> bool {
    false
  }
}

fn alloc_key(cx: &mut VmJsWebIdlCx<'_>, s: &str) -> Result<vm_js::GcString, VmError> {
  let units: Vec<u16> = s.encode_utf16().collect();
  cx.alloc_string_from_code_units(&units)
}

#[test]
fn object_ops_smoke_data_property_roundtrip() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let hooks = NoHooks;
  let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, WebIdlLimits::default(), &hooks);

  let obj = cx.alloc_object()?;

  let key = alloc_key(&mut cx, "x")?;
  cx.create_data_property_or_throw(obj, PropertyKey::String(key), Value::Number(123.0))?;
  let got = cx.get(obj, PropertyKey::String(key))?;
  assert_eq!(got, Value::Number(123.0));
  Ok(())
}

#[test]
fn object_ops_own_property_keys_orders_indices_then_strings_then_symbols() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let hooks = NoHooks;
  let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, WebIdlLimits::default(), &hooks);

  let obj = cx.alloc_object()?;

  // Allocate keys.
  let key_b = alloc_key(&mut cx, "b")?;
  let key_1 = alloc_key(&mut cx, "1")?;
  let key_01 = alloc_key(&mut cx, "01")?;
  let key_0 = alloc_key(&mut cx, "0")?;
  let key_a = alloc_key(&mut cx, "a")?;
  let key_2 = alloc_key(&mut cx, "2")?;

  let sym1 = cx.scope.alloc_symbol(None)?;
  let sym2 = cx.scope.alloc_symbol(None)?;

  // Define in a deliberately mixed order.
  cx.create_data_property_or_throw(obj, PropertyKey::String(key_b), Value::Null)?;
  cx.create_data_property_or_throw(obj, PropertyKey::String(key_1), Value::Null)?;
  cx.create_data_property_or_throw(obj, PropertyKey::String(key_01), Value::Null)?;
  cx.create_data_property_or_throw(obj, PropertyKey::String(key_0), Value::Null)?;
  cx.create_data_property_or_throw(obj, PropertyKey::Symbol(sym1), Value::Null)?;
  cx.create_data_property_or_throw(obj, PropertyKey::String(key_a), Value::Null)?;
  cx.create_data_property_or_throw(obj, PropertyKey::Symbol(sym2), Value::Null)?;
  cx.create_data_property_or_throw(obj, PropertyKey::String(key_2), Value::Null)?;

  let keys = cx.own_property_keys(obj)?;

  let sym1_label = format!("sym{}", cx.scope.heap().get_symbol_id(sym1)?);
  let sym2_label = format!("sym{}", cx.scope.heap().get_symbol_id(sym2)?);

  let rendered: Vec<String> = keys
    .into_iter()
    .map(|k| match k {
      PropertyKey::String(s) => cx.scope.heap().get_string(s).unwrap().to_utf8_lossy(),
      PropertyKey::Symbol(sym) => format!("sym{}", cx.scope.heap().get_symbol_id(sym).unwrap()),
    })
    .collect();

  assert_eq!(
    rendered,
    vec![
      "0".to_string(),
      "1".to_string(),
      "2".to_string(),
      "b".to_string(),
      "01".to_string(),
      "a".to_string(),
      sym1_label,
      sym2_label,
    ]
  );
  Ok(())
}
