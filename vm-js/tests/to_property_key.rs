use vm_js::{Heap, HeapLimits, PropertyKey, Value, VmError};

#[test]
fn to_property_key_number_produces_string_key() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let key = heap.to_property_key(Value::Number(1.0))?;
  let PropertyKey::String(s) = key else {
    panic!("expected string key, got {key:?}");
  };
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "1");
  Ok(())
}

#[test]
fn to_property_key_bool_produces_string_key() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let key = heap.to_property_key(Value::Bool(true))?;
  let PropertyKey::String(s) = key else {
    panic!("expected string key, got {key:?}");
  };
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "true");
  Ok(())
}

