use vm_js::{Heap, HeapLimits, PropertyKey, Value, VmError};

fn assert_string_key(heap: &Heap, key: PropertyKey, expected: &str) {
  match key {
    PropertyKey::String(s) => assert_eq!(heap.get_string(s).unwrap().to_utf8_lossy(), expected),
    PropertyKey::Symbol(_) => panic!("expected a string property key"),
  }
}

#[test]
fn to_property_key_number_zero_and_negative_zero() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let key = heap.to_property_key(Value::Number(0.0))?;
  assert_string_key(&heap, key, "0");

  let key = heap.to_property_key(Value::Number(-0.0))?;
  assert_string_key(&heap, key, "0");

  Ok(())
}

#[test]
fn to_property_key_number_decimal() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let key = heap.to_property_key(Value::Number(1.5))?;
  assert_string_key(&heap, key, "1.5");

  Ok(())
}

#[test]
fn to_property_key_number_nan_and_infinity() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let key = heap.to_property_key(Value::Number(f64::NAN))?;
  assert_string_key(&heap, key, "NaN");

  let key = heap.to_property_key(Value::Number(f64::INFINITY))?;
  assert_string_key(&heap, key, "Infinity");

  let key = heap.to_property_key(Value::Number(f64::NEG_INFINITY))?;
  assert_string_key(&heap, key, "-Infinity");

  Ok(())
}

#[test]
fn to_property_key_bool_true() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let key = heap.to_property_key(Value::Bool(true))?;
  assert_string_key(&heap, key, "true");

  Ok(())
}

#[test]
fn to_string_symbol_is_type_error() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let sym = {
    let mut scope = heap.scope();
    scope.alloc_symbol(None)?
  };

  let err = heap.to_string(Value::Symbol(sym)).unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));

  Ok(())
}

#[test]
fn to_property_key_number_avoids_exponent_for_common_ranges() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  // `ToString(1000000000)` is `"1000000000"` (not `"1e9"`).
  let key = heap.to_property_key(Value::Number(1_000_000_000.0))?;
  assert_string_key(&heap, key, "1000000000");

  // `ToString(0.000001)` is `"0.000001"` (not `"1e-6"`).
  let key = heap.to_property_key(Value::Number(0.000001))?;
  assert_string_key(&heap, key, "0.000001");

  Ok(())
}

#[test]
fn to_property_key_object_is_string_placeholder() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let obj = {
    let mut scope = heap.scope();
    scope.alloc_object()?
  };

  let key = heap.to_property_key(Value::Object(obj))?;
  assert_string_key(&heap, key, "[object Object]");

  Ok(())
}
