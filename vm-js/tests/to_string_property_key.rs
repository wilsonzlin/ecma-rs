use vm_js::{Heap, HeapLimits, PropertyKey, Value, VmError};

fn assert_to_string(heap: &mut Heap, value: Value, expected: &str) {
  let s = heap.to_string(value).expect("ToString");
  let actual = heap.get_string(s).expect("get string").to_utf8_lossy();
  assert_eq!(actual, expected);
}

#[test]
fn to_string_primitives() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  // String returns as-is.
  let hello = {
    let mut scope = heap.scope();
    scope.alloc_string("hello").expect("alloc string")
  };
  let _hello_root = heap.add_root(Value::String(hello));
  assert_eq!(heap.to_string(Value::String(hello)).unwrap(), hello);

  assert_to_string(&mut heap, Value::Undefined, "undefined");
  assert_to_string(&mut heap, Value::Null, "null");
  assert_to_string(&mut heap, Value::Bool(true), "true");
  assert_to_string(&mut heap, Value::Bool(false), "false");

  // Number corner cases.
  assert_to_string(&mut heap, Value::Number(f64::NAN), "NaN");
  assert_to_string(&mut heap, Value::Number(0.0), "0");
  assert_to_string(&mut heap, Value::Number(-0.0), "0");
  assert_to_string(&mut heap, Value::Number(f64::INFINITY), "Infinity");
  assert_to_string(&mut heap, Value::Number(f64::NEG_INFINITY), "-Infinity");

  // A representative normal number (shortest-roundtrip formatting).
  assert_to_string(&mut heap, Value::Number(1.5), "1.5");

  // Symbol throws.
  let sym = {
    let mut scope = heap.scope();
    scope.alloc_symbol(Some("desc")).expect("alloc symbol")
  };
  let _sym_root = heap.add_root(Value::Symbol(sym));
  let err = heap.to_string(Value::Symbol(sym)).unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));

  // Object coercion is not implemented yet.
  let obj = {
    let mut scope = heap.scope();
    scope.alloc_object().expect("alloc object")
  };
  let _obj_root = heap.add_root(Value::Object(obj));
  let err = heap.to_string(Value::Object(obj)).unwrap_err();
  assert!(matches!(err, VmError::Unimplemented(_)));
}

#[test]
fn to_property_key_primitives() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let foo = {
    let mut scope = heap.scope();
    scope.alloc_string("foo").expect("alloc string")
  };
  let _foo_root = heap.add_root(Value::String(foo));

  let sym = {
    let mut scope = heap.scope();
    scope.alloc_symbol(Some("desc")).expect("alloc symbol")
  };
  let _sym_root = heap.add_root(Value::Symbol(sym));

  assert!(matches!(
    heap.to_property_key(Value::String(foo)).unwrap(),
    PropertyKey::String(s) if s == foo
  ));
  assert!(matches!(
    heap.to_property_key(Value::Symbol(sym)).unwrap(),
    PropertyKey::Symbol(s) if s == sym
  ));

  // Other primitives go through ToString.
  match heap.to_property_key(Value::Undefined).unwrap() {
    PropertyKey::String(s) => assert_eq!(heap.get_string(s).unwrap().to_utf8_lossy(), "undefined"),
    _ => panic!("expected string key"),
  }
  match heap.to_property_key(Value::Null).unwrap() {
    PropertyKey::String(s) => assert_eq!(heap.get_string(s).unwrap().to_utf8_lossy(), "null"),
    _ => panic!("expected string key"),
  }
  match heap.to_property_key(Value::Bool(true)).unwrap() {
    PropertyKey::String(s) => assert_eq!(heap.get_string(s).unwrap().to_utf8_lossy(), "true"),
    _ => panic!("expected string key"),
  }
  match heap.to_property_key(Value::Bool(false)).unwrap() {
    PropertyKey::String(s) => assert_eq!(heap.get_string(s).unwrap().to_utf8_lossy(), "false"),
    _ => panic!("expected string key"),
  }
  match heap.to_property_key(Value::Number(-0.0)).unwrap() {
    PropertyKey::String(s) => assert_eq!(heap.get_string(s).unwrap().to_utf8_lossy(), "0"),
    _ => panic!("expected string key"),
  }
  match heap.to_property_key(Value::Number(f64::NAN)).unwrap() {
    PropertyKey::String(s) => assert_eq!(heap.get_string(s).unwrap().to_utf8_lossy(), "NaN"),
    _ => panic!("expected string key"),
  }

  // Object coercion is not implemented yet.
  let obj = {
    let mut scope = heap.scope();
    scope.alloc_object().expect("alloc object")
  };
  let _obj_root = heap.add_root(Value::Object(obj));
  let err = heap.to_property_key(Value::Object(obj)).unwrap_err();
  assert!(matches!(err, VmError::Unimplemented(_)));
}
