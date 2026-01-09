use vm_js::{Heap, HeapLimits, VmError};

#[test]
fn utf8_to_utf16_roundtrip_bmp_and_astral() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  // BMP + astral code point (surrogate pair).
  let original = "A\u{2603}\u{1F4A9}B";
  let s = scope.alloc_string_from_utf8(original).unwrap();

  let js = scope.heap().get_string(s).unwrap();
  assert_eq!(js.as_code_units(), &[0x0041, 0x2603, 0xD83D, 0xDCA9, 0x0042]);
  assert_eq!(js.to_utf8_lossy(), original);
}

#[test]
fn lone_surrogate_to_utf8_lossy_does_not_panic() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let s = scope.alloc_string_from_code_units(&[0xD800]).unwrap();
  let js = scope.heap().get_string(s).unwrap();

  assert_eq!(js.as_code_units(), &[0xD800]);
  assert_eq!(js.to_utf8_lossy(), "\u{FFFD}");

  // Debug should never panic.
  let _ = format!("{js:?}");
}

#[test]
fn equality_compares_code_units() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let a = scope
    .alloc_string_from_code_units(&[0x0061, 0xD800, 0x0062])
    .unwrap();
  let b = scope
    .alloc_string_from_code_units(&[0x0061, 0xD800, 0x0062])
    .unwrap();
  let c = scope
    .alloc_string_from_code_units(&[0x0061, 0x0062])
    .unwrap();

  assert_eq!(
    scope.heap().get_string(a).unwrap(),
    scope.heap().get_string(b).unwrap()
  );
  assert_ne!(
    scope.heap().get_string(a).unwrap(),
    scope.heap().get_string(c).unwrap()
  );
}

#[test]
fn heap_limit_is_enforced() {
  let units = vec![0u16; 10];
  let payload_bytes = units.len() * 2;

  // Determine the exact total budget required for this allocation, including heap metadata.
  let required_total = {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    scope.alloc_string_from_code_units(&units).unwrap();
    scope.heap().estimated_total_bytes()
  };

  {
    let mut heap = Heap::new(HeapLimits::new(required_total - 1, required_total - 1));
    let mut scope = heap.scope();
    let err = scope.alloc_string_from_code_units(&units).unwrap_err();
    assert!(matches!(err, VmError::OutOfMemory));
  }

  {
    let mut heap = Heap::new(HeapLimits::new(required_total, required_total));
    let mut scope = heap.scope();
    scope.alloc_string_from_code_units(&units).unwrap();
    assert_eq!(scope.heap().used_bytes(), payload_bytes);
    assert!(
      scope.heap().estimated_total_bytes() <= required_total,
      "expected heap.estimated_total_bytes() <= configured max_bytes"
    );
  }
}
