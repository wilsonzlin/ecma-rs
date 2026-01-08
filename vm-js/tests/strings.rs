use std::mem;

use vm_js::{JsString, Scope, TerminationReason, VmError};

#[test]
fn utf8_to_utf16_roundtrip_bmp_and_astral() {
  let mut scope = Scope::new(1024 * 1024);

  // BMP + astral code point (surrogate pair).
  let original = "A\u{2603}\u{1F4A9}B";
  let s = scope.alloc_string_from_utf8(original).unwrap();

  let js = scope.heap().get_string(s);
  assert_eq!(js.as_code_units(), &[0x0041, 0x2603, 0xD83D, 0xDCA9, 0x0042]);
  assert_eq!(js.to_utf8_lossy(), original);
}

#[test]
fn lone_surrogate_to_utf8_lossy_does_not_panic() {
  let mut scope = Scope::new(1024 * 1024);

  let s = scope.alloc_string_from_code_units(&[0xD800]).unwrap();
  let js = scope.heap().get_string(s);

  assert_eq!(js.as_code_units(), &[0xD800]);
  assert_eq!(js.to_utf8_lossy(), "\u{FFFD}");

  // Debug should never panic.
  let _ = format!("{js:?}");
}

#[test]
fn equality_compares_code_units() {
  let mut scope = Scope::new(1024 * 1024);

  let a = scope
    .alloc_string_from_code_units(&[0x0061, 0xD800, 0x0062])
    .unwrap();
  let b = scope
    .alloc_string_from_code_units(&[0x0061, 0xD800, 0x0062])
    .unwrap();
  let c = scope
    .alloc_string_from_code_units(&[0x0061, 0x0062])
    .unwrap();

  assert_eq!(scope.heap().get_string(a), scope.heap().get_string(b));
  assert_ne!(scope.heap().get_string(a), scope.heap().get_string(c));
}

#[test]
fn heap_limit_is_enforced() {
  let units = vec![0u16; 10];
  let bytes = mem::size_of::<JsString>() + units.len() * 2;

  let mut scope = Scope::new(bytes - 1);
  let err = scope.alloc_string_from_code_units(&units).unwrap_err();
  assert!(matches!(
    err,
    VmError::Termination(ref termination) if termination.reason == TerminationReason::OutOfMemory
  ));

  let mut scope = Scope::new(bytes);
  scope.alloc_string_from_code_units(&units).unwrap();
  assert_eq!(scope.heap().used_bytes(), bytes);
}
