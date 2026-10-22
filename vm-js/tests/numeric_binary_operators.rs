//! Regression tests for the numeric/bitwise/shift/exponentiation binary
//! operators, the sequence (comma) operator, and Abstract Relational Comparison.
//!
//! Expected values are derived from ECMA-262 (§7.2.15, §13.5.6, §13.6, §13.9,
//! §13.10, §13.12, §13.16), not from the interpreter's current output.

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn eval(src: &str) -> Value {
  new_runtime().exec_script(src).unwrap()
}

fn assert_true(src: &str) {
  assert_eq!(eval(src), Value::Bool(true), "expected `{src}` to be true");
}

#[test]
fn bitwise_operators_operate_on_toint32() {
  // ECMA-262 §13.12: BitwiseAND/OR/XOR coerce via ToInt32.
  assert_true("(5 & 3) === 1");
  assert_true("(5 | 2) === 7");
  assert_true("(5 ^ 1) === 4");
  // ToInt32(4294967295) === -1, so `| 0` reveals the wrap-around.
  assert_true("(4294967295 | 0) === -1");
  // ToInt32 ignores the fractional part and bits above 2^32.
  assert_true("(4294967296 | 0) === 0");
}

#[test]
fn bitwise_not_is_minus_x_minus_one() {
  // ECMA-262 §13.5.6 / Number::bitwiseNOT: ~x === -(ToInt32(x)) - 1.
  assert_true("(~5) === -6");
  assert_true("(~-1) === 0");
  assert_true("(~0) === -1");
}

#[test]
fn shift_operators() {
  // ECMA-262 §13.9. Shift count is ToUint32(rhs) & 0x1F.
  assert_true("(1 << 4) === 16");
  // >> is sign-propagating (arithmetic).
  assert_true("(-8 >> 1) === -4");
  // >>> is zero-filling (logical): -1 is 0xFFFFFFFF, shifted right 28 → 0xF.
  assert_true("(-1 >>> 28) === 15");
  // A shift count of 32 masks to 0, leaving the value unchanged.
  assert_true("(1 << 32) === 1");
}

#[test]
fn exponentiation_matches_number_exponentiate() {
  // ECMA-262 §13.6 / Number::exponentiate.
  assert_true("(2 ** 10) === 1024");
  assert_true("(2 ** -1) === 0.5");
  // `(-1) ** Infinity` is NaN (differs from IEEE-754 pow). NaN !== NaN.
  assert_true("((-1) ** (1/0)) !== ((-1) ** (1/0))");
  // Anything ** 0 is 1, even NaN.
  assert_true("((0/0) ** 0) === 1");
}

#[test]
fn subtraction_division_remainder() {
  assert_true("(7 - 2) === 5");
  assert_true("(7 / 2) === 3.5");
  // Number::remainder takes the sign of the dividend.
  assert_true("(-5 % 3) === -2");
  assert_true("(5 % -3) === 2");
}

#[test]
fn relational_string_comparison_uses_code_units() {
  // ECMA-262 §7.2.15 step 3.a: strings compare by UTF-16 code units, not numerically.
  assert_true("('a' < 'b')");
  assert_true("!('b' < 'a')");
  assert_true("('abc' < 'abd')");
  // '2' (U+0032) > '1' (U+0031), so "2" is NOT less than "10" as strings...
  assert_true("!('2' < '10')");
  // ...whereas the numeric comparison is the opposite.
  assert_true("(2 < 10)");
}

#[test]
fn relational_nan_yields_false() {
  // A NaN operand makes IsLessThan return undefined, which every operator maps
  // to false (ECMA-262 §13.10.1).
  assert_true("!((0/0) < 1)");
  assert_true("!((0/0) > 1)");
  assert_true("!((0/0) <= 1)");
  assert_true("!((0/0) >= 1)");
  assert_true("!(1 <= (0/0))");
}

#[test]
fn relational_bigint_string_uses_string_to_bigint() {
  // ECMA-262 §7.2.15: BigInt↔String goes through StringToBigInt, not ToNumber.
  // Incomparable strings → undefined → `<`/`>` false; `<=`/`>=` also false.
  assert_true("!(1n > '0.')");
  assert_true("!(1n >= '0.')");
  assert_true("!('0.' < 1n)");
  assert_true("!('0.' <= 1n)");
  // Past Number.MAX_SAFE_INTEGER: must not round the string through f64.
  assert_true("9007199254740993n > '9007199254740992'");
  assert_true("'9007199254740993' > 9007199254740992n");
  assert_true("!(9007199254740993n <= '9007199254740992')");
  assert_true("!('9007199254740993' <= 9007199254740992n)");
  assert_true("16n > '0xF'");
  assert_true("'0x10' > 15n");
}

#[test]
fn comma_operator_returns_right_operand() {
  // ECMA-262 §13.16: evaluate the left operand (for side effects) and return the right.
  assert_eq!(eval("(1, 2, 3)"), Value::Number(3.0));
  assert_true("(function(){ var x = 0; return (x = 5, x); })() === 5");
}
