use std::borrow::Cow;
use std::hash::{Hash, Hasher};
use std::ptr::NonNull;

use num_bigint::BigInt;
use num_bigint::Sign;
use num_traits::{ToPrimitive, Zero};

use crate::{GcObject, GcString, GcSymbol, Heap};

/// A JavaScript BigInt primitive value.
///
/// Hybrid representation (keeps [`Value`] `Copy`):
/// - **Inline fast path**: sign + `u128` magnitude for
///   `[-(2^128-1), 2^128-1]` ? no allocation.
/// - **Wide path**: `NonNull<BigInt>` to a `num_bigint::BigInt` allocated for the
///   lifetime of the process (immortal / leaked). Wide BigInts are rare relative
///   to inline ones; tracking them in the GC heap is a follow-up if embedders
///   need reclaimability. Bitwise/`**`/`<<` that exceed 128 bits take this path.
///
/// Bitwise `& | ^ << >>` (?6.1.6.2) use infinite two's-complement semantics.
#[derive(Clone, Copy, Debug)]
pub struct JsBigInt {
  inner: JsBigIntInner,
}

#[derive(Clone, Copy, Debug)]
enum JsBigIntInner {
  Inline {
    negative: bool,
    magnitude: u128,
  },
  /// Immortal `BigInt` (from `Box::leak`). Safe to dereference for the VM process.
  Heap(NonNull<BigInt>),
}

// Safety: `Heap(NonNull<BigInt>)` points at leaked, immutable BigInt data shared
// by Copy handles. No concurrent mutation.
unsafe impl Send for JsBigInt {}
unsafe impl Sync for JsBigInt {}

impl PartialEq for JsBigInt {
  fn eq(&self, other: &Self) -> bool {
    match (self.inner, other.inner) {
      (
        JsBigIntInner::Inline {
          negative: n1,
          magnitude: m1,
        },
        JsBigIntInner::Inline {
          negative: n2,
          magnitude: m2,
        },
      ) => (m1 == 0 && m2 == 0) || (n1 == n2 && m1 == m2),
      _ => self.as_big().as_ref() == other.as_big().as_ref(),
    }
  }
}

impl Eq for JsBigInt {}

impl Hash for JsBigInt {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.as_big().as_ref().hash(state);
  }
}

impl JsBigInt {
  pub fn zero() -> Self {
    Self {
      inner: JsBigIntInner::Inline {
        negative: false,
        magnitude: 0,
      },
    }
  }

  pub fn from_u128(value: u128) -> Self {
    Self {
      inner: JsBigIntInner::Inline {
        negative: false,
        magnitude: value,
      },
    }
  }

  /// Parse a canonical decimal string (as produced by `parse-js` BigInt literals).
  pub fn from_decimal_str(s: &str) -> Option<Self> {
    let b: BigInt = s.parse().ok()?;
    Some(Self::from_big(b))
  }

  /// ECMA-262 `StringToBigInt` / `StringIntegerLiteral` grammar (§7.1.14).
  ///
  /// Trims ECMAScript white space; empty (after trim) → `0n`. Accepts optional
  /// sign + decimal / `0x` / `0b` / `0o` integer text. Returns `None` when the
  /// string is not a StringIntegerLiteral (e.g. `"1.5"`, `"1e2"`, `"foo"`).
  pub fn from_string_integer_literal(s: &str) -> Option<Self> {
    let trimmed = s.trim_matches(|c: char| {
      matches!(
        c,
        '\u{0009}'
          | '\u{000B}'
          | '\u{000C}'
          | '\u{0020}'
          | '\u{00A0}'
          | '\u{FEFF}'
          | '\u{000A}'
          | '\u{000D}'
          | '\u{2028}'
          | '\u{2029}'
      ) || (c >= '\u{1680}'
        && matches!(
          c,
          '\u{1680}'
            | '\u{2000}'
            | '\u{2001}'
            | '\u{2002}'
            | '\u{2003}'
            | '\u{2004}'
            | '\u{2005}'
            | '\u{2006}'
            | '\u{2007}'
            | '\u{2008}'
            | '\u{2009}'
            | '\u{200A}'
            | '\u{202F}'
            | '\u{205F}'
            | '\u{3000}'
        ))
    });
    if trimmed.is_empty() {
      return Some(Self::zero());
    }
    let (negative, rest) = if let Some(r) = trimmed.strip_prefix('-') {
      (true, r)
    } else if let Some(r) = trimmed.strip_prefix('+') {
      (false, r)
    } else {
      (false, trimmed)
    };
    if rest.is_empty() {
      return None;
    }
    let (radix, digits) =
      if let Some(d) = rest.strip_prefix("0x").or_else(|| rest.strip_prefix("0X")) {
        (16, d)
      } else if let Some(d) = rest.strip_prefix("0b").or_else(|| rest.strip_prefix("0B")) {
        (2, d)
      } else if let Some(d) = rest.strip_prefix("0o").or_else(|| rest.strip_prefix("0O")) {
        (8, d)
      } else {
        (10, rest)
      };
    if digits.is_empty() {
      return None;
    }
    // Reject non-integer forms that `str::parse` / radix parsers may not cover
    // uniformly (exponent, decimal point, underscore separators deferred).
    if digits
      .bytes()
      .any(|b| b == b'.' || b == b'e' || b == b'E' || b == b'+' || b == b'-' || b == b'_')
    {
      return None;
    }
    let b = BigInt::parse_bytes(digits.as_bytes(), radix)?;
    let b = if negative { -b } else { b };
    Some(Self::from_big(b))
  }

  fn from_big(b: BigInt) -> Self {
    if b.is_zero() {
      return Self::zero();
    }
    let negative = b.sign() == Sign::Minus;
    let mag = b.magnitude();
    if let Some(magnitude) = mag.to_u128() {
      Self {
        inner: JsBigIntInner::Inline {
          negative,
          magnitude,
        },
      }
    } else {
      let leaked: &'static BigInt = Box::leak(Box::new(b));
      Self {
        inner: JsBigIntInner::Heap(NonNull::from(leaked)),
      }
    }
  }

  fn as_big(self) -> Cow<'static, BigInt> {
    match self.inner {
      JsBigIntInner::Inline {
        negative,
        magnitude,
      } => {
        let mut b = BigInt::from(magnitude);
        if negative {
          b = -b;
        }
        Cow::Owned(b)
      }
      JsBigIntInner::Heap(ptr) => {
        // SAFETY: pointer from `Box::leak` in `from_big`; never freed.
        Cow::Borrowed(unsafe { ptr.as_ref() })
      }
    }
  }

  fn inline_parts(self) -> Option<(bool, u128)> {
    match self.inner {
      JsBigIntInner::Inline {
        negative,
        magnitude,
      } => Some((negative, magnitude)),
      JsBigIntInner::Heap(_) => None,
    }
  }

  pub fn is_zero(self) -> bool {
    match self.inner {
      JsBigIntInner::Inline { magnitude, .. } => magnitude == 0,
      JsBigIntInner::Heap(ptr) => unsafe { ptr.as_ref() }.is_zero(),
    }
  }

  pub fn is_negative(self) -> bool {
    match self.inner {
      JsBigIntInner::Inline {
        negative,
        magnitude,
      } => negative && magnitude != 0,
      JsBigIntInner::Heap(ptr) => unsafe { ptr.as_ref() }.sign() == Sign::Minus,
    }
  }

  pub fn negate(self) -> Self {
    if self.is_zero() {
      return Self::zero();
    }
    match self.inner {
      JsBigIntInner::Inline {
        negative,
        magnitude,
      } => Self {
        inner: JsBigIntInner::Inline {
          negative: !negative,
          magnitude,
        },
      },
      JsBigIntInner::Heap(_) => Self::from_big(-self.as_big().as_ref()),
    }
  }

  pub fn checked_add(self, other: Self) -> Option<Self> {
    if let (Some(_), Some(_)) = (self.inline_parts(), other.inline_parts()) {
      if let Some(out) = inline_checked_add(self, other) {
        return Some(out);
      }
    }
    Some(Self::from_big(
      self.as_big().as_ref() + other.as_big().as_ref(),
    ))
  }

  pub fn checked_mul(self, other: Self) -> Option<Self> {
    match (self.inline_parts(), other.inline_parts()) {
      (Some((sn, sm)), Some((on, om))) => {
        if let Some(mag) = sm.checked_mul(om) {
          if mag == 0 {
            return Some(Self::zero());
          }
          return Some(Self {
            inner: JsBigIntInner::Inline {
              negative: sn ^ on,
              magnitude: mag,
            },
          });
        }
      }
      _ => {}
    }
    Some(Self::from_big(
      self.as_big().as_ref() * other.as_big().as_ref(),
    ))
  }

  /// ECMA-262 `BigInt::subtract`. Implemented as `x + (-y)`.
  pub fn checked_sub(self, other: Self) -> Option<Self> {
    self.checked_add(other.negate())
  }

  /// ECMA-262 `BigInt::divide` (?6.1.6.2.5): integer division truncated toward
  /// zero. Returns `None` when `other` is zero (the caller throws `RangeError`).
  pub fn checked_div(self, other: Self) -> Option<Self> {
    if other.is_zero() {
      return None;
    }
    match (self.inline_parts(), other.inline_parts()) {
      (Some((sn, sm)), Some((on, om))) => {
        let mag = sm / om;
        return Some(if mag == 0 {
          Self::zero()
        } else {
          Self {
            inner: JsBigIntInner::Inline {
              negative: sn ^ on,
              magnitude: mag,
            },
          }
        });
      }
      _ => {}
    }
    Some(Self::from_big(
      self.as_big().as_ref() / other.as_big().as_ref(),
    ))
  }

  /// ECMA-262 `BigInt::remainder` (?6.1.6.2.6): the result has the sign of the
  /// dividend. Returns `None` when `other` is zero (the caller throws `RangeError`).
  pub fn checked_rem(self, other: Self) -> Option<Self> {
    if other.is_zero() {
      return None;
    }
    match (self.inline_parts(), other.inline_parts()) {
      (Some((sn, sm)), Some((_, om))) => {
        let mag = sm % om;
        return Some(if mag == 0 {
          Self::zero()
        } else {
          Self {
            inner: JsBigIntInner::Inline {
              negative: sn,
              magnitude: mag,
            },
          }
        });
      }
      _ => {}
    }
    Some(Self::from_big(
      self.as_big().as_ref() % other.as_big().as_ref(),
    ))
  }

  /// ECMA-262 `BigInt::exponentiate` (?6.1.6.2.3) for a non-negative `exponent`.
  /// The caller must reject negative exponents (`RangeError`) before calling.
  pub fn checked_pow(self, exponent: Self) -> Option<Self> {
    debug_assert!(
      !exponent.is_negative(),
      "caller must reject negative exponents"
    );
    if exponent.is_zero() {
      return Some(Self::from_u128(1));
    }
    if self.is_zero() {
      return Some(Self::zero());
    }
    if let Some((_, 1)) = self.inline_parts() {
      let negative = self.is_negative() && exponent_is_odd(exponent);
      return Some(Self {
        inner: JsBigIntInner::Inline {
          negative,
          magnitude: 1,
        },
      });
    }
    match (self.inline_parts(), exponent.inline_parts()) {
      (Some((sn, sm)), Some((false, em))) => {
        if let Ok(exp) = u32::try_from(em) {
          if let Some(mag) = sm.checked_pow(exp) {
            return Some(Self {
              inner: JsBigIntInner::Inline {
                negative: sn && (exp % 2 == 1),
                magnitude: mag,
              },
            });
          }
        }
      }
      _ => {}
    }
    let exp_u32 = exponent.as_big().to_u32()?;
    Some(Self::from_big(self.as_big().as_ref().pow(exp_u32)))
  }

  /// Best-effort conversion to `f64`. Large magnitudes become ?Infinity when
  /// outside the finite `f64` range.
  pub fn to_f64(self) -> f64 {
    match self.inner {
      JsBigIntInner::Inline {
        negative,
        magnitude,
      } => {
        let mag = magnitude as f64;
        if negative {
          -mag
        } else {
          mag
        }
      }
      JsBigIntInner::Heap(_) => bigint_to_f64(self.as_big().as_ref()),
    }
  }

  /// Exact mathematical equality with a Number (ECMA-262 abstract equality for
  /// BigInt/Number). Non-finite / non-integer Numbers are never equal.
  pub fn mathematically_equal_to_number(self, n: f64) -> bool {
    let Some(n_bi) = f64_to_bigint_if_integer(n) else {
      return false;
    };
    self.as_big().as_ref() == &n_bi
  }

  /// ECMA-262 mixed BigInt/Number `lessThan` via mathematical values (?7.2.15).
  pub fn less_than_number(self, n: f64) -> Option<bool> {
    if n.is_nan() {
      return None;
    }
    if n == f64::INFINITY {
      return Some(true);
    }
    if n == f64::NEG_INFINITY {
      return Some(false);
    }
    if let Some(n_bi) = f64_to_bigint_if_integer(n) {
      return Some(self.as_big().as_ref() < &n_bi);
    }
    // Non-integer finite: bigint < n ? bigint <= floor(n)
    let floor = n.floor();
    let floor_bi = f64_to_bigint_if_integer(floor).expect("floor of finite is finite integer");
    Some(self.as_big().as_ref() <= &floor_bi)
  }

  /// ECMA-262 `BigInt::lessThan` (?6.1.6.2.12).
  pub fn less_than(self, other: Self) -> bool {
    match (self.inline_parts(), other.inline_parts()) {
      (Some((sn, sm)), Some((on, om))) => match (sn, on) {
        (true, false) => true,
        (false, true) => false,
        (false, false) => sm < om,
        (true, true) => sm > om,
      },
      _ => self.as_big().as_ref() < other.as_big().as_ref(),
    }
  }

  pub fn to_decimal_string(self) -> String {
    match self.inner {
      JsBigIntInner::Inline {
        negative,
        magnitude,
      } => {
        let mag_str = magnitude.to_string();
        if negative {
          format!("-{mag_str}")
        } else {
          mag_str
        }
      }
      JsBigIntInner::Heap(_) => self.as_big().to_str_radix(10),
    }
  }

  fn twos_complement_inline(negative: bool, magnitude: u128) -> (u128, bool) {
    if negative && magnitude != 0 {
      (magnitude.wrapping_neg(), true)
    } else {
      (magnitude, false)
    }
  }

  fn from_twos_complement_inline(low: u128, sign_ext: bool) -> Option<Self> {
    if !sign_ext {
      Some(Self::from_u128(low))
    } else {
      let magnitude = low.wrapping_neg();
      if magnitude == 0 {
        // -2^128: promote to wide path.
        let mut b = BigInt::from(1u8) << 128u32;
        b = -b;
        Some(Self::from_big(b))
      } else {
        Some(Self {
          inner: JsBigIntInner::Inline {
            negative: true,
            magnitude,
          },
        })
      }
    }
  }

  /// ECMA-262 `BigInt::bitwiseAND` (?6.1.6.2.20).
  pub fn checked_bit_and(self, other: Self) -> Option<Self> {
    match (self.inline_parts(), other.inline_parts()) {
      (Some((sn, sm)), Some((on, om))) => {
        let (xl, xs) = Self::twos_complement_inline(sn, sm);
        let (yl, ys) = Self::twos_complement_inline(on, om);
        return Self::from_twos_complement_inline(xl & yl, xs & ys);
      }
      _ => {}
    }
    Some(Self::from_big(
      self.as_big().as_ref() & other.as_big().as_ref(),
    ))
  }

  /// ECMA-262 `BigInt::bitwiseOR` (?6.1.6.2.22).
  pub fn checked_bit_or(self, other: Self) -> Option<Self> {
    match (self.inline_parts(), other.inline_parts()) {
      (Some((sn, sm)), Some((on, om))) => {
        let (xl, xs) = Self::twos_complement_inline(sn, sm);
        let (yl, ys) = Self::twos_complement_inline(on, om);
        return Self::from_twos_complement_inline(xl | yl, xs | ys);
      }
      _ => {}
    }
    Some(Self::from_big(
      self.as_big().as_ref() | other.as_big().as_ref(),
    ))
  }

  /// ECMA-262 `BigInt::bitwiseXOR` (?6.1.6.2.21).
  pub fn checked_bit_xor(self, other: Self) -> Option<Self> {
    match (self.inline_parts(), other.inline_parts()) {
      (Some((sn, sm)), Some((on, om))) => {
        let (xl, xs) = Self::twos_complement_inline(sn, sm);
        let (yl, ys) = Self::twos_complement_inline(on, om);
        return Self::from_twos_complement_inline(xl ^ yl, xs ^ ys);
      }
      _ => {}
    }
    Some(Self::from_big(
      self.as_big().as_ref() ^ other.as_big().as_ref(),
    ))
  }

  /// ECMA-262 `BigInt::leftShift` (?6.1.6.2.18).
  pub fn checked_shift_left(self, shift: Self) -> Option<Self> {
    if shift.is_negative() {
      return self.checked_shift_right(shift.negate());
    }
    if self.is_zero() {
      return Some(Self::zero());
    }
    match (self.inline_parts(), shift.inline_parts()) {
      (Some((sn, sm)), Some((false, nmag))) => {
        if let Ok(n) = u32::try_from(nmag) {
          if n < 128 && sm.leading_zeros() >= n {
            return Some(Self {
              inner: JsBigIntInner::Inline {
                negative: sn,
                magnitude: sm << n,
              },
            });
          }
        }
      }
      _ => {}
    }
    let n = shift.as_big().to_u32()?;
    Some(Self::from_big(self.as_big().as_ref() << n))
  }

  /// ECMA-262 `BigInt::signedRightShift` (?6.1.6.2.19).
  pub fn checked_shift_right(self, shift: Self) -> Option<Self> {
    if shift.is_negative() {
      return self.checked_shift_left(shift.negate());
    }
    match (self.inline_parts(), shift.inline_parts()) {
      (Some((sn, sm)), Some((false, nmag))) => {
        let (low, sign_ext) = Self::twos_complement_inline(sn, sm);
        let Ok(n) = u32::try_from(nmag) else {
          let filled = if sign_ext { u128::MAX } else { 0 };
          return Self::from_twos_complement_inline(filled, sign_ext);
        };
        if n == 0 {
          return Some(self);
        }
        if n >= 128 {
          let filled = if sign_ext { u128::MAX } else { 0 };
          return Self::from_twos_complement_inline(filled, sign_ext);
        }
        let fill = if sign_ext { u128::MAX << (128 - n) } else { 0 };
        let result_low = (low >> n) | fill;
        return Self::from_twos_complement_inline(result_low, sign_ext);
      }
      _ => {}
    }
    let n = shift.as_big().to_u32()?;
    Some(Self::from_big(self.as_big().as_ref() >> n))
  }
}

fn exponent_is_odd(exponent: JsBigInt) -> bool {
  match exponent.inline_parts() {
    Some((_, mag)) => mag % 2 == 1,
    None => exponent.as_big().as_ref() % 2u8 == BigInt::from(1),
  }
}

fn inline_checked_add(self_v: JsBigInt, other: JsBigInt) -> Option<JsBigInt> {
  let (Some((sn, sm)), Some((on, om))) = (self_v.inline_parts(), other.inline_parts()) else {
    return None;
  };
  match (sn, on) {
    (false, false) => sm.checked_add(om).map(JsBigInt::from_u128),
    (true, true) => sm.checked_add(om).map(|mag| JsBigInt {
      inner: JsBigIntInner::Inline {
        negative: true,
        magnitude: mag,
      },
    }),
    _ => {
      let (larger, smaller, larger_negative) = if sm >= om { (sm, om, sn) } else { (om, sm, on) };
      let mag = larger - smaller;
      Some(if mag == 0 {
        JsBigInt::zero()
      } else {
        JsBigInt {
          inner: JsBigIntInner::Inline {
            negative: larger_negative,
            magnitude: mag,
          },
        }
      })
    }
  }
}

fn f64_to_bigint_if_integer(n: f64) -> Option<BigInt> {
  if !n.is_finite() {
    return None;
  }
  if n.fract() != 0.0 {
    return None;
  }
  f64_to_bigint_bits(n)
}

fn f64_to_bigint_bits(n: f64) -> Option<BigInt> {
  if !n.is_finite() {
    return None;
  }
  if n == 0.0 {
    return Some(BigInt::from(0));
  }
  let bits = n.to_bits();
  let negative = (bits >> 63) != 0;
  let exp = ((bits >> 52) & 0x7ff) as i32;
  let mut mant = bits & 0x000f_ffff_ffff_ffff;
  if exp == 0 {
    // Subnormals are never non-zero integers.
    return None;
  }
  mant |= 1u64 << 52;
  let shift = exp - 1023 - 52;
  let mut result = BigInt::from(mant);
  if shift > 0 {
    result <<= shift as u32;
  } else if shift < 0 {
    let rshift = (-shift) as u32;
    if rshift > 52 {
      return None;
    }
    let mask = (1u64 << rshift) - 1;
    if (mant & mask) != 0 {
      return None;
    }
    result >>= rshift;
  }
  if negative {
    result = -result;
  }
  Some(result)
}

fn bigint_to_f64(b: &BigInt) -> f64 {
  if b.is_zero() {
    return 0.0;
  }
  let negative = b.sign() == Sign::Minus;
  let bits = b.magnitude().bits();
  if bits > 1024 {
    return if negative {
      f64::NEG_INFINITY
    } else {
      f64::INFINITY
    };
  }
  let s = b.to_str_radix(10);
  s.parse().unwrap_or(if negative {
    f64::NEG_INFINITY
  } else {
    f64::INFINITY
  })
}

/// A JavaScript value.
///
/// This is the VM's canonical value representation. Heap-allocated values are represented using
/// GC-managed handles (e.g. [`GcString`]).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value {
  /// The JavaScript `undefined` value.
  Undefined,
  /// The JavaScript `null` value.
  Null,
  /// A JavaScript boolean.
  Bool(bool),
  /// A JavaScript number (IEEE-754 double).
  Number(f64),
  /// A JavaScript BigInt.
  BigInt(JsBigInt),
  /// A GC-managed JavaScript string.
  String(GcString),
  /// A GC-managed JavaScript symbol.
  Symbol(GcSymbol),
  /// A GC-managed JavaScript object.
  Object(GcObject),
}

impl Value {
  /// ECMAScript `SameValue(x, y)`.
  ///
  /// This differs from `==`/`===` for Numbers:
  /// - `NaN` is the same as `NaN`
  /// - `+0` and `-0` are distinct
  pub fn same_value(self, other: Self, heap: &Heap) -> bool {
    match (self, other) {
      (Value::Undefined, Value::Undefined) => true,
      (Value::Null, Value::Null) => true,
      (Value::Bool(a), Value::Bool(b)) => a == b,
      (Value::Number(a), Value::Number(b)) => {
        if a.is_nan() && b.is_nan() {
          return true;
        }
        if a == 0.0 && b == 0.0 {
          // Distinguish +0 and -0.
          return a.to_bits() == b.to_bits();
        }
        a == b
      }
      (Value::BigInt(a), Value::BigInt(b)) => a == b,
      (Value::String(a), Value::String(b)) => {
        let Ok(a) = heap.get_string(a) else {
          return false;
        };
        let Ok(b) = heap.get_string(b) else {
          return false;
        };
        a.as_code_units() == b.as_code_units()
      }
      (Value::Symbol(a), Value::Symbol(b)) => a == b,
      (Value::Object(a), Value::Object(b)) => a == b,
      _ => false,
    }
  }

  /// ECMAScript `SameValueZero(x, y)` (ECMA-262 §7.2.11).
  ///
  /// Like [`Self::same_value`], except `+0` and `-0` are equal. Used by Map/Set key equality.
  pub fn same_value_zero(self, other: Self, heap: &Heap) -> bool {
    match (self, other) {
      (Value::Number(a), Value::Number(b)) => {
        if a.is_nan() && b.is_nan() {
          return true;
        }
        // IEEE-754: `+0.0 == -0.0`.
        a == b
      }
      _ => self.same_value(other, heap),
    }
  }
}

impl From<GcString> for Value {
  fn from(value: GcString) -> Self {
    Self::String(value)
  }
}

impl From<GcSymbol> for Value {
  fn from(value: GcSymbol) -> Self {
    Self::Symbol(value)
  }
}

impl From<GcObject> for Value {
  fn from(value: GcObject) -> Self {
    Self::Object(value)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn inline_add_mul_stay_inline() {
    let a = JsBigInt::from_u128(10);
    let b = JsBigInt::from_u128(20);
    let s = a.checked_add(b).unwrap();
    assert_eq!(s, JsBigInt::from_u128(30));
    assert!(matches!(s.inner, JsBigIntInner::Inline { .. }));
  }

  #[test]
  fn large_literal_and_pow_use_wide_path() {
    let lit = JsBigInt::from_decimal_str(
      "179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368",
    )
    .unwrap();
    assert!(matches!(lit.inner, JsBigIntInner::Heap(_)));
    assert!(lit.mathematically_equal_to_number(f64::MAX));

    let base = JsBigInt::from_u128(2);
    let exp = JsBigInt::from_u128(200);
    let p = base.checked_pow(exp).unwrap();
    assert!(matches!(p.inner, JsBigIntInner::Heap(_)));
    assert_eq!(
      p.to_decimal_string(),
      (BigInt::from(2u8).pow(200)).to_str_radix(10)
    );
  }

  #[test]
  fn shift_beyond_128_bits() {
    let x = JsBigInt::from_u128(1);
    let s = JsBigInt::from_u128(200);
    let out = x.checked_shift_left(s).unwrap();
    assert_eq!(out, JsBigInt::from_big(BigInt::from(1u8) << 200u32));
  }

  #[test]
  fn bitwise_negatives_and_minus_two_pow_128() {
    let neg1 = JsBigInt::from_u128(1).negate();
    assert_eq!(neg1.checked_bit_and(neg1).unwrap(), neg1);
    let low0_sign = JsBigInt::from_twos_complement_inline(0, true).unwrap();
    assert!(low0_sign.is_negative());
    assert_eq!(
      low0_sign.to_decimal_string(),
      (-(BigInt::from(1u8) << 128u32)).to_str_radix(10)
    );
  }
}
