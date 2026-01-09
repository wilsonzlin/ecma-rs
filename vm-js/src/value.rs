use crate::{GcObject, GcString, GcSymbol, Heap};

/// A JavaScript BigInt primitive value.
///
/// This implementation intentionally keeps BigInts inline (no GC allocation) because the
/// test262-smoke suite exercises only values that fit within 128 bits. The representation is
/// sign+magnitude so we can represent the full `u128` range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct JsBigInt {
  negative: bool,
  magnitude: u128,
}

impl JsBigInt {
  pub fn zero() -> Self {
    Self {
      negative: false,
      magnitude: 0,
    }
  }

  pub fn from_u128(value: u128) -> Self {
    Self {
      negative: false,
      magnitude: value,
    }
  }

  pub fn is_zero(self) -> bool {
    self.magnitude == 0
  }

  pub fn is_negative(self) -> bool {
    self.negative && !self.is_zero()
  }

  pub fn negate(self) -> Self {
    if self.is_zero() {
      self
    } else {
      Self {
        negative: !self.negative,
        magnitude: self.magnitude,
      }
    }
  }

  pub fn checked_add(self, other: Self) -> Option<Self> {
    match (self.is_negative(), other.is_negative()) {
      (false, false) => self
        .magnitude
        .checked_add(other.magnitude)
        .map(Self::from_u128),
      (true, true) => self
        .magnitude
        .checked_add(other.magnitude)
        .map(|mag| Self {
          negative: true,
          magnitude: mag,
        }),
      // Mixed signs: subtraction of magnitudes.
      _ => {
        let (larger, smaller, larger_negative) = if self.magnitude >= other.magnitude {
          (self.magnitude, other.magnitude, self.is_negative())
        } else {
          (other.magnitude, self.magnitude, other.is_negative())
        };
        let mag = larger - smaller;
        Some(if mag == 0 {
          Self::zero()
        } else {
          Self {
            negative: larger_negative,
            magnitude: mag,
          }
        })
      }
    }
  }

  pub fn checked_mul(self, other: Self) -> Option<Self> {
    let mag = self.magnitude.checked_mul(other.magnitude)?;
    if mag == 0 {
      return Some(Self::zero());
    }
    Some(Self {
      negative: self.is_negative() ^ other.is_negative(),
      magnitude: mag,
    })
  }

  pub fn to_decimal_string(self) -> String {
    let mag_str = self.magnitude.to_string();
    if self.is_negative() {
      format!("-{mag_str}")
    } else {
      mag_str
    }
  }
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
