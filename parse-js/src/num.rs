use core::hash::Hash;
use core::hash::Hasher;
use num_bigint::BigUint;
use serde::Serialize;
use serde::Serializer;
use std::cmp::Ordering;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;

#[derive(Copy, Clone, Debug)]
pub struct JsNumber(pub f64);

impl JsNumber {
  /// Parse a source text numeric literal (with prefixes/separators) into a JS number value.
  pub fn from_literal(raw: &str) -> Option<Self> {
    parse_number_literal(raw).map(Self)
  }

  fn is_negative_zero(self) -> bool {
    self.0 == 0.0 && self.0.is_sign_negative()
  }

  pub fn to_bits(self) -> u64 {
    self.0.to_bits()
  }
}

impl Display for JsNumber {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    if self.0.is_infinite() {
      if self.0.is_sign_negative() {
        return f.write_str("-1e400");
      } else {
        return f.write_str("1e400");
      }
    }

    if self.0.is_nan() {
      // There is no numeric literal for NaN. Fall back to the identifier.
      return f.write_str("NaN");
    }

    if self.is_negative_zero() {
      return f.write_str("-0");
    }

    if self.0 == 0.0 {
      return f.write_str("0");
    }

    let mut buffer = ryu::Buffer::new();
    let formatted = buffer.format_finite(self.0);
    if let Some(stripped) = formatted.strip_suffix(".0") {
      f.write_str(stripped)
    } else {
      f.write_str(formatted)
    }
  }
}

impl PartialEq for JsNumber {
  fn eq(&self, other: &Self) -> bool {
    if self.0.is_nan() {
      return other.0.is_nan();
    };
    self.0.eq(&other.0)
  }
}

impl Eq for JsNumber {}

impl Ord for JsNumber {
  fn cmp(&self, other: &Self) -> Ordering {
    // Only NaNs cannot be compared, and we treat them as equal.
    self.0.partial_cmp(&other.0).unwrap_or(Ordering::Equal)
  }
}

impl PartialOrd for JsNumber {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Hash for JsNumber {
  fn hash<H: Hasher>(&self, state: &mut H) {
    if !self.0.is_nan() {
      self.0.to_bits().hash(state);
    };
  }
}

impl Serialize for JsNumber {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_f64(self.0)
  }
}

fn strip_numeric_separators(raw: &str) -> String {
  raw.chars().filter(|c| *c != '_').collect()
}

fn parse_decimal(raw: &str) -> Option<f64> {
  fast_float::parse(raw).ok()
}

fn parse_decimal_literal(raw: &str) -> Option<f64> {
  let mut cleaned = strip_numeric_separators(raw);
  if cleaned.starts_with('.') {
    cleaned.insert(0, '0');
  }
  if cleaned.ends_with('.') {
    cleaned.push('0');
  }
  parse_decimal(&cleaned)
}

fn parse_integer_literal(raw_digits: &str, radix: u32) -> Option<f64> {
  let cleaned = strip_numeric_separators(raw_digits);
  if cleaned.is_empty() {
    return None;
  }
  let bigint = BigUint::parse_bytes(cleaned.as_bytes(), radix)?;
  let decimal = bigint.to_str_radix(10);
  parse_decimal(&decimal)
}

pub(crate) fn is_legacy_octal_literal(raw: &str) -> bool {
  if !raw.starts_with('0') || raw.len() <= 1 {
    return false;
  }
  if raw.contains(['.', 'e', 'E']) {
    return false;
  }
  if raw.contains('_') {
    // Numeric separators are not permitted in legacy octal integer literals.
    return false;
  }

  let mut saw_octal = false;
  for ch in raw.chars().skip(1) {
    match ch {
      '0'..='7' => saw_octal = true,
      _ => return false,
    }
  }

  saw_octal
}

pub(crate) fn is_leading_zero_decimal_literal(raw: &str) -> bool {
  if !raw.starts_with('0') || raw.len() <= 1 {
    return false;
  }
  if raw
    .strip_prefix("0x")
    .or_else(|| raw.strip_prefix("0X"))
    .or_else(|| raw.strip_prefix("0o"))
    .or_else(|| raw.strip_prefix("0O"))
    .or_else(|| raw.strip_prefix("0b"))
    .or_else(|| raw.strip_prefix("0B"))
    .is_some()
  {
    return false;
  }

  let mut saw_digit = false;
  let mut saw_decimal = false;
  for ch in raw.chars().skip(1) {
    match ch {
      '.' | 'e' | 'E' => break,
      '_' => {}
      '0'..='7' => saw_digit = true,
      '8' | '9' => {
        saw_digit = true;
        saw_decimal = true;
      }
      _ => return false,
    }
  }

  saw_digit && saw_decimal
}

fn parse_number_literal(raw: &str) -> Option<f64> {
  if let Some(rest) = raw.strip_prefix("0b").or_else(|| raw.strip_prefix("0B")) {
    return parse_integer_literal(rest, 2);
  }
  if let Some(rest) = raw.strip_prefix("0o").or_else(|| raw.strip_prefix("0O")) {
    return parse_integer_literal(rest, 8);
  }
  if let Some(rest) = raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
    return parse_integer_literal(rest, 16);
  }

  // Legacy leading-zero literals are special-cased for both value parsing and
  // numeric separator validation.
  if raw.starts_with('0') && raw.len() > 1 {
    let mut int_end = raw.len();
    for (idx, ch) in raw.char_indices().skip(1) {
      if matches!(ch, '.' | 'e' | 'E') {
        int_end = idx;
        break;
      }
    }
    let int_part = &raw[..int_end];

    // Numeric separators are not permitted in legacy leading-zero literals
    // (e.g. `0_0`, `08_1`, `010_7`).
    if int_part.contains('_') {
      return None;
    }

    let mut saw_digit = false;
    let mut saw_decimal_digit = false;
    for ch in int_part.chars().skip(1) {
      match ch {
        '0'..='7' => saw_digit = true,
        '8' | '9' => {
          saw_digit = true;
          saw_decimal_digit = true;
        }
        _ => return None,
      }
    }

    if saw_digit {
      if int_end != raw.len() {
        // `010e1` and `010.1` are invalid in JS; treat them as malformed.
        if !saw_decimal_digit {
          return None;
        }
        // `08.1`, `08e1`, etc are still decimal literals; parse normally.
        return parse_decimal_literal(raw);
      }

      if saw_decimal_digit {
        // `08`, `09`, etc are decimal (not octal) in non-strict code.
        return parse_decimal_literal(raw);
      }

      // All remaining digits are octal digits; parse as a legacy octal literal.
      return parse_integer_literal(raw, 8);
    }
  }
  parse_decimal_literal(raw)
}
