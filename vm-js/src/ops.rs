use crate::{GcString, Heap, Value, VmError};

/// ECMAScript "abstract operations" used by expression evaluation.
///
/// This module focuses on primitive semantics first; object conversions are implemented as minimal
/// stubs until built-ins and `ToPrimitive` hooks exist.
pub fn to_primitive(heap: &mut Heap, value: Value) -> Result<Value, VmError> {
  match value {
    Value::Object(obj) => {
      // Placeholder: a proper `ToPrimitive` implementation requires invoking @@toPrimitive,
      // `valueOf`, and `toString`.
      //
      // Returning a string matches `Object.prototype.toString` for plain objects and makes
      // `Number({})` produce `NaN`, and `({}) + "x"` produce "[object Object]x".
      let mut scope = heap.scope();
      scope.push_root(Value::Object(obj))?;
      let s = scope.alloc_string("[object Object]")?;
      Ok(Value::String(s))
    }
    other => Ok(other),
  }
}

/// ECMAScript `ToNumber` for the supported value types.
pub fn to_number(heap: &mut Heap, value: Value) -> Result<f64, VmError> {
  match value {
    Value::Undefined => Ok(f64::NAN),
    Value::Null => Ok(0.0),
    Value::Bool(b) => Ok(if b { 1.0 } else { 0.0 }),
    Value::Number(n) => Ok(n),
    Value::BigInt(_) => Err(VmError::TypeError(
      "Cannot convert a BigInt value to a number",
    )),
    Value::String(s) => string_to_number(heap, s),
    Value::Symbol(_) => Err(VmError::TypeError("Cannot convert a Symbol value to a number")),
    Value::Object(_) => {
      // Per spec: ToPrimitive, then ToNumber.
      let prim = to_primitive(heap, value)?;
      to_number(heap, prim)
    }
  }
}

/// ECMAScript Abstract Equality Comparison (`==`) for the supported value types.
pub fn abstract_equality(heap: &mut Heap, a: Value, b: Value) -> Result<bool, VmError> {
  use Value::*;

  // `==` can allocate when converting objects to primitives (via `ToPrimitive`), so root operands
  // for the duration of the comparison.
  let mut scope = heap.scope();
  let mut a = scope.push_root(a)?;
  let mut b = scope.push_root(b)?;

  loop {
    match (a, b) {
      // Same-type comparisons use Strict Equality Comparison.
      (Undefined, Undefined) => return Ok(true),
      (Null, Null) => return Ok(true),
      (Bool(x), Bool(y)) => return Ok(x == y),
      (Number(x), Number(y)) => return Ok(x == y),
      (BigInt(x), BigInt(y)) => return Ok(x == y),
      (String(x), String(y)) => return Ok(scope.heap().get_string(x)? == scope.heap().get_string(y)?),
      (Symbol(x), Symbol(y)) => return Ok(x == y),
      (Object(x), Object(y)) => return Ok(x == y),

      // `null == undefined`
      (Undefined, Null) | (Null, Undefined) => return Ok(true),

      // Number/string conversions.
      (Number(_), String(_)) => {
        let bn = to_number(scope.heap_mut(), b)?;
        b = scope.push_root(Number(bn))?;
      }
      (String(_), Number(_)) => {
        let an = to_number(scope.heap_mut(), a)?;
        a = scope.push_root(Number(an))?;
      }

      // Boolean conversions.
      (Bool(_), _) => {
        let an = to_number(scope.heap_mut(), a)?;
        a = scope.push_root(Number(an))?;
      }
      (_, Bool(_)) => {
        let bn = to_number(scope.heap_mut(), b)?;
        b = scope.push_root(Number(bn))?;
      }

      // Object-to-primitive conversions.
      (Object(_), String(_) | Number(_) | BigInt(_) | Symbol(_)) => {
        let prim = to_primitive(scope.heap_mut(), a)?;
        a = scope.push_root(prim)?;
      }
      (String(_) | Number(_) | BigInt(_) | Symbol(_), Object(_)) => {
        let prim = to_primitive(scope.heap_mut(), b)?;
        b = scope.push_root(prim)?;
      }

      _ => return Ok(false),
    }
  }
}

fn string_to_number(heap: &Heap, s: GcString) -> Result<f64, VmError> {
  let raw = heap.get_string(s)?.to_utf8_lossy();
  let trimmed = raw.trim_matches(is_ecma_whitespace);

  if trimmed.is_empty() {
    return Ok(0.0);
  }

  // Infinity is case-sensitive in ECMAScript string numeric literals.
  match trimmed {
    "Infinity" | "+Infinity" => return Ok(f64::INFINITY),
    "-Infinity" => return Ok(f64::NEG_INFINITY),
    _ => {}
  }

  // Guard against Rust accepting "inf"/"infinity" case-insensitively.
  let rest = trimmed
    .strip_prefix('+')
    .or_else(|| trimmed.strip_prefix('-'))
    .unwrap_or(trimmed);
  if rest.eq_ignore_ascii_case("inf") || rest.eq_ignore_ascii_case("infinity") {
    // Only the exact "Infinity" spelling is accepted above.
    return Ok(f64::NAN);
  }

  if let Some(hex) = trimmed.strip_prefix("0x").or_else(|| trimmed.strip_prefix("0X")) {
    return Ok(parse_ascii_int_radix(hex, 16).unwrap_or(f64::NAN));
  }
  if let Some(bin) = trimmed.strip_prefix("0b").or_else(|| trimmed.strip_prefix("0B")) {
    return Ok(parse_ascii_int_radix(bin, 2).unwrap_or(f64::NAN));
  }
  if let Some(oct) = trimmed.strip_prefix("0o").or_else(|| trimmed.strip_prefix("0O")) {
    return Ok(parse_ascii_int_radix(oct, 8).unwrap_or(f64::NAN));
  }

  Ok(trimmed.parse::<f64>().unwrap_or(f64::NAN))
}

fn parse_ascii_int_radix(s: &str, radix: u32) -> Option<f64> {
  if s.is_empty() {
    return None;
  }
  let radix_f = radix as f64;
  let mut value = 0.0f64;
  for b in s.bytes() {
    let digit = match b {
      b'0'..=b'9' => (b - b'0') as u32,
      b'a'..=b'f' => (b - b'a' + 10) as u32,
      b'A'..=b'F' => (b - b'A' + 10) as u32,
      _ => return None,
    };
    if digit >= radix {
      return None;
    }
    value = value * radix_f + digit as f64;
  }
  Some(value)
}

fn is_ecma_whitespace(c: char) -> bool {
  // ECMA-262 WhiteSpace + LineTerminator (used by TrimString / StringToNumber).
  matches!(
    c,
    '\u{0009}' // Tab
    | '\u{000A}' // LF
    | '\u{000B}' // VT
    | '\u{000C}' // FF
    | '\u{000D}' // CR
    | '\u{0020}' // Space
    | '\u{00A0}' // No-break space
    | '\u{1680}' // Ogham space mark
    | '\u{2000}'..='\u{200A}' // En quad..hair space
    | '\u{2028}' // Line separator
    | '\u{2029}' // Paragraph separator
    | '\u{202F}' // Narrow no-break space
    | '\u{205F}' // Medium mathematical space
    | '\u{3000}' // Ideographic space
    | '\u{FEFF}' // BOM
  )
}
