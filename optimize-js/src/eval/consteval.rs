use crate::il::inst::BinOp;
use crate::il::inst::BinOp::*;
use crate::il::inst::Const;
use crate::il::inst::Const::*;
use crate::il::inst::UnOp;
use crate::il::inst::UnOp::*;
use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;
use parse_js::char::{ECMASCRIPT_LINE_TERMINATORS, ECMASCRIPT_WHITESPACE};
use parse_js::num::JsNumber as JN;
use std::cmp::Ordering;
use std::f64::consts::E;
use std::f64::consts::PI;
use std::mem::discriminant;

/**
 * NOTES ON BUILTINS
 *
 * We often intentionally skip const evaluating builtin values (i.e. at least one arg is a Arg::Builtin). Their values are opaque to us.
 * Yes technically we have the list of all builtins. But we may have forgotten some or new ones may be added in the future and we haven't implemented them yet (and our compiler shouldn't emit incorrect code even then). We don't want to give an incorrect answer.
 * Note that all of these are unsafe:
 * - Checking if they strictly equal. Even if paths are identical, they could point to NaN (e.g. `Number.NaN`); even if paths are unidentical, they could still point to the same object (e.g. `Number.POSITIVE_INFINITY` and `Infinity`). It's incorrect to return either true or false, because there are exceptions in both cases. And these exceptions could change in the future, even if our compiler doesn't, but our compiler still has to be correct then.
 * - Checking if either is null or undefined. A builtin could be null or undefined. Accessing an unknown property on a builtin object results in undefined *today* but may not in the future.
 * - Even `void (Builtin)` is not safe because the builtin path may not exist and we could be suppressing an error.
 */
fn is_ecmascript_whitespace(ch: char) -> bool {
  ECMASCRIPT_WHITESPACE.contains(&ch) || ECMASCRIPT_LINE_TERMINATORS.contains(&ch)
}

fn trim_js_whitespace(raw: &str) -> &str {
  raw.trim_matches(is_ecmascript_whitespace)
}

fn bigint_to_f64(value: &BigInt) -> f64 {
  value.to_f64().unwrap_or_else(|| {
    if value.sign() == Sign::Minus {
      f64::NEG_INFINITY
    } else {
      f64::INFINITY
    }
  })
}

fn parse_int_digits_to_bigint(digits: &str, radix: u32) -> Option<BigInt> {
  if digits.is_empty() || digits.contains('_') {
    return None;
  }
  if !digits.chars().all(|ch| ch.to_digit(radix).is_some()) {
    return None;
  }
  BigInt::parse_bytes(digits.as_bytes(), radix)
}

pub fn parse_bigint(raw: &str) -> Option<BigInt> {
  let trimmed = trim_js_whitespace(raw);
  if trimmed.is_empty() {
    return None;
  }
  let (sign, body) = match trimmed.strip_prefix('+') {
    Some(rest) => (1, rest),
    None => match trimmed.strip_prefix('-') {
      Some(rest) => (-1, rest),
      None => (1, trimmed),
    },
  };
  if body.is_empty() {
    return None;
  }
  let (radix, digits) = match body {
    s if s.starts_with("0b") || s.starts_with("0B") => (2, &s[2..]),
    s if s.starts_with("0o") || s.starts_with("0O") => (8, &s[2..]),
    s if s.starts_with("0x") || s.starts_with("0X") => (16, &s[2..]),
    s => (10, s),
  };
  let mut value = parse_int_digits_to_bigint(digits, radix)?;
  if sign == -1 {
    value = -value;
  }
  Some(value)
}

pub fn coerce_bigint_to_num(v: &BigInt) -> f64 {
  bigint_to_f64(v)
}

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number#number_coercion
pub fn coerce_str_to_num(raw: &str) -> f64 {
  let raw = trim_js_whitespace(raw);
  if raw.is_empty() {
    return 0.0;
  };
  let mut sign = 1.0_f64;
  let mut had_sign = false;
  let mut body = raw;
  if let Some(rest) = body.strip_prefix('+') {
    had_sign = true;
    body = rest;
  } else if let Some(rest) = body.strip_prefix('-') {
    had_sign = true;
    sign = -1.0;
    body = rest;
  };
  if body.is_empty() {
    return f64::NAN;
  };
  if body == "Infinity" {
    return sign * f64::INFINITY;
  };

  let parse_int =
    |digits: &str, radix: u32| parse_int_digits_to_bigint(digits, radix).map(|v| bigint_to_f64(&v));

  if body.starts_with("0x") || body.starts_with("0X") {
    if had_sign {
      return f64::NAN;
    }
    return parse_int(&body[2..], 16).unwrap_or(f64::NAN);
  }
  if body.starts_with("0b") || body.starts_with("0B") {
    if had_sign {
      return f64::NAN;
    }
    return parse_int(&body[2..], 2).unwrap_or(f64::NAN);
  }
  if body.starts_with("0o") || body.starts_with("0O") {
    if had_sign {
      return f64::NAN;
    }
    return parse_int(&body[2..], 8).unwrap_or(f64::NAN);
  }

  if body.contains('_') {
    return f64::NAN;
  }

  let mut saw_digit_before_exp = false;
  let mut saw_dot = false;
  let mut saw_exp = false;
  let mut iter = body.chars().peekable();
  while let Some(ch) = iter.next() {
    match ch {
      '0'..='9' => {
        if !saw_exp {
          saw_digit_before_exp = true;
        }
      }
      '.' => {
        if saw_dot || saw_exp {
          return f64::NAN;
        }
        saw_dot = true;
      }
      'e' | 'E' => {
        if saw_exp || !saw_digit_before_exp {
          return f64::NAN;
        }
        saw_exp = true;
        if matches!(iter.peek(), Some('+' | '-')) {
          iter.next();
        }
        let mut exp_digits = 0;
        while matches!(iter.peek(), Some('0'..='9')) {
          exp_digits += 1;
          iter.next();
        }
        if exp_digits == 0 {
          return f64::NAN;
        }
      }
      _ => return f64::NAN,
    }
  }
  if !saw_digit_before_exp {
    return f64::NAN;
  }

  body.parse::<f64>().map(|v| sign * v).unwrap_or(f64::NAN)
}

// https://tc39.es/ecma262/multipage/abstract-operations.html#sec-tonumber
pub fn coerce_to_num(v: &Const) -> f64 {
  match v {
    BigInt(_) => panic!("cannot coerce bigint to num according to spec"),
    Bool(false) => 0.0,
    Bool(true) => 1.0,
    Null => 0.0,
    Num(v) => v.0,
    Str(v) => coerce_str_to_num(&v),
    Undefined => f64::NAN,
  }
}

// https://tc39.es/ecma262/multipage/abstract-operations.html#sec-toint32
fn coerce_to_uint32(v: &Const) -> Option<u32> {
  if matches!(v, BigInt(_)) {
    return None;
  }
  let n = coerce_to_num(v);
  if !n.is_finite() || n == 0.0 {
    return Some(0);
  }
  let int = n.trunc();
  let wrapped = int.rem_euclid(4294967296.0);
  Some(wrapped as u32)
}

fn coerce_to_int32(v: &Const) -> Option<i32> {
  coerce_to_uint32(v).map(|v| v as i32)
}

// https://developer.mozilla.org/en-US/docs/Glossary/Falsy
pub fn coerce_to_bool(v: &Const) -> bool {
  match v {
    BigInt(v) => v == &BigInt::from(0),
    Bool(b) => *b,
    Null => false,
    Num(JN(v)) => !v.is_nan() && *v != 0.0,
    Str(v) => !v.is_empty(),
    Undefined => false,
  }
}

// If return value is None, then all comparison operators between `a` and `b` result in false.
// https://tc39.es/ecma262/multipage/abstract-operations.html#sec-islessthan
pub fn js_cmp(a: &Const, b: &Const) -> Option<Ordering> {
  match (a, b) {
    (Str(a), Str(b)) => Some(a.cmp(b)),
    (Str(a), BigInt(b)) => parse_bigint(a).map(|a| a.cmp(b)),
    (BigInt(a), Str(b)) => parse_bigint(b).map(|b| a.cmp(&b)),
    (BigInt(a), BigInt(b)) => Some(a.cmp(b)),
    (a, b) => {
      // https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-lessThan
      let a = coerce_to_num(a);
      let b = coerce_to_num(b);
      if a.is_nan() || b.is_nan() {
        None
      } else {
        Some(a.partial_cmp(&b).unwrap())
      }
    }
  }
}

pub fn js_div(a: f64, b: f64) -> f64 {
  a / b
}

pub fn js_mod(a: f64, b: f64) -> f64 {
  match (a, b) {
    (_, 0.0) => f64::NAN,
    (a, _) if a.is_infinite() => f64::NAN,
    _ => a % b,
  }
}

// https://tc39.es/ecma262/multipage/abstract-operations.html#sec-islooselyequal
pub fn js_loose_eq(a: &Const, b: &Const) -> bool {
  if discriminant(a) == discriminant(b) {
    return js_strict_eq(a, b);
  };
  match (a, b) {
    (Null, Undefined) => true,
    (Undefined, Null) => true,
    (Num(l), Str(r)) => l.0 == coerce_str_to_num(&r),
    (Str(l), Num(r)) => coerce_str_to_num(&l) == r.0,
    (BigInt(l), Str(r)) => parse_bigint(r).is_some_and(|r| l == &r),
    (Str(l), BigInt(r)) => parse_bigint(l).is_some_and(|l| &l == r),
    (Bool(l), r) => js_loose_eq(&Num(JN(*l as u8 as f64)), r),
    (l, Bool(r)) => js_loose_eq(l, &Num(JN(*r as u8 as f64))),
    (BigInt(l), Num(r)) => r.0.is_finite() && coerce_bigint_to_num(l) == r.0,
    (Num(l), BigInt(r)) => l.0.is_finite() && l.0 == coerce_bigint_to_num(r),
    _ => false,
  }
}

pub fn js_strict_eq(a: &Const, b: &Const) -> bool {
  match (a, b) {
    (Num(v), _) if v.0.is_nan() => false,
    (_, Num(v)) if v.0.is_nan() => false,
    (a, b) => a == b,
  }
}

pub fn maybe_eval_const_bin_expr(op: BinOp, a: &Const, b: &Const) -> Option<Const> {
  #[rustfmt::skip]
  let res = match (op, a, b) {
    (Add, Num(l), Num(r)) => Num(JN(l.0 + r.0)),
    (Add, Num(l), Str(r)) => Str(format!("{l}{r}")),
    (Add, Str(l), Num(r)) => Str(format!("{l}{r}")),
    (Add, Str(l), Str(r)) => Str(format!("{l}{r}")),
    (Div, Num(l), Num(r)) => Num(JN(js_div(l.0, r.0))),
    (Div, Num(l), Str(r)) => Num(JN(js_div(l.0, coerce_str_to_num(r)))),
    (Div, Str(l), Num(r)) => Num(JN(js_div(coerce_str_to_num(l), r.0))),
    (Div, Str(l), Str(r)) => Num(JN(js_div(coerce_str_to_num(l), coerce_str_to_num(r)))),
    (BitAnd, l, r) => Num(JN((coerce_to_int32(l)? & coerce_to_int32(r)?) as f64)),
    (BitOr, l, r) => Num(JN((coerce_to_int32(l)? | coerce_to_int32(r)?) as f64)),
    (BitXor, l, r) => Num(JN((coerce_to_int32(l)? ^ coerce_to_int32(r)?) as f64)),
    (Exp, Num(l), Num(r)) => Num(JN(l.0.powf(r.0))),
    (Exp, Num(l), Str(r)) => Num(JN(l.0.powf(coerce_str_to_num(r)))),
    (Exp, Str(l), Num(r)) => Num(JN(coerce_str_to_num(l).powf(r.0))),
    (Exp, Str(l), Str(r)) => Num(JN(coerce_str_to_num(l).powf(coerce_str_to_num(r)))),
    (Geq, l, r) => Bool(js_cmp(l, r).is_some_and(|c| c.is_ge())),
    (Gt, l, r) => Bool(js_cmp(l, r).is_some_and(|c| c.is_gt())),
    (Leq, l, r) => Bool(js_cmp(l, r).is_some_and(|c| c.is_le())),
    (LooseEq, l, r) => Bool(js_loose_eq(l, r)),
    (Lt, l, r) => Bool(js_cmp(l, r).is_some_and(|c| c.is_lt())),
    (Mod, Num(l), Num(r)) => Num(JN(js_mod(l.0, r.0))),
    (Mod, Num(l), Str(r)) => Num(JN(js_mod(l.0, coerce_str_to_num(r)))),
    (Mod, Str(l), Num(r)) => Num(JN(js_mod(coerce_str_to_num(l), r.0))),
    (Mod, Str(l), Str(r)) => Num(JN(js_mod(coerce_str_to_num(l), coerce_str_to_num(r)))),
    (Mul, Num(l), Num(r)) => Num(JN(l.0 * r.0)),
    (Mul, Num(l), Str(r)) => Num(JN(l.0 * coerce_str_to_num(r))),
    (Mul, Str(l), Num(r)) => Num(JN(coerce_str_to_num(l) * r.0)),
    (Mul, Str(l), Str(r)) => Num(JN(coerce_str_to_num(l) * coerce_str_to_num(r))),
    (NotLooseEq, l, r) => Bool(!js_loose_eq(l, r)),
    (NotStrictEq, l, r) => Bool(!js_strict_eq(l, r)),
    (Shl, l, r) => {
      let shift = (coerce_to_uint32(r)? & 0x1f) as u32;
      Num(JN(coerce_to_int32(l)?.wrapping_shl(shift) as f64))
    }
    (Shr, l, r) => {
      let shift = (coerce_to_uint32(r)? & 0x1f) as u32;
      Num(JN(coerce_to_int32(l)?.wrapping_shr(shift) as f64))
    }
    (UShr, l, r) => {
      let shift = (coerce_to_uint32(r)? & 0x1f) as u32;
      Num(JN(coerce_to_uint32(l)?.wrapping_shr(shift) as f64))
    }
    (StrictEq, l, r) => Bool(js_strict_eq(l, r)),
    (Sub, Num(l), Num(r)) => Num(JN(l.0 - r.0)),
    (Sub, Num(l), Str(r)) => Num(JN(l.0 - coerce_str_to_num(r))),
    (Sub, Str(l), Num(r)) => Num(JN(coerce_str_to_num(l) - r.0)),
    (Sub, Str(l), Str(r)) => Num(JN(coerce_str_to_num(l) - coerce_str_to_num(r))),
    _ => return None,
  };
  Some(res)
}

pub fn maybe_eval_const_un_expr(op: UnOp, a: &Const) -> Option<Const> {
  #[rustfmt::skip]
  let res = match (op, a) {
    (BitNot, a) => Num(JN((!coerce_to_int32(a)?) as f64)),
    (Neg, Num(l)) => Num(JN(-l.0)),
    (Not, a) => Bool(!coerce_to_bool(a)),
    (Plus, BigInt(_)) => return None,
    (Plus, l) => Num(JN(coerce_to_num(&l))),
    (Typeof, BigInt(_)) => Str("bigint".into()),
    (Typeof, Bool(_)) => Str("boolean".into()),
    (Typeof, Null) => Str("object".into()),
    (Typeof, Num(_)) => Str("number".into()),
    (Typeof, Str(_)) => Str("string".into()),
    (Typeof, Undefined) => Str("undefined".into()),
    (Void, _) => Undefined,
    _ => return None,
  };
  Some(res)
}

pub fn maybe_eval_const_builtin_call(func: &str, args: &[Const]) -> Option<Const> {
  #[rustfmt::skip]
  let v = match args.len() {
    1 => match (func, &args[0]) {
      ("Math.abs", Num(a)) => Num(JN(a.0.abs())),
      ("Math.acos", Num(a)) => Num(JN(a.0.acos())),
      ("Math.asin", Num(a)) => Num(JN(a.0.asin())),
      ("Math.atan", Num(a)) => Num(JN(a.0.atan())),
      ("Math.ceil", Num(a)) => Num(JN(a.0.ceil())),
      ("Math.cos", Num(a)) => Num(JN(a.0.cos())),
      ("Math.floor", Num(a)) => Num(JN(a.0.floor())),
      ("Math.log", Num(a)) => Num(JN(a.0.ln())),
      ("Math.log10", Num(a)) => Num(JN(a.0.log10())),
      ("Math.log1p", Num(a)) => Num(JN(a.0.ln_1p())),
      ("Math.log2", Num(a)) => Num(JN(a.0.log2())),
      ("Math.round", Num(a)) => Num(JN(a.0.round())),
      ("Math.sin", Num(a)) => Num(JN(a.0.sin())),
      ("Math.sqrt", Num(a)) => Num(JN(a.0.sqrt())),
      ("Math.tan", Num(a)) => Num(JN(a.0.tan())),
      ("Math.trunc", Num(a)) => Num(JN(a.0.trunc())),
      ("Number", Str(a)) => Num(JN(coerce_str_to_num(&a))),
      _ => return None,
    }
    _ => return None,
  };
  Some(v)
}

pub fn maybe_eval_const_builtin_val(path: &str) -> Option<Const> {
  #[rustfmt::skip]
  let v = match path {
    "Math.E" => Num(JN(E)),
    "Math.PI" => Num(JN(PI)),
    "NaN" => Num(JN(f64::NAN)),
    "Number.EPSILON" => Num(JN(f64::EPSILON)),
    "Number.MAX_SAFE_INTEGER" => Num(JN((2u64.pow(53) - 1) as f64)),
    "Number.MIN_SAFE_INTEGER" => Num(JN(-(2i64.pow(53) - 1) as f64)),
    "Number.NaN" => Num(JN(f64::NAN)),
    "Number.NEGATIVE_INFINITY" => Num(JN(f64::NEG_INFINITY)),
    "Number.POSITIVE_INFINITY" => Num(JN(f64::INFINITY)),
    _ => return None,
  };
  Some(v)
}
