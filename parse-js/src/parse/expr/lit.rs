use super::pat::is_valid_pattern_identifier;
use super::Asi;
use super::ParseCtx;
use super::Parser;
use crate::ast::class_or_object::ClassOrObjKey;
use crate::ast::class_or_object::ClassOrObjMemberDirectKey;
use crate::ast::class_or_object::ClassOrObjVal;
use crate::ast::class_or_object::ObjMember;
use crate::ast::class_or_object::ObjMemberType;
use crate::ast::expr::lit::LitArrElem;
use crate::ast::expr::lit::LitArrExpr;
use crate::ast::expr::lit::LitBigIntExpr;
use crate::ast::expr::lit::LitBoolExpr;
use crate::ast::expr::lit::LitNullExpr;
use crate::ast::expr::lit::LitNumExpr;
use crate::ast::expr::lit::LitObjExpr;
use crate::ast::expr::lit::LitRegexExpr;
use crate::ast::expr::lit::LitStrExpr;
use crate::ast::expr::lit::LitTemplateExpr;
use crate::ast::expr::lit::LitTemplatePart;
use crate::ast::expr::BinaryExpr;
use crate::ast::expr::IdExpr;
use crate::ast::node::InvalidTemplateEscapeSequence;
use crate::ast::node::LeadingZeroDecimalLiteral;
use crate::ast::node::LegacyOctalEscapeSequence;
use crate::ast::node::LegacyOctalNumberLiteral;
use crate::ast::node::LiteralStringCodeUnits;
use crate::ast::node::Node;
use crate::char::is_line_terminator;
use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::LexMode;
use crate::lex::KEYWORDS_MAPPING;
use crate::loc::Loc;
use crate::num::JsNumber;
use crate::operator::OperatorName;
use crate::token::TT;
use num_bigint::BigInt;
pub fn normalise_literal_number(raw: &str) -> Option<JsNumber> {
  JsNumber::from_literal(raw)
}

pub fn normalise_literal_bigint(raw: &str) -> Option<String> {
  // Canonicalise BigInt literals while preserving their original radix. Prefixes are normalised
  // to lowercase (`0b`/`0o`/`0x`), numeric separators are stripped, and hex digits are emitted in
  // lowercase via `char::from_digit`. The value is returned as a canonical decimal string (without
  // the trailing `n`) so downstream consumers can parse it deterministically.
  if !raw.ends_with('n') {
    return None;
  }
  let body = &raw[..raw.len().saturating_sub(1)];
  let (radix, digits) =
    if let Some(rest) = body.strip_prefix("0b").or_else(|| body.strip_prefix("0B")) {
      (2, rest)
    } else if let Some(rest) = body.strip_prefix("0o").or_else(|| body.strip_prefix("0O")) {
      (8, rest)
    } else if let Some(rest) = body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
      (16, rest)
    } else {
      (10, body)
    };

  let mut normalised_digits = String::with_capacity(digits.len());
  let mut prev_sep = false;
  let mut saw_digit = false;
  for ch in digits.chars() {
    if ch == '_' {
      // Separators must be sandwiched between digits.
      if prev_sep || !saw_digit {
        return None;
      }
      prev_sep = true;
      continue;
    }
    let value = ch.to_digit(radix)?;
    let digit = char::from_digit(value, radix)?;
    normalised_digits.push(digit);
    saw_digit = true;
    prev_sep = false;
  }
  if prev_sep || !saw_digit {
    return None;
  }

  if radix == 10 && normalised_digits.len() > 1 && normalised_digits.starts_with('0') {
    // Decimal BigInt literals cannot use a leading zero.
    return None;
  }

  let value = BigInt::parse_bytes(normalised_digits.as_bytes(), radix)?;
  Some(value.to_str_radix(10))
}

#[derive(Clone, Copy, Debug)]
enum LiteralErrorKind {
  InvalidEscape,
  UnexpectedEnd,
  LineTerminator,
}

#[derive(Clone, Copy, Debug)]
struct LiteralError {
  kind: LiteralErrorKind,
  offset: usize,
  len: usize,
}

fn decode_escape_sequence(
  raw: &str,
  escape_start: usize,
) -> Result<(usize, Option<char>), LiteralError> {
  let mut chars = raw.chars();
  let Some(first) = chars.next() else {
    return Err(LiteralError {
      kind: LiteralErrorKind::UnexpectedEnd,
      offset: escape_start,
      len: 0,
    });
  };
  match first {
    '\r' => {
      let mut consumed = first.len_utf8();
      if raw[first.len_utf8()..].starts_with('\n') {
        consumed += '\n'.len_utf8();
      }
      Ok((consumed, None))
    }
    '\n' | '\u{2028}' | '\u{2029}' => Ok((first.len_utf8(), None)),
    'b' => Ok((1, Some('\x08'))),
    'f' => Ok((1, Some('\x0c'))),
    'n' => Ok((1, Some('\n'))),
    'r' => Ok((1, Some('\r'))),
    't' => Ok((1, Some('\t'))),
    'v' => Ok((1, Some('\x0b'))),
    '0'..='7' => {
      let mut consumed = first.len_utf8();
      let mut value = first.to_digit(8).unwrap();
      for ch in raw[consumed..].chars().take(2) {
        if ('0'..='7').contains(&ch) {
          consumed += ch.len_utf8();
          value = (value << 3) + ch.to_digit(8).unwrap();
        } else {
          break;
        }
      }
      let Some(c) = char::from_u32(value) else {
        return Err(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        });
      };
      Ok((consumed, Some(c)))
    }
    'x' => {
      let mut hex_iter = raw[first.len_utf8()..].chars();
      let Some(h1) = hex_iter.next() else {
        return Err(LiteralError {
          kind: LiteralErrorKind::UnexpectedEnd,
          offset: escape_start,
          len: 0,
        });
      };
      let Some(h2) = hex_iter.next() else {
        return Err(LiteralError {
          kind: LiteralErrorKind::UnexpectedEnd,
          offset: escape_start,
          len: 0,
        });
      };
      if !h1.is_ascii_hexdigit() || !h2.is_ascii_hexdigit() {
        return Err(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        });
      }
      let cp = u32::from_str_radix(&format!("{h1}{h2}"), 16).unwrap();
      let Some(c) = char::from_u32(cp) else {
        return Err(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        });
      };
      let consumed = first.len_utf8() + h1.len_utf8() + h2.len_utf8();
      Ok((consumed, Some(c)))
    }
    'u' => {
      let after_u = &raw[first.len_utf8()..];
      if after_u.starts_with('{') {
        let Some(end) = after_u.find('}') else {
          return Err(LiteralError {
            kind: LiteralErrorKind::UnexpectedEnd,
            offset: escape_start,
            len: 0,
          });
        };
        let hex = &after_u[1..end];
        if hex.is_empty() || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
          return Err(LiteralError {
            kind: LiteralErrorKind::InvalidEscape,
            offset: escape_start,
            len: 1,
          });
        }
        let value = u32::from_str_radix(hex, 16).ok().ok_or(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        })?;
        if value > 0x10FFFF {
          return Err(LiteralError {
            kind: LiteralErrorKind::InvalidEscape,
            offset: escape_start,
            len: 1,
          });
        }
        // JavaScript strings are UTF-16; allow surrogate code points by mapping
        // them to U+FFFD so we can represent them in Rust `String`s.
        let cp = char::from_u32(value).unwrap_or('\u{FFFD}');
        let consumed = first.len_utf8() + end + 1;
        Ok((consumed, Some(cp)))
      } else {
        let mut hex = String::new();
        let mut consumed = first.len_utf8();
        for ch in after_u.chars().take(4) {
          hex.push(ch);
          consumed += ch.len_utf8();
        }
        if hex.len() < 4 {
          return Err(LiteralError {
            kind: LiteralErrorKind::UnexpectedEnd,
            offset: escape_start,
            len: 0,
          });
        }
        if !hex.chars().all(|c| c.is_ascii_hexdigit()) {
          return Err(LiteralError {
            kind: LiteralErrorKind::InvalidEscape,
            offset: escape_start,
            len: 1,
          });
        }
        let value = u32::from_str_radix(&hex, 16).ok().ok_or(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        })?;
        // Combine surrogate pairs when possible so sequences like `\\uD83D\\uDE00`
        // decode to a valid Unicode scalar.
        if (0xD800..=0xDBFF).contains(&value) {
          let rest = &after_u[4..];
          if rest.len() >= 6 && rest.starts_with("\\u") {
            let low_hex = &rest[2..6];
            if low_hex.chars().all(|c| c.is_ascii_hexdigit()) {
              let low = u32::from_str_radix(low_hex, 16).unwrap();
              if (0xDC00..=0xDFFF).contains(&low) {
                let high_ten = (value - 0xD800) << 10;
                let low_ten = low - 0xDC00;
                let combined = 0x10000 + high_ten + low_ten;
                if let Some(cp) = char::from_u32(combined) {
                  return Ok((consumed + 6, Some(cp)));
                }
              }
            }
          }
        }
        let cp = char::from_u32(value).unwrap_or('\u{FFFD}');
        Ok((consumed, Some(cp)))
      }
    }
    c => Ok((c.len_utf8(), Some(c))),
  }
}

#[derive(Clone, Copy, Debug)]
enum Utf16Escape {
  None,
  One(u16),
  Two(u16, u16),
}

fn decode_escape_sequence_utf16(
  raw: &str,
  escape_start: usize,
) -> Result<(usize, Utf16Escape), LiteralError> {
  let mut chars = raw.chars();
  let Some(first) = chars.next() else {
    return Err(LiteralError {
      kind: LiteralErrorKind::UnexpectedEnd,
      offset: escape_start,
      len: 0,
    });
  };
  match first {
    '\r' => {
      let mut consumed = first.len_utf8();
      if raw[first.len_utf8()..].starts_with('\n') {
        consumed += '\n'.len_utf8();
      }
      Ok((consumed, Utf16Escape::None))
    }
    '\n' | '\u{2028}' | '\u{2029}' => Ok((first.len_utf8(), Utf16Escape::None)),
    'b' => Ok((1, Utf16Escape::One(0x08))),
    'f' => Ok((1, Utf16Escape::One(0x0c))),
    'n' => Ok((1, Utf16Escape::One(0x0a))),
    'r' => Ok((1, Utf16Escape::One(0x0d))),
    't' => Ok((1, Utf16Escape::One(0x09))),
    'v' => Ok((1, Utf16Escape::One(0x0b))),
    '0'..='7' => {
      let mut consumed = first.len_utf8();
      let mut value = first.to_digit(8).unwrap() as u16;
      for ch in raw[consumed..].chars().take(2) {
        if ('0'..='7').contains(&ch) {
          consumed += ch.len_utf8();
          value = (value << 3) + ch.to_digit(8).unwrap() as u16;
        } else {
          break;
        }
      }
      Ok((consumed, Utf16Escape::One(value)))
    }
    'x' => {
      let mut hex_iter = raw[first.len_utf8()..].chars();
      let Some(h1) = hex_iter.next() else {
        return Err(LiteralError {
          kind: LiteralErrorKind::UnexpectedEnd,
          offset: escape_start,
          len: 0,
        });
      };
      let Some(h2) = hex_iter.next() else {
        return Err(LiteralError {
          kind: LiteralErrorKind::UnexpectedEnd,
          offset: escape_start,
          len: 0,
        });
      };
      if !h1.is_ascii_hexdigit() || !h2.is_ascii_hexdigit() {
        return Err(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        });
      }
      let value = u16::from_str_radix(&format!("{h1}{h2}"), 16).unwrap();
      let consumed = first.len_utf8() + h1.len_utf8() + h2.len_utf8();
      Ok((consumed, Utf16Escape::One(value)))
    }
    'u' => {
      let after_u = &raw[first.len_utf8()..];
      if after_u.starts_with('{') {
        let Some(end) = after_u.find('}') else {
          return Err(LiteralError {
            kind: LiteralErrorKind::UnexpectedEnd,
            offset: escape_start,
            len: 0,
          });
        };
        let hex = &after_u[1..end];
        if hex.is_empty() || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
          return Err(LiteralError {
            kind: LiteralErrorKind::InvalidEscape,
            offset: escape_start,
            len: 1,
          });
        }
        let value = u32::from_str_radix(hex, 16).ok().ok_or(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        })?;
        if value > 0x10FFFF {
          return Err(LiteralError {
            kind: LiteralErrorKind::InvalidEscape,
            offset: escape_start,
            len: 1,
          });
        }
        let consumed = first.len_utf8() + end + 1;
        Ok(if value <= 0xFFFF {
          (consumed, Utf16Escape::One(value as u16))
        } else {
          let v = value - 0x10000;
          let high = 0xD800 + ((v >> 10) as u16);
          let low = 0xDC00 + ((v & 0x3FF) as u16);
          (consumed, Utf16Escape::Two(high, low))
        })
      } else {
        let mut hex = String::new();
        let mut consumed = first.len_utf8();
        for ch in after_u.chars().take(4) {
          hex.push(ch);
          consumed += ch.len_utf8();
        }
        if hex.len() < 4 {
          return Err(LiteralError {
            kind: LiteralErrorKind::UnexpectedEnd,
            offset: escape_start,
            len: 0,
          });
        }
        if !hex.chars().all(|c| c.is_ascii_hexdigit()) {
          return Err(LiteralError {
            kind: LiteralErrorKind::InvalidEscape,
            offset: escape_start,
            len: 1,
          });
        }
        let value = u16::from_str_radix(&hex, 16).ok().ok_or(LiteralError {
          kind: LiteralErrorKind::InvalidEscape,
          offset: escape_start,
          len: 1,
        })?;
        Ok((consumed, Utf16Escape::One(value)))
      }
    }
    c => {
      let mut buf = [0u16; 2];
      let encoded = c.encode_utf16(&mut buf);
      let addition = if encoded.len() == 1 {
        Utf16Escape::One(encoded[0])
      } else {
        Utf16Escape::Two(encoded[0], encoded[1])
      };
      Ok((c.len_utf8(), addition))
    }
  }
}

fn decode_literal(raw: &str, allow_line_terminators: bool) -> Result<String, LiteralError> {
  let mut norm = String::new();
  let mut offset = 0;
  while offset < raw.len() {
    let mut iter = raw[offset..].char_indices();
    let (rel, ch) = iter.next().unwrap();
    debug_assert_eq!(rel, 0);
    if ch == '\\' {
      let escape_start = offset;
      let after_backslash = offset + ch.len_utf8();
      let (consumed, addition) = decode_escape_sequence(&raw[after_backslash..], escape_start)?;
      if let Some(c) = addition {
        norm.push(c);
      }
      offset = after_backslash + consumed;
    } else {
      // ECMAScript 2019 permits U+2028/U+2029 (line/paragraph separators) in
      // string literals; only CR/LF terminate literal lines.
      if !allow_line_terminators && matches!(ch, '\n' | '\r') {
        return Err(LiteralError {
          kind: LiteralErrorKind::LineTerminator,
          offset,
          len: ch.len_utf8(),
        });
      }
      norm.push(ch);
      offset += ch.len_utf8();
    }
  }
  Ok(norm)
}

fn decode_literal_utf16(raw: &str, allow_line_terminators: bool) -> Result<Vec<u16>, LiteralError> {
  let mut norm = Vec::<u16>::new();
  let mut offset = 0;
  while offset < raw.len() {
    let mut iter = raw[offset..].char_indices();
    let (rel, ch) = iter.next().unwrap();
    debug_assert_eq!(rel, 0);
    if ch == '\\' {
      let escape_start = offset;
      let after_backslash = offset + ch.len_utf8();
      let (consumed, addition) =
        decode_escape_sequence_utf16(&raw[after_backslash..], escape_start)?;
      match addition {
        Utf16Escape::None => {}
        Utf16Escape::One(v) => norm.push(v),
        Utf16Escape::Two(a, b) => {
          norm.push(a);
          norm.push(b);
        }
      }
      offset = after_backslash + consumed;
    } else {
      // ECMAScript 2019 permits U+2028/U+2029 (line/paragraph separators) in
      // string literals; only CR/LF terminate literal lines.
      if !allow_line_terminators && matches!(ch, '\n' | '\r') {
        return Err(LiteralError {
          kind: LiteralErrorKind::LineTerminator,
          offset,
          len: ch.len_utf8(),
        });
      }
      let mut buf = [0u16; 2];
      let encoded = ch.encode_utf16(&mut buf);
      norm.extend_from_slice(encoded);
      offset += ch.len_utf8();
    }
  }
  Ok(norm)
}

fn find_legacy_escape_sequence(raw: &str) -> Option<(usize, usize)> {
  let bytes = raw.as_bytes();
  let mut i = 0;
  while i < bytes.len() {
    if bytes[i] != b'\\' {
      i += 1;
      continue;
    }
    if i + 1 >= bytes.len() {
      break;
    }
    match bytes[i + 1] {
      b'0' => {
        if i + 2 >= bytes.len() {
          i += 2;
          continue;
        }
        let next = bytes[i + 2];
        if !next.is_ascii_digit() {
          // `\0` (null escape) is permitted; only `\0` followed by a decimal
          // digit counts as a legacy escape sequence.
          i += 2;
          continue;
        }
        if next == b'8' || next == b'9' {
          return Some((i, 3));
        }
        let mut len = 2;
        let mut digits = 1;
        let mut j = i + 2;
        while digits < 3 && j < bytes.len() {
          let c = bytes[j];
          if !(b'0'..=b'7').contains(&c) {
            break;
          }
          len += 1;
          digits += 1;
          j += 1;
        }
        return Some((i, len));
      }
      b'1'..=b'7' => {
        let mut len = 2;
        let mut digits = 1;
        let mut j = i + 2;
        while digits < 3 && j < bytes.len() {
          let c = bytes[j];
          if !(b'0'..=b'7').contains(&c) {
            break;
          }
          len += 1;
          digits += 1;
          j += 1;
        }
        return Some((i, len));
      }
      b'8' | b'9' => return Some((i, 2)),
      _ => {}
    }
    i += 2;
  }
  None
}

fn literal_error_to_syntax(
  err: LiteralError,
  base: usize,
  token: TT,
  line_error: SyntaxErrorType,
) -> SyntaxError {
  let typ = match err.kind {
    LiteralErrorKind::InvalidEscape => SyntaxErrorType::InvalidCharacterEscape,
    LiteralErrorKind::UnexpectedEnd => SyntaxErrorType::UnexpectedEnd,
    LiteralErrorKind::LineTerminator => line_error,
  };
  let start = base + err.offset;
  let end = start + err.len;
  Loc(start, end).error(typ, Some(token))
}

fn template_content(raw: &str, is_end: bool) -> Option<(usize, &str)> {
  let mut start = 0;
  let mut end = raw.len();
  if raw.starts_with('`') && raw.len() > '`'.len_utf8() {
    start += '`'.len_utf8();
  }
  if is_end {
    if !raw.ends_with('`') {
      return None;
    }
    end = end.saturating_sub('`'.len_utf8());
  } else {
    if !raw.ends_with("${") {
      return None;
    }
    end = end.saturating_sub("${".len());
  }
  if end < start {
    return None;
  }
  raw.get(start..end).map(|body| (start, body))
}

#[derive(Debug)]
enum RegexErrorKind {
  LineTerminator,
  Unterminated,
  InvalidFlag,
  DuplicateFlag,
}

#[derive(Debug)]
struct RegexError {
  kind: RegexErrorKind,
  offset: usize,
  len: usize,
}

fn validate_regex_flags(raw: &str, start: usize) -> Result<(), RegexError> {
  let mut seen_flags: u16 = 0;
  for (offset, ch) in raw[start..].char_indices() {
    let bit = match ch {
      'd' => 1 << 0,
      'g' => 1 << 1,
      'i' => 1 << 2,
      'm' => 1 << 3,
      's' => 1 << 4,
      'u' => 1 << 5,
      'v' => 1 << 6,
      'y' => 1 << 7,
      _ => {
        return Err(RegexError {
          kind: RegexErrorKind::InvalidFlag,
          offset: start + offset,
          len: ch.len_utf8(),
        })
      }
    };
    if seen_flags & bit != 0 {
      return Err(RegexError {
        kind: RegexErrorKind::DuplicateFlag,
        offset: start + offset,
        len: ch.len_utf8(),
      });
    }
    seen_flags |= bit;
  }
  Ok(())
}

fn validate_regex_literal(raw: &str) -> Result<(), RegexError> {
  let mut offset = '/'.len_utf8();
  let mut in_charset = false;
  while offset < raw.len() {
    let mut iter = raw[offset..].char_indices();
    let (rel, ch) = iter.next().unwrap();
    debug_assert_eq!(rel, 0);
    if ch == '\\' {
      let after_backslash = offset + ch.len_utf8();
      let Some(escaped) = raw[after_backslash..].chars().next() else {
        return Err(RegexError {
          kind: RegexErrorKind::Unterminated,
          offset: after_backslash,
          len: 0,
        });
      };
      offset = after_backslash + escaped.len_utf8();
      continue;
    }
    if !in_charset && ch == '/' {
      let flags_start = offset + ch.len_utf8();
      return validate_regex_flags(raw, flags_start);
    }
    if ch == '[' {
      in_charset = true;
    } else if ch == ']' && in_charset {
      in_charset = false;
    } else if is_line_terminator(ch) {
      return Err(RegexError {
        kind: RegexErrorKind::LineTerminator,
        offset,
        len: ch.len_utf8(),
      });
    }
    offset += ch.len_utf8();
  }
  Err(RegexError {
    kind: RegexErrorKind::Unterminated,
    offset: raw.len(),
    len: 0,
  })
}

fn regex_error_to_syntax(err: RegexError, token_start: usize) -> SyntaxError {
  let typ = match err.kind {
    RegexErrorKind::LineTerminator => SyntaxErrorType::LineTerminatorInRegex,
    RegexErrorKind::Unterminated => SyntaxErrorType::UnexpectedEnd,
    RegexErrorKind::InvalidFlag | RegexErrorKind::DuplicateFlag => {
      SyntaxErrorType::ExpectedSyntax("valid regex flags")
    }
  };
  let start = token_start + err.offset;
  let end = start + err.len;
  Loc(start, end).error(typ, Some(TT::LiteralRegex))
}

pub fn normalise_literal_string_or_template_inner(raw: &str) -> Option<String> {
  decode_literal(raw, true).ok()
}

pub fn normalise_literal_string(raw: &str) -> Option<String> {
  if raw.len() < 2 {
    return None;
  }
  decode_literal(&raw[1..raw.len() - 1], false).ok()
}

impl<'a> Parser<'a> {
  pub fn lit_arr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LitArrExpr>> {
    self.with_loc(|p| {
      p.require(TT::BracketOpen)?;
      let mut elements = Vec::<LitArrElem>::new();
      loop {
        if p.consume_if(TT::Comma).is_match() {
          elements.push(LitArrElem::Empty);
          continue;
        };
        if p.peek().typ == TT::BracketClose {
          break;
        };
        let rest = p.consume_if(TT::DotDotDot).is_match();
        let value = p.expr(ctx, [TT::Comma, TT::BracketClose])?;
        elements.push(if rest {
          LitArrElem::Rest(value)
        } else {
          LitArrElem::Single(value)
        });
        if p.peek().typ == TT::BracketClose {
          break;
        };
        p.require(TT::Comma)?;
      }
      p.require(TT::BracketClose)?;
      Ok(LitArrExpr { elements })
    })
  }

  pub fn lit_bigint(&mut self) -> SyntaxResult<Node<LitBigIntExpr>> {
    self.with_loc(|p| {
      let value = p.lit_bigint_val()?;
      Ok(LitBigIntExpr { value })
    })
  }

  pub fn lit_bigint_val(&mut self) -> SyntaxResult<String> {
    let t = self.require(TT::LiteralBigInt)?;
    normalise_literal_bigint(self.str(t.loc))
      .ok_or_else(|| t.loc.error(SyntaxErrorType::MalformedLiteralBigInt, None))
  }

  pub fn lit_bool(&mut self) -> SyntaxResult<Node<LitBoolExpr>> {
    self.with_loc(|p| {
      if p.consume_if(TT::LiteralTrue).is_match() {
        Ok(LitBoolExpr { value: true })
      } else {
        p.require(TT::LiteralFalse)?;
        Ok(LitBoolExpr { value: false })
      }
    })
  }

  pub fn lit_null(&mut self) -> SyntaxResult<Node<LitNullExpr>> {
    self.with_loc(|p| {
      p.require(TT::LiteralNull)?;
      Ok(LitNullExpr {})
    })
  }

  pub fn lit_num(&mut self) -> SyntaxResult<Node<LitNumExpr>> {
    let t = self.require(TT::LiteralNumber)?;
    let raw = self.str(t.loc);
    if self.is_strict_ecmascript()
      && self.is_strict_mode()
      && (crate::num::is_legacy_octal_literal(raw)
        || crate::num::is_leading_zero_decimal_literal(raw))
    {
      return Err(t.error(SyntaxErrorType::ExpectedSyntax(
        "numeric literals with leading zeros are not allowed in strict mode",
      )));
    }
    let value = normalise_literal_number(raw)
      .ok_or_else(|| t.loc.error(SyntaxErrorType::MalformedLiteralNumber, None))?;

    let mut node = Node::new(t.loc, LitNumExpr { value });
    if crate::num::is_legacy_octal_literal(raw) {
      node.assoc.set(LegacyOctalNumberLiteral);
    } else if crate::num::is_leading_zero_decimal_literal(raw) {
      node.assoc.set(LeadingZeroDecimalLiteral);
    }
    Ok(node)
  }

  pub fn lit_num_val(&mut self) -> SyntaxResult<JsNumber> {
    let t = self.require(TT::LiteralNumber)?;
    normalise_literal_number(self.str(t.loc))
      .ok_or_else(|| t.loc.error(SyntaxErrorType::MalformedLiteralNumber, None))
  }

  pub fn lit_obj(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LitObjExpr>> {
    self.with_loc(|p| {
      p.require(TT::BraceOpen)?.loc;
      let mut members = Vec::new();
      while p.peek().typ != TT::BraceClose && p.peek().typ != TT::EOF {
        let member_start = p.peek().loc;
        // TypeScript-style recovery: class declarations in object literals are
        // not allowed, but try to skip them so the rest of the literal can be
        // parsed.
        let looks_like_nested_class = p.should_recover()
          && p.peek().typ == TT::KeywordClass
          && matches!(
            p.peek_n::<3>()[1].typ,
            TT::Identifier | TT::BraceOpen | TT::KeywordExtends
          );
        if looks_like_nested_class {
          // Skip the entire class declaration
          p.consume(); // consume 'class'
                       // Skip optional class name
          if p.peek().typ == TT::Identifier {
            p.consume();
          }
          // Skip optional type parameters
          if p.peek().typ == TT::ChevronLeft {
            let mut depth = 0;
            while p.peek().typ != TT::EOF {
              if p.peek().typ == TT::ChevronLeft {
                depth += 1;
                p.consume();
              } else if p.peek().typ == TT::ChevronRight {
                p.consume();
                depth -= 1;
                if depth == 0 {
                  break;
                }
              } else if p.peek().typ == TT::BraceOpen {
                break;
              } else {
                p.consume();
              }
            }
          }
          // Skip optional extends clause
          if p.consume_if(TT::KeywordExtends).is_match() {
            // Skip until we reach the class body
            while p.peek().typ != TT::BraceOpen && p.peek().typ != TT::EOF {
              p.consume();
            }
          }
          // Skip optional implements clause
          if p.consume_if(TT::KeywordImplements).is_match() {
            // Skip until we reach the class body
            while p.peek().typ != TT::BraceOpen && p.peek().typ != TT::EOF {
              p.consume();
            }
          }
          // Skip the class body
          if p.peek().typ == TT::BraceOpen {
            let mut depth = 0;
            while p.peek().typ != TT::EOF {
              if p.peek().typ == TT::BraceOpen {
                depth += 1;
                p.consume();
              } else if p.peek().typ == TT::BraceClose {
                p.consume();
                depth -= 1;
                if depth == 0 {
                  break;
                }
              } else {
                p.consume();
              }
            }
          }
          // Return a dummy member (will be ignored by error recovery)
          // Use an empty shorthand property as a placeholder
          use crate::ast::expr::IdExpr;
          use crate::loc::Loc;
          members.push(Node::new(
            member_start,
            ObjMember {
              typ: ObjMemberType::Shorthand {
                id: Node::new(
                  Loc(0, 0),
                  IdExpr {
                    name: String::new(),
                  },
                ),
              },
            },
          ));
          continue;
        }

        let rest = p.consume_if(TT::DotDotDot).is_match();
        let mut allow_semicolon_separator = false;
        if rest {
          let value = p.expr(ctx, [TT::Comma, TT::Semicolon, TT::BraceClose])?;
          members.push(Node::new(
            member_start,
            ObjMember {
              typ: ObjMemberType::Rest { val: value },
            },
          ));
        } else {
          let (key, value) = p.class_or_obj_member(
            ctx,
            TT::Colon,
            TT::Comma,
            &mut Asi::no(),
            false, // Object literals don't have abstract methods
          )?;
          allow_semicolon_separator = matches!(value, ClassOrObjVal::IndexSignature(_));
          let typ = match value {
            ClassOrObjVal::Prop(None) => {
              // This property had no value, so it's a shorthand property. Therefore, check
              // that it's a valid identifier name.
              match key {
                ClassOrObjKey::Computed(expr) => {
                  if !p.should_recover() {
                    return Err(
                      expr.error(SyntaxErrorType::ExpectedSyntax("object literal value")),
                    );
                  }
                  // TypeScript-style recovery - computed properties without value like `{ [e] }`.
                  let loc = expr.loc;
                  let synthetic_value = Node::new(
                    loc,
                    IdExpr {
                      name: "undefined".to_string(),
                    },
                  )
                  .into_wrapped();
                  ObjMemberType::Valued {
                    key: ClassOrObjKey::Computed(expr),
                    val: ClassOrObjVal::Prop(Some(synthetic_value)),
                  }
                }
                ClassOrObjKey::Direct(direct_key) => {
                  if p.should_recover() {
                    // TypeScript-style recovery: accept malformed shorthand properties
                    // like `{ while }` / `{ "while" }` / `{ 1 }`.
                    if direct_key.stx.tt != TT::Identifier
                      && !KEYWORDS_MAPPING.contains_key(&direct_key.stx.tt)
                      && direct_key.stx.tt != TT::LiteralString
                      && direct_key.stx.tt != TT::LiteralNumber
                      && direct_key.stx.tt != TT::LiteralBigInt
                    {
                      return Err(direct_key.error(SyntaxErrorType::ExpectedNotFound));
                    };
                    // TypeScript-style recovery: definite assignment assertion (e.g., `{ a! }`).
                    let _definite_assignment = p.consume_if(TT::Exclamation).is_match();
                    // TypeScript-style recovery: default value (e.g., `{ c = 1 }`).
                    if p.consume_if(TT::Equals).is_match() {
                      let key_name = direct_key.stx.key.clone();
                      let key_loc = direct_key.loc;
                      let default_val = p.expr(ctx, [TT::Comma, TT::Semicolon, TT::BraceClose])?;
                      let id_expr = Node::new(
                        key_loc,
                        IdExpr {
                          name: key_name.clone(),
                        },
                      )
                      .into_wrapped();
                      let bin_expr = Node::new(
                        key_loc + default_val.loc,
                        BinaryExpr {
                          operator: OperatorName::Assignment,
                          left: id_expr,
                          right: default_val,
                        },
                      )
                      .into_wrapped();
                      ObjMemberType::Valued {
                        key: ClassOrObjKey::Direct(Node::new(
                          key_loc,
                          ClassOrObjMemberDirectKey {
                            key: key_name,
                            tt: TT::Identifier,
                          },
                        )),
                        val: ClassOrObjVal::Prop(Some(bin_expr)),
                      }
                    } else {
                      ObjMemberType::Shorthand {
                        id: direct_key.map_stx(|n| IdExpr { name: n.key }),
                      }
                    }
                  } else {
                    if !is_valid_pattern_identifier(direct_key.stx.tt, ctx.rules) {
                      return Err(direct_key.error(SyntaxErrorType::ExpectedSyntax("identifier")));
                    }
                    ObjMemberType::Shorthand {
                      id: direct_key.map_stx(|n| IdExpr { name: n.key }),
                    }
                  }
                }
              }
            }
            _ => ObjMemberType::Valued { key, val: value },
          };
          members.push(Node::new(member_start, ObjMember { typ }));
        }
        if p.consume_if(TT::Comma).is_match() {
          continue;
        }
        if p.peek().typ == TT::Semicolon {
          let semi = p.consume();
          if allow_semicolon_separator {
            continue;
          }
          return Err(semi.error(SyntaxErrorType::ExpectedSyntax("`,`")));
        }
        if p.peek().typ == TT::BraceClose {
          break;
        }
        return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax("`,`")));
      }
      p.require(TT::BraceClose)?;
      Ok(LitObjExpr { members })
    })
  }

  pub fn lit_regex(&mut self) -> SyntaxResult<Node<LitRegexExpr>> {
    self.with_loc(|p| {
      let t = match p.peek().typ {
        TT::LiteralRegex | TT::Invalid => p.consume_with_mode(LexMode::SlashIsRegex),
        _ => p.require_with_mode(TT::LiteralRegex, LexMode::SlashIsRegex)?,
      };
      let value = p.string(t.loc);
      validate_regex_literal(&value).map_err(|err| regex_error_to_syntax(err, t.loc.0))?;
      Ok(LitRegexExpr { value })
    })
  }

  pub fn lit_str(&mut self) -> SyntaxResult<Node<LitStrExpr>> {
    let (loc, value, escape_loc, code_units) =
      self.lit_str_val_with_mode_and_legacy_escape(LexMode::Standard)?;
    if self.is_strict_ecmascript() && self.is_strict_mode() {
      if let Some(escape_loc) = escape_loc {
        return Err(escape_loc.error(
          SyntaxErrorType::ExpectedSyntax("octal escape sequences not allowed in strict mode"),
          Some(TT::LiteralString),
        ));
      }
    }
    let mut node = Node::new(loc, LitStrExpr { value });
    node
      .assoc
      .set(LiteralStringCodeUnits(code_units.into_boxed_slice()));
    if let Some(escape_loc) = escape_loc {
      node.assoc.set(LegacyOctalEscapeSequence(escape_loc));
    }
    Ok(node)
  }

  /// Parses a literal string and returns the raw string value normalized (e.g. escapes decoded).
  /// Does *not* return a node; use `lit_str` for that.
  pub fn lit_str_val(&mut self) -> SyntaxResult<String> {
    self.lit_str_val_with_mode(LexMode::Standard)
  }

  pub fn lit_str_val_with_mode(&mut self, mode: LexMode) -> SyntaxResult<String> {
    self
      .lit_str_val_with_mode_and_legacy_escape(mode)
      .map(|(_, value, _, _)| value)
  }

  pub(crate) fn lit_str_val_with_mode_and_legacy_escape(
    &mut self,
    mode: LexMode,
  ) -> SyntaxResult<(Loc, String, Option<Loc>, Vec<u16>)> {
    let peek = self.peek_with_mode(mode);
    let t = if matches!(peek.typ, TT::LiteralString | TT::Invalid)
      && self
        .str(peek.loc)
        .starts_with(|c: char| c == '"' || c == '\'')
    {
      self.consume_with_mode(mode)
    } else {
      self.require_with_mode(TT::LiteralString, mode)?
    };
    let raw = self.bytes(t.loc);
    let quote = raw
      .chars()
      .next()
      .ok_or_else(|| t.error(SyntaxErrorType::UnexpectedEnd))?;
    let has_closing = raw.ends_with(quote);
    let body_start = t.loc.0 + quote.len_utf8();
    let body_end = if has_closing {
      t.loc.1.saturating_sub(quote.len_utf8())
    } else {
      t.loc.1
    };
    let body = self.bytes(Loc(body_start, body_end));
    let escape_loc = find_legacy_escape_sequence(body)
      .map(|(offset, len)| Loc(body_start + offset, body_start + offset + len));

    if mode == LexMode::JsxTag {
      if !has_closing {
        return Err(
          Loc(body_end, body_end).error(SyntaxErrorType::UnexpectedEnd, Some(TT::LiteralString)),
        );
      }
      let code_units = body.encode_utf16().collect();
      return Ok((t.loc, body.to_string(), escape_loc, code_units));
    }
    let code_units = decode_literal_utf16(body, false).map_err(|err| {
      literal_error_to_syntax(
        err,
        body_start,
        TT::LiteralString,
        SyntaxErrorType::LineTerminatorInString,
      )
    })?;
    let decoded = String::from_utf16_lossy(&code_units);
    if !has_closing {
      return Err(
        Loc(body_end, body_end).error(SyntaxErrorType::UnexpectedEnd, Some(TT::LiteralString)),
      );
    }
    Ok((t.loc, decoded, escape_loc, code_units))
  }

  pub fn lit_template(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LitTemplateExpr>> {
    let start = self.checkpoint();
    let (parts, invalid_escape) = self.lit_template_parts_with_invalid_escape(ctx, false)?;
    let loc = self.since_checkpoint(&start);
    let mut node = Node::new(loc, LitTemplateExpr { parts });
    if let Some(invalid_escape) = invalid_escape {
      node
        .assoc
        .set(InvalidTemplateEscapeSequence(invalid_escape));
    }
    Ok(node)
  }

  // NOTE: The next token must definitely be LiteralTemplatePartString{,End}.
  // ES2018: Tagged templates can have invalid escape sequences (cooked value is undefined, raw is available)
  // TypeScript: All templates allow invalid escapes (permissive parsing, semantic errors caught later)
  pub fn lit_template_parts(
    &mut self,
    ctx: ParseCtx,
    tagged: bool,
  ) -> SyntaxResult<Vec<LitTemplatePart>> {
    self
      .lit_template_parts_with_invalid_escape(ctx, tagged)
      .map(|(parts, _)| parts)
  }

  fn lit_template_parts_with_invalid_escape(
    &mut self,
    ctx: ParseCtx,
    tagged: bool,
  ) -> SyntaxResult<(Vec<LitTemplatePart>, Option<Loc>)> {
    let t = self.consume();
    let is_end = match t.typ {
      TT::LiteralTemplatePartString => false,
      TT::LiteralTemplatePartStringEnd => true,
      TT::Invalid => return Err(t.error(SyntaxErrorType::UnexpectedEnd)),
      _ => return Err(t.error(SyntaxErrorType::ExpectedSyntax("template string part"))),
    };

    let mut parts = Vec::new();
    let mut invalid_escape = None;
    let raw = self.bytes(t.loc);
    let (content_offset, first_content) =
      template_content(raw, is_end).ok_or_else(|| t.error(SyntaxErrorType::UnexpectedEnd))?;
    if !tagged {
      if let Some((rel, len)) = find_legacy_escape_sequence(first_content) {
        invalid_escape = Some(Loc(
          t.loc.0 + content_offset + rel,
          t.loc.0 + content_offset + rel + len,
        ));
      }
    }
    let first_str = match decode_literal(first_content, true) {
      Ok(val) => val,
      Err(_err) if tagged => String::new(),
      Err(err) => {
        return Err(literal_error_to_syntax(
          err,
          t.loc.0 + content_offset,
          t.typ,
          SyntaxErrorType::InvalidCharacterEscape,
        ))
      }
    };
    parts.push(LitTemplatePart::String(first_str));
    if !is_end {
      loop {
        let substitution = self.expr(ctx, [TT::BraceClose])?;
        self.require(TT::BraceClose)?;
        parts.push(LitTemplatePart::Substitution(substitution));
        let string = self.consume_with_mode(LexMode::TemplateStrContinue);
        let string_is_end = match string.typ {
          TT::LiteralTemplatePartString => false,
          TT::LiteralTemplatePartStringEnd => true,
          TT::Invalid => {
            return Err(Loc(string.loc.1, string.loc.1).error(
              SyntaxErrorType::UnexpectedEnd,
              Some(TT::LiteralTemplatePartString),
            ))
          }
          _ => {
            return Err(string.error(SyntaxErrorType::ExpectedSyntax("template string part")));
          }
        };
        let raw = self.bytes(string.loc);
        let (offset, content) = template_content(raw, string_is_end)
          .ok_or_else(|| string.error(SyntaxErrorType::UnexpectedEnd))?;
        if !tagged && invalid_escape.is_none() {
          if let Some((rel, len)) = find_legacy_escape_sequence(content) {
            invalid_escape = Some(Loc(
              string.loc.0 + offset + rel,
              string.loc.0 + offset + rel + len,
            ));
          }
        }
        let part_str = match decode_literal(content, true) {
          Ok(val) => val,
          Err(_err) if tagged => String::new(),
          Err(err) => {
            return Err(literal_error_to_syntax(
              err,
              string.loc.0 + offset,
              string.typ,
              SyntaxErrorType::InvalidCharacterEscape,
            ))
          }
        };
        parts.push(LitTemplatePart::String(part_str));
        if string_is_end {
          break;
        };
      }
    };

    Ok((parts, invalid_escape))
  }
}
