use crate::EmitMode;
use std::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QuoteStyle {
  Single,
  Double,
}

impl QuoteStyle {
  fn as_char(self) -> char {
    match self {
      QuoteStyle::Single => '\'',
      QuoteStyle::Double => '"',
    }
  }
}

pub fn emit_string_literal<W: fmt::Write>(out: &mut W, value: &str, mode: EmitMode) -> fmt::Result {
  let (quote, escaped) = match mode {
    EmitMode::Canonical => (
      QuoteStyle::Double,
      escape_with_quote(value, QuoteStyle::Double),
    ),
    EmitMode::Minified => {
      let escaped_single = escape_with_quote(value, QuoteStyle::Single);
      let escaped_double = escape_with_quote(value, QuoteStyle::Double);

      let single_len = escaped_single.len() + 2;
      let double_len = escaped_double.len() + 2;
      if single_len < double_len {
        (QuoteStyle::Single, escaped_single)
      } else if double_len < single_len {
        (QuoteStyle::Double, escaped_double)
      } else {
        (QuoteStyle::Double, escaped_double)
      }
    }
  };

  out.write_char(quote.as_char())?;
  out.write_str(&escaped)?;
  out.write_char(quote.as_char())
}

pub fn emit_template_part<W: fmt::Write>(out: &mut W, value: &str) -> fmt::Result {
  let mut iter = value.chars().peekable();
  while let Some(ch) = iter.next() {
    match ch {
      '\\' => out.write_str("\\\\")?,
      '`' => out.write_str("\\`")?,
      '$' if matches!(iter.peek(), Some('{')) => {
        out.write_str("\\${")?;
        iter.next();
      }
      _ => out.write_char(ch)?,
    }
  }
  Ok(())
}

fn escape_with_quote(value: &str, quote: QuoteStyle) -> String {
  let mut out = String::new();
  escape_with_quote_to(&mut out, value, quote).unwrap();
  out
}

fn escape_with_quote_to<W: fmt::Write>(out: &mut W, value: &str, quote: QuoteStyle) -> fmt::Result {
  let mut iter = value.chars().peekable();
  while let Some(ch) = iter.next() {
    match ch {
      '\\' => out.write_str("\\\\")?,
      '\n' => out.write_str("\\n")?,
      '\r' => out.write_str("\\r")?,
      '\t' => out.write_str("\\t")?,
      '\u{08}' => out.write_str("\\b")?,
      '\u{0c}' => out.write_str("\\f")?,
      '\u{0b}' => out.write_str("\\v")?,
      '"' if quote == QuoteStyle::Double => out.write_str("\\\"")?,
      '\'' if quote == QuoteStyle::Single => out.write_str("\\'")?,
      '\0' => {
        if matches!(iter.peek(), Some(next) if next.is_ascii_digit()) {
          out.write_str("\\x00")?
        } else {
          out.write_str("\\0")?
        }
      }
      '\u{2028}' => out.write_str("\\u2028")?,
      '\u{2029}' => out.write_str("\\u2029")?,
      _ if ch.is_control() => write!(out, "\\x{:02X}", ch as u32)?,
      _ => out.write_char(ch)?,
    }
  }
  Ok(())
}
