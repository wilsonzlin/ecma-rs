use crate::emitter::QuoteStyle;

/// Emit a JavaScript/TypeScript string literal using the provided quoting
/// strategy, escaping characters that would otherwise terminate or change the
/// meaning of the literal. Non-ASCII characters are preserved as UTF-8 except
/// for the Unicode line separators U+2028/U+2029, which must always be
/// escaped.
pub fn emit_string_literal(out: &mut Vec<u8>, value: &str, quote_style: QuoteStyle, minify: bool) {
  let emit_with_quote = |quote: u8| {
    let mut escaped = Vec::new();
    escape_string_into(&mut escaped, value, quote);
    (quote, escaped)
  };

  let (quote, escaped) = match quote_style {
    QuoteStyle::Double => emit_with_quote(b'"'),
    QuoteStyle::Single => emit_with_quote(b'\''),
    QuoteStyle::Auto => {
      let (double_quote, double_escaped) = emit_with_quote(b'"');
      let (single_quote, single_escaped) = emit_with_quote(b'\'');
      let double_len = double_escaped.len() + 2;
      let single_len = single_escaped.len() + 2;
      if minify && single_len < double_len {
        (single_quote, single_escaped)
      } else {
        (double_quote, double_escaped)
      }
    }
  };

  out.push(quote);
  out.extend_from_slice(&escaped);
  out.push(quote);
}

/// Emit a JavaScript regex literal, escaping line terminators for stability.
pub fn emit_regex_literal(out: &mut Vec<u8>, value: &str) {
  out.clear();
  for ch in value.chars() {
    match ch {
      '\n' => out.extend_from_slice(b"\\n"),
      '\r' => out.extend_from_slice(b"\\r"),
      '\u{2028}' => out.extend_from_slice(b"\\u2028"),
      '\u{2029}' => out.extend_from_slice(b"\\u2029"),
      ch => {
        let mut buf = [0u8; 4];
        let encoded = ch.encode_utf8(&mut buf);
        out.extend_from_slice(encoded.as_bytes());
      }
    }
  }
}

/// Emit a JavaScript/TypeScript string literal delimited by double quotes,
/// escaping characters that would otherwise terminate or change the meaning of
/// the literal. Non-ASCII characters are preserved as UTF-8 except for the
/// Unicode line separators U+2028/U+2029, which must always be escaped.
pub fn emit_string_literal_double_quoted(out: &mut Vec<u8>, value: &str) {
  emit_string_literal(out, value, QuoteStyle::Double, false);
}

fn escape_string_into(out: &mut Vec<u8>, value: &str, quote: u8) {
  out.clear();

  let mut chars = value.chars().peekable();
  while let Some(ch) = chars.next() {
    match ch {
      '\\' => out.extend_from_slice(b"\\\\"),
      '"' if quote == b'"' => out.extend_from_slice(b"\\\""),
      '\'' if quote == b'\'' => out.extend_from_slice(b"\\'"),
      '\n' => out.extend_from_slice(b"\\n"),
      '\r' => out.extend_from_slice(b"\\r"),
      '\t' => out.extend_from_slice(b"\\t"),
      '\0' => {
        let next_is_digit = chars.peek().map(|c| c.is_ascii_digit()).unwrap_or(false);
        if next_is_digit {
          out.extend_from_slice(b"\\x00");
        } else {
          out.extend_from_slice(b"\\0");
        }
      }
      '\u{2028}' => out.extend_from_slice(b"\\u2028"),
      '\u{2029}' => out.extend_from_slice(b"\\u2029"),
      ch if ch < '\u{20}' => {
        // Other control characters are emitted as fixed-width hex escapes for
        // determinism.
        out.extend_from_slice(format!("\\x{:02X}", ch as u32).as_bytes());
      }
      ch => {
        let mut buf = [0u8; 4];
        let encoded = ch.encode_utf8(&mut buf);
        out.extend_from_slice(encoded.as_bytes());
      }
    }
  }
}

/// Emit a JavaScript template literal segment (head or span literal),
/// escaping characters so that the cooked value roundtrips when parsed.
pub fn emit_template_literal_segment(out: &mut Vec<u8>, cooked: &str) {
  for ch in cooked.chars() {
    match ch {
      '\\' => out.extend_from_slice(b"\\\\"),
      '`' => out.extend_from_slice(b"\\`"),
      '$' => out.extend_from_slice(b"\\$"),
      '\n' => out.extend_from_slice(b"\\n"),
      '\r' => out.extend_from_slice(b"\\r"),
      '\u{2028}' => out.extend_from_slice(b"\\u2028"),
      '\u{2029}' => out.extend_from_slice(b"\\u2029"),
      ch if ch < '\u{20}' => {
        out.extend_from_slice(format!("\\x{:02X}", ch as u32).as_bytes());
      }
      ch => {
        let mut buf = [0u8; 4];
        let encoded = ch.encode_utf8(&mut buf);
        out.extend_from_slice(encoded.as_bytes());
      }
    }
  }
}

/// Remove leading/trailing template delimiters from a raw template part as
/// stored by the parser, yielding the cooked segment value.
pub fn cooked_template_segment<'a>(raw: &'a str, is_first: bool, is_last: bool) -> &'a str {
  let mut cooked = raw;

  if is_first {
    if let Some(stripped) = cooked.strip_prefix('`') {
      cooked = stripped;
    }
  }

  if is_last {
    if let Some(stripped) = cooked.strip_suffix('`') {
      cooked = stripped;
    }
  } else if cooked.ends_with("${") {
    cooked = &cooked[..cooked.len() - 2];
  }

  cooked
}

/// Emit a raw template literal segment (head or span literal) for template
/// literal *types*. We conservatively escape characters that could start
/// placeholders or terminate the template.
pub fn emit_template_raw_segment(out: &mut Vec<u8>, raw: &str) {
  for ch in raw.chars() {
    match ch {
      '\\' => out.extend_from_slice(b"\\\\"),
      '`' => out.extend_from_slice(b"\\`"),
      '$' => out.extend_from_slice(b"\\$"),
      ch => {
        let mut buf = [0u8; 4];
        let encoded = ch.encode_utf8(&mut buf);
        out.extend_from_slice(encoded.as_bytes());
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn emit_string(value: &str) -> String {
    let mut out = Vec::new();
    emit_string_literal_double_quoted(&mut out, value);
    String::from_utf8(out).unwrap()
  }

  #[test]
  fn escapes_regex_line_terminators() {
    let mut out = Vec::new();
    emit_regex_literal(&mut out, "/a\nb\u{2028}c/");
    assert_eq!(String::from_utf8(out).unwrap(), "/a\\nb\\u2028c/");
  }

  #[test]
  fn escapes_quotes_and_backslashes() {
    assert_eq!(emit_string("a\"b\\c"), "\"a\\\"b\\\\c\"");
  }

  #[test]
  fn escapes_control_characters() {
    assert_eq!(emit_string("a\nb\tc"), "\"a\\nb\\tc\"");
    assert_eq!(emit_string("a\u{0007}b"), "\"a\\x07b\"");
  }

  #[test]
  fn escapes_zero_followed_by_digit() {
    assert_eq!(emit_string("\u{0000}9"), "\"\\x009\"");
  }

  #[test]
  fn escapes_line_separators() {
    assert_eq!(emit_string("a\u{2028}b"), "\"a\\u2028b\"");
    assert_eq!(emit_string("a\u{2029}b"), "\"a\\u2029b\"");
  }

  #[test]
  fn template_raw_segment_escapes() {
    let mut out = Vec::new();
    emit_template_raw_segment(&mut out, "a`b$\\c");
    assert_eq!(String::from_utf8(out).unwrap(), "a\\`b\\$\\\\c");
  }

  #[test]
  fn template_literal_segment_escapes() {
    let mut out = Vec::new();
    emit_template_literal_segment(&mut out, "a`b$\\c\n\r\u{2028}\u{2029}\u{0001}");
    assert_eq!(
      String::from_utf8(out).unwrap(),
      "a\\`b\\$\\\\c\\n\\r\\u2028\\u2029\\x01"
    );
  }

  #[test]
  fn strips_template_delimiters() {
    assert_eq!(cooked_template_segment("`a${", true, false), "a");
    assert_eq!(cooked_template_segment("b${", false, false), "b");
    assert_eq!(cooked_template_segment("c`", false, true), "c");
    assert_eq!(cooked_template_segment("`only`", true, true), "only");
  }
}
