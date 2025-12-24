/// Emit a JavaScript/TypeScript string literal delimited by double quotes,
/// escaping characters that would otherwise terminate or change the meaning of
/// the literal. Non-ASCII characters are preserved as UTF-8 except for the
/// Unicode line separators U+2028/U+2029, which must always be escaped.
pub fn emit_string_literal_double_quoted(out: &mut Vec<u8>, value: &str) {
  out.push(b'"');

  let mut chars = value.chars().peekable();
  while let Some(ch) = chars.next() {
    match ch {
      '\\' => out.extend_from_slice(b"\\\\"),
      '"' => out.extend_from_slice(b"\\\""),
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

  out.push(b'"');
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
}
