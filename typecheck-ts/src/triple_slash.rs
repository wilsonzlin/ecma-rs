use std::borrow::Cow;

use diagnostics::TextRange;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TripleSlashReferenceKind {
  Path,
  Types,
  Lib,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TripleSlashReference {
  pub kind: TripleSlashReferenceKind,
  /// UTF-8 byte offsets for the attribute value within the file.
  pub value_range: TextRange,
}

impl TripleSlashReference {
  pub fn value<'a>(&self, source: &'a str) -> &'a str {
    let start = self.value_range.start as usize;
    let end = self.value_range.end as usize;
    source.get(start..end).unwrap_or("")
  }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TripleSlashDirectives {
  pub references: Vec<TripleSlashReference>,
  pub no_default_lib: bool,
}

fn is_ws_byte(b: u8) -> bool {
  matches!(b, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c)
}

fn eq_ignore_ascii_case(input: &[u8], lowercase: &[u8]) -> bool {
  if input.len() != lowercase.len() {
    return false;
  }
  input
    .iter()
    .zip(lowercase.iter())
    .all(|(a, b)| a.to_ascii_lowercase() == *b)
}

fn parse_bool_value(value: &str) -> bool {
  let trimmed = value.trim();
  trimmed.is_empty() || trimmed.eq_ignore_ascii_case("true") || trimmed == "1"
}

fn starts_with_drive_letter(path: &str) -> bool {
  let bytes = path.as_bytes();
  bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':'
}

/// Normalize a `/// <reference path="..." />` value into a module-specifier-like
/// string.
///
/// TypeScript treats the `path` attribute as a file path relative to the
/// containing file even when it lacks a leading `./`. Most module resolvers
/// treat bare specifiers as packages, so we prefix `./` when needed.
pub fn normalize_reference_path_specifier(raw: &str) -> Cow<'_, str> {
  let mut needs_slash_fix = false;
  for b in raw.as_bytes() {
    if *b == b'\\' {
      needs_slash_fix = true;
      break;
    }
  }

  let mut normalized: Cow<'_, str> = if needs_slash_fix {
    Cow::Owned(raw.replace('\\', "/"))
  } else {
    Cow::Borrowed(raw)
  };

  let value = normalized.as_ref();
  let needs_prefix = !(value.starts_with("./")
    || value.starts_with("../")
    || value.starts_with('/')
    || value.starts_with('\\')
    || starts_with_drive_letter(value));

  if !needs_prefix {
    return normalized;
  }

  let mut with_prefix = String::with_capacity(2 + value.len());
  with_prefix.push_str("./");
  with_prefix.push_str(value);
  normalized = Cow::Owned(with_prefix);
  normalized
}

fn parse_reference_directive(
  out: &mut TripleSlashDirectives,
  source: &str,
  comment_offset: usize,
  comment: &str,
) {
  let bytes = comment.as_bytes();
  let mut idx = 0usize;
  while idx < bytes.len() && is_ws_byte(bytes[idx]) {
    idx += 1;
  }
  if idx >= bytes.len() {
    return;
  }
  let remaining = &bytes[idx..];
  const OPEN: &[u8] = b"<reference";
  if remaining.len() < OPEN.len() || !eq_ignore_ascii_case(&remaining[..OPEN.len()], OPEN) {
    return;
  }
  idx += OPEN.len();

  while idx < bytes.len() {
    while idx < bytes.len() && is_ws_byte(bytes[idx]) {
      idx += 1;
    }
    if idx >= bytes.len() {
      return;
    }

    if bytes[idx] == b'/' {
      return;
    }
    if bytes[idx] == b'>' {
      return;
    }

    let name_start = idx;
    while idx < bytes.len()
      && (bytes[idx].is_ascii_alphanumeric() || matches!(bytes[idx], b'-' | b'_'))
    {
      idx += 1;
    }
    if idx == name_start {
      return;
    }
    let name_bytes = &bytes[name_start..idx];
    while idx < bytes.len() && is_ws_byte(bytes[idx]) {
      idx += 1;
    }
    if idx >= bytes.len() || bytes[idx] != b'=' {
      continue;
    }
    idx += 1;
    while idx < bytes.len() && is_ws_byte(bytes[idx]) {
      idx += 1;
    }
    if idx >= bytes.len() {
      return;
    }

    let (value_start, value_end) = match bytes[idx] {
      b'"' | b'\'' => {
        let quote = bytes[idx];
        idx += 1;
        let start = idx;
        while idx < bytes.len() && bytes[idx] != quote {
          idx += 1;
        }
        let end = idx;
        if idx < bytes.len() {
          idx += 1;
        }
        (start, end)
      }
      _ => {
        let start = idx;
        while idx < bytes.len()
          && !is_ws_byte(bytes[idx])
          && bytes[idx] != b'>'
          && !(bytes[idx] == b'/' && bytes.get(idx + 1) == Some(&b'>'))
        {
          idx += 1;
        }
        (start, idx)
      }
    };

    let global_start = comment_offset + value_start;
    let global_end = comment_offset + value_end;
    let range = TextRange::new(global_start as u32, global_end as u32);
    if range.start >= range.end {
      continue;
    }
    let value = source.get(global_start..global_end).unwrap_or("");

    if eq_ignore_ascii_case(name_bytes, b"path") {
      out.references.push(TripleSlashReference {
        kind: TripleSlashReferenceKind::Path,
        value_range: range,
      });
    } else if eq_ignore_ascii_case(name_bytes, b"types") {
      out.references.push(TripleSlashReference {
        kind: TripleSlashReferenceKind::Types,
        value_range: range,
      });
    } else if eq_ignore_ascii_case(name_bytes, b"lib") {
      out.references.push(TripleSlashReference {
        kind: TripleSlashReferenceKind::Lib,
        value_range: range,
      });
    } else if eq_ignore_ascii_case(name_bytes, b"no-default-lib") || eq_ignore_ascii_case(name_bytes, b"nolib") {
      out.no_default_lib = parse_bool_value(value);
    }
  }
}

/// Scan the leading trivia region of `source` and extract TypeScript triple-slash
/// reference directives.
///
/// Only `///` line comments are considered. Scanning stops once a non-trivia
/// token is encountered (matching TypeScript's requirement that directives
/// appear before code).
pub fn scan_triple_slash_directives(source: &str) -> TripleSlashDirectives {
  let bytes = source.as_bytes();
  let mut idx = 0usize;
  if bytes.starts_with(&[0xef, 0xbb, 0xbf]) {
    idx = 3;
  }

  let mut directives = TripleSlashDirectives::default();
  while idx < bytes.len() {
    while idx < bytes.len() && is_ws_byte(bytes[idx]) {
      idx += 1;
    }
    if idx >= bytes.len() {
      break;
    }

    if bytes.get(idx) == Some(&b'/') && bytes.get(idx + 1) == Some(&b'/') {
      let is_triple = bytes.get(idx + 2) == Some(&b'/') && bytes.get(idx + 3) != Some(&b'/');
      let comment_start = idx + if is_triple { 3 } else { 2 };
      let mut end = comment_start;
      while end < bytes.len() && !matches!(bytes[end], b'\n' | b'\r') {
        end += 1;
      }
      if is_triple {
        if let Some(comment) = source.get(comment_start..end) {
          parse_reference_directive(&mut directives, source, comment_start, comment);
        }
      }
      idx = end;
      if idx < bytes.len() && bytes[idx] == b'\r' {
        idx += 1;
        if idx < bytes.len() && bytes[idx] == b'\n' {
          idx += 1;
        }
      } else if idx < bytes.len() && bytes[idx] == b'\n' {
        idx += 1;
      }
      continue;
    }

    if bytes.get(idx) == Some(&b'/') && bytes.get(idx + 1) == Some(&b'*') {
      idx += 2;
      while idx + 1 < bytes.len() {
        if bytes[idx] == b'*' && bytes[idx + 1] == b'/' {
          idx += 2;
          break;
        }
        idx += 1;
      }
      continue;
    }

    break;
  }

  directives
}

#[cfg(test)]
mod tests {
  use super::*;

  fn values(source: &str) -> Vec<(TripleSlashReferenceKind, String)> {
    scan_triple_slash_directives(source)
      .references
      .iter()
      .map(|r| (r.kind, r.value(source).to_string()))
      .collect()
  }

  #[test]
  fn parses_bom_prefixed_directives() {
    let source = "\u{feff}/// <reference path=\"./dep.ts\" />\nconst x = 1;";
    assert_eq!(
      values(source),
      vec![(TripleSlashReferenceKind::Path, "./dep.ts".to_string())]
    );
  }

  #[test]
  fn ignores_non_triple_slash_comments() {
    let source = "// <reference path=\"./dep.ts\" />\n/// <reference path=\"./real.ts\" />";
    assert_eq!(
      values(source),
      vec![(TripleSlashReferenceKind::Path, "./real.ts".to_string())]
    );
  }

  #[test]
  fn stops_at_first_non_trivia_token() {
    let source = "const x = 1;\n/// <reference path=\"./dep.ts\" />\n";
    assert!(values(source).is_empty());
  }

  #[test]
  fn parses_multiple_directives() {
    let source = "/// <reference types='node' />\n/// <reference lib=\"es2015.promise\" />\n";
    assert_eq!(
      values(source),
      vec![
        (TripleSlashReferenceKind::Types, "node".to_string()),
        (TripleSlashReferenceKind::Lib, "es2015.promise".to_string())
      ]
    );
  }

  #[test]
  fn parses_no_default_lib_flags() {
    let source = "/// <reference no-default-lib=\"true\" />\n";
    let directives = scan_triple_slash_directives(source);
    assert!(directives.no_default_lib);

    let source = "/// <reference noLib='1' />\n";
    let directives = scan_triple_slash_directives(source);
    assert!(directives.no_default_lib);
  }

  #[test]
  fn normalizes_reference_paths() {
    assert_eq!(
      normalize_reference_path_specifier("dep.ts").as_ref(),
      "./dep.ts"
    );
    assert_eq!(
      normalize_reference_path_specifier("./dep.ts").as_ref(),
      "./dep.ts"
    );
    assert_eq!(
      normalize_reference_path_specifier("..\\dep.ts").as_ref(),
      "../dep.ts"
    );
    assert_eq!(
      normalize_reference_path_specifier("C:\\dep.ts").as_ref(),
      "C:/dep.ts"
    );
  }
}
