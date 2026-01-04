use crate::multifile::normalize_name_into;
use crate::tsc::TscDiagnostic;
use crate::tsc_codes::rust_code_matches_tsc;
use serde::{Deserialize, Serialize};
use typecheck_ts::{Diagnostic, FileId, Severity};

#[derive(Debug, Clone)]
pub struct NormalizationOptions {
  pub span_tolerance: u32,
  pub normalize_severity: bool,
  pub normalize_paths: bool,
}

impl Default for NormalizationOptions {
  fn default() -> Self {
    Self {
      span_tolerance: 0,
      normalize_severity: true,
      normalize_paths: true,
    }
  }
}

impl NormalizationOptions {
  pub fn with_span_tolerance(span_tolerance: u32) -> Self {
    Self {
      span_tolerance,
      ..Default::default()
    }
  }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticEngine {
  Rust,
  Tsc,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(untagged)]
pub enum DiagnosticCode {
  Rust(String),
  Tsc(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NormalizedDiagnostic {
  pub engine: DiagnosticEngine,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub code: Option<DiagnosticCode>,
  pub file: Option<String>,
  pub start: u32,
  pub end: u32,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub severity: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub message: Option<String>,
}

pub fn normalize_rust_diagnostics(
  diags: &[Diagnostic],
  file_name: impl Fn(FileId) -> Option<String>,
) -> Vec<NormalizedDiagnostic> {
  normalize_rust_diagnostics_with_options(diags, file_name, &NormalizationOptions::default())
}

pub fn normalize_rust_diagnostics_with_options(
  diags: &[Diagnostic],
  file_name: impl Fn(FileId) -> Option<String>,
  options: &NormalizationOptions,
) -> Vec<NormalizedDiagnostic> {
  let mut name_buf = String::new();
  diags
    .iter()
    .map(|diag| {
      let file = normalize_file_name_owned(file_name(diag.primary.file), options, &mut name_buf);
      let (start, end) = normalize_span(diag.primary.range.start, diag.primary.range.end);

      NormalizedDiagnostic {
        engine: DiagnosticEngine::Rust,
        code: Some(DiagnosticCode::Rust(diag.code.as_str().to_string())),
        file,
        start,
        end,
        severity: normalize_severity(
          Some(match diag.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
            Severity::Help => "help",
          }),
          options,
        ),
        message: Some(diag.message.clone()),
      }
    })
    .collect()
}

pub fn normalize_tsc_diagnostics(diags: &[TscDiagnostic]) -> Vec<NormalizedDiagnostic> {
  normalize_tsc_diagnostics_with_options(diags, &NormalizationOptions::default())
}

pub fn normalize_tsc_diagnostics_with_options(
  diags: &[TscDiagnostic],
  options: &NormalizationOptions,
) -> Vec<NormalizedDiagnostic> {
  diags
    .iter()
    .map(|diag| NormalizedDiagnostic {
      engine: DiagnosticEngine::Tsc,
      code: Some(DiagnosticCode::Tsc(diag.code)),
      file: normalize_file_name_borrowed(diag.file.as_deref(), options),
      start: diag.start,
      end: diag.end,
      severity: normalize_severity(diag.category.as_deref(), options),
      message: None,
    })
    .collect()
}

pub fn sort_diagnostics(diags: &mut Vec<NormalizedDiagnostic>) {
  fn compare_codes(a: &Option<DiagnosticCode>, b: &Option<DiagnosticCode>) -> std::cmp::Ordering {
    match (a, b) {
      (None, None) => std::cmp::Ordering::Equal,
      // Sort diagnostics without codes last (they are generally less actionable).
      (None, Some(_)) => std::cmp::Ordering::Greater,
      (Some(_), None) => std::cmp::Ordering::Less,
      (Some(DiagnosticCode::Rust(a)), Some(DiagnosticCode::Rust(b))) => a.cmp(b),
      (Some(DiagnosticCode::Tsc(a)), Some(DiagnosticCode::Tsc(b))) => a.cmp(b),
      // Keep Rust/tsc codes grouped for determinism (and easier reading).
      (Some(DiagnosticCode::Rust(_)), Some(DiagnosticCode::Tsc(_))) => std::cmp::Ordering::Less,
      (Some(DiagnosticCode::Tsc(_)), Some(DiagnosticCode::Rust(_))) => std::cmp::Ordering::Greater,
    }
  }

  diags.sort_by(|a, b| {
    a.file
      .as_deref()
      .unwrap_or("")
      .cmp(b.file.as_deref().unwrap_or(""))
      .then_with(|| a.start.cmp(&b.start))
      .then_with(|| a.end.cmp(&b.end))
      .then_with(|| compare_codes(&a.code, &b.code))
  });
}

pub fn describe(diag: &NormalizedDiagnostic) -> String {
  let location = diag
    .file
    .as_deref()
    .map(|f| format!("{f}:{}-{}", diag.start, diag.end))
    .unwrap_or_else(|| format!("<unknown>:{}-{}", diag.start, diag.end));
  let code = diag
    .code
    .as_ref()
    .map(code_to_string)
    .unwrap_or_else(|| "unknown".to_string());
  format!("{location} [{code}]")
}

pub fn within_tolerance(a: u32, b: u32, tolerance: u32) -> bool {
  let (min, max) = if a <= b { (a, b) } else { (b, a) };
  max - min <= tolerance
}

impl NormalizedDiagnostic {
  pub fn matches(&self, other: &NormalizedDiagnostic, options: &NormalizationOptions) -> bool {
    files_match(&self.file, &other.file)
      && spans_match(self, other, options)
      && codes_match(&self.code, &other.code)
      && severity_matches(&self.severity, &other.severity)
  }

  pub fn spans_match(&self, other: &NormalizedDiagnostic, options: &NormalizationOptions) -> bool {
    spans_match(self, other, options)
  }

  pub fn codes_match(&self, other: &NormalizedDiagnostic) -> bool {
    codes_match(&self.code, &other.code)
  }

  pub fn severity_matches(&self, other: &NormalizedDiagnostic) -> bool {
    severity_matches(&self.severity, &other.severity)
  }
}

fn spans_match(
  a: &NormalizedDiagnostic,
  b: &NormalizedDiagnostic,
  options: &NormalizationOptions,
) -> bool {
  within_tolerance(a.start, b.start, options.span_tolerance)
    && within_tolerance(a.end, b.end, options.span_tolerance)
}

fn files_match(a: &Option<String>, b: &Option<String>) -> bool {
  match (a, b) {
    (Some(a), Some(b)) => a == b,
    (None, None) => true,
    _ => false,
  }
}

fn codes_match(a: &Option<DiagnosticCode>, b: &Option<DiagnosticCode>) -> bool {
  match (a, b) {
    (Some(a), Some(b)) => match (a, b) {
      (DiagnosticCode::Rust(a_code), DiagnosticCode::Rust(b_code)) => a_code == b_code,
      (DiagnosticCode::Tsc(a_code), DiagnosticCode::Tsc(b_code)) => a_code == b_code,
      (DiagnosticCode::Rust(rust_code), DiagnosticCode::Tsc(tsc_code))
      | (DiagnosticCode::Tsc(tsc_code), DiagnosticCode::Rust(rust_code)) => {
        rust_code_matches_tsc(rust_code, *tsc_code)
      }
    },
    (None, None) => true,
    _ => false,
  }
}

fn severity_matches(a: &Option<String>, b: &Option<String>) -> bool {
  match (a, b) {
    (Some(a), Some(b)) => a == b,
    (None, None) => true,
    _ => false,
  }
}

fn normalize_span(start: u32, end: u32) -> (u32, u32) {
  if end < start {
    (end, start)
  } else {
    (start, end)
  }
}

fn normalize_file_name_owned(
  file: Option<String>,
  options: &NormalizationOptions,
  normalized_buf: &mut String,
) -> Option<String> {
  if !options.normalize_paths {
    return file;
  }

  let mut name = file?;
  normalize_file_name_into(&name, options, normalized_buf);
  std::mem::swap(&mut name, normalized_buf);
  Some(name)
}

fn normalize_file_name_borrowed(
  file: Option<&str>,
  options: &NormalizationOptions,
) -> Option<String> {
  let file = file?;
  if !options.normalize_paths {
    return Some(file.to_string());
  }

  let mut normalized = String::with_capacity(file.len() + 1);
  normalize_file_name_into(file, options, &mut normalized);
  Some(normalized)
}

fn normalize_file_name_into(raw: &str, options: &NormalizationOptions, out: &mut String) {
  debug_assert!(options.normalize_paths);
  normalize_name_into(raw, out);
  if !out.starts_with('/') {
    out.insert(0, '/');
  }

  strip_drive_prefix(out);
  strip_synthetic_drive_prefix(out);
}

fn strip_drive_prefix(name: &mut String) {
  let (is_drive, strip_start, len) = {
    let bytes = name.as_bytes();
    if bytes.len() >= 3 && bytes[0] == b'/' && bytes[2] == b':' && bytes[1].is_ascii_alphabetic() {
      let mut idx = 3usize;
      while idx < bytes.len() && bytes[idx] == b'/' {
        idx += 1;
      }
      (true, idx, bytes.len())
    } else {
      (false, 0usize, bytes.len())
    }
  };

  if !is_drive {
    return;
  }

  if strip_start >= len {
    name.truncate(1);
  } else {
    name.replace_range(1..strip_start, "");
  }
}

fn strip_synthetic_drive_prefix(name: &mut String) {
  // Some fixtures/baselines may contain synthetic `drive_<letter>/...` prefixes (historically used
  // to keep drive-rooted paths relative on Windows). Strip that segment back to the canonical form.
  let (is_synthetic, strip_start, len) = {
    let bytes = name.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'/' {
      return;
    }

    let mut seg_end = 1usize;
    while seg_end < bytes.len() && bytes[seg_end] != b'/' {
      seg_end += 1;
    }

    let seg_len = seg_end - 1;
    if seg_len == 7
      && bytes.len() >= 8
      && bytes[1..7] == *b"drive_"
      && bytes[7].is_ascii_alphabetic()
    {
      let mut idx = seg_end;
      while idx < bytes.len() && bytes[idx] == b'/' {
        idx += 1;
      }
      (true, idx, bytes.len())
    } else {
      (false, 0usize, bytes.len())
    }
  };

  if !is_synthetic {
    return;
  }

  if strip_start >= len {
    name.truncate(1);
  } else {
    name.replace_range(1..strip_start, "");
  }
}

fn normalize_severity(raw: Option<&str>, options: &NormalizationOptions) -> Option<String> {
  let severity = raw?;
  let lowered = severity.to_ascii_lowercase();
  if !options.normalize_severity {
    return Some(lowered);
  }

  match lowered.as_str() {
    "suggestion" | "message" | "hint" | "note" | "help" => Some("info".to_string()),
    _ => Some(lowered),
  }
}

fn code_to_string(code: &DiagnosticCode) -> String {
  match code {
    DiagnosticCode::Rust(c) => c.clone(),
    DiagnosticCode::Tsc(c) => c.to_string(),
  }
}

pub fn diagnostic_code_display(code: &DiagnosticCode) -> String {
  code_to_string(code)
}

pub fn normalize_path_for_compare(path: &str, options: &NormalizationOptions) -> String {
  normalize_file_name_borrowed(Some(path), options).unwrap_or_else(|| path.to_string())
}

/// Normalize a rendered type string for stable comparisons.
///
/// The normalizer is intentionally lightweight; it collapses whitespace, sorts
/// top-level union and intersection members, normalizes call/construct signature
/// members in object types, and strips parameter names from signatures so
/// differences in source-level identifiers (or overload ordering) do not cause
/// spurious diffs.
pub fn normalize_type_string(raw: &str) -> String {
  fn collapse_whitespace(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    let mut pending_space = false;
    for ch in raw.chars() {
      if ch.is_whitespace() {
        if !out.is_empty() {
          pending_space = true;
        }
        continue;
      }
      if pending_space {
        out.push(' ');
        pending_space = false;
      }
      out.push(ch);
    }
    out
  }

  fn split_top_level<'a>(raw: &'a str, delim: char) -> Option<Vec<&'a str>> {
    let mut parts = Vec::new();
    let mut start = 0usize;
    let mut saw_delim = false;
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let mut depth_angle = 0i32;
    for (idx, ch) in raw.char_indices() {
      match ch {
        '(' => depth_paren += 1,
        ')' => depth_paren -= 1,
        '{' => depth_brace += 1,
        '}' => depth_brace -= 1,
        '[' => depth_bracket += 1,
        ']' => depth_bracket -= 1,
        '<' => depth_angle += 1,
        '>' => {
          // Ignore `>` characters that are not closing a `<...>` pair (e.g. the `>` in `=>`).
          if depth_angle > 0 {
            depth_angle -= 1;
          }
        }
        _ => {}
      }
      if ch == delim
        && depth_paren == 0
        && depth_brace == 0
        && depth_bracket == 0
        && depth_angle == 0
      {
        parts.push(raw[start..idx].trim());
        start = idx + ch.len_utf8();
        saw_delim = true;
      }
    }
    if !saw_delim {
      return None;
    }
    parts.push(raw[start..].trim());
    Some(parts)
  }

  fn strip_param_names(params: &str) -> String {
    fn split_params<'a>(raw: &'a str) -> Vec<&'a str> {
      let mut parts = Vec::new();
      let mut start = 0usize;
      let mut depth_paren = 0i32;
      let mut depth_brace = 0i32;
      let mut depth_bracket = 0i32;
      let mut depth_angle = 0i32;
      for (idx, ch) in raw.char_indices() {
        match ch {
          '(' => depth_paren += 1,
          ')' => depth_paren -= 1,
          '{' => depth_brace += 1,
          '}' => depth_brace -= 1,
          '[' => depth_bracket += 1,
          ']' => depth_bracket -= 1,
          '<' => depth_angle += 1,
          '>' => {
            if depth_angle > 0 {
              depth_angle -= 1;
            }
          }
          ',' => {
            if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 && depth_angle == 0 {
              parts.push(raw[start..idx].trim());
              start = idx + 1;
            }
          }
          _ => {}
        }
      }
      parts.push(raw[start..].trim());
      parts
    }

    fn strip_single_param(raw: &str) -> String {
      let mut depth_paren = 0i32;
      let mut depth_brace = 0i32;
      let mut depth_bracket = 0i32;
      let mut depth_angle = 0i32;
      for (idx, ch) in raw.char_indices() {
        match ch {
          '(' => depth_paren += 1,
          ')' => depth_paren -= 1,
          '{' => depth_brace += 1,
          '}' => depth_brace -= 1,
          '[' => depth_bracket += 1,
          ']' => depth_bracket -= 1,
          '<' => depth_angle += 1,
          '>' => {
            if depth_angle > 0 {
              depth_angle -= 1;
            }
          }
          ':' => {
            if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 && depth_angle == 0 {
              let rest = raw[idx + ch.len_utf8()..].trim();
              let is_rest = raw.trim_start().starts_with("...");
              let rest = normalize_type_string(rest);
              return if is_rest { format!("...{rest}") } else { rest };
            }
          }
          _ => {}
        }
      }
      normalize_type_string(raw.trim())
    }

    let mut normalized = Vec::new();
    for param in split_params(params) {
      if param.is_empty() {
        continue;
      }
      normalized.push(strip_single_param(param));
    }
    normalized.join(", ")
  }

  fn strip_trailing_object_semicolons(raw: String) -> String {
    if !raw.contains(';') {
      return raw;
    }

    let mut out = String::with_capacity(raw.len());
    let mut iter = raw.chars().peekable();
    while let Some(ch) = iter.next() {
      if ch == ';' {
        let mut lookahead = iter.clone();
        while let Some(next) = lookahead.peek() {
          if next.is_whitespace() {
            lookahead.next();
            continue;
          }
          break;
        }
        if matches!(lookahead.peek(), Some('}')) {
          continue;
        }
      }
      out.push(ch);
    }
    out
  }

  fn find_top_level_arrow(raw: &str) -> Option<usize> {
    let mut depth_paren = 0i32;
    let mut depth_brace = 0i32;
    let mut depth_bracket = 0i32;
    let mut depth_angle = 0i32;
    let bytes = raw.as_bytes();
    for (idx, ch) in raw.char_indices() {
      match ch {
        '(' => depth_paren += 1,
        ')' => depth_paren -= 1,
        '{' => depth_brace += 1,
        '}' => depth_brace -= 1,
        '[' => depth_bracket += 1,
        ']' => depth_bracket -= 1,
        '<' => depth_angle += 1,
        '>' => {
          if depth_angle > 0 {
            depth_angle -= 1;
          }
        }
        '=' => {
          if depth_paren == 0
            && depth_brace == 0
            && depth_bracket == 0
            && depth_angle == 0
            && bytes.get(idx..idx + 2) == Some(&b"=>"[..])
          {
            return Some(idx);
          }
        }
        _ => {}
      }
    }
    None
  }

  fn normalize_object_member(raw: &str) -> String {
    let member = raw.trim();
    if member.is_empty() {
      return String::new();
    }

    if (member.starts_with('(') || member.starts_with('<')) && find_top_level_arrow(member).is_some() {
      return normalize_type_string(member);
    }

    let Some(start_paren) = member.find('(') else {
      return member.to_string();
    };

    let mut depth_paren = 0i32;
    let mut end_paren = None;
    for (idx, ch) in member.char_indices().skip(start_paren) {
      match ch {
        '(' => depth_paren += 1,
        ')' => {
          depth_paren -= 1;
          if depth_paren == 0 {
            end_paren = Some(idx);
            break;
          }
        }
        _ => {}
      }
    }
    let Some(end_paren) = end_paren else {
      return member.to_string();
    };

    let suffix = &member[end_paren + 1..];
    let suffix = suffix.trim_start();
    if !suffix.starts_with(':') {
      return member.to_string();
    }

    let prefix = member[..start_paren].trim_start();
    let params = &member[start_paren + 1..end_paren];
    let stripped = strip_param_names(params);
    let ret = normalize_type_string(suffix[1..].trim_start());
    format!("{prefix}({stripped}) => {ret}")
  }

  fn normalize_object_members(raw: &str) -> Option<String> {
    let trimmed = raw.trim();
    if !(trimmed.starts_with('{') && trimmed.ends_with('}')) {
      return None;
    }

    let inner = trimmed[1..trimmed.len() - 1].trim();
    if inner.is_empty() {
      return Some("{}".to_string());
    }

    let parts = split_top_level(inner, ';').unwrap_or_else(|| vec![inner]);
    let mut members: Vec<String> = parts
      .into_iter()
      .map(normalize_object_member)
      .filter(|member| !member.is_empty())
      .collect();

    members.sort();
    members.dedup();
    Some(format!("{{ {} }}", members.join("; ")))
  }

  fn tighten(value: String) -> String {
    if !value.contains("< ") && !value.contains(" >") {
      return value;
    }

    let mut out = String::with_capacity(value.len());
    let mut chars = value.chars().peekable();
    while let Some(ch) = chars.next() {
      match ch {
        '<' => {
          out.push('<');
          if matches!(chars.peek(), Some(' ')) {
            chars.next();
          }
        }
        ' ' => {
          if matches!(chars.peek(), Some('>')) {
            continue;
          }
          out.push(' ');
        }
        _ => out.push(ch),
      }
    }
    out
  }

  let collapsed = collapse_whitespace(raw);
  let normalized = strip_trailing_object_semicolons(collapsed);

  if let Some(arrow_idx) = find_top_level_arrow(&normalized) {
    let params_part = normalized[..arrow_idx].trim_end();
    let ret_part = normalized[arrow_idx + 2..].trim_start();
    if let Some(start_paren) = params_part.rfind('(') {
      if params_part.ends_with(')') && start_paren < params_part.len() {
        let params = &params_part[start_paren + 1..params_part.len() - 1];
        let before = params_part[..start_paren].trim();
        let stripped = strip_param_names(params);
        let before = if before.is_empty() {
          String::new()
        } else {
          format!("{before}")
        };
        let ret = normalize_type_string(ret_part);
        return tighten(format!("{before}({stripped}) => {ret}"));
      }
    }
  }

  if let Some(parts) = split_top_level(&normalized, '|') {
    let mut normalized_parts: Vec<_> = parts
      .into_iter()
      .filter(|p| !p.is_empty())
      .map(|p| normalize_type_string(&p))
      .collect();
    normalized_parts.sort();
    normalized_parts.dedup();
    return tighten(normalized_parts.join(" | "));
  }

  if let Some(parts) = split_top_level(&normalized, '&') {
    let mut normalized_parts: Vec<_> = parts
      .into_iter()
      .filter(|p| !p.is_empty())
      .map(|p| normalize_type_string(&p))
      .collect();
    normalized_parts.sort();
    normalized_parts.dedup();
    return tighten(normalized_parts.join(" & "));
  }

  if let Some(obj) = normalize_object_members(&normalized) {
    return tighten(obj);
  }

  tighten(normalized)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn normalizes_windows_style_paths_and_strips_drive() {
    let diags = vec![TscDiagnostic {
      code: 1,
      file: Some("C:\\case\\src\\a.ts".to_string()),
      start: 0,
      end: 1,
      category: Some("error".to_string()),
      message: None,
    }];
    let normalized =
      normalize_tsc_diagnostics_with_options(&diags, &NormalizationOptions::default());
    assert_eq!(normalized[0].file.as_deref(), Some("/case/src/a.ts"));
  }

  #[test]
  fn strips_synthetic_drive_prefix_paths() {
    let diags = vec![TscDiagnostic {
      code: 1,
      file: Some("drive_c/case/src/a.ts".to_string()),
      start: 0,
      end: 1,
      category: Some("error".to_string()),
      message: None,
    }];
    let normalized =
      normalize_tsc_diagnostics_with_options(&diags, &NormalizationOptions::default());
    assert_eq!(normalized[0].file.as_deref(), Some("/case/src/a.ts"));
  }

  #[test]
  fn treats_lf_and_crlf_spans_with_tolerance() {
    let options = NormalizationOptions::with_span_tolerance(1);
    let rust = NormalizedDiagnostic {
      engine: DiagnosticEngine::Rust,
      code: Some(DiagnosticCode::Rust("2345".into())),
      file: Some(normalize_path_for_compare("/file.ts", &options)),
      start: 5,
      end: 10,
      severity: Some("error".into()),
      message: None,
    };
    let tsc_raw = TscDiagnostic {
      code: 2345,
      file: Some("\\file.ts".into()),
      start: 6,
      end: 11,
      category: Some("error".into()),
      message: None,
    };
    let tsc = normalize_tsc_diagnostics_with_options(&[tsc_raw], &options).remove(0);
    assert!(rust.matches(&tsc, &options));
  }

  #[test]
  fn canonicalizes_multifile_virtual_ids() {
    let options = NormalizationOptions::default();
    let diags = vec![
      TscDiagnostic {
        code: 1,
        file: Some("subdir\\..\\a.ts".to_string()),
        start: 0,
        end: 1,
        category: None,
        message: None,
      },
      TscDiagnostic {
        code: 1,
        file: Some("/a.ts".to_string()),
        start: 0,
        end: 1,
        category: None,
        message: None,
      },
    ];
    let normalized = normalize_tsc_diagnostics_with_options(&diags, &options);
    assert_eq!(normalized[0].file, normalized[1].file);
  }

  #[test]
  fn normalizes_type_strings() {
    assert_eq!(
      normalize_type_string("string | number"),
      "number | string".to_string()
    );
    assert_eq!(
      normalize_type_string("(a: number, b: string)=>Promise< string >"),
      "(number, string) => Promise<string>".to_string()
    );
    assert_eq!(
      normalize_type_string("(string | number) => number | string"),
      "(number | string) => number | string".to_string()
    );
    assert_eq!(
      normalize_type_string("(number | string) => string | number"),
      "(number | string) => number | string".to_string()
    );
    assert_eq!(
      normalize_type_string("{ a: number; b: string; }"),
      "{ a: number; b: string }".to_string()
    );
    assert_eq!(
      normalize_type_string("Promise< string | number >"),
      "Promise<string | number>".to_string()
    );
    assert_eq!(
      normalize_type_string("{ (x: string): 1; (x: number): 2 }"),
      "{ (number) => 2; (string) => 1 }".to_string()
    );
    assert_eq!(
      normalize_type_string("{(string) => 1;(number) => 2 }"),
      "{ (number) => 2; (string) => 1 }".to_string()
    );
  }

  #[test]
  fn normalizes_call_signature_param_names_and_overload_order() {
    let expected = "{ (x: string): 1; (x: number): 2 }";
    let actual = "{ (number): 2; (string): 1 }";
    assert_eq!(normalize_type_string(expected), normalize_type_string(actual));
  }
}
