use crate::multifile::normalize_name;
use crate::tsc::TscDiagnostic;
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
  diags
    .iter()
    .map(|diag| {
      let file = normalize_file_name(file_name(diag.primary.file), options);
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
      file: normalize_file_name(diag.file.clone(), options),
      start: diag.start,
      end: diag.end,
      severity: normalize_severity(diag.category.as_deref(), options),
      message: None,
    })
    .collect()
}

pub fn sort_diagnostics(diags: &mut Vec<NormalizedDiagnostic>) {
  diags.sort_by(|a, b| {
    (
      a.file.as_deref().unwrap_or(""),
      a.start,
      a.end,
      code_key(&a.code),
    )
      .cmp(&(
        b.file.as_deref().unwrap_or(""),
        b.start,
        b.end,
        code_key(&b.code),
      ))
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
        numeric_code(rust_code).map_or(false, |num| num == *tsc_code)
      }
    },
    (None, None) => true,
    _ => false,
  }
}

fn numeric_code(raw: &str) -> Option<u32> {
  let trimmed = raw
    .trim_start_matches(|c| c == 't' || c == 'T')
    .trim_start_matches('S');
  trimmed.parse().ok()
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

fn normalize_file_name(file: Option<String>, options: &NormalizationOptions) -> Option<String> {
  if !options.normalize_paths {
    return file;
  }

  let mut name = file?;
  name = normalize_name(&name);

  if !name.starts_with('/') {
    name = format!("/{}", name.trim_start_matches('/'));
  }

  if let Some(rest) = name.strip_prefix('/') {
    let bytes = rest.as_bytes();
    if bytes.len() >= 2 && bytes[1] == b':' && bytes[0].is_ascii_alphabetic() {
      let stripped = rest[2..].trim_start_matches('/');
      if stripped.is_empty() {
        name = "/".to_string();
      } else {
        name = format!("/{}", stripped);
      }
    }
  }

  // Some fixtures/baselines may contain synthetic `drive_<letter>/...` prefixes (historically used
  // to keep drive-rooted paths relative on Windows). Strip that segment back to the canonical form.
  if let Some(rest) = name.strip_prefix('/') {
    let (first, remaining) = rest.split_once('/').unwrap_or((rest, ""));
    if let Some(letter) = first.strip_prefix("drive_") {
      let bytes = letter.as_bytes();
      if bytes.len() == 1 && bytes[0].is_ascii_alphabetic() {
        let remaining = remaining.trim_start_matches('/');
        if remaining.is_empty() {
          name = "/".to_string();
        } else {
          name = format!("/{}", remaining);
        }
      }
    }
  }

  Some(name)
}

fn normalize_severity(raw: Option<&str>, options: &NormalizationOptions) -> Option<String> {
  let severity = raw?;
  let lowered = severity.to_ascii_lowercase();
  if !options.normalize_severity {
    return Some(lowered);
  }

  Some(match lowered.as_str() {
    "error" => "error".to_string(),
    "warning" => "warning".to_string(),
    "suggestion" | "message" | "hint" => "info".to_string(),
    "note" | "help" => "info".to_string(),
    other => other.to_string(),
  })
}

fn code_key(code: &Option<DiagnosticCode>) -> (u8, String) {
  match code {
    Some(DiagnosticCode::Rust(val)) => (0, val.clone()),
    Some(DiagnosticCode::Tsc(val)) => (1, val.to_string()),
    None => (2, String::new()),
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
  normalize_file_name(Some(path.to_string()), options).unwrap_or_else(|| path.to_string())
}

/// Normalize a rendered type string for stable comparisons.
///
/// The normalizer is intentionally lightweight; it collapses whitespace, sorts
/// top-level union and intersection members, and strips parameter names from
/// arrow-function signatures so differences in source-level identifiers do not
/// cause spurious diffs.
pub fn normalize_type_string(raw: &str) -> String {
  fn split_top_level(raw: &str, delim: char) -> Option<Vec<String>> {
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
        '>' => depth_angle -= 1,
        _ => {}
      }
      if ch == delim
        && depth_paren == 0
        && depth_brace == 0
        && depth_bracket == 0
        && depth_angle == 0
      {
        parts.push(raw[start..idx].trim().to_string());
        start = idx + ch.len_utf8();
      }
    }
    if parts.is_empty() {
      return None;
    }
    parts.push(raw[start..].trim().to_string());
    Some(parts)
  }

  fn strip_param_names(params: &str) -> String {
    fn split_params(raw: &str) -> Vec<String> {
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
          '>' => depth_angle -= 1,
          ',' => {
            if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 && depth_angle == 0 {
              parts.push(raw[start..idx].trim().to_string());
              start = idx + 1;
            }
          }
          _ => {}
        }
      }
      parts.push(raw[start..].trim().to_string());
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
          '>' => depth_angle -= 1,
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
      normalized.push(strip_single_param(&param));
    }
    normalized.join(", ")
  }

  fn strip_trailing_object_semicolons(raw: &str) -> String {
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

  let collapsed = raw.split_whitespace().collect::<Vec<_>>().join(" ");
  let normalized = strip_trailing_object_semicolons(collapsed.trim());
  let tighten = |s: String| s.replace("< ", "<").replace(" >", ">");

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

  if let Some(arrow_idx) = normalized.find("=>") {
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
      normalize_type_string("{ a: number; b: string; }"),
      "{ a: number; b: string }".to_string()
    );
    assert_eq!(
      normalize_type_string("Promise< string | number >"),
      "Promise<string | number>".to_string()
    );
  }
}
