use crate::multifile::normalize_name;
use crate::tsc::TscDiagnostic;
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use typecheck_ts::{Diagnostic, Severity};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NormalizedDiagnostic {
  pub code: Option<String>,
  pub category: Option<String>,
  pub file: Option<String>,
  pub start: u32,
  pub end: u32,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub message: Option<String>,
}

impl NormalizedDiagnostic {
  fn sort_key(&self) -> (String, u32, u32, String, String) {
    (
      self.file.clone().unwrap_or_default(),
      self.start,
      self.end,
      self.code.clone().unwrap_or_default(),
      self.category.clone().unwrap_or_default(),
    )
  }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DiagnosticDiff {
  pub missing: Vec<NormalizedDiagnostic>,
  pub unexpected: Vec<NormalizedDiagnostic>,
  pub mismatched: Vec<MismatchedDiagnostic>,
}

impl DiagnosticDiff {
  pub fn is_empty(&self) -> bool {
    self.missing.is_empty() && self.unexpected.is_empty() && self.mismatched.is_empty()
  }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MismatchedDiagnostic {
  pub expected: NormalizedDiagnostic,
  pub actual: NormalizedDiagnostic,
}

pub fn normalize_tsc_diagnostics(diags: &[TscDiagnostic]) -> Vec<NormalizedDiagnostic> {
  diags
    .iter()
    .map(|d| NormalizedDiagnostic {
      code: Some(d.code.to_string()),
      category: d.category.clone(),
      file: d.file.as_ref().map(|f| normalize_name(f)),
      start: d.start,
      end: d.end,
      message: d.message.clone(),
    })
    .collect()
}

pub fn normalize_rust_diagnostics(
  diags: &[Diagnostic],
  file_names: &[String],
) -> Vec<NormalizedDiagnostic> {
  diags
    .iter()
    .map(|d| {
      let (file, start, end) = match d.span {
        Some(span) => {
          let file_name = file_names
            .get(span.file.0 as usize)
            .cloned()
            .unwrap_or_else(|| format!("file{}", span.file.0));
          (Some(file_name), span.range.start, span.range.end)
        }
        None => (None, 0, 0),
      };

      NormalizedDiagnostic {
        code: d.code.clone(),
        category: Some(severity_to_str(d.severity).to_string()),
        file: file.as_deref().map(normalize_name),
        start,
        end,
        message: Some(d.message.clone()),
      }
    })
    .collect()
}

pub fn diff_diagnostics(
  expected: &[NormalizedDiagnostic],
  actual: &[NormalizedDiagnostic],
  tolerance: u32,
) -> Option<DiagnosticDiff> {
  let mut expected_sorted: Vec<_> = expected.to_vec();
  let mut actual_sorted: Vec<_> = actual.to_vec();

  expected_sorted.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
  actual_sorted.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));

  let mut idx_exp = 0;
  let mut idx_act = 0;

  let mut diff = DiagnosticDiff::default();

  while idx_exp < expected_sorted.len() && idx_act < actual_sorted.len() {
    let exp = &expected_sorted[idx_exp];
    let act = &actual_sorted[idx_act];

    if diag_eq(exp, act, tolerance) {
      idx_exp += 1;
      idx_act += 1;
      continue;
    }

    match exp.sort_key().cmp(&act.sort_key()) {
      Ordering::Less => {
        diff.missing.push(exp.clone());
        idx_exp += 1;
      }
      Ordering::Greater => {
        diff.unexpected.push(act.clone());
        idx_act += 1;
      }
      Ordering::Equal => {
        diff.mismatched.push(MismatchedDiagnostic {
          expected: exp.clone(),
          actual: act.clone(),
        });
        idx_exp += 1;
        idx_act += 1;
      }
    }
  }

  if idx_exp < expected_sorted.len() {
    diff
      .missing
      .extend(expected_sorted[idx_exp..].iter().cloned());
  }
  if idx_act < actual_sorted.len() {
    diff
      .unexpected
      .extend(actual_sorted[idx_act..].iter().cloned());
  }

  if diff.is_empty() {
    None
  } else {
    Some(diff)
  }
}

fn diag_eq(a: &NormalizedDiagnostic, b: &NormalizedDiagnostic, tolerance: u32) -> bool {
  a.code == b.code
    && a.category == b.category
    && a.file == b.file
    && within_tolerance(a.start, b.start, tolerance)
    && within_tolerance(a.end, b.end, tolerance)
}

fn within_tolerance(a: u32, b: u32, tolerance: u32) -> bool {
  let (min, max) = if a <= b { (a, b) } else { (b, a) };
  max - min <= tolerance
}

fn severity_to_str(severity: Severity) -> &'static str {
  match severity {
    Severity::Error => "error",
    Severity::Warning => "warning",
    Severity::Note => "note",
    Severity::Help => "help",
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn diff_reports_mismatched_lengths() {
    let expected = vec![NormalizedDiagnostic {
      code: Some("1".to_string()),
      category: None,
      file: Some("a.ts".to_string()),
      start: 0,
      end: 1,
      message: None,
    }];
    let actual = Vec::new();
    let diff = diff_diagnostics(&expected, &actual, 0).unwrap();
    assert_eq!(diff.missing.len(), 1);
    assert!(diff.unexpected.is_empty());
    assert!(diff.mismatched.is_empty());
  }

  #[test]
  fn diff_honors_tolerance() {
    let expected = vec![NormalizedDiagnostic {
      code: Some("1".to_string()),
      category: None,
      file: Some("a.ts".to_string()),
      start: 0,
      end: 4,
      message: None,
    }];
    let actual = vec![NormalizedDiagnostic {
      code: Some("1".to_string()),
      category: None,
      file: Some("a.ts".to_string()),
      start: 1,
      end: 5,
      message: None,
    }];

    assert!(diff_diagnostics(&expected, &actual, 0).is_some());
    assert!(diff_diagnostics(&expected, &actual, 1).is_none());
  }
}
