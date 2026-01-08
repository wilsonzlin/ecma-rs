use anyhow::Context;
use serde::Serialize;
use std::fs;
use std::io::{self, BufWriter, Write};
use std::path::Path;

/// A top-level report wrapper shared by conformance runners.
///
/// Runners should define their own `REPORT_SCHEMA_VERSION` and pass it to
/// [`ReportRef::new`].
#[derive(Debug, Serialize)]
pub struct ReportRef<'a, Summary, Result> {
  pub schema_version: u32,
  pub summary: &'a Summary,
  pub results: &'a [Result],
}

impl<'a, Summary, Result> ReportRef<'a, Summary, Result> {
  pub fn new(schema_version: u32, summary: &'a Summary, results: &'a [Result]) -> Self {
    Self {
      schema_version,
      summary,
      results,
    }
  }
}

/// Serialize `value` as pretty JSON.
///
/// Deterministic output requires that `value` itself is deterministic:
/// - use a stable ordering for result lists (e.g. sort by test id)
/// - prefer deterministic map types (`BTreeMap`) over `HashMap` for any fields
///   that are part of the serialized report
pub fn to_json_pretty_stable<T: Serialize>(value: &T) -> anyhow::Result<String> {
  serde_json::to_string_pretty(value).context("format JSON report")
}

/// Write a pretty, deterministic JSON report to `path`, creating parent
/// directories as needed.
pub fn write_json_report<T: Serialize>(path: &Path, report: &T) -> anyhow::Result<()> {
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
  }

  let file = fs::File::create(path).with_context(|| format!("create {}", path.display()))?;
  let mut writer = BufWriter::new(file);
  write_json_report_to_writer(&mut writer, report)
    .with_context(|| format!("write report to {}", path.display()))?;
  writer.flush().ok();
  Ok(())
}

/// Write a pretty, deterministic JSON report to `writer`.
pub fn write_json_report_to_writer<W: Write, T: Serialize>(
  writer: &mut W,
  report: &T,
) -> anyhow::Result<()> {
  serde_json::to_writer_pretty(&mut *writer, report).context("write JSON report")?;
  writeln!(&mut *writer).ok();
  Ok(())
}

/// Write a pretty, deterministic JSON report to stdout.
pub fn write_json_report_to_stdout<T: Serialize>(report: &T) -> anyhow::Result<()> {
  let stdout = io::stdout();
  let mut handle = stdout.lock();
  write_json_report_to_writer(&mut handle, report)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn json_report_serialization_is_stable_and_ordered() {
    #[derive(Debug, Serialize)]
    struct Summary {
      total: u32,
    }
    #[derive(Debug, Serialize)]
    struct ResultEntry {
      id: &'static str,
    }

    let summary = Summary { total: 1 };
    let results = [ResultEntry { id: "a" }];
    let report = ReportRef::new(7, &summary, &results);

    let json_one = to_json_pretty_stable(&report).unwrap();
    let json_two = to_json_pretty_stable(&report).unwrap();
    assert_eq!(json_one, json_two);

    let schema_idx = json_one.find("\"schema_version\"").unwrap();
    let summary_idx = json_one.find("\"summary\"").unwrap();
    let results_idx = json_one.find("\"results\"").unwrap();
    assert!(schema_idx < summary_idx);
    assert!(summary_idx < results_idx);
  }
}
