use clap::command;
use clap::Parser;
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{diagnostic_from_syntax_error, Diagnostic, FileId};
use rayon::prelude::*;
use std::fs;
use std::fs::read_dir;
use std::path::PathBuf;

struct SingleFileSource<'a> {
  file_name: &'a str,
  text: &'a str,
}

impl SourceProvider for SingleFileSource<'_> {
  fn file_name(&self, _file: FileId) -> &str {
    self.file_name
  }

  fn file_text(&self, _file: FileId) -> &str {
    self.text
  }
}

struct TestResult {
  file_name: String,
  source: Option<String>,
  error: Option<Diagnostic>,
}

#[derive(Parser, Debug)]
#[command(version)]
struct Cli {
  /// Path to tc39/test262-parser-tests repository folder.
  #[arg(long)]
  data_dir: PathBuf,
}

fn main() {
  let cli = Cli::parse();

  let entries = read_dir(cli.data_dir.join("pass"))
    .unwrap()
    .collect::<Result<Vec<_>, _>>()
    .unwrap();

  let mut results: Vec<TestResult> = entries
    .par_iter()
    .map(|entry| {
      let file_name = entry.file_name().to_string_lossy().into_owned();
      let src = fs::read_to_string(entry.path()).unwrap();
      let error = parse_js::parse(&src)
        .err()
        .map(|err| diagnostic_from_syntax_error(FileId(0), &err));
      let source = error.as_ref().map(|_| src);
      TestResult {
        file_name,
        source,
        error,
      }
    })
    .collect();

  results.sort_by(|a, b| a.file_name.cmp(&b.file_name));

  let mut passed_count = 0;
  let mut failed_count = 0;
  let total_count = results.len();
  for result in &results {
    match &result.error {
      Some(error) => {
        let source = result
          .source
          .as_deref()
          .expect("source must be present when rendering a diagnostic");
        let source_provider = SingleFileSource {
          file_name: &result.file_name,
          text: source,
        };
        eprintln!(
          "Test {} failed:\n{}",
          result.file_name,
          render_diagnostic(&source_provider, error)
        );
        failed_count += 1;
      }
      None => {
        passed_count += 1;
      }
    };
  }
  println!(
    "{} ({}%) passed, {} ({}%) failed",
    passed_count,
    passed_count as f64 / total_count as f64 * 100.0,
    failed_count,
    failed_count as f64 / total_count as f64 * 100.0
  );
}
