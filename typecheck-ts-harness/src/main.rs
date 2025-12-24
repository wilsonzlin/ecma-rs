use clap::Parser;
use clap::Subcommand;
use std::process::ExitCode;
use std::time::Duration;
use typecheck_ts_harness::build_filter;
use typecheck_ts_harness::difftsc::CommandStatus;
use typecheck_ts_harness::difftsc::DifftscArgs;
use typecheck_ts_harness::difftsc::{self};
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::HarnessError;
use typecheck_ts_harness::Shard;
use typecheck_ts_harness::DEFAULT_EXTENSIONS;

const DEFAULT_ROOT: &str = "parse-js/tests/TypeScript/tests/cases/conformance";
const DEFAULT_TIMEOUT: u64 = 10;

#[derive(Parser)]
#[command(author, version, about = "TypeScript type-checking harness utilities", long_about = None)]
struct Cli {
  #[command(subcommand)]
  command: Commands,
}

#[derive(Subcommand)]
enum Commands {
  /// Run differential tests against tsc diagnostics
  Difftsc(DifftscArgs),

  /// Run TypeScript conformance tests using the Rust checker
  Conformance {
    /// Glob or regex to filter tests
    #[arg(long)]
    filter: Option<String>,

    /// Run only a shard (zero-based): `i/n`
    #[arg(long)]
    shard: Option<String>,

    /// Emit JSON output in addition to the human summary
    #[arg(long)]
    json: bool,

    /// Update stored snapshots (placeholder)
    #[arg(long)]
    update_snapshots: bool,

    /// Timeout per test case
    #[arg(long, default_value_t = DEFAULT_TIMEOUT)]
    timeout_secs: u64,

    /// Enable tracing in the checker (passthrough)
    #[arg(long)]
    trace: bool,

    /// Enable profiling output (passthrough)
    #[arg(long)]
    profile: bool,

    /// Override the conformance root directory
    #[arg(long)]
    root: Option<std::path::PathBuf>,

    /// Comma-separated list of extensions to include (default: ts,tsx,d.ts)
    #[arg(long)]
    extensions: Option<String>,

    /// Allow running with zero discovered tests
    #[arg(long)]
    allow_empty: bool,
  },
}

fn main() -> ExitCode {
  let cli = Cli::parse();
  match cli.command {
    Commands::Difftsc(args) => match difftsc::run(args) {
      Ok(CommandStatus::Success) | Ok(CommandStatus::Skipped) => ExitCode::SUCCESS,
      Err(err) => {
        eprintln!("{err:?}");
        ExitCode::from(1)
      }
    },
    Commands::Conformance {
      filter,
      shard,
      json,
      update_snapshots,
      timeout_secs,
      trace,
      profile,
      root,
      extensions,
      allow_empty,
    } => {
      let filter = match build_filter(filter.as_deref()) {
        Ok(filter) => filter,
        Err(err) => return print_error(err),
      };
      let shard = match shard {
        Some(raw) => match Shard::parse(&raw) {
          Ok(shard) => Some(shard),
          Err(err) => return print_error(err),
        },
        None => None,
      };

      let extensions = match parse_extensions(extensions.as_deref()) {
        Ok(ext) => ext,
        Err(err) => return print_error(err),
      };

      let options = ConformanceOptions {
        root: root.unwrap_or_else(|| DEFAULT_ROOT.into()),
        filter,
        shard,
        json,
        update_snapshots,
        timeout: Duration::from_secs(timeout_secs),
        trace,
        profile,
        extensions,
        allow_empty,
      };

      match run_conformance(options) {
        Ok(report) => {
          if json {
            match serde_json::to_string_pretty(&report) {
              Ok(output) => println!("{output}"),
              Err(err) => return print_error(err),
            }
          } else {
            println!("Ran {} test(s)", report.summary.total);
            println!(
              "Passed: {}, Failed: {}, Timed out: {}",
              report.summary.passed, report.summary.failed, report.summary.timed_out
            );
          }
          ExitCode::SUCCESS
        }
        Err(err) => print_error(err),
      }
    }
  }
}

fn print_error(err: impl std::fmt::Display) -> ExitCode {
  eprintln!("error: {err}");
  ExitCode::from(1)
}

fn parse_extensions(raw: Option<&str>) -> Result<Vec<String>, HarnessError> {
  match raw {
    Some(raw) => {
      let mut parsed = Vec::new();
      for part in raw.split(',') {
        let trimmed = part.trim().trim_start_matches('.');
        if trimmed.is_empty() {
          continue;
        }

        let value = trimmed.to_string();
        if !parsed.contains(&value) {
          parsed.push(value);
        }
      }

      if parsed.is_empty() {
        return Err(HarnessError::InvalidExtensions(raw.to_string()));
      }

      Ok(parsed)
    }
    None => Ok(
      DEFAULT_EXTENSIONS
        .iter()
        .map(|ext| ext.to_string())
        .collect(),
    ),
  }
}
