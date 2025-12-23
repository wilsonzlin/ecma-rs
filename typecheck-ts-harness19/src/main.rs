use clap::Parser;
use clap::Subcommand;
use std::path::PathBuf;
use std::time::Duration;
use typecheck_ts_harness19::build_filter;
use typecheck_ts_harness19::run_conformance;
use typecheck_ts_harness19::ConformanceOptions;
use typecheck_ts_harness19::HarnessError;
use typecheck_ts_harness19::JsonReport;
use typecheck_ts_harness19::Shard;
use typecheck_ts_harness19::TestStatus;

const DEFAULT_ROOT: &str = "parse-js/tests/TypeScript/tests/cases/conformance";
const DEFAULT_TIMEOUT: u64 = 10;

#[derive(Parser)]
#[command(author, version, about = "TypeScript type checking conformance harness", long_about = None)]
struct Cli {
  #[command(subcommand)]
  command: Commands,
}

#[derive(Subcommand)]
enum Commands {
  /// Run TypeScript conformance tests
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
    root: Option<PathBuf>,
  },
}

fn main() {
  if let Err(err) = real_main() {
    eprintln!("error: {err}");
    std::process::exit(1);
  }
}

fn real_main() -> Result<(), HarnessError> {
  let cli = Cli::parse();

  match cli.command {
    Commands::Conformance {
      filter,
      shard,
      json,
      update_snapshots,
      timeout_secs,
      trace,
      profile,
      root,
    } => run_conformance_command(
      filter,
      shard,
      json,
      update_snapshots,
      timeout_secs,
      trace,
      profile,
      root,
    )?,
  }

  Ok(())
}

fn run_conformance_command(
  filter: Option<String>,
  shard: Option<String>,
  json: bool,
  update_snapshots: bool,
  timeout_secs: u64,
  trace: bool,
  profile: bool,
  root: Option<PathBuf>,
) -> Result<(), HarnessError> {
  let filter = build_filter(filter.as_deref())?;
  let shard = match shard {
    Some(raw) => Some(Shard::parse(&raw)?),
    None => None,
  };

  let options = ConformanceOptions {
    root: root.unwrap_or_else(|| PathBuf::from(DEFAULT_ROOT)),
    filter,
    shard,
    json,
    update_snapshots,
    timeout: Duration::from_secs(timeout_secs),
    trace,
    profile,
  };

  let report = run_conformance(options)?;

  print_summary(&report);

  if json {
    let json_output =
      serde_json::to_string_pretty(&report).map_err(|err| HarnessError::Output(err.to_string()))?;
    println!("{}", json_output);
  }

  Ok(())
}

fn print_summary(report: &JsonReport) {
  println!("Ran {} test(s)", report.summary.total);
  println!(
    "Passed: {}, Failed: {}, Timed out: {}",
    report.summary.passed, report.summary.failed, report.summary.timed_out
  );

  for result in &report.results {
    println!(
      "- {} [{}] ({:?} ms)",
      result.id,
      format_status(&result.status),
      result.duration_ms
    );
    if let Some(first) = result.diagnostics.first() {
      println!("  first diagnostic: {} {}", first.code, first.message);
    }
  }
}

fn format_status(status: &TestStatus) -> &'static str {
  match status {
    TestStatus::Passed => "passed",
    TestStatus::ParseError => "parse",
    TestStatus::BindError => "bind",
    TestStatus::TypeError => "type",
    TestStatus::Ice => "ice",
    TestStatus::InternalError => "internal",
    TestStatus::Timeout => "timeout",
  }
}
