use clap::Parser;
use clap::Subcommand;
use clap::ValueEnum;
use num_cpus;
use std::process::ExitCode;
use std::time::Duration;
use typecheck_ts_harness::build_filter;
use typecheck_ts_harness::difftsc::CommandStatus;
use typecheck_ts_harness::difftsc::DifftscArgs;
use typecheck_ts_harness::difftsc::{self};
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::CompareMode;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::FailOn;
use typecheck_ts_harness::Shard;

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

    /// Comma-separated list of allowed extensions
    #[arg(long)]
    extensions: Option<String>,

    /// Run only a shard (zero-based): `i/n`
    #[arg(long)]
    shard: Option<String>,

    /// Emit JSON output in addition to the human summary
    #[arg(long)]
    json: bool,

    /// Update stored snapshots (placeholder)
    #[arg(long)]
    update_snapshots: bool,

    /// Comparison strategy (default: auto-detect)
    #[arg(long, value_enum, default_value_t = CompareArg::Auto)]
    compare: CompareArg,

    /// Path to the Node.js executable
    #[arg(long, default_value = "node")]
    node: std::path::PathBuf,

    /// Allowed byte tolerance when comparing spans
    #[arg(long, default_value_t = 0)]
    span_tolerance: u32,

    /// Timeout per test case
    #[arg(long, default_value_t = DEFAULT_TIMEOUT)]
    timeout_secs: u64,

    /// Enable tracing in the checker (passthrough)
    #[arg(long)]
    trace: bool,

    /// Enable profiling output (passthrough)
    #[arg(long)]
    profile: bool,

    /// Write the profile JSON output to this path (only used with --profile)
    #[arg(long, default_value = "typecheck_profile.json")]
    profile_out: std::path::PathBuf,

    /// Override the conformance root directory
    #[arg(long)]
    root: Option<std::path::PathBuf>,

    /// Allow non-matching results without failing the process
    #[arg(long)]
    allow_mismatches: bool,

    /// Allow missing/empty conformance suites without erroring
    #[arg(long, alias = "allow-missing-suite")]
    allow_empty: bool,

    /// Path to a manifest of expected failures/skips
    #[arg(long)]
    manifest: Option<std::path::PathBuf>,

    /// When to fail the run on mismatches
    #[arg(long, value_enum, default_value_t = FailOn::New)]
    fail_on: FailOn,

    /// Number of worker threads to use (defaults to CPU count)
    #[arg(long, default_value_t = num_cpus::get())]
    jobs: usize,
  },
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum CompareArg {
  Auto,
  None,
  Tsc,
  Snapshot,
}

impl From<CompareArg> for CompareMode {
  fn from(value: CompareArg) -> Self {
    match value {
      CompareArg::Auto => CompareMode::Auto,
      CompareArg::None => CompareMode::None,
      CompareArg::Tsc => CompareMode::Tsc,
      CompareArg::Snapshot => CompareMode::Snapshot,
    }
  }
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
      extensions,
      shard,
      json,
      update_snapshots,
      compare,
      node,
      span_tolerance,
      timeout_secs,
      trace,
      profile,
      profile_out,
      root,
      allow_mismatches,
      allow_empty,
      manifest,
      fail_on,
      jobs,
    } => {
      let filter_pattern = filter.clone();
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

      let extensions = match extensions {
        Some(raw) => raw
          .split(',')
          .map(|s| s.trim().to_string())
          .filter(|s| !s.is_empty())
          .collect(),
        None => typecheck_ts_harness::DEFAULT_EXTENSIONS
          .iter()
          .map(|s| s.to_string())
          .collect(),
      };

      let options = ConformanceOptions {
        root: root.unwrap_or_else(|| DEFAULT_ROOT.into()),
        filter,
        filter_pattern,
        shard,
        json,
        update_snapshots,
        timeout: Duration::from_secs(timeout_secs),
        trace,
        profile,
        profile_out,
        compare: compare.into(),
        node_path: node,
        span_tolerance,
        allow_mismatches,
        manifest,
        fail_on,
        extensions,
        allow_empty,
        jobs,
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
            let o = &report.summary.outcomes;
            println!(
              "Match: {}, Extra: {}, Missing: {}, Span mismatch: {}, Code mismatch: {}, Rust ICE: {}, tsc crashed: {}, Timeout: {}",
              o.match_,
              o.rust_extra_diagnostics,
              o.rust_missing_diagnostics,
              o.span_mismatch,
              o.code_mismatch,
              o.rust_ice,
              o.tsc_crashed,
              o.timeout
            );
            if let Some(m) = &report.summary.mismatches {
              println!(
                "Mismatches — expected: {}, unexpected: {}, flaky: {}",
                m.expected, m.unexpected, m.flaky
              );
            }
          }
          if !allow_mismatches
            && report
              .summary
              .should_fail(fail_on, report.summary.outcomes.mismatches())
          {
            ExitCode::from(1)
          } else {
            ExitCode::SUCCESS
          }
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
