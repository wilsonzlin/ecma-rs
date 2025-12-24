use clap::Parser;
use clap::Subcommand;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;
use tracing_subscriber::fmt;
use tracing_subscriber::EnvFilter;
use typecheck_ts_harness::build_filter;
use typecheck_ts_harness::difftsc::CommandStatus;
use typecheck_ts_harness::difftsc::DifftscArgs;
use typecheck_ts_harness::difftsc::{self};
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::run_single_conformance;
use typecheck_ts_harness::CompareMode;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::HarnessError;
use typecheck_ts_harness::Isolation;
use typecheck_ts_harness::Shard;
use typecheck_ts_harness::SingleTestOptions;
use typecheck_ts_harness::DEFAULT_EXTENSIONS;
use typecheck_ts_harness::DEFAULT_PROFILE_OUT;

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

    /// Enable tracing output from the harness
    #[arg(long)]
    trace: bool,

    /// Enable profiling output
    #[arg(long)]
    profile: bool,

    /// Path to write profiling data to (used with --profile)
    #[arg(long, value_name = "PATH", default_value = DEFAULT_PROFILE_OUT)]
    profile_out: PathBuf,

    /// Override the conformance root directory
    #[arg(long)]
    root: Option<PathBuf>,

    /// Comma-separated list of extensions to include (default: ts,tsx,d.ts)
    #[arg(long)]
    extensions: Option<String>,

    /// Allow running with zero discovered tests
    #[arg(long)]
    allow_empty: bool,

    /// Maximum number of child processes to run concurrently
    #[arg(long, default_value_t = default_jobs())]
    jobs: usize,

    /// Isolation strategy for individual tests
    #[arg(long, value_enum)]
    isolate: Option<Isolation>,

    /// Run only a single test id and emit a single TestResult JSON line
    #[arg(long)]
    single: Option<String>,

    /// Comparison strategy (placeholder)
    #[arg(long, value_enum, default_value_t = CompareMode::None)]
    compare: CompareMode,
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
      profile_out,
      root,
      extensions,
      allow_empty,
      jobs,
      isolate,
      compare,
      single,
    } => {
      init_tracing(trace);

      let raw_filter = filter.clone();
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

      let isolate = isolate.unwrap_or_else(|| {
        if timeout_secs > 0 || jobs > 1 {
          Isolation::Process
        } else {
          Isolation::None
        }
      });

      if let Some(id) = single {
        let options = SingleTestOptions {
          root: root.clone().unwrap_or_else(|| DEFAULT_ROOT.into()),
          id,
          timeout: Duration::from_secs(timeout_secs),
          trace,
          profile,
          profile_out,
          compare,
        };

        match run_single_conformance(options) {
          Ok(result) => match serde_json::to_string(&result) {
            Ok(output) => {
              println!("{output}");
              ExitCode::SUCCESS
            }
            Err(err) => print_error(err),
          },
          Err(err) => print_error(err),
        }
      } else {
        let options = ConformanceOptions {
          root: root.unwrap_or_else(|| DEFAULT_ROOT.into()),
          filter,
          filter_pattern: raw_filter,
          shard,
          json,
          update_snapshots,
          timeout: Duration::from_secs(timeout_secs),
          trace,
          profile,
          profile_out,
          extensions,
          allow_empty,
          jobs,
          isolate,
          compare,
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
}

fn print_error(err: impl std::fmt::Display) -> ExitCode {
  eprintln!("error: {err}");
  ExitCode::from(1)
}

fn init_tracing(enable: bool) {
  if !enable {
    return;
  }

  let env_filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
  let builder = fmt()
    .with_env_filter(env_filter)
    .with_writer(std::io::stderr);
  if let Err(err) = builder.try_init() {
    eprintln!("failed to install tracing subscriber: {err}");
  }
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

fn default_jobs() -> usize {
  num_cpus::get().max(1)
}
