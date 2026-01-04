use clap::Parser;
use clap::Subcommand;
use clap::ValueEnum;
use num_cpus;
use std::io::Read;
use std::io::Write;
use std::process::ExitCode;
use std::time::Duration;
use typecheck_ts_harness::build_filter;
use typecheck_ts_harness::difftsc::CommandStatus;
use typecheck_ts_harness::difftsc::DifftscArgs;
use typecheck_ts_harness::difftsc::{self};
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::triage;
use typecheck_ts_harness::CompareMode;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::FailOn;
use typecheck_ts_harness::Shard;

const DEFAULT_ROOT: &str = "parse-js/tests/TypeScript/tests/cases/conformance";
const DEFAULT_TIMEOUT: u64 = 10;

fn default_jobs() -> usize {
  // Keep defaults conservative to avoid excessive memory usage when many
  // independent programs are checked in parallel. Callers can override via
  // `--jobs`.
  num_cpus::get().min(4)
}

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

    /// Update stored snapshots (implies `--compare snapshot`)
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
    #[arg(long, default_value_t = default_jobs())]
    jobs: usize,
  },

  /// Summarize a conformance/difftsc JSON report into a triage report
  Triage {
    /// Path to a JSON report produced by `conformance --json` or `difftsc --json`
    #[arg(long)]
    input: std::path::PathBuf,

    /// Optional previous JSON report to diff against (regressions/fixes vs baseline)
    #[arg(long)]
    baseline: Option<std::path::PathBuf>,

    /// Emit a structured triage report JSON to stdout
    #[arg(long)]
    json: bool,

    /// Number of top groups/cases to include
    #[arg(long, default_value_t = triage::DEFAULT_TOP)]
    top: usize,
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
        None => Vec::new(),
      };

      let root_dir = root.unwrap_or_else(|| DEFAULT_ROOT.into());
      let mut options = ConformanceOptions::new(root_dir);
      options.filter = filter;
      options.filter_pattern = filter_pattern;
      options.shard = shard;
      options.json = json;
      options.update_snapshots = update_snapshots;
      options.timeout = Duration::from_secs(timeout_secs);
      options.trace = trace;
      options.profile = profile;
      options.profile_out = profile_out;
      options.compare = compare.into();
      options.node_path = node;
      options.span_tolerance = span_tolerance;
      options.allow_mismatches = allow_mismatches;
      options.manifest = manifest;
      options.fail_on = fail_on;
      options.extensions = extensions;
      options.allow_empty = allow_empty;
      options.jobs = jobs;

      match run_conformance(options) {
        Ok(report) => {
          if json {
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            if let Err(err) = serde_json::to_writer_pretty(&mut handle, &report) {
              return print_error(err);
            }
            if let Err(err) = writeln!(&mut handle) {
              return print_error(err);
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
    Commands::Triage {
      input,
      baseline,
      json,
      top,
    } => {
      let input_raw = if input.as_os_str() == "-" {
        let mut raw = String::new();
        if let Err(err) = std::io::stdin().read_to_string(&mut raw) {
          return print_error(err);
        }
        raw
      } else {
        match std::fs::read_to_string(&input) {
          Ok(raw) => raw,
          Err(err) => return print_error(err),
        }
      };

      let baseline_raw = match baseline.as_deref() {
        Some(path) if path.as_os_str() == "-" => {
          if input.as_os_str() == "-" {
            return print_error("triage: cannot read both --input - and --baseline - from stdin");
          }
          let mut raw = String::new();
          if let Err(err) = std::io::stdin().read_to_string(&mut raw) {
            return print_error(err);
          }
          Some(raw)
        }
        Some(path) => match std::fs::read_to_string(path) {
          Ok(raw) => Some(raw),
          Err(err) => return print_error(err),
        },
        None => None,
      };

      let report = match triage::analyze_report_json_strs(&input_raw, baseline_raw.as_deref(), top)
      {
        Ok(report) => report,
        Err(err) => return print_error(err),
      };

      let stderr = std::io::stderr();
      let mut stderr_handle = stderr.lock();
      if let Err(err) = triage::print_human_summary(&report, &mut stderr_handle) {
        return print_error(err);
      }

      if json {
        let stdout = std::io::stdout();
        let mut handle = stdout.lock();
        if let Err(err) = serde_json::to_writer_pretty(&mut handle, &report) {
          return print_error(err);
        }
        if let Err(err) = writeln!(&mut handle) {
          return print_error(err);
        }
      }

      ExitCode::SUCCESS
    }
  }
}

fn print_error(err: impl std::fmt::Display) -> ExitCode {
  eprintln!("error: {err}");
  ExitCode::from(1)
}
