use anyhow::{bail, Context, Result};
use clap::{Args, Parser, Subcommand};
use conformance_harness::{FailOn, Expectations, Shard, TimeoutManager};
use std::collections::BTreeSet;
use std::fs;
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;
use test262_semantic::discover::discover_tests;
use test262_semantic::executor::default_executor;
use test262_semantic::report;
use test262_semantic::runner::{apply_shard, build_filter, expand_cases, run_cases, summarize};
use test262_semantic::suite::{load_builtin_suite, load_suite_from_path, select_tests};

mod validate;

const DEFAULT_TEST262_DIR: &str = "test262-semantic/data";

fn default_jobs() -> usize {
  // Keep defaults conservative to avoid runaway memory usage when/if parallel
  // execution is enabled.
  std::thread::available_parallelism()
    .map(|count| count.get())
    .unwrap_or(1)
    .min(4)
}

#[derive(Parser, Debug)]
#[command(version, about = "Run a curated subset of tc39/test262 language semantics tests")]
struct Cli {
  #[command(subcommand)]
  command: Option<Command>,

  #[command(flatten)]
  run: RunArgs,
}

#[derive(Subcommand, Debug)]
enum Command {
  /// Validate suite and expectation manifest files against the discovered test262 corpus.
  Validate(validate::ValidateArgs),

  /// Work with JSON report artifacts.
  Report(ReportArgs),

  /// Discover tests in the test262 corpus and print how many were found.
  List(ListArgs),
}

#[derive(Args, Debug)]
struct ReportArgs {
  #[command(subcommand)]
  command: ReportCommand,
}

#[derive(Subcommand, Debug)]
enum ReportCommand {
  /// Compare two JSON reports (baseline vs current).
  Compare(report::CompareArgs),
}

#[derive(Args, Debug)]
struct ListArgs {
  /// Path to a local checkout of the tc39/test262 repository.
  #[arg(long, value_name = "DIR", default_value = DEFAULT_TEST262_DIR)]
  test262_dir: PathBuf,
}

#[derive(Args, Debug)]
struct RunArgs {
  /// Path to a local checkout of the tc39/test262 repository.
  #[arg(long, value_name = "PATH", default_value = DEFAULT_TEST262_DIR)]
  test262_dir: PathBuf,

  /// Built-in curated suite name (e.g. `smoke`); can be passed multiple times.
  #[arg(long, value_name = "NAME")]
  suite: Vec<String>,

  /// Path to a suite file (TOML/JSON); can be passed multiple times.
  #[arg(long, value_name = "PATH")]
  suite_path: Vec<PathBuf>,

  /// Optional manifest describing expected failures or skips.
  #[arg(long)]
  manifest: Option<PathBuf>,

  /// Run only the given shard (format: <index>/<total>).
  #[arg(long)]
  shard: Option<Shard>,

  /// Timeout in seconds for each test case (best-effort cooperative cancellation).
  #[arg(long, default_value_t = 10)]
  timeout_secs: u64,

  /// Number of worker threads to use (reserved for future parallel execution).
  #[arg(long, default_value_t = default_jobs())]
  jobs: usize,

  /// Emit JSON to stdout.
  #[arg(long)]
  json: bool,

  /// Also write the JSON report to the given path.
  #[arg(long, value_name = "PATH")]
  report_path: Option<PathBuf>,

  /// Control which mismatches cause a non-zero exit code.
  #[arg(long, default_value_t = FailOn::New, value_enum)]
  fail_on: FailOn,

  /// Glob or regex to filter tests by id (after suite selection).
  #[arg(long)]
  filter: Option<String>,
}

fn main() -> ExitCode {
  match try_main() {
    Ok(code) => code,
    Err(err) => {
      eprintln!("{err}");
      ExitCode::FAILURE
    }
  }
}

fn try_main() -> Result<ExitCode> {
  let cli = Cli::parse();
  match cli.command {
    Some(Command::Validate(args)) => validate::run_cli(args),
    Some(Command::Report(args)) => match args.command {
      ReportCommand::Compare(args) => report::run_cli(args),
    },
    Some(Command::List(args)) => {
      let tests = discover_tests(&args.test262_dir)?;
      println!("{}", tests.len());
      Ok(ExitCode::SUCCESS)
    }
    None => run_cli(cli.run),
  }
}

fn run_cli(cli: RunArgs) -> Result<ExitCode> {
  let _ = cli.jobs;

  let expectations = match &cli.manifest {
    Some(path) => Expectations::from_path(path)?,
    None => Expectations::empty(),
  };

  let discovered = discover_tests(&cli.test262_dir)?;
  let selected = select_tests_from_cli(&discovered, &cli)?;
  let filter = build_filter(cli.filter.as_deref())?;

  let mut cases = expand_cases(&selected, &filter)?;
  let total_cases = cases.len();
  cases = apply_shard(cases, cli.shard)?;

  if let Some(shard) = cli.shard {
    eprintln!(
      "Running shard {}/{}: {} of {} cases",
      shard.index + 1,
      shard.total,
      cases.len(),
      total_cases
    );
  }

  let timeout_manager = TimeoutManager::new();
  let timeout = Duration::from_secs(cli.timeout_secs);
  let executor = default_executor();

  let mut results = run_cases(
    &cli.test262_dir,
    &cases,
    &expectations,
    executor.as_ref(),
    timeout,
    &timeout_manager,
  );
  results.sort_by(|a, b| a.id.cmp(&b.id).then_with(|| a.variant.cmp(&b.variant)));

  let summary = summarize(&results);
  let report_json = test262_semantic::report::Report {
    schema_version: test262_semantic::report::REPORT_SCHEMA_VERSION,
    summary: summary.clone(),
    results,
  };

  if let Some(path) = &cli.report_path {
    write_report(path, &report_json)?;
    eprintln!("Wrote test262 semantic report to {}", path.display());
  }

  if cli.json {
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    serde_json::to_writer_pretty(&mut handle, &report_json).context("write JSON report to stdout")?;
    writeln!(handle).ok();
  } else {
    print_human_summary(&summary);
  }

  Ok(if summary.should_fail(cli.fail_on) {
    ExitCode::FAILURE
  } else {
    ExitCode::SUCCESS
  })
}

fn write_report(path: &std::path::Path, report: &test262_semantic::report::Report) -> Result<()> {
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
  }

  let file = fs::File::create(path).with_context(|| format!("create {}", path.display()))?;
  let mut writer = BufWriter::new(file);
  serde_json::to_writer_pretty(&mut writer, report)
    .with_context(|| format!("write report to {}", path.display()))?;
  writer.flush().ok();
  Ok(())
}

fn print_human_summary(summary: &test262_semantic::report::Summary) {
  println!(
    "test262 semantic: total={}, passed={}, failed={}, timed_out={}, skipped={}",
    summary.total, summary.passed, summary.failed, summary.timed_out, summary.skipped
  );
  if let Some(mismatches) = &summary.mismatches {
    println!(
      "mismatches: unexpected={}, expected={}, flaky={}",
      mismatches.unexpected, mismatches.expected, mismatches.flaky
    );
  }
}

fn select_tests_from_cli(
  discovered: &[test262_semantic::discover::DiscoveredTest],
  cli: &RunArgs,
) -> Result<Vec<test262_semantic::discover::DiscoveredTest>> {
  if cli.suite.is_empty() && cli.suite_path.is_empty() {
    return Ok(discovered.to_vec());
  }

  let mut ids = BTreeSet::new();
  for name in &cli.suite {
    let suite = load_builtin_suite(name)?;
    for id in select_tests(&suite, discovered)? {
      ids.insert(id);
    }
  }
  for path in &cli.suite_path {
    let suite = load_suite_from_path(path)?;
    for id in select_tests(&suite, discovered)? {
      ids.insert(id);
    }
  }

  if ids.is_empty() {
    bail!("suite selection produced zero test ids");
  }

  let ids: Vec<String> = ids.into_iter().collect();
  test262_semantic::runner::select_by_ids(discovered, &ids)
}

