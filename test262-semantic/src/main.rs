use anyhow::{bail, Context, Result};
use clap::{Args, Parser, Subcommand};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use walkdir::WalkDir;

mod report;
mod validate;

#[derive(Parser, Debug)]
#[command(version)]
struct Cli {
  #[command(subcommand)]
  command: Command,
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
    Command::Validate(args) => validate::run_cli(args),
    Command::Report(args) => match args.command {
      ReportCommand::Compare(args) => report::run_cli(args),
    },
    Command::List(args) => {
      let count = discover_test_count(&args.test262_dir)?;
      println!("{count}");
      Ok(ExitCode::SUCCESS)
    }
  }
}

#[derive(Args, Debug)]
struct ListArgs {
  /// Path to a local checkout of the tc39/test262 repository.
  #[arg(long, value_name = "DIR", default_value = "test262-semantic/data")]
  test262_dir: PathBuf,
}

fn discover_test_count(test262_dir: &Path) -> Result<usize> {
  if !test262_dir.exists() {
    bail!(
      "test262 corpus not found at {} (did you run `git submodule update --init test262-semantic/data`?)",
      test262_dir.display()
    );
  }

  let discovery_root = {
    let candidate = test262_dir.join("test");
    if candidate.is_dir() {
      candidate
    } else {
      test262_dir.to_path_buf()
    }
  };

  let mut count = 0usize;
  for entry in WalkDir::new(&discovery_root) {
    let entry = entry.context("walk test262 corpus")?;
    if !entry.file_type().is_file() {
      continue;
    }
    if entry.path().extension().and_then(|ext| ext.to_str()) != Some("js") {
      continue;
    }
    count += 1;
  }

  Ok(count)
}
