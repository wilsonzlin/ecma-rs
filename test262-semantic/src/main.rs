use anyhow::Result;
use clap::{Args, Parser, Subcommand};
use std::process::ExitCode;

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
  }
}
