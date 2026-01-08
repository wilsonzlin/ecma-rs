use anyhow::Result;
use clap::{Parser, Subcommand};
use std::process::ExitCode;

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
  }
}

