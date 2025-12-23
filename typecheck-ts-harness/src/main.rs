use clap::Parser;
use std::process::ExitCode;
use typecheck_ts_harness::difftsc::{self, CommandStatus, DifftscArgs};

#[derive(Parser)]
#[command(
  name = "typecheck-ts-harness",
  about = "TypeScript type-checking harness utilities"
)]
enum Cli {
  #[command(about = "Run differential tests against tsc diagnostics")]
  Difftsc(DifftscArgs),
}

fn main() -> ExitCode {
  let cli = Cli::parse();
  let status = match cli {
    Cli::Difftsc(args) => difftsc::run(args),
  };

  match status {
    Ok(CommandStatus::Success) | Ok(CommandStatus::Skipped) => ExitCode::SUCCESS,
    Err(err) => {
      eprintln!("{err:?}");
      ExitCode::from(1)
    }
  }
}
