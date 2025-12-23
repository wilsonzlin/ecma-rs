use clap::Parser;
use clap::Subcommand;
use std::path::PathBuf;
use tracing_subscriber::fmt;
use tracing_subscriber::EnvFilter;
use typecheck_ts_harness_trace23::run_conformance;
use typecheck_ts_harness_trace23::HarnessConfig;

#[derive(Parser, Debug)]
#[command(author, version, about = "TypeScript checker harness", long_about = None)]
struct Args {
  /// Enable pretty tracing output to stderr.
  #[arg(long, global = true)]
  trace: bool,

  /// Write JSON profile output to the given path (default: profile.json).
  #[arg(
        long,
        global = true,
        value_name = "PATH",
        num_args = 0..=1,
        default_missing_value = "profile.json"
    )]
  profile: Option<PathBuf>,

  #[command(subcommand)]
  command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
  /// Run a small conformance sweep.
  Conformance {
    /// Restrict fixtures to those containing the given string.
    #[arg(long)]
    filter: Option<String>,
  },
}

fn install_subscriber(trace: bool) {
  if !trace {
    return;
  }

  let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
  fmt().with_env_filter(filter).pretty().init();
}

fn main() {
  let args = Args::parse();
  install_subscriber(args.trace);

  let Command::Conformance { filter } = args.command;

  let config = HarnessConfig {
    trace: args.trace,
    profile: args.profile,
    filter,
  };

  if let Err(err) = run_conformance(config) {
    eprintln!("error: {err}");
    std::process::exit(1);
  }
}
