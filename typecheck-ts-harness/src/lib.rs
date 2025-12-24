use std::io;
use thiserror::Error;

pub mod difftsc;
pub mod directives;
pub mod discover;
pub mod multifile;
pub mod runner;

pub type Result<T> = std::result::Result<T, HarnessError>;

#[derive(Debug, Error)]
pub enum HarnessError {
  #[error(transparent)]
  Io(#[from] io::Error),
  #[error("invalid shard specification '{0}'")]
  InvalidShard(String),
  #[error("invalid filter '{0}'")]
  InvalidFilter(String),
  #[error("invalid extensions list '{0}'")]
  InvalidExtensions(String),
  #[error("typecheck failed: {0}")]
  Typecheck(String),
  #[error("output failed: {0}")]
  Output(String),
  #[error(
    "no conformance tests discovered under '{root}' (extensions: {extensions}); ensure the TypeScript suite is present or pass --allow-empty"
  )]
  EmptySuite { root: String, extensions: String },
}

pub use directives::HarnessDirective;
pub use directives::HarnessOptions;
pub use discover::build_filter;
pub use discover::discover_conformance_tests;
pub use discover::Filter;
pub use discover::Shard;
pub use discover::TestCase;
pub use discover::DEFAULT_EXTENSIONS;
pub use multifile::split_test_file;
pub use multifile::VirtualFile;
pub use runner::run_conformance;
pub use runner::ConformanceOptions;
pub use runner::JsonReport;
pub use runner::TestResult;
pub use runner::TestStatus;
