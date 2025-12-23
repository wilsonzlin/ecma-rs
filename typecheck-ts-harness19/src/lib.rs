use std::io;
use thiserror::Error;

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
  #[error("typecheck failed: {0}")]
  Typecheck(String),
  #[error("output failed: {0}")]
  Output(String),
}

pub use discover::build_filter;
pub use discover::discover_conformance_tests;
pub use discover::Filter;
pub use discover::Shard;
pub use discover::TestCase;
pub use multifile::split_test_file;
pub use multifile::VirtualFile;
pub use runner::run_conformance;
pub use runner::ConformanceOptions;
pub use runner::JsonReport;
pub use runner::TestResult;
pub use runner::TestStatus;
