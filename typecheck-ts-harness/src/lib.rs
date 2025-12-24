use std::io;
use thiserror::Error;

pub mod diagnostic;
pub mod diagnostic_norm;
pub mod difftsc;
pub mod directives;
pub mod discover;
pub mod expectations;
pub mod multifile;
pub mod profile;
pub mod runner;
pub mod tsc;

pub const DEFAULT_PROFILE_OUT: &str = "typecheck_profile.json";

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
  #[error("snapshot error: {0}")]
  Snapshot(String),
  #[error("manifest error: {0}")]
  Manifest(String),
}

pub use directives::HarnessDirective;
pub use directives::HarnessOptions;
pub use discover::build_filter;
pub use discover::discover_conformance_tests;
pub use discover::load_conformance_test;
pub use discover::Filter;
pub use discover::Shard;
pub use discover::TestCase;
pub use discover::DEFAULT_EXTENSIONS;
pub use expectations::Expectations;
pub use expectations::FailOn;
pub use multifile::split_test_file;
pub use multifile::VirtualFile;
pub use runner::run_conformance;
pub use runner::CompareMode;
pub use runner::ConformanceOptions;
pub use runner::ConformanceReport;
pub use runner::JsonReport;
pub use runner::OutcomeCounts;
pub use runner::Summary;
pub use runner::TestOutcome;
pub use runner::TestResult;
