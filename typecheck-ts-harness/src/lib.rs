use std::io;
use std::path::Path;
use thiserror::Error;

pub mod diagnostic_norm;
pub mod difftsc;
pub mod directives;
pub mod discover;
pub mod expectations;
mod file_kind;
pub mod multifile;
pub mod profile;
mod resolve;
pub mod runner;
mod serde_helpers;
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
    "no conformance tests discovered under '{root}' (extensions: {extensions}); ensure the TypeScript suite is checked out (git submodule update --init --recursive parse-js/tests/TypeScript), use --root to point at another suite, or pass --allow-empty to bypass this check"
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
pub use runner::TestOptions;
pub use runner::TestOutcome;
pub use runner::TestResult;

/// Read a UTF-8 file from disk, returning a friendly error if the contents are
/// not valid UTF-8.
pub(crate) fn read_utf8_file(path: &Path) -> std::io::Result<String> {
  let raw = std::fs::read(path)?;
  String::from_utf8(raw).map_err(|err| {
    io::Error::new(
      io::ErrorKind::InvalidData,
      format!("{} is not valid UTF-8: {err}", path.display()),
    )
  })
}
