//! Deterministic path normalisation utilities shared across hosts.
//!
//! This delegates to the shared `diagnostics::paths` helpers so the CLI,
//! harness, and internal resolve module all agree on canonicalisation rules.

use diagnostics::paths::normalize_ts_path;
use std::path::{Path, PathBuf};

/// Canonicalise a path to an absolute path on disk.
pub fn canonicalize_path(path: &Path) -> std::io::Result<PathBuf> {
  let absolute = if path.is_absolute() {
    path.to_path_buf()
  } else {
    std::env::current_dir()?.join(path)
  };
  absolute.canonicalize()
}

/// Normalise an OS path into a deterministic, POSIX-like string representation.
pub fn normalize_path(path: &Path) -> String {
  normalize_path_str(&path.to_string_lossy())
}

/// Normalise a path string into a deterministic, POSIX-like representation.
pub fn normalize_path_str(name: &str) -> String {
  normalize_ts_path(name)
}
