//! Deterministic path normalisation utilities shared across hosts.
//!
//! This mirrors the `typecheck-ts-harness` path canonicalisation to keep file
//! names stable across platforms (including Windows) for diagnostics and
//! snapshots.

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
///
/// - Backslashes become `/`
/// - `.` segments are removed, `..` pops a segment
/// - Paths are rooted at `/` unless a drive letter prefix is present
/// - Drive letters are normalised to lowercase (`C:\foo` → `c:/foo`)
pub fn normalize_path(path: &Path) -> String {
  normalize_path_str(&path.to_string_lossy())
}

/// Normalise a path string into a deterministic, POSIX-like representation.
pub fn normalize_path_str(name: &str) -> String {
  let mut path = name.replace('\\', "/");
  if let Some(stripped) = path.strip_prefix("//?/") {
    path = stripped.to_string();
  }
  let mut rooted = path.starts_with('/');
  let mut rest = path.trim_start_matches('/');

  // Extract an optional drive letter (e.g. c: or C:).
  let mut drive = None;
  if rest.len() >= 2 {
    let bytes = rest.as_bytes();
    if bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
      let mut prefix = rest[..2].to_string();
      prefix.make_ascii_lowercase();
      drive = Some(prefix);
      rest = &rest[2..];
      rest = rest.trim_start_matches('/');
      rooted = true;
    }
  }

  // Treat bare relative inputs as rooted at `/` for determinism.
  if !rooted {
    rooted = true;
  }

  let mut components = Vec::new();
  for part in rest.split('/') {
    if part.is_empty() || part == "." {
      continue;
    }
    if part == ".." {
      components.pop();
      continue;
    }
    components.push(part);
  }

  let mut normalized = String::new();
  if let Some(drive) = drive {
    normalized.push_str(&drive);
    normalized.push('/');
  } else if rooted {
    normalized.push('/');
  }

  normalized.push_str(&components.join("/"));

  if normalized.is_empty() {
    "/".to_string()
  } else {
    normalized
  }
}
