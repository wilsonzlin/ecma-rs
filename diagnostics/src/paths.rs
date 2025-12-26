//! Path normalization helpers shared across tooling.
//!
//! The goal is to produce deterministic, TypeScript-style virtual paths that are
//! stable across platforms and match how the harness/CLI present file names in
//! diagnostics. The rules mirror `ts.normalizePath`:
//! - backslashes are replaced with `/`
//! - `.` segments are removed, `..` pops a segment without escaping the root
//! - drive letters are lowercased (`C:\foo` -> `c:/foo`)
//! - relative inputs are treated as rooted at `/` for deterministic comparison
//!
//! On case-insensitive platforms (Windows), only the drive letter is
//! canonicalized; the rest of the path is left as-is so case-sensitive hosts can
//! still distinguish distinct files when necessary.
use std::path::Path;

/// Normalize a path-like string into a canonical, forward-slashed virtual path.
pub fn normalize_ts_path(raw: &str) -> String {
  let mut path = raw.replace('\\', "/");
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

/// Convenience wrapper for normalizing OS paths into virtual paths.
pub fn normalize_fs_path(path: &Path) -> String {
  normalize_ts_path(&path.to_string_lossy())
}

#[cfg(test)]
mod tests {
  use super::normalize_ts_path;

  #[test]
  fn normalizes_relative_and_rooted_paths() {
    assert_eq!(normalize_ts_path("src/./lib/../main.ts"), "/src/main.ts");
    assert_eq!(normalize_ts_path("/src///./main.ts"), "/src/main.ts");
  }

  #[test]
  fn normalizes_windows_drives_and_backslashes() {
    assert_eq!(
      normalize_ts_path("C:\\Users\\Test\\..\\Project\\file.ts"),
      "c:/Users/Project/file.ts"
    );
    assert_eq!(
      normalize_ts_path("/D:/Folder/./sub\\file.ts"),
      "d:/Folder/sub/file.ts"
    );
  }

  #[test]
  fn collapses_to_root_when_empty() {
    assert_eq!(normalize_ts_path(".."), "/");
    assert_eq!(normalize_ts_path("././"), "/");
  }

  #[test]
  fn strips_windows_extended_prefix() {
    assert_eq!(normalize_ts_path(r"\\?\C:\foo\bar.ts"), "c:/foo/bar.ts");
  }
}
