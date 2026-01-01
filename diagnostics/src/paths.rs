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
  let raw = raw
    .strip_prefix(r"\\?\")
    .or_else(|| raw.strip_prefix("//?/"))
    .unwrap_or(raw);

  let bytes = raw.as_bytes();
  let mut start = 0;
  while start < bytes.len() && (bytes[start] == b'/' || bytes[start] == b'\\') {
    start += 1;
  }
  let mut rest = &raw[start..];

  // Extract an optional drive letter (e.g. c: or C:).
  let mut drive = None;
  if rest.len() >= 2 {
    let bytes = rest.as_bytes();
    if bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
      drive = Some(bytes[0].to_ascii_lowercase() as char);
      rest = &rest[2..];
      let bytes = rest.as_bytes();
      let mut start = 0;
      while start < bytes.len() && (bytes[start] == b'/' || bytes[start] == b'\\') {
        start += 1;
      }
      rest = &rest[start..];
    }
  }

  // Split on either slash flavor so we don't need to allocate a normalized intermediate.
  let mut components: Vec<&str> = Vec::new();
  let bytes = rest.as_bytes();
  let mut segment_start = 0;
  for idx in 0..=bytes.len() {
    if idx == bytes.len() || bytes[idx] == b'/' || bytes[idx] == b'\\' {
      let part = &rest[segment_start..idx];
      segment_start = idx + 1;
      if part.is_empty() || part == "." {
        continue;
      }
      if part == ".." {
        components.pop();
        continue;
      }
      components.push(part);
    }
  }

  let mut normalized = String::with_capacity(raw.len() + 1);
  if let Some(drive) = drive {
    normalized.push(drive);
    normalized.push(':');
    normalized.push('/');
  } else {
    // Treat bare relative inputs as rooted at `/` for determinism.
    normalized.push('/');
  }

  for (idx, part) in components.iter().enumerate() {
    if idx > 0 {
      normalized.push('/');
    }
    normalized.push_str(part);
  }

  normalized
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
