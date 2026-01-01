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
  let mut out = String::with_capacity(raw.len() + 1);
  normalize_ts_path_into(raw, &mut out);
  out
}

/// Normalize a path-like string into a canonical, forward-slashed virtual path, writing the result
/// into an existing string buffer.
///
/// This is useful for hot paths that want to reuse an allocation across many normalization calls.
pub fn normalize_ts_path_into(raw: &str, normalized: &mut String) {
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

  // Build the normalized output directly, using the output buffer itself as the "stack" for `..`
  // segment popping. This avoids allocating a temporary `Vec<&str>` of components.
  normalized.clear();
  normalized.reserve(raw.len() + 1);
  if let Some(drive) = drive {
    normalized.push(drive);
    normalized.push(':');
    normalized.push('/');
  } else {
    // Treat bare relative inputs as rooted at `/` for determinism.
    normalized.push('/');
  }
  let root_len = normalized.len();

  // Split on either slash flavor so we don't need to allocate a normalized intermediate.
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
        if normalized.len() <= root_len {
          continue;
        }

        // Remove the last segment without escaping the root.
        let end = normalized.len();
        // If the current buffer ends with a slash (only happens at the root), skip it so we pop a
        // real segment boundary.
        let search_end = if end > root_len && normalized.ends_with('/') {
          end - 1
        } else {
          end
        };
        if search_end <= root_len {
          normalized.truncate(root_len);
          continue;
        }

        if let Some(pos) = normalized[..search_end].rfind('/') {
          if pos < root_len {
            normalized.truncate(root_len);
          } else {
            normalized.truncate(pos);
          }
        } else {
          normalized.truncate(root_len);
        }
        continue;
      }

      if !normalized.ends_with('/') {
        normalized.push('/');
      }
      normalized.push_str(part);
    }
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
