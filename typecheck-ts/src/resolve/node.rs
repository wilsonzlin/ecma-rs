//! Node/TypeScript-style module resolution.
//!
//! This intentionally mirrors the resolution behaviour advertised by the CLI:
//! - relative specifiers resolve against the importing file
//! - `<spec>.{ts,d.ts,tsx,js,jsx}` and `index.*` variants are considered
//! - when `node_modules` is enabled, bare specifiers walk up parent directories

use std::path::{Path, PathBuf};

use crate::resolve::path::canonicalize_path;

/// Default extension search order for module resolution.
pub const DEFAULT_EXTENSIONS: &[&str] = &["ts", "d.ts", "tsx", "js", "jsx"];

/// Options controlling module resolution behaviour.
#[derive(Clone, Copy, Debug, Default)]
pub struct ResolveOptions {
  /// Whether to walk `node_modules/` when resolving bare specifiers.
  pub node_modules: bool,
}

/// Filesystem abstraction for resolution to allow testing and non-disk hosts.
pub trait ResolveFs: Clone {
  /// Return true if the path points to a file.
  fn is_file(&self, path: &Path) -> bool;
  /// Return true if the path points to a directory.
  fn is_dir(&self, path: &Path) -> bool;
  /// Canonicalise a path into an absolute, platform path.
  fn canonicalize(&self, path: &Path) -> Option<PathBuf>;
}

/// Real filesystem adapter used by the CLI.
#[derive(Clone, Debug, Default)]
pub struct RealFs;

impl ResolveFs for RealFs {
  fn is_file(&self, path: &Path) -> bool {
    std::fs::metadata(path)
      .map(|m| m.is_file())
      .unwrap_or(false)
  }

  fn is_dir(&self, path: &Path) -> bool {
    std::fs::metadata(path).map(|m| m.is_dir()).unwrap_or(false)
  }

  fn canonicalize(&self, path: &Path) -> Option<PathBuf> {
    canonicalize_path(path).ok()
  }
}

/// Deterministic Node/TS resolver.
#[derive(Clone, Debug)]
pub struct NodeResolver<F = RealFs> {
  fs: F,
  options: ResolveOptions,
}

impl NodeResolver<RealFs> {
  /// Construct a resolver that reads from disk.
  pub fn new(options: ResolveOptions) -> Self {
    NodeResolver {
      fs: RealFs,
      options,
    }
  }
}

impl<F: ResolveFs> NodeResolver<F> {
  /// Construct a resolver with a custom filesystem implementation.
  pub fn with_fs(fs: F, options: ResolveOptions) -> Self {
    NodeResolver { fs, options }
  }

  /// Resolve a module specifier relative to `from`.
  pub fn resolve(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    if is_relative_or_absolute(specifier) {
      return self.resolve_relative(from, specifier);
    }

    if !self.options.node_modules {
      return None;
    }

    self.resolve_node_modules(from, specifier)
  }

  fn resolve_relative(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    let base_dir = from.parent().unwrap_or_else(|| Path::new(""));
    let joined = base_dir.join(specifier);
    self.resolve_with_candidates(&joined)
  }

  fn resolve_node_modules(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    let mut current = from.parent();
    while let Some(dir) = current {
      let candidate = dir.join("node_modules").join(specifier);
      if let Some(found) = self.resolve_with_candidates(&candidate) {
        return Some(found);
      }
      current = dir.parent();
    }

    None
  }

  fn resolve_with_candidates(&self, base: &Path) -> Option<PathBuf> {
    let has_extension = has_known_extension(base);
    let base_is_dir = self.fs.is_dir(base);
    let mut candidates = Vec::new();

    if has_extension {
      candidates.push(base.to_path_buf());
    } else {
      for ext in DEFAULT_EXTENSIONS {
        candidates.push(with_extension(base, ext));
      }
    }

    if !has_extension || base_is_dir {
      for ext in DEFAULT_EXTENSIONS {
        candidates.push(base.join("index").with_extension(ext));
      }
    }

    for candidate in candidates {
      if self.fs.is_file(&candidate) {
        if let Some(canonical) = self.fs.canonicalize(&candidate) {
          return Some(canonical);
        }
      }
    }

    None
  }
}

fn is_relative_or_absolute(specifier: &str) -> bool {
  specifier.starts_with("./") || specifier.starts_with("../") || Path::new(specifier).is_absolute()
}

fn has_known_extension(path: &Path) -> bool {
  let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
  name.ends_with(".d.ts")
    || matches!(
      path.extension().and_then(|e| e.to_str()),
      Some("ts" | "tsx" | "js" | "jsx")
    )
}

fn with_extension(base: &Path, ext: &str) -> PathBuf {
  if ext == "d.ts" {
    let mut path = base.to_path_buf();
    let current_ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
    if current_ext == "ts" || current_ext == "tsx" || current_ext == "js" || current_ext == "jsx" {
      path.set_extension("d.ts");
      return path;
    }
    path.with_extension("d.ts")
  } else {
    base.with_extension(ext)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::BTreeSet;

  #[derive(Clone, Default)]
  struct FakeFs {
    files: BTreeSet<PathBuf>,
  }

  impl FakeFs {
    fn new(paths: &[&str]) -> Self {
      let mut fs = FakeFs::default();
      for path in paths {
        fs.files.insert(PathBuf::from(path));
      }
      fs
    }
  }

  impl ResolveFs for FakeFs {
    fn is_file(&self, path: &Path) -> bool {
      self.files.contains(path)
    }

    fn is_dir(&self, path: &Path) -> bool {
      self
        .files
        .iter()
        .any(|p| p.parent().map(|parent| parent == path).unwrap_or(false))
    }

    fn canonicalize(&self, path: &Path) -> Option<PathBuf> {
      Some(path.to_path_buf())
    }
  }

  #[test]
  fn prefers_ts_before_dts() {
    let fs = FakeFs::new(&["/project/dep.d.ts", "/project/dep.ts"]);
    let resolver = NodeResolver::with_fs(fs, ResolveOptions::default());
    let resolved = resolver
      .resolve(Path::new("/project/main.ts"), "./dep")
      .expect("dep should resolve");
    assert_eq!(resolved, PathBuf::from("/project/dep.ts"));
  }

  #[test]
  fn resolves_index_inside_directory() {
    let fs = FakeFs::new(&["/project/nested/index.ts"]);
    let resolver = NodeResolver::with_fs(fs, ResolveOptions::default());
    let resolved = resolver
      .resolve(Path::new("/project/main.ts"), "./nested")
      .expect("index.ts should resolve");
    assert_eq!(resolved, PathBuf::from("/project/nested/index.ts"));
  }

  #[test]
  fn climbs_node_modules_when_enabled() {
    let fs = FakeFs::new(&["/project/node_modules/pkg/index.ts"]);
    let with_node = NodeResolver::with_fs(fs.clone(), ResolveOptions { node_modules: true });
    let resolved = with_node
      .resolve(Path::new("/project/src/main.ts"), "pkg")
      .expect("pkg should resolve from node_modules");
    assert_eq!(
      resolved,
      PathBuf::from("/project/node_modules/pkg/index.ts")
    );

    let without_node = NodeResolver::with_fs(fs, ResolveOptions::default());
    assert!(without_node
      .resolve(Path::new("/project/src/main.ts"), "pkg")
      .is_none());
  }
}
