use std::path::{Path, PathBuf};

use diagnostics::paths::normalize_ts_path;
use typecheck_ts::resolve::{ResolveFs, ResolveOptions, Resolver};
use typecheck_ts::FileKey;

use crate::runner::HarnessFileSet;

fn starts_with_drive_letter(path: &str) -> bool {
  let bytes = path.as_bytes();
  bytes.len() >= 3
    && bytes[0].is_ascii_alphabetic()
    && bytes[1] == b':'
    && (bytes[2] == b'/' || bytes[2] == b'\\')
}

fn looks_like_source_path(specifier: &str) -> bool {
  // `/// <reference path="a.ts" />` style specifiers are relative paths but do
  // not require a leading `./`.
  const SUFFIXES: &[&str] = &[
    ".ts", ".tsx", ".d.ts", ".mts", ".d.mts", ".cts", ".d.cts", ".js", ".jsx", ".mjs", ".cjs",
  ];
  SUFFIXES.iter().any(|suffix| specifier.ends_with(suffix))
}

#[derive(Clone)]
struct HarnessResolveFs {
  files: HarnessFileSet,
}

impl ResolveFs for HarnessResolveFs {
  fn is_file(&self, path: &Path) -> bool {
    let normalized = normalize_ts_path(&path.to_string_lossy());
    self.files.resolve_ref(&normalized).is_some()
  }

  fn is_dir(&self, _path: &Path) -> bool {
    // The resolver doesn't currently consult directories; keep this conservative.
    false
  }

  fn canonicalize(&self, path: &Path) -> Option<PathBuf> {
    Some(PathBuf::from(normalize_ts_path(&path.to_string_lossy())))
  }

  fn read_to_string(&self, path: &Path) -> Option<String> {
    let normalized = normalize_ts_path(&path.to_string_lossy());
    let key = self.files.resolve_ref(&normalized)?;
    self.files.content(key).map(|content| content.to_string())
  }
}

pub(crate) fn resolve_module_specifier(
  files: &HarnessFileSet,
  from: &FileKey,
  specifier: &str,
) -> Option<FileKey> {
  if specifier.starts_with('/') || specifier.starts_with('\\') || specifier.starts_with("./") {
    // `typecheck_ts::resolve` already handles absolute/relative specifiers.
  } else if !specifier.starts_with("../")
    && !specifier.starts_with('#')
    && !specifier.contains('/')
    && !specifier.contains('\\')
    && (specifier.ends_with(".ts")
      || specifier.ends_with(".tsx")
      || specifier.ends_with(".d.ts")
      || specifier.ends_with(".mts")
      || specifier.ends_with(".d.mts")
      || specifier.ends_with(".cts")
      || specifier.ends_with(".d.cts")
      || specifier.ends_with(".js")
      || specifier.ends_with(".jsx")
      || specifier.ends_with(".mjs")
      || specifier.ends_with(".cjs"))
  {
    let parent = Path::new(from.as_str())
      .parent()
      .unwrap_or_else(|| Path::new("/"));
    let candidate = normalize_ts_path(&parent.join(specifier).to_string_lossy());
    if let Some(found) = files.resolve(&candidate) {
      return Some(found);
    }
  }

  let fs = HarnessResolveFs {
    files: files.clone(),
  };
  let resolver = Resolver::with_fs(
    fs,
    ResolveOptions {
      node_modules: true,
      package_imports: true,
    },
  );
  let from_path = Path::new(from.as_str());
  let mut resolved = resolver.resolve(from_path, specifier);
  if resolved.is_none()
    && !specifier.starts_with("./")
    && !specifier.starts_with("../")
    && !specifier.starts_with('#')
    && !specifier.starts_with('/')
    && !specifier.starts_with('\\')
    && !starts_with_drive_letter(specifier)
    && looks_like_source_path(specifier)
  {
    let mut prefixed = String::with_capacity(2 + specifier.len());
    prefixed.push_str("./");
    prefixed.push_str(specifier);
    resolved = resolver.resolve(from_path, &prefixed);
  }
  let resolved = resolved?;
  let resolved = normalize_ts_path(&resolved.to_string_lossy());
  files.resolve(&resolved)
}
