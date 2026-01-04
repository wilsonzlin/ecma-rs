use std::path::{Path, PathBuf};

use diagnostics::paths::normalize_ts_path;
use typecheck_ts::resolve::{ResolveFs, ResolveOptions, Resolver};
use typecheck_ts::FileKey;

use crate::runner::HarnessFileSet;

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
  let resolved = resolver.resolve(Path::new(from.as_str()), specifier)?;
  let resolved = normalize_ts_path(&resolved.to_string_lossy());
  files.resolve(&resolved)
}
