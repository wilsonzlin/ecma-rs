//! Node/TypeScript-style module resolution.
//!
//! This intentionally mirrors the resolution behaviour advertised by the CLI:
//! - relative specifiers resolve against the importing file
//! - extension probing follows the TypeScript resolver ordering
//! - directory specifiers consult `package.json` (`types`, `exports`, `main`) before `index.*`
//! - when enabled, bare specifiers walk `node_modules` directories (including `@types/` fallback)
//! - `#imports` specifiers consult the nearest `package.json` `imports` map

use serde_json::{Map, Value};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::resolve::path::canonicalize_path;

const EXPORT_CONDITIONS: [&str; 4] = ["types", "import", "require", "default"];

/// Default extension search order for module resolution.
///
/// This mirrors the ordering used by the harness resolver and TypeScript's Node-style lookup.
pub const DEFAULT_EXTENSIONS: &[&str] = &[
  "ts", "tsx", "d.ts", "mts", "d.mts", "cts", "d.cts", "js", "jsx", "mjs", "cjs",
];

const INDEX_FILES: [&str; 11] = [
  "index.ts",
  "index.tsx",
  "index.d.ts",
  "index.mts",
  "index.d.mts",
  "index.cts",
  "index.d.cts",
  "index.js",
  "index.jsx",
  "index.mjs",
  "index.cjs",
];

/// Options controlling module resolution behaviour.
#[derive(Clone, Copy, Debug, Default)]
pub struct ResolveOptions {
  /// Whether to walk `node_modules/` when resolving bare specifiers.
  pub node_modules: bool,
  /// Whether to resolve `#imports` specifiers using the nearest package.json.
  pub package_imports: bool,
}

/// Filesystem abstraction for resolution to allow testing and non-disk hosts.
pub trait ResolveFs: Clone {
  /// Return true if the path points to a file.
  fn is_file(&self, path: &Path) -> bool;
  /// Return true if the path points to a directory.
  fn is_dir(&self, path: &Path) -> bool;
  /// Canonicalise a path into an absolute, platform path.
  fn canonicalize(&self, path: &Path) -> Option<PathBuf>;
  /// Read a UTF-8 file to a string.
  fn read_to_string(&self, _path: &Path) -> Option<String> {
    None
  }
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

  fn read_to_string(&self, path: &Path) -> Option<String> {
    std::fs::read_to_string(path).ok()
  }
}

/// Deterministic Node/TS resolver.
#[derive(Clone, Debug)]
pub struct NodeResolver<F = RealFs> {
  fs: F,
  options: ResolveOptions,
  package_json_cache: Arc<Mutex<HashMap<PathBuf, Option<Arc<Value>>>>>,
}

impl NodeResolver<RealFs> {
  /// Construct a resolver that reads from disk.
  pub fn new(options: ResolveOptions) -> Self {
    NodeResolver {
      fs: RealFs,
      options,
      package_json_cache: Arc::new(Mutex::new(HashMap::new())),
    }
  }
}

impl<F: ResolveFs> NodeResolver<F> {
  /// Construct a resolver with a custom filesystem implementation.
  pub fn with_fs(fs: F, options: ResolveOptions) -> Self {
    NodeResolver {
      fs,
      options,
      package_json_cache: Arc::new(Mutex::new(HashMap::new())),
    }
  }

  /// Resolve a module specifier relative to `from`.
  pub fn resolve(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    if is_relative_or_absolute(specifier) {
      return self.resolve_relative(from, specifier);
    }

    if self.options.package_imports && specifier.starts_with('#') {
      return self.resolve_imports_specifier(from, specifier);
    }

    if !self.options.node_modules {
      return None;
    }

    self.resolve_node_modules(from, specifier)
  }

  fn resolve_relative(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    let base_dir = from.parent().unwrap_or_else(|| Path::new(""));
    let joined = base_dir.join(specifier);
    self.resolve_as_file_or_directory(&joined, 0)
  }

  fn resolve_node_modules(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    let (package_name, package_rest) = split_package_name(specifier).unwrap_or((specifier, ""));
    let subpath = package_rest.trim_start_matches('/');
    let exports_subpath = (!subpath.is_empty()).then(|| format!("./{subpath}"));
    let mut types_specifier: Option<String> = None;
    let mut types_checked = false;

    let mut current = from.parent();
    while let Some(dir) = current {
      let package_dir = dir.join("node_modules").join(package_name);
      if let Some(exports_subpath) = exports_subpath.as_deref() {
        let package_json_path = package_dir.join("package.json");
        if let Some(parsed) = self.package_json(&package_json_path) {
          if let Some(exports) = parsed.get("exports") {
            if let Some((target, star_match)) = select_exports_target(exports, exports_subpath) {
              if let Some(found) =
                self.resolve_json_target_to_file(&package_dir, target, star_match, 0)
              {
                return Some(found);
              }
            }
          }
        }

        if let Some(found) = self.resolve_as_file_or_directory(&package_dir.join(subpath), 0) {
          return Some(found);
        }
      } else if let Some(found) = self.resolve_as_file_or_directory(&package_dir, 0) {
        return Some(found);
      }

      if !types_checked {
        types_specifier = types_fallback_specifier(specifier);
        types_checked = true;
      }
      if let Some(types_specifier) = types_specifier.as_deref() {
        let types_dir = dir
          .join("node_modules")
          .join("@types")
          .join(types_specifier);
        if let Some(found) = self.resolve_as_file_or_directory(&types_dir, 0) {
          return Some(found);
        }
      }

      current = dir.parent();
    }

    None
  }

  fn resolve_imports_specifier(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    let mut dir = from.parent();
    while let Some(current) = dir {
      let package_json = current.join("package.json");
      if let Some(parsed) = self.package_json(&package_json) {
        if let Some(imports) = parsed.get("imports").and_then(|v| v.as_object()) {
          let (target, star_match) = if let Some(target) = imports.get(specifier) {
            (target, None)
          } else {
            let (pattern_key, star_match) = best_exports_subpath_pattern(imports, specifier)?;
            (imports.get(pattern_key)?, Some(star_match))
          };
          if let Some(found) = self.resolve_json_target_to_file(current, target, star_match, 0) {
            return Some(found);
          }
        }
      }
      dir = current.parent();
    }

    None
  }

  fn resolve_as_file_or_directory(&self, base_candidate: &Path, depth: usize) -> Option<PathBuf> {
    if depth > 16 {
      return None;
    }

    if let Some(found) = self.try_file(base_candidate) {
      return Some(found);
    }

    let base_is_source_root = is_source_root(base_candidate);
    let name = base_candidate
      .file_name()
      .and_then(|s| s.to_str())
      .unwrap_or("");

    if name.ends_with(".js") {
      let stripped = name.strip_suffix(".js").unwrap_or(name);
      for ext in ["ts", "tsx", "d.ts"] {
        let candidate = base_candidate.with_file_name(format!("{stripped}.{ext}"));
        if let Some(found) = self.try_file(&candidate) {
          return Some(found);
        }
      }
    } else if name.ends_with(".jsx") {
      let stripped = name.strip_suffix(".jsx").unwrap_or(name);
      for ext in ["tsx", "d.ts"] {
        let candidate = base_candidate.with_file_name(format!("{stripped}.{ext}"));
        if let Some(found) = self.try_file(&candidate) {
          return Some(found);
        }
      }
    } else if name.ends_with(".mjs") {
      let stripped = name.strip_suffix(".mjs").unwrap_or(name);
      for ext in ["mts", "d.mts"] {
        let candidate = base_candidate.with_file_name(format!("{stripped}.{ext}"));
        if let Some(found) = self.try_file(&candidate) {
          return Some(found);
        }
      }
    } else if name.ends_with(".cjs") {
      let stripped = name.strip_suffix(".cjs").unwrap_or(name);
      for ext in ["cts", "d.cts"] {
        let candidate = base_candidate.with_file_name(format!("{stripped}.{ext}"));
        if let Some(found) = self.try_file(&candidate) {
          return Some(found);
        }
      }
    } else if !base_is_source_root {
      for ext in DEFAULT_EXTENSIONS {
        let Some(candidate) = append_extension(base_candidate, ext) else {
          continue;
        };
        if let Some(found) = self.try_file(&candidate) {
          return Some(found);
        }
      }
    }

    if !base_is_source_root {
      let package_json_path = base_candidate.join("package.json");
      if let Some(parsed) = self.package_json(&package_json_path) {
        if let Some(entry) = parsed.get("types").and_then(|v| v.as_str()) {
          if let Some(found) = self.resolve_package_entry(base_candidate, entry, depth + 1) {
            return Some(found);
          }
        }

        if let Some(entry) = parsed.get("typings").and_then(|v| v.as_str()) {
          if let Some(found) = self.resolve_package_entry(base_candidate, entry, depth + 1) {
            return Some(found);
          }
        }

        if let Some(exports) = parsed.get("exports") {
          if let Some((target, star_match)) = select_exports_target(exports, ".") {
            if let Some(found) =
              self.resolve_json_target_to_file(base_candidate, target, star_match, depth)
            {
              return Some(found);
            }
          }
        }

        if let Some(entry) = parsed.get("main").and_then(|v| v.as_str()) {
          if let Some(found) = self.resolve_package_entry(base_candidate, entry, depth + 1) {
            return Some(found);
          }
        }
      }

      for index in INDEX_FILES {
        let candidate = base_candidate.join(index);
        if let Some(found) = self.try_file(&candidate) {
          return Some(found);
        }
      }
    }

    None
  }

  fn resolve_package_entry(&self, base_dir: &Path, entry: &str, depth: usize) -> Option<PathBuf> {
    if entry.is_empty() {
      return None;
    }

    if Path::new(entry).is_absolute() {
      return self.resolve_as_file_or_directory(Path::new(entry), depth);
    }

    let stripped = entry.strip_prefix("./").unwrap_or(entry);
    if stripped.is_empty() {
      return self.resolve_as_file_or_directory(base_dir, depth);
    }

    self.resolve_as_file_or_directory(&base_dir.join(stripped), depth)
  }

  fn resolve_json_target_to_file(
    &self,
    base_dir: &Path,
    value: &Value,
    star_match: Option<&str>,
    depth: usize,
  ) -> Option<PathBuf> {
    if depth > 16 {
      return None;
    }

    match value {
      Value::String(entry) => match star_match {
        Some(star) if entry.contains('*') => {
          self.resolve_json_string_to_file(base_dir, &replace_star(entry, star), depth + 1)
        }
        _ => self.resolve_json_string_to_file(base_dir, entry, depth + 1),
      },
      Value::Array(items) => items
        .iter()
        .find_map(|item| self.resolve_json_target_to_file(base_dir, item, star_match, depth + 1)),
      Value::Object(map) => EXPORT_CONDITIONS.iter().find_map(|cond| {
        map
          .get(*cond)
          .and_then(|next| self.resolve_json_target_to_file(base_dir, next, star_match, depth + 1))
      }),
      Value::Null => None,
      _ => None,
    }
  }

  fn resolve_json_string_to_file(
    &self,
    base_dir: &Path,
    entry: &str,
    depth: usize,
  ) -> Option<PathBuf> {
    if entry.is_empty() {
      return None;
    }

    if Path::new(entry).is_absolute() {
      return self.resolve_as_file_or_directory(Path::new(entry), depth);
    }

    let stripped = entry.strip_prefix("./").unwrap_or(entry);
    if stripped.is_empty() {
      return self.resolve_as_file_or_directory(base_dir, depth);
    }

    self.resolve_as_file_or_directory(&base_dir.join(stripped), depth)
  }

  fn try_file(&self, path: &Path) -> Option<PathBuf> {
    self
      .fs
      .is_file(path)
      .then(|| self.fs.canonicalize(path))
      .flatten()
  }

  fn package_json(&self, path: &Path) -> Option<Arc<Value>> {
    {
      let cache = self.package_json_cache.lock().unwrap();
      if let Some(cached) = cache.get(path) {
        return cached.clone();
      }
    }

    let parsed = if self.fs.is_file(path) {
      let text = self.fs.read_to_string(path)?;
      serde_json::from_str::<Value>(&text).ok().map(Arc::new)
    } else {
      None
    };

    let mut cache = self.package_json_cache.lock().unwrap();
    cache.insert(path.to_path_buf(), parsed.clone());
    parsed
  }
}

fn is_relative_or_absolute(specifier: &str) -> bool {
  specifier.starts_with("./") || specifier.starts_with("../") || Path::new(specifier).is_absolute()
}

fn append_extension(base: &Path, ext: &str) -> Option<PathBuf> {
  use std::ffi::OsStr;
  let file_name = base.file_name()?;
  let mut name = file_name.to_os_string();
  name.push(OsStr::new("."));
  name.push(OsStr::new(ext));
  let mut candidate = base.to_path_buf();
  candidate.set_file_name(name);
  Some(candidate)
}

fn is_source_root(path: &Path) -> bool {
  let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
  if name.ends_with(".d.ts") || name.ends_with(".d.mts") || name.ends_with(".d.cts") {
    return true;
  }
  matches!(
    path.extension().and_then(|e| e.to_str()),
    Some("ts" | "tsx" | "js" | "jsx" | "mjs" | "cjs" | "mts" | "cts")
  )
}

fn replace_star(template: &str, star: &str) -> String {
  let mut parts = template.split('*');
  let mut out = String::new();
  if let Some(first) = parts.next() {
    out.push_str(first);
    for part in parts {
      out.push_str(star);
      out.push_str(part);
    }
  }
  out
}

fn select_exports_target<'a, 'b>(
  exports: &'a Value,
  subpath: &'b str,
) -> Option<(&'a Value, Option<&'b str>)> {
  match exports {
    Value::Object(map) => {
      let has_subpath_keys = map.keys().next().is_some_and(|k| k.starts_with('.'));
      if has_subpath_keys {
        if let Some(target) = map.get(subpath) {
          return Some((target, None));
        }
        let (pattern_key, star_match) = best_exports_subpath_pattern(map, subpath)?;
        Some((map.get(pattern_key)?, Some(star_match)))
      } else {
        (subpath == ".").then_some((exports, None))
      }
    }
    _ => (subpath == ".").then_some((exports, None)),
  }
}

fn best_exports_subpath_pattern<'a, 'b>(
  map: &'a Map<String, Value>,
  subpath: &'b str,
) -> Option<(&'a str, &'b str)> {
  let mut best_key: Option<&'a str> = None;
  let mut best_star: Option<&'b str> = None;

  for key in map.keys() {
    let Some((prefix, suffix)) = key.split_once('*') else {
      continue;
    };
    if suffix.contains('*') {
      continue;
    }
    if !subpath.starts_with(prefix) || !subpath.ends_with(suffix) {
      continue;
    }
    if subpath.len() < prefix.len() + suffix.len() {
      continue;
    }
    let star = &subpath[prefix.len()..subpath.len() - suffix.len()];

    let replace = match best_key {
      None => true,
      Some(existing) => {
        key.len() > existing.len() || (key.len() == existing.len() && key.as_str() < existing)
      }
    };
    if replace {
      best_key = Some(key);
      best_star = Some(star);
    }
  }

  Some((best_key?, best_star?))
}

fn types_fallback_specifier(specifier: &str) -> Option<String> {
  let (package, rest) = split_package_name(specifier)?;
  if package.starts_with("@types/") {
    return None;
  }

  if let Some(stripped) = package.strip_prefix('@') {
    let (scope, name) = stripped.split_once('/')?;
    let mut mapped = String::with_capacity(scope.len() + 2 + name.len() + rest.len());
    mapped.push_str(scope);
    mapped.push_str("__");
    mapped.push_str(name);
    mapped.push_str(rest);
    Some(mapped)
  } else {
    Some(specifier.to_string())
  }
}

fn split_package_name(specifier: &str) -> Option<(&str, &str)> {
  if specifier.is_empty() {
    return None;
  }

  if let Some(stripped) = specifier.strip_prefix('@') {
    let Some((scope, rest)) = stripped.split_once('/') else {
      return None;
    };
    let Some((name, _trailing)) = rest.split_once('/') else {
      let package_len = 1 + scope.len() + 1 + rest.len();
      return Some((&specifier[..package_len], ""));
    };

    let package_len = 1 + scope.len() + 1 + name.len();
    Some((&specifier[..package_len], &specifier[package_len..]))
  } else {
    if let Some((package, _trailing)) = specifier.split_once('/') {
      let package_len = package.len();
      Some((&specifier[..package_len], &specifier[package_len..]))
    } else {
      Some((specifier, ""))
    }
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
    let with_node = NodeResolver::with_fs(
      fs.clone(),
      ResolveOptions {
        node_modules: true,
        ..ResolveOptions::default()
      },
    );
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
