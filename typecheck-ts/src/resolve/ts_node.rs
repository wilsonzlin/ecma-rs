//! Deterministic Node/TypeScript-style module resolution.
//!
//! This is a mostly direct port of the resolver used by `typecheck-ts-harness`,
//! adapted to operate over a pluggable [`ResolveFs`] implementation so it can be
//! reused by real hosts (CLI/disk) and in-memory tests.

use diagnostics::paths::normalize_ts_path_into;
use serde_json::{Map, Value};
use std::borrow::Cow;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use super::path::canonicalize_path;
use crate::resolve::path::normalize_path;

const EXPORT_CONDITIONS: [&str; 4] = ["types", "import", "require", "default"];

/// TypeScript-aware extension search order for module resolution.
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
  /// Read a UTF-8 file from disk.
  fn read_to_string(&self, _path: &Path) -> Option<String> {
    None
  }
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

  fn read_to_string(&self, path: &Path) -> Option<String> {
    std::fs::read_to_string(path).ok()
  }

  fn canonicalize(&self, path: &Path) -> Option<PathBuf> {
    canonicalize_path(path).ok()
  }
}

/// Deterministic resolver implementing TypeScript's Node-style module resolution
/// (package.json `exports` / `types` / `imports`, extension probing, node_modules).
#[derive(Clone, Debug)]
pub struct Resolver<F = RealFs> {
  fs: F,
  options: ResolveOptions,
  package_json_cache: Arc<Mutex<HashMap<PathBuf, Option<Arc<Value>>>>>,
}

impl Resolver<RealFs> {
  /// Construct a resolver that reads from disk.
  pub fn new(options: ResolveOptions) -> Self {
    Self {
      fs: RealFs,
      options,
      package_json_cache: Arc::new(Mutex::new(HashMap::new())),
    }
  }
}

impl<F: ResolveFs> Resolver<F> {
  /// Construct a resolver with a custom filesystem implementation.
  pub fn with_fs(fs: F, options: ResolveOptions) -> Self {
    Self {
      fs,
      options,
      package_json_cache: Arc::new(Mutex::new(HashMap::new())),
    }
  }

  /// Resolve a module specifier relative to `from`.
  pub fn resolve(&self, from: &Path, specifier: &str) -> Option<PathBuf> {
    let from_name = normalize_path(from);
    if is_relative_specifier(specifier) {
      return self.resolve_relative(&from_name, specifier);
    }
    self.resolve_non_relative(&from_name, specifier)
  }

  fn resolve_relative(&self, from: &str, specifier: &str) -> Option<PathBuf> {
    let parent = virtual_parent_dir_str(from);
    let mut resolve_scratch = String::new();

    if let Some(entry) = specifier.strip_prefix("./") {
      if entry.is_empty() {
        return self.resolve_as_file_or_directory_normalized_with_scratch(parent, 0, &mut resolve_scratch);
      }

      let mut joined = virtual_join(parent, entry);
      return if entry.starts_with('/') || subpath_needs_normalization(entry) {
        normalize_ts_path_into(&joined, &mut resolve_scratch);
        self.resolve_as_file_or_directory_normalized_with_scratch(&resolve_scratch, 0, &mut joined)
      } else {
        self.resolve_as_file_or_directory_normalized_with_scratch(&joined, 0, &mut resolve_scratch)
      };
    }

    let mut joined = virtual_join(parent, specifier);
    normalize_ts_path_into(&joined, &mut resolve_scratch);
    self.resolve_as_file_or_directory_normalized_with_scratch(&resolve_scratch, 0, &mut joined)
  }

  fn resolve_non_relative(&self, from: &str, specifier: &str) -> Option<PathBuf> {
    let mut resolve_scratch = String::new();

    if specifier.starts_with('#') {
      if !self.options.package_imports {
        return None;
      }
      return self.resolve_imports_specifier(from, specifier);
    }

    if specifier.starts_with('/')
      || specifier.starts_with('\\')
      || starts_with_drive_letter(specifier)
    {
      let normalized = diagnostics::paths::normalize_ts_path(specifier);
      if let Some(found) = self.resolve_as_file_or_directory_normalized_with_scratch(
        &normalized,
        0,
        &mut resolve_scratch,
      ) {
        return Some(found);
      }
    }

    if !self.options.node_modules {
      return None;
    }

    let (package_name, package_rest) = split_package_name(specifier).unwrap_or((specifier, ""));
    let subpath = package_rest.trim_start_matches('/');
    let exports_subpath = (!subpath.is_empty()).then(|| {
      let mut resolved = String::with_capacity(2 + subpath.len());
      resolved.push('.');
      resolved.push('/');
      resolved.push_str(subpath);
      resolved
    });

    let mut types_specifier: Option<Cow<'_, str>> = None;
    let mut types_specifier_checked = false;

    let mut dir = virtual_parent_dir_str(from);
    let mut package_dir = String::with_capacity(
      dir.len() + 2 + "node_modules".len() + package_name.len() + subpath.len(),
    );
    let mut types_base = String::with_capacity(
      dir.len() + 2 + "node_modules/@types".len() + specifier.len() + subpath.len(),
    );

    loop {
      virtual_join3_into(&mut package_dir, dir, "node_modules", package_name);
      let package_dir_len = package_dir.len();
      if let Some(exports_subpath) = exports_subpath.as_deref() {
        virtual_join_into(&mut types_base, &package_dir, "package.json");
        if self.fs.is_file(Path::new(types_base.as_str())) {
          if let Some(parsed) = self.package_json(&types_base) {
            if let Some(exports) = parsed.get("exports") {
              if let Some((target, star_match)) = select_exports_target(exports, exports_subpath) {
                if let Some(found) = self.resolve_json_target_to_file(
                  &package_dir,
                  target,
                  star_match,
                  0,
                  &mut types_base,
                  &mut resolve_scratch,
                ) {
                  return Some(found);
                }
              }
            }
          }
        }
        package_dir.push('/');
        package_dir.push_str(subpath);
        let found = if subpath_needs_normalization(subpath) {
          normalize_ts_path_into(&package_dir, &mut resolve_scratch);
          self.resolve_as_file_or_directory_normalized_with_scratch(
            &resolve_scratch,
            0,
            &mut types_base,
          )
        } else {
          self.resolve_as_file_or_directory_normalized_with_scratch(
            &package_dir,
            0,
            &mut resolve_scratch,
          )
        };
        package_dir.truncate(package_dir_len);
        if let Some(found) = found {
          return Some(found);
        }
      } else if let Some(found) =
        self.resolve_as_file_or_directory_normalized_with_scratch(&package_dir, 0, &mut resolve_scratch)
      {
        return Some(found);
      }

      if !types_specifier_checked {
        types_specifier = types_fallback_specifier(specifier);
        types_specifier_checked = true;
      }
      if let Some(types_specifier) = types_specifier.as_deref() {
        virtual_join3_into(&mut types_base, dir, "node_modules/@types", types_specifier);
        if let Some(found) =
          self.resolve_as_file_or_directory_normalized_with_scratch(&types_base, 0, &mut resolve_scratch)
        {
          return Some(found);
        }
      }

      let parent = virtual_parent_dir_str(dir);
      if parent == dir {
        break;
      }
      dir = parent;
    }

    None
  }

  fn resolve_imports_specifier(&self, from: &str, specifier: &str) -> Option<PathBuf> {
    let mut dir = virtual_parent_dir_str(from);
    let mut package_json_path = String::with_capacity(dir.len() + 1 + "package.json".len());
    let mut resolve_scratch = String::new();
    loop {
      virtual_join_into(&mut package_json_path, dir, "package.json");
      if let Some(found) =
        self.resolve_imports_in_dir(dir, &mut package_json_path, &mut resolve_scratch, specifier)
      {
        return Some(found);
      }

      let parent = virtual_parent_dir_str(dir);
      if parent == dir {
        break;
      }
      dir = parent;
    }

    None
  }

  fn resolve_imports_in_dir(
    &self,
    dir: &str,
    package_json_path: &mut String,
    resolve_scratch: &mut String,
    specifier: &str,
  ) -> Option<PathBuf> {
    let parsed = self.package_json(package_json_path.as_str())?;
    let imports = parsed.get("imports")?.as_object()?;

    let (target, star_match) = if let Some(target) = imports.get(specifier) {
      (target, None)
    } else {
      let (pattern_key, star_match) = best_exports_subpath_pattern(imports, specifier)?;
      (imports.get(pattern_key)?, Some(star_match))
    };

    self.resolve_json_target_to_file(
      dir,
      target,
      star_match,
      0,
      package_json_path,
      resolve_scratch,
    )
  }

  fn resolve_as_file_or_directory_normalized_with_scratch(
    &self,
    base_candidate: &str,
    depth: usize,
    scratch: &mut String,
  ) -> Option<PathBuf> {
    if depth > 16 {
      return None;
    }

    if let Some(found) = self.try_file(base_candidate) {
      return Some(found);
    }

    let base_is_source_root = is_source_root(base_candidate);

    if base_candidate.ends_with(".js") {
      let trimmed = base_candidate.trim_end_matches(".js");
      scratch.clear();
      scratch.push_str(trimmed);
      scratch.push('.');
      let prefix_len = scratch.len();
      for ext in ["ts", "tsx", "d.ts"] {
        scratch.truncate(prefix_len);
        scratch.push_str(ext);
        if let Some(found) = self.try_file(scratch) {
          return Some(found);
        }
      }
    } else if base_candidate.ends_with(".jsx") {
      let trimmed = base_candidate.trim_end_matches(".jsx");
      scratch.clear();
      scratch.push_str(trimmed);
      scratch.push('.');
      let prefix_len = scratch.len();
      for ext in ["tsx", "d.ts"] {
        scratch.truncate(prefix_len);
        scratch.push_str(ext);
        if let Some(found) = self.try_file(scratch) {
          return Some(found);
        }
      }
    } else if base_candidate.ends_with(".mjs") {
      let trimmed = base_candidate.trim_end_matches(".mjs");
      scratch.clear();
      scratch.push_str(trimmed);
      scratch.push('.');
      let prefix_len = scratch.len();
      for ext in ["mts", "d.mts"] {
        scratch.truncate(prefix_len);
        scratch.push_str(ext);
        if let Some(found) = self.try_file(scratch) {
          return Some(found);
        }
      }
    } else if base_candidate.ends_with(".cjs") {
      let trimmed = base_candidate.trim_end_matches(".cjs");
      scratch.clear();
      scratch.push_str(trimmed);
      scratch.push('.');
      let prefix_len = scratch.len();
      for ext in ["cts", "d.cts"] {
        scratch.truncate(prefix_len);
        scratch.push_str(ext);
        if let Some(found) = self.try_file(scratch) {
          return Some(found);
        }
      }
    } else if !base_is_source_root {
      scratch.clear();
      scratch.push_str(base_candidate);
      scratch.push('.');
      let prefix_len = scratch.len();
      for ext in DEFAULT_EXTENSIONS {
        scratch.truncate(prefix_len);
        scratch.push_str(ext);
        if let Some(found) = self.try_file(scratch) {
          return Some(found);
        }
      }
    }

    if !base_is_source_root {
      virtual_join_into(scratch, base_candidate, "package.json");
      if self.fs.is_file(Path::new(scratch.as_str())) {
        if let Some(parsed) = self.package_json(scratch.as_str()) {
          let mut resolve_scratch = String::new();
          let resolve_target = |entry: &str,
                                scratch: &mut String,
                                resolve_scratch: &mut String|
           -> Option<PathBuf> {
            if entry.is_empty() {
              return None;
            }

            if entry.starts_with('/') || entry.starts_with('\\') || starts_with_drive_letter(entry) {
              normalize_ts_path_into(entry, scratch);
              return self.resolve_as_file_or_directory_normalized_with_scratch(
                scratch,
                depth + 1,
                resolve_scratch,
              );
            }

            let entry = entry.strip_prefix("./").unwrap_or(entry);
            if entry.is_empty() {
              return self.resolve_as_file_or_directory_normalized_with_scratch(
                base_candidate,
                depth + 1,
                resolve_scratch,
              );
            }

            virtual_join_into(scratch, base_candidate, entry);
            if entry.starts_with('/') || entry.starts_with('\\') || subpath_needs_normalization(entry)
            {
              normalize_ts_path_into(scratch.as_str(), resolve_scratch);
              self.resolve_as_file_or_directory_normalized_with_scratch(
                resolve_scratch,
                depth + 1,
                scratch,
              )
            } else {
              self.resolve_as_file_or_directory_normalized_with_scratch(
                scratch,
                depth + 1,
                resolve_scratch,
              )
            }
          };

          if let Some(entry) = parsed.get("types").and_then(|v| v.as_str()) {
            if let Some(found) = resolve_target(entry, scratch, &mut resolve_scratch) {
              return Some(found);
            }
          }

          if let Some(entry) = parsed.get("typings").and_then(|v| v.as_str()) {
            if let Some(found) = resolve_target(entry, scratch, &mut resolve_scratch) {
              return Some(found);
            }
          }

          if let Some(exports) = parsed.get("exports") {
            if let Some((target, star_match)) = select_exports_target(exports, ".") {
              if let Some(found) = self.resolve_json_target_to_file(
                base_candidate,
                target,
                star_match,
                depth,
                scratch,
                &mut resolve_scratch,
              ) {
                return Some(found);
              }
            }
          }

          if let Some(entry) = parsed.get("main").and_then(|v| v.as_str()) {
            if let Some(found) = resolve_target(entry, scratch, &mut resolve_scratch) {
              return Some(found);
            }
          }
        }
      }
    }

    scratch.clear();
    scratch.push_str(base_candidate);
    if !base_candidate.ends_with('/') {
      scratch.push('/');
    }
    let prefix_len = scratch.len();
    for index in INDEX_FILES {
      scratch.truncate(prefix_len);
      scratch.push_str(index);
      if let Some(found) = self.try_file(scratch) {
        return Some(found);
      }
    }

    None
  }

  fn resolve_json_target_to_file(
    &self,
    base_dir: &str,
    value: &Value,
    star_match: Option<&str>,
    depth: usize,
    scratch: &mut String,
    resolve_scratch: &mut String,
  ) -> Option<PathBuf> {
    if depth > 16 {
      return None;
    }

    match value {
      Value::String(s) => match star_match {
        Some(star) if s.contains('*') => self.resolve_json_string_to_file_with_star(
          base_dir,
          s,
          star,
          depth + 1,
          scratch,
          resolve_scratch,
        ),
        Some(_) => self.resolve_json_string_to_file(base_dir, s, depth + 1, scratch, resolve_scratch),
        None => self.resolve_json_string_to_file(base_dir, s, depth + 1, scratch, resolve_scratch),
      },
      Value::Array(items) => items.iter().find_map(|item| {
        self.resolve_json_target_to_file(
          base_dir,
          item,
          star_match,
          depth + 1,
          scratch,
          resolve_scratch,
        )
      }),
      Value::Object(map) => EXPORT_CONDITIONS.iter().find_map(|cond| {
        map.get(*cond).and_then(|next| {
          self.resolve_json_target_to_file(
            base_dir,
            next,
            star_match,
            depth + 1,
            scratch,
            resolve_scratch,
          )
        })
      }),
      Value::Null => None,
      _ => None,
    }
  }

  fn resolve_json_string_to_file(
    &self,
    base_dir: &str,
    entry: &str,
    depth: usize,
    scratch: &mut String,
    resolve_scratch: &mut String,
  ) -> Option<PathBuf> {
    if entry.is_empty() {
      return None;
    }
    if entry.starts_with('/') || entry.starts_with('\\') || starts_with_drive_letter(entry) {
      normalize_ts_path_into(entry, scratch);
      return self.resolve_as_file_or_directory_normalized_with_scratch(scratch, depth, resolve_scratch);
    }

    let entry = entry.strip_prefix("./").unwrap_or(entry);
    if entry.is_empty() {
      return self.resolve_as_file_or_directory_normalized_with_scratch(base_dir, depth, resolve_scratch);
    }

    virtual_join_into(scratch, base_dir, entry);
    if entry.starts_with('/') || subpath_needs_normalization(entry) {
      normalize_ts_path_into(scratch.as_str(), resolve_scratch);
      self.resolve_as_file_or_directory_normalized_with_scratch(resolve_scratch, depth, scratch)
    } else {
      self.resolve_as_file_or_directory_normalized_with_scratch(scratch, depth, resolve_scratch)
    }
  }

  fn resolve_json_string_to_file_with_star(
    &self,
    base_dir: &str,
    entry: &str,
    star: &str,
    depth: usize,
    scratch: &mut String,
    resolve_scratch: &mut String,
  ) -> Option<PathBuf> {
    if entry.is_empty() {
      return None;
    }

    if entry.starts_with('/') || entry.starts_with('\\') || starts_with_drive_letter(entry) {
      scratch.clear();
      scratch.reserve(entry.len() + star.len());
      push_star_replaced(scratch, entry, star);
      normalize_ts_path_into(scratch.as_str(), resolve_scratch);
      return self.resolve_as_file_or_directory_normalized_with_scratch(
        resolve_scratch,
        depth,
        scratch,
      );
    }

    let stripped = entry.strip_prefix("./").unwrap_or(entry);
    if stripped.is_empty() {
      return self.resolve_as_file_or_directory_normalized_with_scratch(base_dir, depth, resolve_scratch);
    }

    scratch.clear();
    scratch.reserve(base_dir.len() + stripped.len() + star.len() + 1);
    if base_dir == "/" {
      scratch.push('/');
    } else {
      scratch.push_str(base_dir);
      if !base_dir.ends_with('/') {
        scratch.push('/');
      }
    }
    let entry_start = scratch.len();
    push_star_replaced(scratch, stripped, star);
    let replaced_entry = &scratch[entry_start..];

    if replaced_entry.starts_with('/') || subpath_needs_normalization(replaced_entry) {
      normalize_ts_path_into(scratch.as_str(), resolve_scratch);
      self.resolve_as_file_or_directory_normalized_with_scratch(resolve_scratch, depth, scratch)
    } else {
      self.resolve_as_file_or_directory_normalized_with_scratch(scratch, depth, resolve_scratch)
    }
  }

  fn try_file(&self, candidate: &str) -> Option<PathBuf> {
    let path = Path::new(candidate);
    if !self.fs.is_file(path) {
      return None;
    }
    let canonical = self.fs.canonicalize(path);
    Some(match canonical {
      Some(path) => PathBuf::from(normalize_path(&path)),
      None => PathBuf::from(candidate),
    })
  }

  fn package_json(&self, path: &str) -> Option<Arc<Value>> {
    let path_buf = PathBuf::from(path);
    {
      let cache = self.package_json_cache.lock().unwrap();
      if let Some(cached) = cache.get(&path_buf) {
        return cached.clone();
      }
    }

    let parsed = if self.fs.is_file(Path::new(path)) {
      let raw = self.fs.read_to_string(Path::new(path))?;
      serde_json::from_str::<Value>(&raw).ok().map(Arc::new)
    } else {
      None
    };

    let mut cache = self.package_json_cache.lock().unwrap();
    cache.insert(path_buf, parsed.clone());
    parsed
  }
}

fn push_star_replaced(out: &mut String, template: &str, star: &str) {
  let mut parts = template.split('*');
  if let Some(first) = parts.next() {
    out.push_str(first);
    for part in parts {
      out.push_str(star);
      out.push_str(part);
    }
  }
}

fn select_exports_target<'a, 'b>(
  exports: &'a Value,
  subpath: &'b str,
) -> Option<(&'a Value, Option<&'b str>)> {
  match exports {
    Value::Object(map) => {
      let has_subpath_keys = map.keys().next().map_or(false, |k| k.starts_with('.'));
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
      Some(existing) => key.len() > existing.len() || (key.len() == existing.len() && key.as_str() < existing),
    };
    if replace {
      best_key = Some(key);
      best_star = Some(star);
    }
  }

  Some((best_key?, best_star?))
}

fn is_relative_specifier(specifier: &str) -> bool {
  specifier.starts_with("./") || specifier.starts_with("../")
}

fn subpath_needs_normalization(subpath: &str) -> bool {
  if subpath == "." || subpath == ".." {
    return true;
  }
  let bytes = subpath.as_bytes();
  if bytes.starts_with(b"./") || bytes.starts_with(b"../") {
    return true;
  }
  if bytes.len() >= 2 && bytes[bytes.len() - 2] == b'/' && bytes[bytes.len() - 1] == b'.' {
    return true;
  }
  if bytes.len() >= 3
    && bytes[bytes.len() - 3] == b'/'
    && bytes[bytes.len() - 2] == b'.'
    && bytes[bytes.len() - 1] == b'.'
  {
    return true;
  }

  let mut prev3 = 0u8;
  let mut prev2 = 0u8;
  let mut prev = 0u8;
  for &b in bytes {
    if b == b'\\' {
      return true;
    }
    if prev == b'/' && b == b'/' {
      return true;
    }
    if prev2 == b'/' && prev == b'.' && b == b'/' {
      return true;
    }
    if prev3 == b'/' && prev2 == b'.' && prev == b'.' && b == b'/' {
      return true;
    }
    prev3 = prev2;
    prev2 = prev;
    prev = b;
  }

  false
}

fn is_source_root(name: &str) -> bool {
  match name.as_bytes().last().copied() {
    Some(b's') => {
      name.ends_with(".ts")
        || name.ends_with(".d.ts")
        || name.ends_with(".js")
        || name.ends_with(".mjs")
        || name.ends_with(".cjs")
        || name.ends_with(".mts")
        || name.ends_with(".cts")
        || name.ends_with(".d.mts")
        || name.ends_with(".d.cts")
    }
    Some(b'x') => name.ends_with(".tsx") || name.ends_with(".jsx"),
    _ => false,
  }
}

fn is_drive_root(dir: &str) -> bool {
  let bytes = dir.as_bytes();
  bytes.len() == 3 && bytes[1] == b':' && bytes[2] == b'/' && bytes[0].is_ascii_alphabetic()
}

fn starts_with_drive_letter(path: &str) -> bool {
  let bytes = path.as_bytes();
  bytes.len() >= 3
    && bytes[0].is_ascii_alphabetic()
    && bytes[1] == b':'
    && (bytes[2] == b'/' || bytes[2] == b'\\')
}

fn virtual_parent_dir_str(path: &str) -> &str {
  if path == "/" || is_drive_root(path) {
    return path;
  }

  let trimmed = path.trim_end_matches('/');
  if trimmed == "/" || is_drive_root(trimmed) {
    return trimmed;
  }

  let Some(idx) = trimmed.rfind('/') else {
    return "/";
  };

  if idx == 0 {
    return "/";
  }

  let bytes = trimmed.as_bytes();
  if idx == 2 && bytes.get(1) == Some(&b':') && bytes.get(2) == Some(&b'/') {
    return &trimmed[..3];
  }

  &trimmed[..idx]
}

fn virtual_join(base: &str, segment: &str) -> String {
  if base == "/" {
    let mut joined = String::with_capacity(1 + segment.len());
    joined.push('/');
    joined.push_str(segment);
    joined
  } else {
    let mut joined = String::with_capacity(base.len() + 1 + segment.len());
    joined.push_str(base);
    if !base.ends_with('/') {
      joined.push('/');
    }
    joined.push_str(segment);
    joined
  }
}

fn virtual_join_into(out: &mut String, base: &str, segment: &str) {
  out.clear();
  out.reserve(base.len() + segment.len() + 1);
  if base == "/" {
    out.push('/');
    out.push_str(segment);
  } else {
    out.push_str(base);
    if !base.ends_with('/') {
      out.push('/');
    }
    out.push_str(segment);
  }
}

fn virtual_join3_into(out: &mut String, base: &str, segment: &str, tail: &str) {
  out.clear();
  out.reserve(base.len() + segment.len() + tail.len() + 2);
  out.push_str(base);
  if base != "/" && !base.ends_with('/') {
    out.push('/');
  }
  out.push_str(segment);
  out.push('/');
  out.push_str(tail);
}

fn types_fallback_specifier<'a>(specifier: &'a str) -> Option<Cow<'a, str>> {
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
    Some(Cow::Owned(mapped))
  } else {
    Some(Cow::Borrowed(specifier))
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
  } else if let Some((package, _trailing)) = specifier.split_once('/') {
    let package_len = package.len();
    Some((&specifier[..package_len], &specifier[package_len..]))
  } else {
    Some((specifier, ""))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::BTreeMap;

  #[derive(Clone, Default)]
  struct FakeFs {
    files: BTreeMap<PathBuf, String>,
  }

  impl FakeFs {
    fn insert(&mut self, path: &str, contents: &str) {
      self.files.insert(PathBuf::from(path), contents.to_string());
    }
  }

  impl ResolveFs for FakeFs {
    fn is_file(&self, path: &Path) -> bool {
      self.files.contains_key(path)
    }

    fn is_dir(&self, path: &Path) -> bool {
      self
        .files
        .keys()
        .any(|p| p.starts_with(path) && p != path)
    }

    fn read_to_string(&self, path: &Path) -> Option<String> {
      self.files.get(path).cloned()
    }

    fn canonicalize(&self, path: &Path) -> Option<PathBuf> {
      Some(path.to_path_buf())
    }
  }

  #[test]
  fn resolves_package_json_types_entrypoints() {
    let mut fs = FakeFs::default();
    fs.insert("/src/app.ts", "");
    fs.insert("/node_modules/pkg/package.json", r#"{ "types": "./dist/index.d.ts" }"#);
    fs.insert("/node_modules/pkg/dist/index.d.ts", "export {};\n");

    let resolver = Resolver::with_fs(
      fs,
      ResolveOptions {
        node_modules: true,
        ..ResolveOptions::default()
      },
    );
    let resolved = resolver
      .resolve(Path::new("/src/app.ts"), "pkg")
      .expect("pkg should resolve");
    assert_eq!(resolved, PathBuf::from("/node_modules/pkg/dist/index.d.ts"));
  }

  #[test]
  fn resolves_package_json_exports_types_entrypoints() {
    let mut fs = FakeFs::default();
    fs.insert("/src/app.ts", "");
    fs.insert(
      "/node_modules/pkg/package.json",
      r#"{ "exports": { ".": { "types": "./dist/index.d.ts" } } }"#,
    );
    fs.insert("/node_modules/pkg/dist/index.d.ts", "export {};\n");

    let resolver = Resolver::with_fs(
      fs,
      ResolveOptions {
        node_modules: true,
        ..ResolveOptions::default()
      },
    );
    let resolved = resolver
      .resolve(Path::new("/src/app.ts"), "pkg")
      .expect("pkg should resolve");
    assert_eq!(resolved, PathBuf::from("/node_modules/pkg/dist/index.d.ts"));
  }

  #[test]
  fn resolves_exports_subpath_mapping() {
    let mut fs = FakeFs::default();
    fs.insert("/src/app.ts", "");
    fs.insert(
      "/node_modules/pkg/package.json",
      r#"{ "exports": { "./subpath": { "types": "./dist/sub.d.ts" } } }"#,
    );
    fs.insert("/node_modules/pkg/dist/sub.d.ts", "export {};\n");

    let resolver = Resolver::with_fs(
      fs,
      ResolveOptions {
        node_modules: true,
        ..ResolveOptions::default()
      },
    );
    let resolved = resolver
      .resolve(Path::new("/src/app.ts"), "pkg/subpath")
      .expect("subpath should resolve");
    assert_eq!(resolved, PathBuf::from("/node_modules/pkg/dist/sub.d.ts"));
  }

  #[test]
  fn resolves_package_imports_map() {
    let mut fs = FakeFs::default();
    fs.insert("/project/src/app.ts", "");
    fs.insert(
      "/project/package.json",
      r##"{ "imports": { "#dep": "./src/dep.ts" } }"##,
    );
    fs.insert("/project/src/dep.ts", "export {};\n");

    let resolver = Resolver::with_fs(
      fs,
      ResolveOptions {
        node_modules: true,
        package_imports: true,
      },
    );
    let resolved = resolver
      .resolve(Path::new("/project/src/app.ts"), "#dep")
      .expect("imports entry should resolve");
    assert_eq!(resolved, PathBuf::from("/project/src/dep.ts"));
  }

  #[test]
  fn falls_back_to_at_types_packages() {
    let mut fs = FakeFs::default();
    fs.insert("/src/app.ts", "");
    fs.insert("/node_modules/@types/pkg/index.d.ts", "export {};\n");

    let resolver = Resolver::with_fs(
      fs,
      ResolveOptions {
        node_modules: true,
        ..ResolveOptions::default()
      },
    );
    let resolved = resolver
      .resolve(Path::new("/src/app.ts"), "pkg")
      .expect("@types fallback should resolve");
    assert_eq!(resolved, PathBuf::from("/node_modules/@types/pkg/index.d.ts"));
  }

  #[test]
  fn normalizes_windows_paths_during_resolution() {
    let mut fs = FakeFs::default();
    fs.insert("c:/project/src/app.ts", "");
    fs.insert("c:/project/node_modules/pkg/index.d.ts", "export {};\n");

    let resolver = Resolver::with_fs(
      fs,
      ResolveOptions {
        node_modules: true,
        ..ResolveOptions::default()
      },
    );
    let resolved = resolver
      .resolve(Path::new(r"C:\project\src\app.ts"), "pkg")
      .expect("pkg should resolve under c:/project");
    assert_eq!(resolved, PathBuf::from("c:/project/node_modules/pkg/index.d.ts"));
  }
}
