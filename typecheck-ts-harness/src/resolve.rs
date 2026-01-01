use crate::multifile::normalize_name;
use crate::runner::HarnessFileSet;
use serde_json::{Map, Value};
use typecheck_ts::FileKey;

const EXPORT_CONDITIONS: [&str; 4] = ["types", "default", "import", "require"];
const EXTENSIONS: [&str; 11] = [
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

pub(crate) fn resolve_module_specifier(
  files: &HarnessFileSet,
  from: &FileKey,
  specifier: &str,
) -> Option<FileKey> {
  if is_relative_specifier(specifier) {
    return resolve_relative(files, from, specifier);
  }

  resolve_non_relative(files, from, specifier)
}

fn resolve_relative(files: &HarnessFileSet, from: &FileKey, specifier: &str) -> Option<FileKey> {
  let base = files.name_for_key(from)?;
  let parent = virtual_parent_dir(&base);
  let joined = virtual_join(&parent, specifier);
  resolve_as_file_or_directory(files, &joined)
}

fn resolve_non_relative(
  files: &HarnessFileSet,
  from: &FileKey,
  specifier: &str,
) -> Option<FileKey> {
  // a) Exact match of the normalized specifier (for explicit-path tests).
  let normalized = normalize_name(specifier);
  if let Some(found) = files.resolve(&normalized) {
    return Some(found);
  }

  // b) Treat the specifier as a rooted virtual path and apply file/directory expansion.
  if let Some(found) = resolve_as_file_or_directory(files, &normalized) {
    return Some(found);
  }

  // c) Walk up `node_modules` directories starting from the importing file's directory.
  let from_name = files.name_for_key(from)?;
  let (package_name, package_rest) = split_package_name(specifier).unwrap_or((specifier, ""));
  let subpath = package_rest.trim_start_matches('/');
  let has_subpath = !subpath.is_empty();
  let mut dir = virtual_parent_dir(&from_name);
  loop {
    let package_dir = virtual_join(&virtual_join(&dir, "node_modules"), package_name);
    if has_subpath {
      if let Some(found) = resolve_via_exports(files, &package_dir, &format!("./{subpath}"), 0) {
        return Some(found);
      }
      let entry = virtual_join(&package_dir, subpath);
      if let Some(found) = resolve_as_file_or_directory(files, &entry) {
        return Some(found);
      }
    } else if let Some(found) = resolve_as_file_or_directory(files, &package_dir) {
      return Some(found);
    }

    if let Some(types_specifier) = types_fallback_specifier(specifier) {
      let types_base = virtual_join(
        &virtual_join(&virtual_join(&dir, "node_modules"), "@types"),
        &types_specifier,
      );
      if let Some(found) = resolve_as_file_or_directory(files, &types_base) {
        return Some(found);
      }
    }

    if is_virtual_root_dir(&dir) {
      break;
    }
    dir = virtual_parent_dir(&dir);
  }

  None
}

fn resolve_as_file_or_directory(files: &HarnessFileSet, base: &str) -> Option<FileKey> {
  resolve_as_file_or_directory_inner(files, base, 0)
}

fn resolve_as_file_or_directory_inner(
  files: &HarnessFileSet,
  base: &str,
  depth: usize,
) -> Option<FileKey> {
  if depth > 16 {
    return None;
  }

  let base_candidate = normalize_name(base);

  if let Some(found) = files.resolve(&base_candidate) {
    return Some(found);
  }

  if base_candidate.ends_with(".js") {
    let trimmed = base_candidate.trim_end_matches(".js");
    for ext in ["ts", "tsx", "d.ts"] {
      let candidate = normalize_name(&format!("{trimmed}.{ext}"));
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if base_candidate.ends_with(".jsx") {
    let trimmed = base_candidate.trim_end_matches(".jsx");
    for ext in ["tsx", "d.ts"] {
      let candidate = normalize_name(&format!("{trimmed}.{ext}"));
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if base_candidate.ends_with(".mjs") {
    let trimmed = base_candidate.trim_end_matches(".mjs");
    for ext in ["mts", "d.mts"] {
      let candidate = normalize_name(&format!("{trimmed}.{ext}"));
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if base_candidate.ends_with(".cjs") {
    let trimmed = base_candidate.trim_end_matches(".cjs");
    for ext in ["cts", "d.cts"] {
      let candidate = normalize_name(&format!("{trimmed}.{ext}"));
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if !has_known_extension(&base_candidate) {
    for ext in EXTENSIONS {
      let candidate = normalize_name(&format!("{base_candidate}.{ext}"));
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  }

  if !has_known_extension(&base_candidate) {
    if let Some(found) = resolve_via_package_json(files, &base_candidate, depth) {
      return Some(found);
    }
  }

  for index in INDEX_FILES {
    let joined = normalize_name(&virtual_join(&base_candidate, index));
    if let Some(found) = files.resolve(&joined) {
      return Some(found);
    }
  }

  None
}

fn resolve_via_package_json(
  files: &HarnessFileSet,
  dir: &str,
  depth: usize,
) -> Option<FileKey> {
  let package_json = normalize_name(&virtual_join(dir, "package.json"));
  let package_key = files.resolve(&package_json)?;
  let raw = files.content(&package_key)?;
  let parsed: Value = serde_json::from_str(&raw).ok()?;

  if let Some(entry) = parsed.get("types").and_then(|v| v.as_str()) {
    return resolve_package_json_entry(files, dir, entry, depth);
  }

  if let Some(entry) = parsed.get("typings").and_then(|v| v.as_str()) {
    return resolve_package_json_entry(files, dir, entry, depth);
  }

  if let Some(entry) = resolve_exports_entry(&parsed, ".") {
    return resolve_package_json_entry(files, dir, &entry, depth);
  }

  if let Some(entry) = parsed.get("main").and_then(|v| v.as_str()) {
    return resolve_package_json_entry(files, dir, entry, depth);
  }

  None
}

fn resolve_package_json_entry(
  files: &HarnessFileSet,
  dir: &str,
  entry: &str,
  depth: usize,
) -> Option<FileKey> {
  if entry.is_empty() {
    return None;
  }
  let entry = normalize_name(&virtual_join(dir, entry));
  resolve_as_file_or_directory_inner(files, &entry, depth + 1)
}

fn resolve_via_exports(
  files: &HarnessFileSet,
  package_dir: &str,
  subpath: &str,
  depth: usize,
) -> Option<FileKey> {
  let package_json = normalize_name(&virtual_join(package_dir, "package.json"));
  let package_key = files.resolve(&package_json)?;
  let raw = files.content(&package_key)?;
  let parsed: Value = serde_json::from_str(&raw).ok()?;
  let entry = resolve_exports_entry(&parsed, subpath)?;
  resolve_package_json_entry(files, package_dir, &entry, depth)
}

fn resolve_exports_entry(parsed: &Value, subpath: &str) -> Option<String> {
  let exports = parsed.get("exports")?;
  resolve_exports_value(exports, subpath, 0)
}

fn resolve_exports_value(exports: &Value, subpath: &str, depth: usize) -> Option<String> {
  if depth > 16 {
    return None;
  }

  match exports {
    Value::String(s) => (subpath == ".").then(|| s.clone()),
    Value::Array(items) => items
      .iter()
      .find_map(|item| resolve_exports_value(item, subpath, depth + 1)),
    Value::Object(map) => {
      let has_subpath_keys = map.keys().any(|k| k.starts_with('.'));
      if has_subpath_keys {
        if let Some(target) = map.get(subpath) {
          return resolve_export_target(target, depth + 1);
        }

        let (pattern_key, star_match) = best_exports_subpath_pattern(map, subpath)?;
        let target = map.get(&pattern_key)?;
        let resolved = resolve_export_target(target, depth + 1)?;
        Some(resolved.replace('*', &star_match))
      } else {
        (subpath == ".").then(|| resolve_export_target(exports, depth + 1))?
      }
    }
    Value::Null => None,
    _ => None,
  }
}

fn resolve_export_target(value: &Value, depth: usize) -> Option<String> {
  if depth > 16 {
    return None;
  }

  match value {
    Value::String(s) => Some(s.clone()),
    Value::Array(items) => items
      .iter()
      .find_map(|item| resolve_export_target(item, depth + 1)),
    Value::Object(map) => {
      for cond in EXPORT_CONDITIONS {
        if let Some(next) = map.get(cond) {
          if let Some(resolved) = resolve_export_target(next, depth + 1) {
            return Some(resolved);
          }
        }
      }
      None
    }
    Value::Null => None,
    _ => None,
  }
}

fn best_exports_subpath_pattern(map: &Map<String, Value>, subpath: &str) -> Option<(String, String)> {
  let mut best_key: Option<String> = None;
  let mut best_star: Option<String> = None;

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

    let replace = match best_key.as_ref() {
      None => true,
      Some(existing) => {
        key.len() > existing.len() || (key.len() == existing.len() && key < existing)
      }
    };
    if replace {
      best_key = Some(key.clone());
      best_star = Some(star.to_string());
    }
  }

  Some((best_key?, best_star?))
}

fn is_relative_specifier(specifier: &str) -> bool {
  specifier.starts_with("./") || specifier.starts_with("../")
}

fn has_known_extension(name: &str) -> bool {
  name.ends_with(".d.ts")
    || name.ends_with(".d.mts")
    || name.ends_with(".d.cts")
    || name.ends_with(".ts")
    || name.ends_with(".tsx")
    || name.ends_with(".mts")
    || name.ends_with(".cts")
    || name.ends_with(".js")
    || name.ends_with(".jsx")
    || name.ends_with(".mjs")
    || name.ends_with(".cjs")
}

fn is_virtual_root_dir(dir: &str) -> bool {
  dir == "/" || is_drive_root(dir)
}

fn is_drive_root(dir: &str) -> bool {
  let bytes = dir.as_bytes();
  bytes.len() == 3 && bytes[1] == b':' && bytes[2] == b'/' && bytes[0].is_ascii_alphabetic()
}

fn virtual_parent_dir(path: &str) -> String {
  if path == "/" || is_drive_root(path) {
    return path.to_string();
  }

  let trimmed = path.trim_end_matches('/');
  if trimmed == "/" || is_drive_root(trimmed) {
    return trimmed.to_string();
  }

  let Some(idx) = trimmed.rfind('/') else {
    return "/".to_string();
  };

  if idx == 0 {
    return "/".to_string();
  }

  let bytes = trimmed.as_bytes();
  if idx == 2 && bytes.get(1) == Some(&b':') && bytes.get(2) == Some(&b'/') {
    return trimmed[..3].to_string();
  }

  trimmed[..idx].to_string()
}

fn virtual_join(base: &str, segment: &str) -> String {
  if base == "/" {
    format!("/{segment}")
  } else if base.ends_with('/') {
    format!("{base}{segment}")
  } else {
    format!("{base}/{segment}")
  }
}

fn types_fallback_specifier(specifier: &str) -> Option<String> {
  let (package, rest) = split_package_name(specifier)?;
  if package.starts_with("@types/") {
    return None;
  }

  let mapped = if let Some(stripped) = package.strip_prefix('@') {
    let (scope, name) = stripped.split_once('/')?;
    format!("{scope}__{name}")
  } else {
    package.to_string()
  };

  Some(format!("{mapped}{rest}"))
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
