use crate::multifile::normalize_name;
use crate::runner::{is_source_root, HarnessFileSet};
use serde_json::{Map, Value};
use typecheck_ts::FileKey;

const EXPORT_CONDITIONS: [&str; 4] = ["types", "import", "require", "default"];
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
  let parent = virtual_parent_dir_str(base);

  if let Some(entry) = specifier.strip_prefix("./") {
    if entry.is_empty() {
      return resolve_as_file_or_directory_normalized(files, parent, 0);
    }

    let joined = virtual_join(parent, entry);
    // If the stripped entry starts with `/`, the join will introduce a `//` segment (e.g. `.//foo`).
    // Fall back to the normalizing path to preserve resolution behaviour.
    return if entry.starts_with('/') || subpath_needs_normalization(entry) {
      resolve_as_file_or_directory_inner(files, &joined, 0)
    } else {
      resolve_as_file_or_directory_normalized(files, &joined, 0)
    };
  }

  let joined = virtual_join(parent, specifier);
  resolve_as_file_or_directory(files, &joined)
}

fn resolve_non_relative(
  files: &HarnessFileSet,
  from: &FileKey,
  specifier: &str,
) -> Option<FileKey> {
  if specifier.starts_with('#') {
    return resolve_imports_specifier(files, from, specifier);
  }

  // a) Exact match of the normalized specifier (for explicit-path tests). Avoid normalizing bare
  // package names (e.g. `react`) since they will almost always resolve through `node_modules`.
  if specifier.contains('.')
    || specifier.starts_with('/')
    || specifier.starts_with('\\')
    || starts_with_drive_letter(specifier)
  {
    let normalized = normalize_name(specifier);
    if let Some(found) = files.resolve(&normalized) {
      return Some(found);
    }

    // b) Treat the specifier as a rooted virtual path and apply file/directory expansion.
    if let Some(found) = resolve_as_file_or_directory_normalized(files, &normalized, 0) {
      return Some(found);
    }
  }

  // c) Walk up `node_modules` directories starting from the importing file's directory.
  let from_name = files.name_for_key(from)?;
  let (package_name, package_rest) = split_package_name(specifier).unwrap_or((specifier, ""));
  let subpath = package_rest.trim_start_matches('/');
  let exports_subpath = (!subpath.is_empty()).then(|| {
    let mut resolved = String::with_capacity(2 + subpath.len());
    resolved.push('.');
    resolved.push('/');
    resolved.push_str(subpath);
    resolved
  });
  let mut types_specifier: Option<String> = None;
  let mut types_specifier_checked = false;
  let mut dir = virtual_parent_dir(from_name);
  loop {
    let package_dir = virtual_join3(&dir, "node_modules", package_name);
    if let Some(exports_subpath) = exports_subpath.as_deref() {
      if let Some(found) = resolve_via_exports(files, &package_dir, exports_subpath, 0) {
        return Some(found);
      }
      let entry = virtual_join(&package_dir, subpath);
      let found = if subpath_needs_normalization(subpath) {
        resolve_as_file_or_directory(files, &entry)
      } else {
        resolve_as_file_or_directory_normalized(files, &entry, 0)
      };
      if let Some(found) = found {
        return Some(found);
      }
    } else if let Some(found) = resolve_as_file_or_directory_normalized(files, &package_dir, 0) {
      return Some(found);
    }

    if !types_specifier_checked {
      types_specifier = types_fallback_specifier(specifier);
      types_specifier_checked = true;
    }
    if let Some(types_specifier) = types_specifier.as_deref() {
      let types_base = virtual_join3(&dir, "node_modules/@types", types_specifier);
      if let Some(found) = resolve_as_file_or_directory_normalized(files, &types_base, 0) {
        return Some(found);
      }
    }

    if !virtual_pop_dir(&mut dir) {
      break;
    }
  }

  None
}

fn resolve_imports_specifier(
  files: &HarnessFileSet,
  from: &FileKey,
  specifier: &str,
) -> Option<FileKey> {
  let from_name = files.name_for_key(from)?;
  let mut dir = virtual_parent_dir(from_name);
  loop {
    if let Some(found) = resolve_imports_in_dir(files, &dir, specifier) {
      return Some(found);
    }

    if !virtual_pop_dir(&mut dir) {
      break;
    }
  }

  None
}

fn resolve_imports_in_dir(files: &HarnessFileSet, dir: &str, specifier: &str) -> Option<FileKey> {
  let package_json = virtual_join(dir, "package.json");
  let package_key = files.resolve(&package_json)?;
  let parsed = files.package_json(&package_key)?;
  let imports = parsed.get("imports")?.as_object()?;

  let (target, star_match) = if let Some(target) = imports.get(specifier) {
    (target, None)
  } else {
    let (pattern_key, star_match) = best_exports_subpath_pattern(imports, specifier)?;
    (imports.get(pattern_key)?, Some(star_match))
  };

  resolve_json_target_to_file(files, dir, target, star_match, 0)
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
  resolve_as_file_or_directory_normalized(files, &base_candidate, depth)
}

fn resolve_as_file_or_directory_normalized(
  files: &HarnessFileSet,
  base_candidate: &str,
  depth: usize,
) -> Option<FileKey> {
  if depth > 16 {
    return None;
  }

  if let Some(found) = files.resolve(base_candidate) {
    return Some(found);
  }

  if base_candidate.ends_with(".js") {
    let trimmed = base_candidate.trim_end_matches(".js");
    let mut candidate = String::with_capacity(trimmed.len() + 1 + 4);
    candidate.push_str(trimmed);
    candidate.push('.');
    let prefix_len = candidate.len();
    for ext in ["ts", "tsx", "d.ts"] {
      candidate.truncate(prefix_len);
      candidate.push_str(ext);
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if base_candidate.ends_with(".jsx") {
    let trimmed = base_candidate.trim_end_matches(".jsx");
    let mut candidate = String::with_capacity(trimmed.len() + 1 + 4);
    candidate.push_str(trimmed);
    candidate.push('.');
    let prefix_len = candidate.len();
    for ext in ["tsx", "d.ts"] {
      candidate.truncate(prefix_len);
      candidate.push_str(ext);
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if base_candidate.ends_with(".mjs") {
    let trimmed = base_candidate.trim_end_matches(".mjs");
    let mut candidate = String::with_capacity(trimmed.len() + 1 + 5);
    candidate.push_str(trimmed);
    candidate.push('.');
    let prefix_len = candidate.len();
    for ext in ["mts", "d.mts"] {
      candidate.truncate(prefix_len);
      candidate.push_str(ext);
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if base_candidate.ends_with(".cjs") {
    let trimmed = base_candidate.trim_end_matches(".cjs");
    let mut candidate = String::with_capacity(trimmed.len() + 1 + 5);
    candidate.push_str(trimmed);
    candidate.push('.');
    let prefix_len = candidate.len();
    for ext in ["cts", "d.cts"] {
      candidate.truncate(prefix_len);
      candidate.push_str(ext);
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if !is_source_root(base_candidate) {
    let mut candidate = String::with_capacity(base_candidate.len() + 1 + 5);
    candidate.push_str(base_candidate);
    candidate.push('.');
    let prefix_len = candidate.len();
    for ext in EXTENSIONS {
      candidate.truncate(prefix_len);
      candidate.push_str(ext);
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  }

  if !is_source_root(base_candidate) {
    if let Some(found) = resolve_via_package_json(files, base_candidate, depth) {
      return Some(found);
    }
  }

  let mut index_candidate = String::with_capacity(base_candidate.len() + 1 + 11);
  index_candidate.push_str(base_candidate);
  if !base_candidate.ends_with('/') {
    index_candidate.push('/');
  }
  let prefix_len = index_candidate.len();
  for index in INDEX_FILES {
    index_candidate.truncate(prefix_len);
    index_candidate.push_str(index);
    if let Some(found) = files.resolve(&index_candidate) {
      return Some(found);
    }
  }

  None
}

fn resolve_via_package_json(files: &HarnessFileSet, dir: &str, depth: usize) -> Option<FileKey> {
  let package_json = virtual_join(dir, "package.json");
  let package_key = files.resolve(&package_json)?;
  let parsed = files.package_json(&package_key)?;

  if let Some(entry) = parsed.get("types").and_then(|v| v.as_str()) {
    if let Some(found) = resolve_package_json_entry(files, dir, entry, depth) {
      return Some(found);
    }
  }

  if let Some(entry) = parsed.get("typings").and_then(|v| v.as_str()) {
    if let Some(found) = resolve_package_json_entry(files, dir, entry, depth) {
      return Some(found);
    }
  }

  if let Some(exports) = parsed.get("exports") {
    if let Some((target, star_match)) = select_exports_target(exports, ".") {
      if let Some(found) = resolve_json_target_to_file(files, dir, target, star_match, depth) {
        return Some(found);
      }
    }
  }

  if let Some(entry) = parsed.get("main").and_then(|v| v.as_str()) {
    if let Some(found) = resolve_package_json_entry(files, dir, entry, depth) {
      return Some(found);
    }
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

  // Most `package.json` entries are written as `./foo/bar`. Strip the leading `./` so the joined
  // path is already normalized and we can skip an extra `normalize_name` allocation.
  let entry = entry.strip_prefix("./").unwrap_or(entry);
  if entry.is_empty() {
    return resolve_as_file_or_directory_normalized(files, dir, depth + 1);
  }

  let joined = virtual_join(dir, entry);
  // If the stripped entry starts with `/`, the join will introduce a `//` segment (e.g. `.//foo`).
  // Fall back to the normalizing path to preserve resolution behaviour.
  if entry.starts_with('/') || subpath_needs_normalization(entry) {
    resolve_as_file_or_directory_inner(files, &joined, depth + 1)
  } else {
    resolve_as_file_or_directory_normalized(files, &joined, depth + 1)
  }
}

fn resolve_via_exports(
  files: &HarnessFileSet,
  package_dir: &str,
  subpath: &str,
  depth: usize,
) -> Option<FileKey> {
  let package_json = virtual_join(package_dir, "package.json");
  let package_key = files.resolve(&package_json)?;
  let parsed = files.package_json(&package_key)?;
  let exports = parsed.get("exports")?;
  let (target, star_match) = select_exports_target(exports, subpath)?;
  resolve_json_target_to_file(files, package_dir, target, star_match, depth)
}

fn resolve_json_target_to_file(
  files: &HarnessFileSet,
  base_dir: &str,
  value: &Value,
  star_match: Option<&str>,
  depth: usize,
) -> Option<FileKey> {
  if depth > 16 {
    return None;
  }

  match value {
    Value::String(s) => match star_match {
      Some(star) if s.contains('*') => {
        let entry = s.replace('*', star);
        resolve_json_string_to_file(files, base_dir, &entry, depth + 1)
      }
      Some(_) => resolve_json_string_to_file(files, base_dir, s, depth + 1),
      None => resolve_json_string_to_file(files, base_dir, s, depth + 1),
    },
    Value::Array(items) => items
      .iter()
      .find_map(|item| resolve_json_target_to_file(files, base_dir, item, star_match, depth + 1)),
    Value::Object(map) => EXPORT_CONDITIONS.iter().find_map(|cond| {
      map
        .get(*cond)
        .and_then(|next| resolve_json_target_to_file(files, base_dir, next, star_match, depth + 1))
    }),
    Value::Null => None,
    _ => None,
  }
}

fn resolve_json_string_to_file(
  files: &HarnessFileSet,
  base_dir: &str,
  entry: &str,
  depth: usize,
) -> Option<FileKey> {
  if entry.is_empty() {
    return None;
  }
  if entry.starts_with('/') || is_drive_root(entry) {
    return resolve_as_file_or_directory_inner(files, entry, depth);
  }

  // Most `package.json` targets are written as `./foo/bar`. Strip the leading `./` so the joined
  // path is already normalized and we can skip an extra `normalize_name` allocation.
  let entry = entry.strip_prefix("./").unwrap_or(entry);
  if entry.is_empty() {
    return resolve_as_file_or_directory_normalized(files, base_dir, depth);
  }

  let joined = virtual_join(base_dir, entry);
  // If the stripped entry starts with `/`, the join will introduce a `//` segment (e.g. `.//foo`).
  // Fall back to the normalizing path to preserve resolution behaviour.
  if entry.starts_with('/') || subpath_needs_normalization(entry) {
    resolve_as_file_or_directory_inner(files, &joined, depth)
  } else {
    resolve_as_file_or_directory_normalized(files, &joined, depth)
  }
}

fn select_exports_target<'a, 'b>(
  exports: &'a Value,
  subpath: &'b str,
) -> Option<(&'a Value, Option<&'b str>)> {
  match exports {
    Value::Object(map) => {
      let has_subpath_keys = map.keys().any(|k| k.starts_with('.'));
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

fn is_relative_specifier(specifier: &str) -> bool {
  specifier.starts_with("./") || specifier.starts_with("../")
}

fn subpath_needs_normalization(subpath: &str) -> bool {
  // Most package subpaths are already normalized (e.g. `pkg/dist/index.js`). Skip the more
  // expensive `normalize_name` call when the string cannot contain segments that need collapsing.
  subpath.contains('\\')
    || subpath.contains("//")
    || subpath == "."
    || subpath == ".."
    || subpath.starts_with("./")
    || subpath.starts_with("../")
    || subpath.contains("/./")
    || subpath.contains("/../")
    || subpath.ends_with("/.")
    || subpath.ends_with("/..")
}

fn is_drive_root(dir: &str) -> bool {
  let bytes = dir.as_bytes();
  bytes.len() == 3 && bytes[1] == b':' && bytes[2] == b'/' && bytes[0].is_ascii_alphabetic()
}

fn starts_with_drive_letter(path: &str) -> bool {
  let bytes = path.as_bytes();
  bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':'
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

fn virtual_pop_dir(path: &mut String) -> bool {
  if path == "/" || is_drive_root(path) {
    return false;
  }

  while path.ends_with('/') && path != "/" && !is_drive_root(path) {
    path.pop();
  }

  if path == "/" || is_drive_root(path) {
    return false;
  }

  let trimmed = path.as_str();
  let Some(idx) = trimmed.rfind('/') else {
    path.clear();
    path.push('/');
    return true;
  };

  if idx == 0 {
    path.truncate(1);
    return true;
  }

  let bytes = trimmed.as_bytes();
  if idx == 2 && bytes.get(1) == Some(&b':') && bytes.get(2) == Some(&b'/') {
    path.truncate(3);
    return true;
  }

  path.truncate(idx);
  true
}

fn virtual_parent_dir(path: &str) -> String {
  virtual_parent_dir_str(path).to_string()
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

fn virtual_join3(base: &str, segment: &str, tail: &str) -> String {
  let mut joined = String::with_capacity(base.len() + segment.len() + tail.len() + 2);
  joined.push_str(base);
  if base != "/" && !base.ends_with('/') {
    joined.push('/');
  }
  joined.push_str(segment);
  if !joined.ends_with('/') {
    joined.push('/');
  }
  joined.push_str(tail);
  joined
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
    let mut mapped = String::with_capacity(package.len() + rest.len());
    mapped.push_str(package);
    mapped.push_str(rest);
    Some(mapped)
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
