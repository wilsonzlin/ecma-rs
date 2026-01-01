use crate::multifile::normalize_name;
use crate::runner::HarnessFileSet;
use typecheck_ts::FileKey;

const EXTENSIONS: [&str; 5] = ["ts", "tsx", "d.ts", "js", "jsx"];
const INDEX_FILES: [&str; 5] = ["index.ts", "index.tsx", "index.d.ts", "index.js", "index.jsx"];

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
  let mut dir = virtual_parent_dir(&from_name);
  loop {
    let node_modules_base = virtual_join(&virtual_join(&dir, "node_modules"), specifier);
    if let Some(found) = resolve_as_file_or_directory(files, &node_modules_base) {
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
  let base_candidate = normalize_name(base);

  if let Some(found) = files.resolve(&base_candidate) {
    return Some(found);
  }

  if base_candidate.ends_with(".js") {
    let trimmed = base_candidate.trim_end_matches(".js");
    for ext in ["ts", "tsx"] {
      let candidate = normalize_name(&format!("{trimmed}.{ext}"));
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
    }
  } else if base_candidate.ends_with(".jsx") {
    let trimmed = base_candidate.trim_end_matches(".jsx");
    let candidate = normalize_name(&format!("{trimmed}.tsx"));
    if let Some(found) = files.resolve(&candidate) {
      return Some(found);
    }
  } else if !has_known_extension(&base_candidate) {
    for ext in EXTENSIONS {
      let candidate = normalize_name(&format!("{base_candidate}.{ext}"));
      if let Some(found) = files.resolve(&candidate) {
        return Some(found);
      }
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

fn is_relative_specifier(specifier: &str) -> bool {
  specifier.starts_with("./") || specifier.starts_with("../")
}

fn has_known_extension(name: &str) -> bool {
  name.ends_with(".d.ts")
    || name.ends_with(".ts")
    || name.ends_with(".tsx")
    || name.ends_with(".js")
    || name.ends_with(".jsx")
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
