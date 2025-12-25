use crate::directives::HarnessDirective;
use crate::directives::HarnessOptions;
use crate::multifile::split_test_file;
use crate::HarnessError;
use crate::Result;
use crate::VirtualFile;
use globset::Glob;
use globset::GlobSet;
use globset::GlobSetBuilder;
use regex::Regex;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use walkdir::WalkDir;

pub const DEFAULT_EXTENSIONS: &[&str] = &["ts", "tsx", "d.ts"];

#[derive(Debug, Clone)]
pub struct TestCase {
  pub id: String,
  pub path: PathBuf,
  pub files: Vec<VirtualFile>,
  pub deduped_files: Vec<VirtualFile>,
  pub directives: Vec<HarnessDirective>,
  pub options: HarnessOptions,
  pub notes: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum Filter {
  All,
  Glob(GlobSet),
  Regex(Regex),
}

pub fn build_filter(pattern: Option<&str>) -> Result<Filter> {
  match pattern {
    None => Ok(Filter::All),
    Some(raw) => {
      if let Ok(glob) = Glob::new(raw) {
        let mut builder = GlobSetBuilder::new();
        builder.add(glob);
        let set = builder
          .build()
          .map_err(|err| HarnessError::InvalidFilter(err.to_string()))?;
        return Ok(Filter::Glob(set));
      }

      let regex = Regex::new(raw).map_err(|err| HarnessError::InvalidFilter(err.to_string()))?;
      Ok(Filter::Regex(regex))
    }
  }
}

impl Filter {
  pub fn matches(&self, id: &str) -> bool {
    match self {
      Filter::All => true,
      Filter::Glob(set) => set.is_match(id),
      Filter::Regex(re) => re.is_match(id),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Shard {
  pub index: usize,
  pub total: usize,
}

impl Shard {
  pub fn parse(raw: &str) -> Result<Shard> {
    let parts: Vec<_> = raw.split('/').collect();
    if parts.len() != 2 {
      return Err(HarnessError::InvalidShard(raw.to_string()));
    }

    let index: usize = parts[0]
      .parse()
      .map_err(|_| HarnessError::InvalidShard(raw.to_string()))?;
    let total: usize = parts[1]
      .parse()
      .map_err(|_| HarnessError::InvalidShard(raw.to_string()))?;

    if total == 0 || index >= total {
      return Err(HarnessError::InvalidShard(raw.to_string()));
    }

    Ok(Shard { index, total })
  }

  pub fn includes(&self, position: usize) -> bool {
    position % self.total == self.index
  }
}

pub fn discover_conformance_tests(
  root: &Path,
  filter: &Filter,
  extensions: &[String],
) -> Result<Vec<TestCase>> {
  if !root.exists() {
    return Ok(Vec::new());
  }

  let mut cases = Vec::new();
  let normalized_extensions = normalize_extensions(extensions);

  for entry in WalkDir::new(root).into_iter().filter_map(|e| e.ok()) {
    if !entry.file_type().is_file() {
      continue;
    }

    let path = entry.into_path();
    let file_name = match path.file_name().and_then(|s| s.to_str()) {
      Some(name) => name,
      None => continue,
    };

    if !has_allowed_extension(file_name, &normalized_extensions) {
      continue;
    }

    let id = normalize_id(root, &path);

    if !filter.matches(&id) {
      continue;
    }

    let content = fs::read_to_string(&path)?;
    let split = split_test_file(&path, &content);

    cases.push(TestCase {
      id,
      path,
      files: split.files,
      deduped_files: split.deduped_files,
      directives: split.directives.clone(),
      options: HarnessOptions::from_directives(&split.directives),
      notes: split.notes,
    });
  }

  cases.sort_by(|a, b| a.id.cmp(&b.id));
  Ok(cases)
}

fn normalize_extensions(extensions: &[String]) -> Vec<String> {
  let mut normalized = Vec::new();
  for ext in extensions {
    let trimmed = ext.trim().trim_start_matches('.');
    if trimmed.is_empty() {
      continue;
    }

    let needle = format!(".{trimmed}");
    if !normalized.contains(&needle) {
      normalized.push(needle);
    }
  }
  normalized
}

fn has_allowed_extension(file_name: &str, extensions: &[String]) -> bool {
  extensions.iter().any(|ext| file_name.ends_with(ext))
}

fn normalize_id(root: &Path, path: &Path) -> String {
  path
    .strip_prefix(root)
    .unwrap_or(path)
    .to_string_lossy()
    .replace('\\', "/")
}

pub fn load_conformance_test(root: &Path, id: &str) -> Result<TestCase> {
  if Path::new(id).is_absolute() {
    return Err(HarnessError::Typecheck(format!(
      "test id must be relative: {id}"
    )));
  }

  if !root.exists() {
    return Err(HarnessError::Typecheck(format!(
      "conformance root {} does not exist",
      root.display()
    )));
  }

  let joined = root.join(id);
  if !joined.exists() {
    return Err(HarnessError::Typecheck(format!(
      "test {id} not found under {}",
      root.display()
    )));
  }

  let canonical_root = root.canonicalize()?;
  let canonical_path = joined.canonicalize()?;
  if !canonical_path.starts_with(&canonical_root) {
    return Err(HarnessError::Typecheck(format!(
      "test id '{id}' escapes root {}",
      root.display()
    )));
  }

  let content = fs::read_to_string(&canonical_path)?;
  let split = split_test_file(&canonical_path, &content);

  let normalized_id = canonical_path
    .strip_prefix(&canonical_root)
    .unwrap_or(&canonical_path)
    .to_string_lossy()
    .replace('\\', "/");

  Ok(TestCase {
    id: normalized_id,
    path: canonical_path,
    files: split.files,
    deduped_files: split.deduped_files,
    directives: split.directives.clone(),
    options: HarnessOptions::from_directives(&split.directives),
    notes: split.notes,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::build_filter;
  use std::fs;
  use tempfile::tempdir;

  fn default_extensions() -> Vec<String> {
    DEFAULT_EXTENSIONS
      .iter()
      .map(|ext| ext.to_string())
      .collect()
  }

  #[test]
  fn glob_filter_matches_relative_ids() {
    let dir = tempdir().unwrap();
    let root = dir.path();
    fs::create_dir_all(root.join("ok")).unwrap();
    fs::write(root.join("ok/keep.ts"), "").unwrap();
    fs::write(root.join("skip.ts"), "").unwrap();

    let filter = build_filter(Some("ok/*.ts")).unwrap();
    let cases = discover_conformance_tests(root, &filter, &default_extensions()).unwrap();
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].id, "ok/keep.ts");
  }

  #[test]
  fn regex_filter_applies_to_normalized_ids() {
    let dir = tempdir().unwrap();
    let root = dir.path();
    fs::create_dir_all(root.join("nested")).unwrap();
    fs::write(root.join("nested/file.tsx"), "").unwrap();

    let filter = Filter::Regex(Regex::new("^nested/").unwrap());
    let cases = discover_conformance_tests(root, &filter, &default_extensions()).unwrap();
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].id, "nested/file.tsx");
  }

  #[test]
  fn discovers_declaration_files() {
    let dir = tempdir().unwrap();
    let root = dir.path();
    fs::write(root.join("types.d.ts"), "declare const value: string;").unwrap();

    let cases = discover_conformance_tests(root, &Filter::All, &default_extensions()).unwrap();
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].id, "types.d.ts");
  }

  #[test]
  fn discover_carries_directives_and_options() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("case.ts");
    fs::write(
      &path,
      "// @strict: false\n// @strict: true\n// @filename: subdir/foo.ts\nconst value = 1;\n",
    )
    .unwrap();

    let cases =
      discover_conformance_tests(dir.path(), &Filter::All, &default_extensions()).unwrap();
    assert_eq!(cases.len(), 1);
    let case = &cases[0];
    assert_eq!(case.directives.len(), 3);
    assert_eq!(case.options.strict, Some(true));
    assert_eq!(case.deduped_files.len(), 1);
    assert_eq!(case.files.len(), 1);
    assert_eq!(case.deduped_files[0].name, "subdir/foo.ts");
  }
}
