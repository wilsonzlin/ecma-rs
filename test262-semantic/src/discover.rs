use anyhow::{bail, Context, Result};
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

#[derive(Debug, Clone)]
pub struct DiscoveredTest {
  pub id: String,
  pub path: PathBuf,
}

pub fn discover_tests(test262_dir: &Path) -> Result<Vec<DiscoveredTest>> {
  let test_dir = test262_dir.join("test");
  if !test_dir.is_dir() {
    bail!(
      "test262 test directory not found at {} (expected a tc39/test262 checkout)",
      test_dir.display()
    );
  }

  let mut out = Vec::new();
  for entry in WalkDir::new(&test_dir).into_iter().filter_map(|e| e.ok()) {
    if !entry.file_type().is_file() {
      continue;
    }
    let path = entry.into_path();
    if path.extension().and_then(|ext| ext.to_str()) != Some("js") {
      continue;
    }

    let id = normalize_id(&test_dir, &path);
    out.push(DiscoveredTest { id, path });
  }

  if out.is_empty() {
    bail!("no tests discovered under {}", test_dir.display());
  }

  out.sort_by(|a, b| a.id.cmp(&b.id));
  Ok(out)
}

fn normalize_id(root: &Path, path: &Path) -> String {
  let mut id = path
    .strip_prefix(root)
    .unwrap_or(path)
    .to_string_lossy()
    .into_owned();
  // Avoid allocating a second String on Unix where paths already use `/`.
  if id.contains('\\') {
    id = id.replace('\\', "/");
  }
  id
}

pub fn read_utf8_file(path: &Path) -> Result<String> {
  std::fs::read_to_string(path).with_context(|| format!("read {}", path.display()))
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::fs;
  use tempfile::tempdir;

  #[test]
  fn discovery_is_deterministic_and_normalized() {
    let temp = tempdir().unwrap();
    let test_dir = temp.path().join("test");
    fs::create_dir_all(test_dir.join("nested")).unwrap();
    fs::write(test_dir.join("b.js"), "").unwrap();
    fs::write(test_dir.join("nested/a.js"), "").unwrap();

    let tests = discover_tests(temp.path()).unwrap();
    let ids: Vec<_> = tests.iter().map(|t| t.id.as_str()).collect();
    assert_eq!(ids, vec!["b.js", "nested/a.js"]);
  }
}

