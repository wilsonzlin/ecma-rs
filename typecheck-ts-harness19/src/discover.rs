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

#[derive(Debug, Clone)]
pub struct TestCase {
  pub id: String,
  pub path: PathBuf,
  pub files: Vec<VirtualFile>,
  pub module_directive: Option<String>,
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
  pub fn matches(&self, path: &Path) -> bool {
    match self {
      Filter::All => true,
      Filter::Glob(set) => set.is_match(path),
      Filter::Regex(re) => re.is_match(&path.to_string_lossy()),
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

pub fn discover_conformance_tests(root: &Path, filter: &Filter) -> Result<Vec<TestCase>> {
  if !root.exists() {
    return Ok(Vec::new());
  }

  let mut cases = Vec::new();

  for entry in WalkDir::new(root).into_iter().filter_map(|e| e.ok()) {
    if !entry.file_type().is_file() {
      continue;
    }

    let path = entry.into_path();
    if !matches!(
      path.extension().and_then(|s| s.to_str()),
      Some("ts" | "tsx")
    ) {
      continue;
    }

    if !filter.matches(&path) {
      continue;
    }

    let content = fs::read_to_string(&path)?;
    let split = split_test_file(&path, &content);

    let id = path
      .strip_prefix(root)
      .unwrap_or(&path)
      .to_string_lossy()
      .replace('\\', "/");

    cases.push(TestCase {
      id,
      path,
      files: split.files,
      module_directive: split.module_directive,
      notes: split.notes,
    });
  }

  cases.sort_by(|a, b| a.id.cmp(&b.id));
  Ok(cases)
}
