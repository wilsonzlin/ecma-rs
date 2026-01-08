use crate::discover::DiscoveredTest;
use anyhow::{anyhow, bail, Context, Result};
use globset::{Glob, GlobSet, GlobSetBuilder};
use serde::Deserialize;
use std::collections::{BTreeSet, HashSet};
use std::path::Path;

#[derive(Debug, Clone, Default, Deserialize)]
pub struct Suite {
  #[serde(default)]
  pub tests: Vec<String>,
  #[serde(default)]
  pub include: Vec<String>,
  #[serde(default)]
  pub exclude: Vec<String>,
}

pub fn load_builtin_suite(name: &str) -> Result<Suite> {
  let path = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("suites")
    .join(format!("{name}.toml"));
  load_suite_from_path(&path)
}

pub fn load_suite_from_path(path: &Path) -> Result<Suite> {
  let raw = std::fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
  parse_suite(&raw).map_err(|err| anyhow!("{}: {err}", path.display()))
}

pub fn parse_suite(raw: &str) -> Result<Suite> {
  match toml::from_str::<Suite>(raw) {
    Ok(suite) => Ok(suite),
    Err(toml_err) => serde_json::from_str::<Suite>(raw)
      .map_err(|json_err| anyhow!("failed to parse suite as TOML ({toml_err}) or JSON ({json_err})")),
  }
}

pub fn select_tests(suite: &Suite, available: &[DiscoveredTest]) -> Result<Vec<String>> {
  let available_ids: HashSet<&str> = available.iter().map(|t| t.id.as_str()).collect();
  let mut selected = BTreeSet::new();

  for id in &suite.tests {
    if !available_ids.contains(id.as_str()) {
      bail!("suite references missing test id `{id}`");
    }
    selected.insert(id.clone());
  }

  let include = compile_glob_set(&suite.include, "include")?;
  if let Some(include) = &include {
    for test in available {
      if include.is_match(&test.id) {
        selected.insert(test.id.clone());
      }
    }
  }

  let exclude = compile_glob_set(&suite.exclude, "exclude")?;
  if let Some(exclude) = &exclude {
    selected.retain(|id| !exclude.is_match(id));
  }

  if selected.is_empty() {
    bail!("suite selected zero tests");
  }

  Ok(selected.into_iter().collect())
}

fn compile_glob_set(patterns: &[String], label: &str) -> Result<Option<GlobSet>> {
  if patterns.is_empty() {
    return Ok(None);
  }

  let mut builder = GlobSetBuilder::new();
  for pattern in patterns {
    let glob = Glob::new(pattern)
      .map_err(|err| anyhow!("invalid {label} glob '{pattern}': {err}"))?;
    builder.add(glob);
  }
  Ok(Some(
    builder
      .build()
      .map_err(|err| anyhow!("invalid {label} globs: {err}"))?,
  ))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::discover::discover_tests;
  use std::fs;
  use tempfile::tempdir;

  #[test]
  fn suite_selection_is_deterministic() {
    let temp = tempdir().unwrap();
    let test_dir = temp.path().join("test");
    fs::create_dir_all(&test_dir).unwrap();
    fs::write(test_dir.join("b.js"), "").unwrap();
    fs::write(test_dir.join("a.js"), "").unwrap();

    let discovered = discover_tests(temp.path()).unwrap();
    let suite = Suite {
      include: vec!["*.js".to_string()],
      exclude: vec!["b.js".to_string()],
      ..Suite::default()
    };

    let first = select_tests(&suite, &discovered).unwrap();
    let second = select_tests(&suite, &discovered).unwrap();
    assert_eq!(first, second);
    assert_eq!(first, vec!["a.js"]);
  }

  #[test]
  fn suite_missing_explicit_id_errors() {
    let temp = tempdir().unwrap();
    let test_dir = temp.path().join("test");
    fs::create_dir_all(&test_dir).unwrap();
    fs::write(test_dir.join("a.js"), "").unwrap();
    let discovered = discover_tests(temp.path()).unwrap();

    let suite = Suite {
      tests: vec!["missing.js".to_string()],
      ..Suite::default()
    };

    let err = select_tests(&suite, &discovered).unwrap_err();
    assert!(err.to_string().contains("missing test id"));
  }
}

