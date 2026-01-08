use crate::frontmatter::Frontmatter;
use crate::report::Variant;
use anyhow::{bail, Context, Result};
use std::collections::HashSet;
use std::path::Path;

pub fn assemble_source(
  test262_dir: &Path,
  frontmatter: &Frontmatter,
  variant: Variant,
  body: &str,
) -> Result<String> {
  let harness_dir = test262_dir.join("harness");
  if !harness_dir.is_dir() {
    bail!(
      "test262 harness directory not found at {} (expected a tc39/test262 checkout)",
      harness_dir.display()
    );
  }

  let mut includes: Vec<String> = Vec::new();
  let mut seen: HashSet<String> = HashSet::new();
  for name in ["assert.js", "sta.js"]
    .into_iter()
    .map(|s| s.to_string())
    .chain(frontmatter.includes.iter().cloned())
  {
    if seen.insert(name.clone()) {
      includes.push(name);
    }
  }

  let mut out = String::new();
  for include in includes {
    let path = harness_dir.join(&include);
    let content =
      std::fs::read_to_string(&path).with_context(|| format!("read {}", path.display()))?;
    out.push_str(&content);
    if !content.ends_with('\n') {
      out.push('\n');
    }
    out.push('\n');
  }

  if variant == Variant::Strict {
    out.push_str("'use strict';\n\n");
  }

  out.push_str(body);
  Ok(out)
}
