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
  // Ensure strict-mode variants actually run in strict mode: the directive must
  // appear before any other statements (including harness includes), otherwise
  // the directive prologue is already terminated.
  if variant == Variant::Strict {
    out.push_str("'use strict';\n\n");
  }
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

  out.push_str(body);
  Ok(out)
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::fs;
  use tempfile::tempdir;

  #[test]
  fn strict_variant_begins_with_use_strict_directive() {
    let dir = tempdir().unwrap();
    let harness_dir = dir.path().join("harness");
    fs::create_dir_all(&harness_dir).unwrap();

    // Intentionally include non-directive statements so the directive prologue
    // would be terminated if we appended 'use strict' after includes.
    fs::write(harness_dir.join("assert.js"), "var ASSERT_LOADED = true;").unwrap();
    fs::write(harness_dir.join("sta.js"), "var STA_LOADED = true;").unwrap();

    let src =
      assemble_source(dir.path(), &Frontmatter::default(), Variant::Strict, "body();").unwrap();
    assert!(
      src.starts_with("'use strict';\n\n"),
      "strict source should begin with directive, got: {src:?}"
    );
  }

  #[test]
  fn non_strict_variant_does_not_begin_with_use_strict_directive() {
    let dir = tempdir().unwrap();
    let harness_dir = dir.path().join("harness");
    fs::create_dir_all(&harness_dir).unwrap();
    fs::write(harness_dir.join("assert.js"), "var ASSERT_LOADED = true;").unwrap();
    fs::write(harness_dir.join("sta.js"), "var STA_LOADED = true;").unwrap();

    let src = assemble_source(
      dir.path(),
      &Frontmatter::default(),
      Variant::NonStrict,
      "body();",
    )
    .unwrap();
    assert!(
      !src.starts_with("'use strict';"),
      "non-strict source should not begin with directive, got: {src:?}"
    );
  }
}
