use crate::frontmatter::Frontmatter;
use crate::report::Variant;
use anyhow::{bail, Context, Result};
use std::collections::HashSet;
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum HarnessMode {
  /// Inline the upstream `test262` harness sources (`assert.js` and `sta.js`).
  Inline,
  /// Do not automatically inline the default harness sources.
  ///
  /// The executor/host is expected to provide `assert`, `Test262Error`, and any
  /// other globals normally provided by `assert.js`/`sta.js`.
  Host,
}

pub fn assemble_source(
  test262_dir: &Path,
  frontmatter: &Frontmatter,
  variant: Variant,
  body: &str,
) -> Result<String> {
  assemble_source_with_mode(test262_dir, frontmatter, variant, body, HarnessMode::Inline)
}

pub fn assemble_source_with_mode(
  test262_dir: &Path,
  frontmatter: &Frontmatter,
  variant: Variant,
  body: &str,
  mode: HarnessMode,
) -> Result<String> {
  let default_includes: &[&str] = match mode {
    HarnessMode::Inline => &["assert.js", "sta.js"],
    HarnessMode::Host => &[],
  };

  let mut includes: Vec<String> = Vec::new();
  let mut seen: HashSet<String> = HashSet::new();
  for name in default_includes
    .iter()
    .copied()
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
  if !includes.is_empty() {
    let harness_dir = test262_dir.join("harness");
    if !harness_dir.is_dir() {
      bail!(
        "test262 harness directory not found at {} (expected a tc39/test262 checkout)",
        harness_dir.display()
      );
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
  }

  out.push_str(body);
  Ok(out)
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::fs;
  use tempfile::tempdir;

  fn setup_test262_dir() -> tempfile::TempDir {
    let temp = tempdir().unwrap();
    let harness_dir = temp.path().join("harness");
    fs::create_dir_all(&harness_dir).unwrap();
    fs::write(harness_dir.join("assert.js"), "/*assert*/\n").unwrap();
    fs::write(harness_dir.join("sta.js"), "/*sta*/\n").unwrap();
    fs::write(harness_dir.join("helper.js"), "/*helper*/\n").unwrap();
    temp
  }

  #[test]
  fn inline_includes_default_harness_and_dedupes_frontmatter() {
    let temp = setup_test262_dir();
    let frontmatter = Frontmatter {
      // `assert.js` appears both as an implicit default include and explicitly in
      // frontmatter; it should appear only once.
      includes: vec!["assert.js".to_string(), "helper.js".to_string()],
      ..Frontmatter::default()
    };

    let body = "/*body*/\n";
    let source = assemble_source_with_mode(
      temp.path(),
      &frontmatter,
      Variant::NonStrict,
      body,
      HarnessMode::Inline,
    )
    .unwrap();

    assert_eq!(source.match_indices("/*assert*/").count(), 1);
    assert_eq!(source.match_indices("/*sta*/").count(), 1);
    assert_eq!(source.match_indices("/*helper*/").count(), 1);

    let assert_pos = source.find("/*assert*/").unwrap();
    let sta_pos = source.find("/*sta*/").unwrap();
    let helper_pos = source.find("/*helper*/").unwrap();
    let body_pos = source.find("/*body*/").unwrap();
    assert!(assert_pos < sta_pos);
    assert!(sta_pos < helper_pos);
    assert!(helper_pos < body_pos);
  }

  #[test]
  fn host_omits_default_harness_when_not_explicitly_included() {
    let temp = setup_test262_dir();
    let frontmatter = Frontmatter::default();
    let body = "/*body*/\n";

    let source = assemble_source_with_mode(
      temp.path(),
      &frontmatter,
      Variant::NonStrict,
      body,
      HarnessMode::Host,
    )
    .unwrap();

    assert_eq!(source, body);
  }

  #[test]
  fn host_includes_frontmatter_includes_and_dedupes() {
    let temp = setup_test262_dir();
    let frontmatter = Frontmatter {
      includes: vec![
        "assert.js".to_string(),
        "assert.js".to_string(),
        "helper.js".to_string(),
      ],
      ..Frontmatter::default()
    };
    let body = "/*body*/\n";

    let source = assemble_source_with_mode(
      temp.path(),
      &frontmatter,
      Variant::NonStrict,
      body,
      HarnessMode::Host,
    )
    .unwrap();

    assert_eq!(source.match_indices("/*assert*/").count(), 1);
    assert_eq!(source.match_indices("/*helper*/").count(), 1);
    assert_eq!(source.match_indices("/*sta*/").count(), 0);

    let assert_pos = source.find("/*assert*/").unwrap();
    let helper_pos = source.find("/*helper*/").unwrap();
    let body_pos = source.find("/*body*/").unwrap();
    assert!(assert_pos < helper_pos);
    assert!(helper_pos < body_pos);
  }

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

  #[test]
  fn strict_host_mode_begins_with_use_strict_without_prepended_harness_sources() {
    let dir = tempdir().unwrap();
    let body = "/*body*/\n";

    let src = assemble_source_with_mode(
      dir.path(),
      &Frontmatter::default(),
      Variant::Strict,
      body,
      HarnessMode::Host,
    )
    .unwrap();

    assert_eq!(src, format!("'use strict';\n\n{body}"));
  }
}
