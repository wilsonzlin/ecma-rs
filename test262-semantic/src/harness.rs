use crate::frontmatter::Frontmatter;
use crate::report::Variant;
use anyhow::{bail, Context, Result};
use clap::ValueEnum;
use std::collections::HashSet;
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
#[clap(rename_all = "lowercase")]
pub enum HarnessMode {
  /// Prepend the standard test262 harness (`assert.js`, `sta.js`) plus any additional frontmatter
  /// includes.
  Test262,
  /// Prepend only the harness files explicitly listed in test frontmatter (`includes`).
  Includes,
  /// Prepend no harness files at all.
  None,
}

pub fn assemble_source(
  test262_dir: &Path,
  frontmatter: &Frontmatter,
  variant: Variant,
  body: &str,
  harness_mode: HarnessMode,
) -> Result<String> {
  let mut out = String::new();
  // Ensure strict-mode variants actually run in strict mode: the directive must appear before any
  // other statements (including harness includes), otherwise the directive prologue is already
  // terminated.
  if variant == Variant::Strict {
    out.push_str("'use strict';\n\n");
  }

  // In `none` mode, do not touch the filesystem at all.
  if harness_mode == HarnessMode::None {
    out.push_str(body);
    return Ok(out);
  }

  let harness_dir = test262_dir.join("harness");
  if !harness_dir.is_dir() {
    bail!(
      "test262 harness directory not found at {} (expected a tc39/test262 checkout)",
      harness_dir.display()
    );
  }

  let mut includes: Vec<String> = Vec::new();
  let mut seen: HashSet<String> = HashSet::new();
  let mut maybe_push = |name: &str| {
    let name = name.to_string();
    if seen.insert(name.clone()) {
      includes.push(name);
    }
  };

  match harness_mode {
    HarnessMode::Test262 => {
      maybe_push("assert.js");
      maybe_push("sta.js");
      for include in &frontmatter.includes {
        maybe_push(include);
      }
    }
    HarnessMode::Includes => {
      for include in &frontmatter.includes {
        maybe_push(include);
      }
    }
    HarnessMode::None => {}
  }

  for include in includes {
    let path = harness_dir.join(&include);
    let content = std::fs::read_to_string(&path).with_context(|| format!("read {}", path.display()))?;
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
  fn test262_mode_includes_default_harness_and_dedupes_frontmatter() {
    let temp = setup_test262_dir();
    let frontmatter = Frontmatter {
      // `assert.js` appears both as an implicit default include and explicitly in frontmatter; it
      // should appear only once.
      includes: vec!["assert.js".to_string(), "helper.js".to_string()],
      ..Frontmatter::default()
    };

    let body = "/*body*/\n";
    let source = assemble_source(
      temp.path(),
      &frontmatter,
      Variant::NonStrict,
      body,
      HarnessMode::Test262,
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
  fn includes_mode_omits_default_harness_when_not_explicitly_included() {
    let temp = setup_test262_dir();
    let frontmatter = Frontmatter::default();
    let body = "/*body*/\n";

    let source = assemble_source(
      temp.path(),
      &frontmatter,
      Variant::NonStrict,
      body,
      HarnessMode::Includes,
    )
    .unwrap();

    assert_eq!(source, body);
  }

  #[test]
  fn includes_mode_includes_frontmatter_includes_and_dedupes() {
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

    let source = assemble_source(
      temp.path(),
      &frontmatter,
      Variant::NonStrict,
      body,
      HarnessMode::Includes,
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

    // Intentionally include non-directive statements so the directive prologue would be terminated
    // if we appended 'use strict' after includes.
    fs::write(harness_dir.join("assert.js"), "var ASSERT_LOADED = true;").unwrap();
    fs::write(harness_dir.join("sta.js"), "var STA_LOADED = true;").unwrap();

    let src = assemble_source(
      dir.path(),
      &Frontmatter::default(),
      Variant::Strict,
      "body();",
      HarnessMode::Test262,
    )
    .unwrap();
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
      HarnessMode::Test262,
    )
    .unwrap();
    assert!(
      !src.starts_with("'use strict';"),
      "non-strict source should not begin with directive, got: {src:?}"
    );
  }

  #[test]
  fn none_mode_does_not_require_harness_dir_and_still_inserts_use_strict() {
    let dir = tempdir().unwrap();
    let frontmatter = Frontmatter {
      // If `none` mode attempted to read includes, this would error because the harness directory
      // does not exist.
      includes: vec!["assert.js".to_string(), "missing.js".to_string()],
      ..Frontmatter::default()
    };

    let src = assemble_source(
      dir.path(),
      &frontmatter,
      Variant::Strict,
      "body();",
      HarnessMode::None,
    )
    .unwrap();
    assert_eq!(src, "'use strict';\n\nbody();");
  }

  #[test]
  fn includes_mode_requires_harness_dir() {
    let dir = tempdir().unwrap();
    let frontmatter = Frontmatter {
      includes: vec!["helper.js".to_string()],
      ..Frontmatter::default()
    };

    let err = assemble_source(
      dir.path(),
      &frontmatter,
      Variant::NonStrict,
      "body();",
      HarnessMode::Includes,
    )
    .unwrap_err();
    assert!(
      err.to_string().contains("test262 harness directory not found"),
      "expected missing harness directory error, got: {err:#}"
    );
  }
}
