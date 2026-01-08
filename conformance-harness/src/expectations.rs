use anyhow::{anyhow, bail, Context, Result};
use globset::Glob;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::path::Path;

/// The expected outcome for a test case, as described in a manifest.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExpectationKind {
  Pass,
  Skip,
  Xfail,
  Flaky,
}

impl Default for ExpectationKind {
  fn default() -> Self {
    ExpectationKind::Pass
  }
}

/// An expectation entry (status + optional metadata).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct Expectation {
  #[serde(default)]
  pub kind: ExpectationKind,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub reason: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub tracking_issue: Option<String>,
}

/// The expectation after applying a manifest lookup.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AppliedExpectation {
  pub expectation: Expectation,
  pub from_manifest: bool,
}

impl AppliedExpectation {
  /// Returns whether a test with the given `mismatched` status was expected.
  ///
  /// - `pass`: expected when there is no mismatch
  /// - `skip`: always expected
  /// - `xfail`/`flaky`: expected when there is a mismatch
  pub fn matches(&self, mismatched: bool) -> bool {
    match self.expectation.kind {
      ExpectationKind::Pass => !mismatched,
      ExpectationKind::Skip => true,
      ExpectationKind::Xfail | ExpectationKind::Flaky => mismatched,
    }
  }

  pub fn covers_mismatch(&self) -> bool {
    matches!(
      self.expectation.kind,
      ExpectationKind::Skip | ExpectationKind::Xfail | ExpectationKind::Flaky
    )
  }

  pub fn is_flaky(&self) -> bool {
    self.expectation.kind == ExpectationKind::Flaky
  }
}

/// A parsed manifest of expectations.
///
/// Precedence is deterministic and intentionally ignores manifest entry order:
/// `id` (exact) > `glob` > `regex`.
#[derive(Debug, Clone, Default)]
pub struct Expectations {
  exact: Vec<Entry>,
  globs: Vec<Entry>,
  regexes: Vec<Entry>,
}

impl Expectations {
  pub fn empty() -> Self {
    Self::default()
  }

  pub fn from_path(path: &Path) -> Result<Self> {
    let raw = std::fs::read_to_string(path)
      .with_context(|| format!("read manifest {}", path.display()))?;
    Self::from_str(&raw).map_err(|err| anyhow!("{}: {err}", path.display()))
  }

  pub fn from_str(raw: &str) -> Result<Self> {
    let manifest = match toml::from_str::<RawManifest>(raw) {
      Ok(manifest) => manifest,
      Err(toml_err) => serde_json::from_str::<RawManifest>(raw).map_err(|json_err| {
        anyhow!("failed to parse manifest as TOML ({toml_err}) or JSON ({json_err})")
      })?,
    };

    Self::from_manifest(manifest)
  }

  pub fn lookup(&self, id: &str) -> AppliedExpectation {
    if let Some(found) = self.lookup_in(&self.exact, id) {
      return found;
    }

    if let Some(found) = self.lookup_in(&self.globs, id) {
      return found;
    }

    if let Some(found) = self.lookup_in(&self.regexes, id) {
      return found;
    }

    AppliedExpectation::default()
  }

  fn lookup_in(&self, entries: &[Entry], id: &str) -> Option<AppliedExpectation> {
    for entry in entries {
      if entry.matches(id) {
        return Some(AppliedExpectation {
          expectation: entry.expectation.clone(),
          from_manifest: true,
        });
      }
    }

    None
  }

  fn from_manifest(manifest: RawManifest) -> Result<Self> {
    let mut expectations = Expectations::default();
    for entry in manifest.expectations {
      let matcher = entry.matcher()?;
      let expectation = Expectation {
        kind: entry
          .status
          .ok_or_else(|| anyhow!("manifest entry missing `status`"))?,
        reason: entry.reason,
        tracking_issue: entry.tracking_issue,
      };

      match matcher {
        Matcher::Exact(pattern) => expectations.exact.push(Entry {
          matcher: Matcher::Exact(pattern),
          expectation,
        }),
        Matcher::Glob(pattern) => expectations.globs.push(Entry {
          matcher: Matcher::Glob(pattern),
          expectation,
        }),
        Matcher::Regex(pattern) => expectations.regexes.push(Entry {
          matcher: Matcher::Regex(pattern),
          expectation,
        }),
      }
    }

    Ok(expectations)
  }
}

#[derive(Debug, Clone)]
struct Entry {
  matcher: Matcher,
  expectation: Expectation,
}

impl Entry {
  fn matches(&self, id: &str) -> bool {
    self.matcher.matches(id)
  }
}

#[derive(Debug, Clone)]
enum Matcher {
  Exact(String),
  Glob(globset::GlobMatcher),
  Regex(Regex),
}

impl Matcher {
  fn matches(&self, id: &str) -> bool {
    match self {
      Matcher::Exact(pattern) => pattern == id,
      Matcher::Glob(glob) => glob.is_match(id),
      Matcher::Regex(re) => re.is_match(id),
    }
  }
}

#[derive(Debug, Clone, Deserialize)]
struct RawManifest {
  #[serde(default)]
  expectations: Vec<RawEntry>,
}

#[derive(Debug, Clone, Deserialize)]
struct RawEntry {
  id: Option<String>,
  glob: Option<String>,
  regex: Option<String>,
  #[serde(alias = "expectation")]
  status: Option<ExpectationKind>,
  reason: Option<String>,
  tracking_issue: Option<String>,
}

impl RawEntry {
  fn matcher(&self) -> Result<Matcher> {
    let mut seen = 0;
    if self.id.is_some() {
      seen += 1;
    }
    if self.glob.is_some() {
      seen += 1;
    }
    if self.regex.is_some() {
      seen += 1;
    }

    if seen == 0 {
      bail!("manifest entry missing `id`/`glob`/`regex`");
    }

    if seen > 1 {
      bail!("manifest entry must specify exactly one of `id`/`glob`/`regex`");
    }

    if let Some(id) = &self.id {
      return Ok(Matcher::Exact(id.clone()));
    }

    if let Some(glob) = &self.glob {
      let compiled = Glob::new(glob)
        .map_err(|err| anyhow!("invalid glob '{glob}': {err}"))?
        .compile_matcher();
      return Ok(Matcher::Glob(compiled));
    }

    let regex = self.regex.as_ref().expect("validated regex presence");
    let compiled = Regex::new(regex).map_err(|err| anyhow!("invalid regex '{regex}': {err}"))?;

    Ok(Matcher::Regex(compiled))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn manifest_prefers_exact_then_glob_then_regex() {
    let manifest = r#"
[[expectations]]
glob = "a/**"
status = "xfail"

[[expectations]]
regex = "a/.*"
status = "flaky"

[[expectations]]
id = "a/b/c.js"
status = "skip"
    "#;

    let expectations = Expectations::from_str(manifest).expect("manifest parsed");
    let applied = expectations.lookup("a/b/c.js");
    assert_eq!(applied.expectation.kind, ExpectationKind::Skip);
  }

  #[test]
  fn manifest_supports_json() {
    let manifest = r#"
{
  "expectations": [
    { "glob": "a/**", "status": "xfail" }
  ]
}
    "#;
    let expectations = Expectations::from_str(manifest).expect("manifest parsed");
    let applied = expectations.lookup("a/b/c.js");
    assert_eq!(applied.expectation.kind, ExpectationKind::Xfail);
  }
}
