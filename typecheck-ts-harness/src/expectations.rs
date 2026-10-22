//! Expectation manifests and `--fail-on` policy.
//!
//! Owned by [`conformance_harness`]; this module re-exports the shared types and
//! adapts I/O errors into [`crate::HarnessError`].

pub use conformance_harness::{AppliedExpectation, Expectation, ExpectationKind, FailOn};

use crate::HarnessError;
use conformance_harness::Expectations as SharedExpectations;
use std::path::Path;

/// Manifest of expected outcomes (`pass`/`skip`/`xfail`/`flaky`).
///
/// Thin wrapper so manifest parse failures surface as [`HarnessError::Manifest`].
#[derive(Debug, Clone, Default)]
pub struct Expectations {
  inner: SharedExpectations,
}

impl Expectations {
  pub fn empty() -> Self {
    Self {
      inner: SharedExpectations::empty(),
    }
  }

  pub fn from_path(path: &Path) -> Result<Self, HarnessError> {
    SharedExpectations::from_path(path)
      .map(|inner| Self { inner })
      .map_err(|err| HarnessError::Manifest(err.to_string()))
  }

  pub fn from_str(raw: &str) -> Result<Self, HarnessError> {
    SharedExpectations::from_str(raw)
      .map(|inner| Self { inner })
      .map_err(|err| HarnessError::Manifest(err.to_string()))
  }

  pub fn lookup(&self, id: &str) -> AppliedExpectation {
    self.inner.lookup(id)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::path::Path;

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
id = "a/b/c.ts"
status = "skip"
    "#;

    let expectations = Expectations::from_str(manifest).expect("manifest parsed");
    let applied = expectations.lookup("a/b/c.ts");
    assert_eq!(applied.expectation.kind, ExpectationKind::Skip);
  }

  #[test]
  fn manifest_uses_first_match_within_priority() {
    let manifest = r#"
[[expectations]]
glob = "cases/**"
status = "xfail"
reason = "first"

[[expectations]]
glob = "cases/**"
status = "flaky"
reason = "second"
    "#;

    let expectations = Expectations::from_str(manifest).expect("manifest parsed");
    let applied = expectations.lookup("cases/sample.ts");
    assert_eq!(applied.expectation.kind, ExpectationKind::Xfail);
    assert_eq!(applied.expectation.reason.as_deref(), Some("first"));
  }

  #[test]
  fn manifest_loads_from_fixture_path() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/conformance_manifest.toml");
    let expectations = Expectations::from_path(&path).expect("manifest parsed from file");

    // The fixture is the live conformance manifest (id-keyed xfails only);
    // look up two entries that exist today.
    let xfail = expectations.lookup("salsa/chainedPrototypeAssignment.ts");
    assert_eq!(xfail.expectation.kind, ExpectationKind::Xfail);

    let other = expectations.lookup("Symbols/ES5SymbolProperty1.ts");
    assert_eq!(other.expectation.kind, ExpectationKind::Xfail);
  }
}
