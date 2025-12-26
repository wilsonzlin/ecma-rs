use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::{FatalError, FileKey, Host, HostError, Program, Severity};

struct PanickingHost;

impl Host for PanickingHost {
  fn file_text(&self, _file: &FileKey) -> Result<Arc<str>, HostError> {
    panic!("forced invariant failure");
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }
}

#[test]
fn internal_failure_surfaces_as_ice() {
  let program = Program::new(PanickingHost, vec![FileKey::new("input.ts")]);
  match program.check_fallible() {
    Err(FatalError::Ice(_)) => {}
    other => panic!("expected fatal ICE, got {other:?}"),
  }

  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1);
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::INTERNAL_COMPILER_ERROR.as_str());
  assert_eq!(diag.severity, Severity::Error);
  assert!(
    diag
      .notes
      .iter()
      .any(|note| note.contains("please file an issue")),
    "ICE diagnostics should include a help note"
  );
}
