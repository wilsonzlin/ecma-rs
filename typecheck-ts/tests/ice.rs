use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::{FatalError, FileId, Host, HostError, Program, Severity};

struct PanickingHost;

impl Host for PanickingHost {
  fn file_text(&self, _file: FileId) -> Result<Arc<str>, HostError> {
    panic!("forced invariant failure");
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

#[test]
fn internal_failure_surfaces_as_ice() {
  let program = Program::new(PanickingHost, vec![FileId(0)]);
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
