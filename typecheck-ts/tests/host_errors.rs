use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::{FatalError, FileId, Host, HostError, Program};

struct MissingHost;

impl Host for MissingHost {
  fn file_text(&self, _file: FileId) -> Result<Arc<str>, HostError> {
    Err(HostError::new("missing file text"))
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

#[test]
fn missing_file_is_fatal_host_error() {
  let program = Program::new(MissingHost, vec![FileId(0)]);
  match program.check_fallible() {
    Err(FatalError::Host(err)) => assert_eq!(err.to_string(), "missing file text"),
    other => panic!("expected fatal host error, got {other:?}"),
  }

  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1);
  assert_eq!(diagnostics[0].code.as_str(), codes::HOST_ERROR.as_str());
  assert_eq!(diagnostics[0].notes.len(), 1);
  assert!(
    diagnostics[0].notes[0].contains("no source span available"),
    "expected host error note explaining missing span"
  );
}
