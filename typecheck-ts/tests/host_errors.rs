use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::{FatalError, FileKey, Host, HostError, Program};

struct MissingHost;

impl Host for MissingHost {
  fn file_text(&self, _file: &FileKey) -> Result<Arc<str>, HostError> {
    Err(HostError::new("missing file text"))
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }
}

#[test]
fn missing_file_is_fatal_host_error() {
  let program = Program::new(MissingHost, vec![FileKey::new("missing.ts")]);
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
