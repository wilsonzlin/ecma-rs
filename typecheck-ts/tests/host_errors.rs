use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind};
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

#[derive(Clone)]
struct InconsistentHost {
  main: FileKey,
  dep: FileKey,
  main_text: Arc<str>,
}

impl Default for InconsistentHost {
  fn default() -> Self {
    InconsistentHost {
      main: FileKey::new("main.ts"),
      dep: FileKey::new("dep.ts"),
      main_text: Arc::from("import \"./dep\";\nexport const x = 1;\n"),
    }
  }
}

impl Host for InconsistentHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    if file.as_str() == self.main.as_str() {
      Ok(Arc::clone(&self.main_text))
    } else {
      Err(HostError::new("missing dependency file text"))
    }
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    if from.as_str() == self.main.as_str() && specifier == "./dep" {
      Some(self.dep.clone())
    } else {
      None
    }
  }

  fn compiler_options(&self) -> CompilerOptions {
    CompilerOptions {
      no_default_lib: true,
      ..CompilerOptions::default()
    }
  }

  fn file_kind(&self, _file: &FileKey) -> FileKind {
    FileKind::Ts
  }
}

#[test]
fn missing_dependency_is_reported_as_unresolved_module() {
  let host = InconsistentHost::default();
  let root = host.main.clone();
  let program = Program::new(host, vec![root]);

  let diagnostics = program
    .check_fallible()
    .expect("missing import should not surface as a fatal host error");

  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::UNRESOLVED_MODULE.as_str()),
    "expected unresolved module diagnostics, got {diagnostics:?}"
  );
  assert!(
    diagnostics
      .iter()
      .all(|diag| diag.code.as_str() != codes::HOST_ERROR.as_str()),
    "missing dependency should not be treated as host error: {diagnostics:?}"
  );
  assert!(
    diagnostics
      .iter()
      .all(|diag| !diag.code.as_str().starts_with("ICE")),
    "missing dependency produced ICE diagnostics: {diagnostics:?}"
  );
}
