use proptest::prelude::*;
use std::sync::Arc;
use typecheck_ts::{BodyId, Diagnostic, DiagnosticSeverity, FatalError, FileId, Host, Program};

fn arb_source() -> impl Strategy<Value = String> {
  prop::collection::vec(any::<char>(), 0..96).prop_map(|chars| chars.into_iter().collect())
}

#[derive(Clone)]
struct StubHost {
  text: Arc<str>,
}

impl Host for StubHost {
  fn root_files(&self) -> Vec<FileId> {
    vec![FileId(0)]
  }

  fn file_text(&self, _file: FileId) -> Result<Arc<str>, typecheck_ts::HostError> {
    Ok(self.text.clone())
  }

  fn bodies_of(&self, _file: FileId) -> Result<Vec<BodyId>, typecheck_ts::HostError> {
    Ok(vec![BodyId(0)])
  }

  fn check_body(
    &self,
    _file: FileId,
    _body: BodyId,
    diagnostics: &mut Vec<Diagnostic>,
  ) -> Result<(), FatalError> {
    diagnostics.push(Diagnostic {
      code: "NOTE",
      message: "checked".into(),
      severity: DiagnosticSeverity::Note,
      notes: vec![],
      context: vec![],
      #[cfg(feature = "capture-backtrace")]
      backtrace: None,
    });
    Ok(())
  }
}

proptest! {
  #[test]
  fn program_check_never_panics(src in arb_source()) {
    let host = Arc::new(StubHost { text: Arc::<str>::from(src) });
    let program = Program::new(host);
    let _report = program.check();
  }
}
