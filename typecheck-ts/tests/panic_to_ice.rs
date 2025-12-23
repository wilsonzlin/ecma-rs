use std::collections::HashMap;
use std::sync::Arc;
use std::sync::Mutex;
use typecheck_ts::BodyId;
use typecheck_ts::Diagnostic;
use typecheck_ts::DiagnosticSeverity;
use typecheck_ts::FatalError;
use typecheck_ts::FileId;
use typecheck_ts::Host;
use typecheck_ts::HostError;
use typecheck_ts::Program;
use types_ts::RelationEngine;
use types_ts::RelationOutcome;
use types_ts::TypeId;
use types_ts::TypeKind;
use types_ts::TypeStore;

#[derive(Default)]
struct RecordingHost {
  files: Vec<FileId>,
  texts: HashMap<FileId, Arc<str>>,
  bodies: HashMap<FileId, Vec<BodyId>>,
  panic_body: Mutex<Option<(FileId, BodyId)>>,
  checked: Mutex<Vec<(FileId, BodyId)>>,
}

impl RecordingHost {
  fn with_file(mut self, file: FileId, text: &str, body_ids: Vec<BodyId>) -> Self {
    self.files.push(file);
    self.texts.insert(file, Arc::<str>::from(text));
    self.bodies.insert(file, body_ids);
    self
  }

  fn set_panic_body(&self, body: (FileId, BodyId)) {
    *self.panic_body.lock().unwrap() = Some(body);
  }

  fn checked(&self) -> Vec<(FileId, BodyId)> {
    self.checked.lock().unwrap().clone()
  }

  fn panic_requested(&self, file: FileId, body: BodyId) -> bool {
    *self.panic_body.lock().unwrap() == Some((file, body))
  }
}

impl Host for RecordingHost {
  fn root_files(&self) -> Vec<FileId> {
    self.files.clone()
  }

  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .texts
      .get(&file)
      .cloned()
      .ok_or(HostError::MissingFileText { file })
  }

  fn bodies_of(&self, file: FileId) -> Result<Vec<BodyId>, HostError> {
    self
      .bodies
      .get(&file)
      .cloned()
      .ok_or(HostError::MissingFileText { file })
  }

  fn check_body(
    &self,
    file: FileId,
    body: BodyId,
    diagnostics: &mut Vec<Diagnostic>,
  ) -> Result<(), FatalError> {
    self.checked.lock().unwrap().push((file, body));
    if self.panic_requested(file, body) {
      panic!("boom while checking {file}/{body}");
    }

    diagnostics.push(simple_note(format!("checked {file}/{body}")));
    Ok(())
  }
}

fn simple_note(message: String) -> Diagnostic {
  Diagnostic {
    code: "USER0001",
    message,
    severity: DiagnosticSeverity::Note,
    notes: vec![],
    context: vec![],
    #[cfg(feature = "capture-backtrace")]
    backtrace: None,
  }
}

#[test]
fn panic_is_converted_to_ice_diagnostic_and_execution_continues() {
  let host = Arc::new(
    RecordingHost::default()
      .with_file(FileId(0), "first", vec![BodyId(0)])
      .with_file(FileId(1), "second", vec![BodyId(0)]),
  );
  host.set_panic_body((FileId(0), BodyId(0)));

  let program = Program::new(host.clone());
  let report = program.check();

  assert!(report
    .diagnostics
    .iter()
    .any(|diag| diag.code == "ICE0001" && diag.message.contains("boom while checking")));

  // The second file/body should still have been visited even after the first panic.
  assert!(report
    .diagnostics
    .iter()
    .any(|diag| diag.message.contains("checked 1/0")));

  assert!(report.has_ice());
  assert!(host.checked().contains(&(FileId(1), BodyId(0))));
}

#[test]
fn host_errors_are_reported_as_diagnostics() {
  let host = Arc::new(RecordingHost {
    files: vec![FileId(99)],
    texts: HashMap::new(),
    bodies: HashMap::new(),
    panic_body: Mutex::new(None),
    checked: Mutex::new(Vec::new()),
  });

  let program = Program::new(host);
  let report = program.check();
  assert!(report
    .diagnostics
    .iter()
    .any(|diag| diag.code == "HOST0001"));
}

#[test]
fn relations_engine_handles_cyclic_types() {
  let mut store = TypeStore::new();
  let cycle = store.intern(TypeKind::Union(vec![TypeId::from_raw(0)]));
  let mut engine = RelationEngine::new(&store);
  let result = engine.is_assignable(cycle, cycle);
  assert_eq!(result.outcome, RelationOutcome::Unknown);
  assert!(result.ice_note.is_some());
}
