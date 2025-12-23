use crate::host::FileId;
use crate::host::FileKind;
use crate::host::Host;
use crate::host::Resolver;
use crate::CompilerOptions;
use crate::DiagnosticCode;
use crate::Program;
use crate::Severity;
use std::collections::HashMap;
use std::sync::Arc;

struct InMemoryHost {
  files: HashMap<FileId, (Arc<str>, FileKind)>,
  resolutions: HashMap<(FileId, String), FileId>,
  options: CompilerOptions,
}

impl InMemoryHost {
  fn new(options: CompilerOptions) -> Self {
    Self {
      files: HashMap::new(),
      resolutions: HashMap::new(),
      options,
    }
  }

  fn with_file(mut self, id: FileId, text: impl Into<Arc<str>>, kind: FileKind) -> Self {
    self.files.insert(id, (text.into(), kind));
    self
  }

  fn with_resolution(mut self, from: FileId, spec: impl Into<String>, to: FileId) -> Self {
    self.resolutions.insert((from, spec.into()), to);
    self
  }
}

impl Resolver for InMemoryHost {
  fn resolve(&self, from: FileId, spec: &str) -> Option<FileId> {
    self.resolutions.get(&(from, spec.to_string())).copied()
  }
}

impl Host for InMemoryHost {
  fn file_text(&self, file: FileId) -> Arc<str> {
    self
      .files
      .get(&file)
      .map(|(text, _)| text.clone())
      .unwrap_or_else(|| Arc::<str>::from(""))
  }

  fn file_kind(&self, file: FileId) -> FileKind {
    self
      .files
      .get(&file)
      .map(|(_, kind)| *kind)
      .unwrap_or(FileKind::Ts)
  }

  fn options(&self) -> CompilerOptions {
    self.options
  }
}

#[test]
fn module_graph_edges_are_sorted() {
  let host = InMemoryHost::new(CompilerOptions::default())
    .with_file(
      FileId(0),
      "import \"./b\";\nimport \"./a\";\n",
      FileKind::Ts,
    )
    .with_file(FileId(1), "", FileKind::Ts)
    .with_file(FileId(2), "", FileKind::Ts)
    .with_resolution(FileId(0), "./b", FileId(2))
    .with_resolution(FileId(0), "./a", FileId(1));

  let mut program = Program::new(Arc::new(host), vec![FileId(0)]);
  let graph = program.module_graph();

  let keys: Vec<_> = graph.files().collect();
  assert_eq!(keys, vec![FileId(0), FileId(1), FileId(2)]);

  let edges = graph.edges.get(&FileId(0)).expect("root present");
  let specs: Vec<_> = edges
    .iter()
    .map(|edge| edge.specifier.as_ref().to_string())
    .collect();
  assert_eq!(specs, vec!["./a", "./b"]);
  assert_eq!(edges[0].target, Some(FileId(1)));
  assert_eq!(edges[1].target, Some(FileId(2)));
}

#[test]
fn parse_errors_are_reported() {
  let host = InMemoryHost::new(CompilerOptions::default()).with_file(
    FileId(0),
    "function () {",
    FileKind::Ts,
  );

  let mut program = Program::new(Arc::new(host), vec![FileId(0)]);
  let diagnostics = program.check_parse_only();

  assert_eq!(diagnostics.len(), 1);
  let diagnostic = &diagnostics[0];
  assert_eq!(diagnostic.code, DiagnosticCode("PARSE"));
  assert_eq!(diagnostic.severity, Severity::Error);
  assert!(diagnostic.primary.is_some());
  assert!(!diagnostic.message.is_empty());
}
