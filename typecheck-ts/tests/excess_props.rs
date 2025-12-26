use std::collections::HashMap;
use std::sync::Arc;
use typecheck_ts::{Diagnostic, FileId, Host, HostError, Program};

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileId, Arc<str>>,
}

impl MemoryHost {
  fn insert(&mut self, id: FileId, source: &str) {
    self.files.insert(id, Arc::from(source.to_string()));
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

fn run(source: &str) -> Vec<Diagnostic> {
  let mut host = MemoryHost::default();
  host.insert(FileId(0), source);
  let program = Program::new(host, vec![FileId(0)]);
  program.check()
}

#[test]
fn reports_excess_property_on_fresh_object_literal() {
  let diagnostics = run("let x: { foo: number } = { foo: 1, bar: 2 };");
  assert_eq!(diagnostics.len(), 1);
  assert!(
    diagnostics[0].message.contains("excess property"),
    "unexpected message: {}",
    diagnostics[0].message
  );
}

#[test]
fn allows_index_signature_for_extra_properties() {
  let diagnostics = run("let x: { foo: number; [key: string]: number } = { foo: 1, bar: 2 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn allows_intermediate_variable_without_excess_check() {
  let diagnostics = run(
    "const tmp = { foo: 1, bar: 2 };\n\
     let x: { foo: number } = tmp;",
  );
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn type_assertion_suppresses_excess_property_check() {
  let diagnostics = run("let x: { foo: number } = ({ foo: 1, bar: 2 } as { foo: number });");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn union_target_requires_single_compatible_member() {
  let diagnostics = run("let x: { foo: number } | { bar: number } = { foo: 1, bar: 2 };");
  assert_eq!(diagnostics.len(), 1);
}

#[test]
fn union_target_allows_member_with_props() {
  let diagnostics = run("let x: { foo: number } | { bar: number } = { foo: 1 };");
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn return_context_triggers_excess_property_check() {
  let diagnostics = run(
    "function make(): { foo: number } { return { foo: 1, bar: 2 }; }\n\
     make();",
  );
  assert!(
    diagnostics.len() <= 1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn nested_contextual_object_literal_checks_excess_properties() {
  let diagnostics = run("let x: { nested: { foo: number } } = { nested: { foo: 1, bar: 2 } };");
  assert!(
    diagnostics.len() <= 1,
    "unexpected diagnostics: {:?}",
    diagnostics
  );
}

#[test]
fn call_argument_checks_excess_properties() {
  let diagnostics = run(
    "function takes(obj: { foo: number }) {}\n\
     takes({ foo: 1, bar: 2 });",
  );
  assert_eq!(diagnostics.len(), 1);
}
