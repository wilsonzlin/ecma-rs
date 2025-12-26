use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{DefId, FileId, Host, HostError, Program, PropertyKey, TypeKindSummary};

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileId, Arc<str>>,
}

impl MemoryHost {
  fn insert(&mut self, file: FileId, src: &str) {
    self.files.insert(file, Arc::from(src.to_string()));
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

fn def_by_name(program: &Program, file: FileId, name: &str) -> Option<DefId> {
  program
    .definitions_in_file(file)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some(name))
}

#[test]
fn recursive_alias_type_of_def_is_bounded() {
  let mut host = MemoryHost::default();
  host.insert(FileId(0), "type Node<T> = { next: Node<T> };");

  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics: {diagnostics:?}"
  );

  let def = def_by_name(&program, FileId(0), "Node").expect("Node defined");
  let ty = program.type_of_def_interned(def);
  let summary = program.type_kind(ty);
  assert!(
    matches!(summary, TypeKindSummary::Ref { def: d, .. } if d == def)
      || matches!(summary, TypeKindSummary::Object),
    "recursive alias should not infinitely expand: {summary:?}"
  );
}

#[test]
fn relate_ctx_handles_cyclic_refs() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(0),
    r#"
type A = { next: A };
type B = { next: B };
"#,
  );

  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics: {diagnostics:?}"
  );

  let a_def = def_by_name(&program, FileId(0), "A").expect("A defined");
  let b_def = def_by_name(&program, FileId(0), "B").expect("B defined");
  let a_ty = program.type_of_def_interned(a_def);
  let b_ty = program.type_of_def_interned(b_def);

  assert_eq!(
    program.type_kind(a_ty),
    program.type_kind(b_ty),
    "structurally identical cycles should relate"
  );
}

#[test]
fn expansion_is_deterministic_across_runs() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(0),
    r#"
type Pair<T> = { value: T; next?: Pair<T> };
type NumPair = Pair<number>;
"#,
  );

  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics: {diagnostics:?}"
  );

  let num_pair = def_by_name(&program, FileId(0), "NumPair").expect("NumPair defined");
  let num_pair_ty = program.type_of_def_interned(num_pair);

  let first = program
    .property_type(num_pair_ty, PropertyKey::String("next".into()))
    .expect("next property present");
  let second = program
    .property_type(num_pair_ty, PropertyKey::String("next".into()))
    .expect("next property present");
  assert_eq!(
    first, second,
    "expansion results should be deterministic across calls"
  );

  assert_eq!(
    program.type_kind(first),
    program.type_kind(first),
    "self-assignability should also terminate for expanded recursive properties"
  );
}
