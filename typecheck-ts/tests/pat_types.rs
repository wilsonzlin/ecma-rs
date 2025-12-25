use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{BodyId, FileId, Host, HostError, PatId, Program};

#[derive(Clone, Default)]
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
      .ok_or_else(|| HostError::new(format!("missing file {:?}", file)))
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

fn body_for(program: &mut Program, file: FileId, name: &str) -> BodyId {
  let def = program
    .definitions_in_file(file)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some(name))
    .expect("definition present");
  program.body_of_def(def).expect("body present")
}

#[test]
fn records_pattern_types_for_params_and_vars() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(0),
    "function add(a: number, b: number) { const c = a + b; return c; }",
  );
  let mut program = Program::new(host, vec![FileId(0)]);
  let body = body_for(&mut program, FileId(0), "add");
  let result = program.check_body(body);

  let a_type = result
    .pat_type(PatId(0))
    .expect("first param pat type present");
  let b_type = result
    .pat_type(PatId(1))
    .expect("second param pat type present");
  let c_type = result
    .pat_type(PatId(2))
    .expect("variable pat type present");

  assert_eq!(program.display_type(a_type).to_string(), "number");
  assert_eq!(program.display_type(b_type).to_string(), "number");
  assert_eq!(program.display_type(c_type).to_string(), "number");
}
