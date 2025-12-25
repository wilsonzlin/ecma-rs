use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{BodyId, FileId, Host, HostError, Program};

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileId, Arc<str>>,
}

impl MemoryHost {
  fn insert(&mut self, id: FileId, src: &str) {
    self.files.insert(id, Arc::from(src.to_string()));
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

fn body_of(program: &Program, file: FileId, name: &str) -> BodyId {
  let def = program
    .definitions_in_file(file)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some(name))
    .unwrap();
  program.body_of_def(def).unwrap()
}

#[test]
fn narrows_truthiness() {
  let src =
    "function f(x: string | null) { if (x) { return x; } else { return x; } return x; }";
  let mut host = MemoryHost::default();
  host.insert(FileId(0), src);
  let program = Program::new(host, vec![FileId(0)]);
  let body = body_of(&program, FileId(0), "f");

  let res = program.check_body(body);
  let ret_types = res.return_types();

  let then_ty = program.display_type(ret_types[0]).to_string();
  let else_ty = program.display_type(ret_types[1]).to_string();

  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "null");
}

#[test]
fn narrows_typeof_checks() {
  let src = "function f(x: string | number) { if (typeof x === \"string\") { return x; } else { return x; } }";
  let mut host = MemoryHost::default();
  host.insert(FileId(0), src);
  let program = Program::new(host, vec![FileId(0)]);
  let body = body_of(&program, FileId(0), "f");

  let res = program.check_body(body);
  let ret_types = res.return_types();
  let then_ty = program.display_type(ret_types[0]).to_string();
  let else_ty = program.display_type(ret_types[1]).to_string();

  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}

#[test]
fn narrows_discriminants() {
  let src = "function g(x: { kind: \"foo\", value: string } | { kind: \"bar\", value: number }) { if (x.kind === \"foo\") { return x.value; } else { return x.value; } }";
  let mut host = MemoryHost::default();
  host.insert(FileId(0), src);
  let program = Program::new(host, vec![FileId(0)]);
  let body = body_of(&program, FileId(0), "g");

  let res = program.check_body(body);
  let ret_types = res.return_types();
  let then_ty = program.display_type(ret_types[0]).to_string();
  let else_ty = program.display_type(ret_types[1]).to_string();

  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}

#[test]
fn user_defined_type_guards() {
  let src = r#"
function isStr(x: string | number): x is string {
  return typeof x === "string";
}
function test(x: string | number) {
  if (isStr(x)) {
    return x;
  }
  return x;
}
"#;
  let mut host = MemoryHost::default();
  host.insert(FileId(0), src);
  let program = Program::new(host, vec![FileId(0)]);
  let body = body_of(&program, FileId(0), "test");

  let res = program.check_body(body);
  let ret_types = res.return_types();

  let then_ty = program.display_type(ret_types[0]).to_string();
  let else_ty = program.display_type(ret_types[1]).to_string();

  assert_eq!(then_ty, "string");
  assert_eq!(else_ty, "number");
}

#[test]
fn assertion_functions_narrow() {
  let src = r#"
function assertStr(x: string | number): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("bad");
  }
}
function useIt(val: string | number) {
  assertStr(val);
  return val;
}
"#;
  let mut host = MemoryHost::default();
  host.insert(FileId(0), src);
  let program = Program::new(host, vec![FileId(0)]);
  let body = body_of(&program, FileId(0), "useIt");

  let res = program.check_body(body);
  let ty = program.display_type(res.return_types()[0]).to_string();
  assert_eq!(ty, "string");
}
