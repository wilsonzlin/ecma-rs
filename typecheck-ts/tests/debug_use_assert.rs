use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{BodyId, ExprId, FileId, FileKey, Host, HostError, Program};

#[derive(Clone)]
struct SimpleHost {
  files: HashMap<FileKey, Arc<str>>,
}

impl Host for SimpleHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new("missing file".to_string()))
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }
}

#[test]
fn debug_use_assert_return_type() {
  let path = FileKey::new("narrowing.ts".to_string());
  let source = std::fs::read_to_string(
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("tests/litmus/narrowing_patterns/main.ts"),
  )
  .expect("read fixture");
  let host = SimpleHost {
    files: HashMap::from([(path.clone(), Arc::from(source))]),
  };
  let program = Program::new(host, vec![path.clone()]);
  let file_id: FileId = program.file_id(&path).unwrap();
  let defs = program.definitions_in_file(file_id);
  let assert_number = defs
    .iter()
    .copied()
    .find(|d| program.def_name(*d).as_deref() == Some("assertNumber"))
    .expect("assertNumber def");
  let assert_ty = program
    .display_type(program.type_of_def(assert_number))
    .to_string();
  eprintln!("assertNumber type {assert_ty}");
  let use_assert = defs
    .iter()
    .copied()
    .find(|d| program.def_name(*d).as_deref() == Some("useAssert"))
    .expect("useAssert def");
  let body: BodyId = program.body_of_def(use_assert).unwrap();
  let result = program.check_body(body);
  let rendered: Vec<_> = result
    .return_types()
    .iter()
    .map(|ty| program.display_type(*ty).to_string())
    .collect();
  eprintln!("return_types {:?}", rendered);
  let def_ty = program
    .display_type(program.type_of_def(use_assert))
    .to_string();
  eprintln!("def type {def_ty}");
  for (idx, span) in result.expr_spans().iter().enumerate() {
    let desc = result
      .expr_type(ExprId(idx as u32))
      .map(|ty| program.display_type(ty).to_string())
      .unwrap_or_else(|| "<none>".to_string());
    eprintln!("{idx}: {:?} -> {}", span, desc);
  }
}
