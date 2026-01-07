use diagnostics::TextRange;
use std::sync::Arc;
use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn explicit_type_arguments_affect_call_checking() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source = "function f<T>(x: T): T { return x; }\nf<string>(1);\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected a single diagnostic, got {diagnostics:?}"
  );
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::ARGUMENT_TYPE_MISMATCH.as_str());

  let start = source.find('1').expect("numeric literal present") as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, start + 1));
}

#[test]
fn instantiation_expression_without_call_affects_later_calls() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source = "function f<T>(x: T): T { return x; }\nconst g = f<string>;\ng(1);\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected a single diagnostic, got {diagnostics:?}"
  );
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::ARGUMENT_TYPE_MISMATCH.as_str());

  let start = source.rfind('1').expect("numeric literal present") as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, start + 1));
}

#[test]
fn reports_too_many_type_arguments() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source = "function f<T>(x: T): T { return x; }\nf<string, number>(\"x\");\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected a single diagnostic, got {diagnostics:?}"
  );
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::WRONG_TYPE_ARGUMENT_COUNT.as_str());

  let needle = "f<string, number>";
  let start = source.find(needle).expect("type arguments present") as u32;
  let end = start + needle.len() as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

#[test]
fn reports_constraint_violation_for_explicit_type_arguments() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source =
    "function c<T extends string>(x: T): T { return x; }\nc<number>(\"x\");\n";
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();

  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::TYPE_ARGUMENT_CONSTRAINT_VIOLATION.as_str()),
    "expected a TS2344 constraint diagnostic, got {diagnostics:?}"
  );
}

