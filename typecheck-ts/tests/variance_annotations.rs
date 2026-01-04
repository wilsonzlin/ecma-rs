use diagnostics::TextRange;
use typecheck_ts::codes;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn accepts_covariant_type_parameter() {
  let source = "interface Producer<out T> { value: T }\n";
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();

  assert_eq!(diagnostics, Vec::new());
}

#[test]
fn rejects_out_type_parameter_used_contravariantly() {
  let source = "interface Bad<out T> { consume: (value: T) => void }\n";
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  let diag = diagnostics
    .iter()
    .find(|d| d.code.as_str() == codes::INVALID_VARIANCE_ANNOTATION.as_str())
    .unwrap_or_else(|| panic!("expected invalid variance diagnostic, got {diagnostics:?}"));

  let start = source.find("out T").expect("out T in source") as u32;
  let end = start + "out T".len() as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

#[test]
fn accepts_invariant_type_parameter_used_in_and_out() {
  let source = "interface Invariant<in out T> { produce: () => T; consume: (value: T) => void }\n";
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();

  assert_eq!(diagnostics, Vec::new());
}

#[test]
fn accepts_invariant_type_parameter_used_only_covariantly() {
  let source = "interface Wrong<in out T> { value: T }\n";
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert_eq!(diagnostics, Vec::new());
}
