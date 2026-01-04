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

#[test]
fn invariant_type_arguments_are_checked_during_assignment() {
  let source = r#"
interface Animal { kind: "animal" }
interface Dog extends Animal { bark(): void }
interface Box<in out T> { readonly value: T }
const dogBox: Box<Dog> = { value: { kind: "animal", bark() {} } };
const animalBox: Box<Animal> = dogBox;
"#;
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id");
  let diagnostics = program.check();

  let diag = diagnostics
    .iter()
    .find(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .unwrap_or_else(|| panic!("expected type mismatch diagnostic, got {diagnostics:?}"));

  let start = source.find("animalBox").expect("animalBox in source") as u32;
  let end = start + "animalBox".len() as u32;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range.start, start);
  assert!(
    diag.primary.range.end == end || diag.primary.range.end == end + 1,
    "expected diagnostic span to cover `animalBox`, got {:?}",
    diag.primary.range
  );
  let span_text = &source[start as usize..diag.primary.range.end as usize];
  assert!(
    span_text.starts_with("animalBox"),
    "expected diagnostic span to start with `animalBox`, got {span_text:?}"
  );
}
