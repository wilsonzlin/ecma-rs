use diagnostics::{FileId, Label, Span, TextRange};
use typecheck_ts::codes;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn normalize_sorts_diagnostics_and_labels() {
  let mut later =
    codes::TYPE_MISMATCH.error("later span", Span::new(FileId(1), TextRange::new(5, 6)));
  later.push_label(Label::secondary(
    Span::new(FileId(1), TextRange::new(0, 1)),
    "secondary",
  ));
  later.push_label(Label::primary(
    Span::new(FileId(1), TextRange::new(5, 6)),
    "primary",
  ));

  let mut earlier =
    codes::UNKNOWN_IDENTIFIER.error("earlier span", Span::new(FileId(0), TextRange::new(10, 11)));
  earlier.push_label(Label::secondary(
    Span::new(FileId(0), TextRange::new(2, 3)),
    "later secondary",
  ));
  earlier.push_label(Label::secondary(
    Span::new(FileId(0), TextRange::new(0, 1)),
    "earlier secondary",
  ));

  let mut diagnostics = vec![later, earlier];
  codes::normalize_diagnostics(&mut diagnostics);

  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::UNKNOWN_IDENTIFIER.as_str()
  );
  assert_eq!(diagnostics[1].code.as_str(), codes::TYPE_MISMATCH.as_str());

  let first_labels = &diagnostics[0].labels;
  assert_eq!(first_labels.len(), 2);
  assert_eq!(first_labels[0].span.range.start, 0);
  assert_eq!(first_labels[1].span.range.start, 2);

  let second_labels = &diagnostics[1].labels;
  assert!(!second_labels.is_empty());
  assert!(second_labels[0].is_primary);
}

#[test]
fn repeated_checks_are_stable() {
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), "const value: number = 'not a number';");

  let program = Program::new(host, vec![key]);
  let first = program.check();
  let second = program.check();

  assert_eq!(first, second);
}

#[test]
fn repeated_checks_with_multiple_files_are_identical() {
  let mut host = MemoryHost::new();
  let first = FileKey::new("first.ts");
  let second = FileKey::new("second.ts");
  host.insert(first.clone(), "const value: number = 'still wrong';");
  host.insert(second.clone(), "let ;");

  let program = Program::new(host, vec![first, second]);
  let first_run = program.check();
  let second_run = program.check();

  assert_eq!(first_run, second_run);
}

#[test]
fn diagnostics_remain_stable_after_body_check() {
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(
    key.clone(),
    "function f(): number { return 'not a number'; }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let file_id = program.file_id(&key).expect("file id available");
  let body = program
    .bodies_in_file(file_id)
    .into_iter()
    .next()
    .expect("body available");
  let _ = program.check_body(body);

  let first = program.check();
  let second = program.check();

  assert!(!first.is_empty());
  assert_eq!(first, second);
}

#[test]
fn program_check_remains_stable_with_unresolved_imports() {
  let mut host = MemoryHost::new();
  let key = FileKey::new("index.ts");
  host.insert(
    key.clone(),
    "import { missing } from \"./absent\";\nconst value: number = 'not a number';",
  );

  let program = Program::new(host, vec![key]);
  let first = program.check();
  let second = program.check();

  assert!(!first.is_empty(), "expected diagnostics to be reported");
  assert_eq!(first, second);
}
