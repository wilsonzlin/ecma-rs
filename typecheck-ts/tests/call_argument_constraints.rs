use diagnostics::TextRange;
use std::sync::Arc;

use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn call_argument_constraint_errors_on_argument_span() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("main.ts");
  let source = "function f<T extends string>(x: T): T { return x; }\nf(1);\n";
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
  assert_eq!(
    diag.code.as_str(),
    codes::TYPE_MISMATCH.as_str(),
    "expected TYPE_MISMATCH diagnostic, got {diagnostics:?}"
  );

  let start = source
    .find('1')
    .expect("numeric literal present in source") as u32;
  let end = start + 1;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
}

