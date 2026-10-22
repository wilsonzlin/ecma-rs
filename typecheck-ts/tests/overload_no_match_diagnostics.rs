use diagnostics::TextRange;
use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn multi_overload_miss_emits_ts2769_on_argument_span() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let file = FileKey::new("main.ts");
  let source = r#"
function pick(x: string): string;
function pick(x: number): number;
function pick(x: string | number): string | number {
  return x;
}
const bad = pick(true);
"#;
  host.insert(file.clone(), Arc::from(source));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let diagnostics = program.check();

  let overload_diags: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::NO_OVERLOAD_MATCHES.as_str())
    .collect();
  assert_eq!(
    overload_diags.len(),
    1,
    "expected a single TS2769, got {diagnostics:?}"
  );
  let diag = overload_diags[0];

  let start = source.find("true").expect("true literal present") as u32;
  let end = start + 4;
  assert_eq!(diag.primary.file, file_id);
  assert_eq!(diag.primary.range, TextRange::new(start, end));
  assert!(
    diag.notes.iter().any(|n| n.contains("Overload 1 of 2")),
    "expected tsc-shaped overload notes, got {:?}",
    diag.notes
  );
}
