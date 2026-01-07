use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn spread_array_literal_is_contextually_typed_as_tuple_in_call() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("input.ts");
  host.insert(
    file.clone(),
    r#"
function takes(cb: (n: number) => number) {}
takes(...[(n) => n + 1]);
"#,
  );

  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn spread_array_literal_is_contextually_typed_as_tuple_in_new() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("input.ts");
  host.insert(
    file.clone(),
    r#"
class C {
  constructor(cb: (n: number) => number) {}
}

export const value = new C(...[(n) => n + 1]);
"#,
  );

  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}
