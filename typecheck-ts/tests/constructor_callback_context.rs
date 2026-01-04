use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn constructor_arguments_use_contextual_function_types() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("input.ts");
  host.insert(
    file.clone(),
    r#"
class C {
  constructor(cb: (n: number) => number) {}
}

export const value = new C((n) => n + 1);
"#,
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "unexpected diagnostics: {diagnostics:?}");
}

