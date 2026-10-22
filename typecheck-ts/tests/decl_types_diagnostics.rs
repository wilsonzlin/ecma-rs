use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn decl_type_diagnostics_are_reported() {
  let mut host = MemoryHost::new();
  let key = FileKey::new("main.ts");
  host.insert(key.clone(), "type A = DoesNotExist;");
  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == "TC2008"),
    "expected unresolved type reference (TC2008) from decl type lowering, got {diagnostics:?}"
  );
}
