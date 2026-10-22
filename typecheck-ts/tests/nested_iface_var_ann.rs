use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn top_level_interface_var_annotation_ok() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
interface Base {
  a: number;
}
var b: Base;
var _ = b.a;
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags.iter().map(|d| d.code.to_string()).collect();
  assert!(
    !codes.iter().any(|c| c == "TC2008"),
    "top-level Base should resolve, got {codes:?}"
  );
}

#[test]
fn nested_namespace_interface_var_annotation() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
namespace N {
  interface Base {
    a: number;
  }
  var b: Base;
  var _ = b.a;
}
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags.iter().map(|d| d.code.to_string()).collect();
  assert!(
    !codes.iter().any(|c| c == "TC2008"),
    "expected Base to resolve in nested namespace, got {codes:?} {diags:?}"
  );
}
