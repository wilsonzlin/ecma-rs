use std::sync::Arc;

use hir_js::LocalKind;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn body_local_vars_typed_via_type_of_local() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("main.ts");
  let source: Arc<str> = Arc::from(
    r#"
      export function f(a: number) {
        const x: string = "hi";
        let y = a;
        return x;
      }
    "#,
  );
  host.insert(file.clone(), Arc::clone(&source));

  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let lowered = program.hir_lowered(file_id).expect("hir");
  let f_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("f"))
    .expect("function f");
  let body_id = program.body_of_def(f_def).expect("body");
  let body = lowered.body(body_id).expect("hir body");

  // No DefKind::Var for body locals.
  assert!(
    !program.definitions_in_file(file_id).into_iter().any(|def| {
      program.def_name(def).as_deref() == Some("x") || program.def_name(def).as_deref() == Some("y")
    }),
    "body-local vars must not appear as DefIds"
  );

  let mut by_name = std::collections::BTreeMap::new();
  for (local_id, local) in body.locals_with_kind(LocalKind::Var) {
    let name = lowered.names.resolve(local.name).unwrap().to_string();
    let ty = program.type_of_local(body_id, local_id);
    by_name.insert(name, program.display_type(ty).to_string());
  }
  assert_eq!(by_name.get("x").map(String::as_str), Some("string"));
  assert_eq!(by_name.get("y").map(String::as_str), Some("number"));
}
