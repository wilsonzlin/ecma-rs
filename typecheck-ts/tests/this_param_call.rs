use std::sync::Arc;

use typecheck_ts::{codes, FileKey, MemoryHost, Program};

#[test]
fn reports_type_mismatch_for_this_param_call() {
  let mut host = MemoryHost::default();

  let entry = FileKey::new("a.ts");
  let decl = FileKey::new("m.d.ts");
  let source = r#"import { f } from "./m";

f.call({ x: 1 }, 2);
f.call({ x: "no" }, 2);
"#;
  host.insert(entry.clone(), Arc::from(source.to_string()));
  host.insert(
    decl.clone(),
    Arc::from("export function f(this: { x: number }, y: number): number;".to_string()),
  );
  host.link(entry.clone(), "./m", decl.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();

  let file_id = program.file_id(&entry).expect("entry file id");
  let offset = source
    .find("x: \"no\"")
    .expect("mismatched property")
    .try_into()
    .expect("offset fits in u32");

  let mismatch = diagnostics
    .iter()
    .find(|diag| diag.code.as_str() == codes::TYPE_MISMATCH.as_str())
    .unwrap_or_else(|| panic!("expected type mismatch diagnostic; got {diagnostics:?}"));

  assert_eq!(mismatch.primary.file, file_id);
  assert!(
    mismatch.primary.range.start <= offset && mismatch.primary.range.end >= offset + 1,
    "expected mismatch span {:?} to include offset {offset}",
    mismatch.primary.range
  );
}
