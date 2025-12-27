use std::sync::Arc;

use typecheck_ts::db::TypecheckDb;
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{codes, FileId, FileKey, FileOrigin};

#[test]
fn reachable_files_are_deterministic_and_cycle_safe() {
  let mut db = TypecheckDb::default();
  let file_a = FileId(0);
  let file_b = FileId(1);
  let file_c = FileId(2);
  let key_a = FileKey::new("a.ts");
  let key_b = FileKey::new("b.ts");
  let key_c = FileKey::new("c.ts");

  db.set_roots(Arc::from([key_c.clone(), key_a.clone()]));
  db.set_file(
    file_a,
    key_a.clone(),
    FileKind::Ts,
    Arc::from(r#"import { value } from "./b"; export const a = value;"#),
    FileOrigin::Source,
  );
  db.set_file(
    file_b,
    key_b.clone(),
    FileKind::Ts,
    Arc::from(r#"export { c as value } from "./c";"#),
    FileOrigin::Source,
  );
  db.set_file(
    file_c,
    key_c.clone(),
    FileKind::Ts,
    Arc::from(r#"export * from "./a"; export const c = 1;"#),
    FileOrigin::Source,
  );

  db.set_module_resolution(file_a, Arc::<str>::from("./b"), Some(file_b));
  db.set_module_resolution(file_b, Arc::<str>::from("./c"), Some(file_c));
  db.set_module_resolution(file_c, Arc::<str>::from("./a"), Some(file_a));

  let reachable = db.reachable_files();
  assert_eq!(
    reachable.as_ref(),
    &[file_a, file_b, file_c],
    "reachable files should include cycle members in a stable order"
  );
  assert_eq!(
    db.module_deps(file_c).as_ref(),
    &[file_a],
    "cycles should not cause duplicate deps"
  );

  db.set_roots(Arc::from([key_a, key_c]));
  let reordered = db.reachable_files();
  assert_eq!(
    reordered.as_ref(),
    reachable.as_ref(),
    "reordering roots should not affect reachable ordering"
  );
}

#[test]
fn unresolved_modules_emit_diagnostics() {
  let mut db = TypecheckDb::default();
  let file = FileId(10);
  let key = FileKey::new("entry.ts");
  db.set_roots(Arc::from([key.clone()]));
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from("import \"./missing\";\nexport * from \"./also\";"),
    FileOrigin::Source,
  );
  db.set_module_resolution(file, Arc::<str>::from("./missing"), None);
  db.set_module_resolution(file, Arc::<str>::from("./also"), None);

  let diags = db.module_dep_diagnostics(file);
  assert_eq!(
    diags.len(),
    2,
    "missing resolutions should produce diagnostics per specifier"
  );
  for diag in diags.iter() {
    assert_eq!(diag.code.as_str(), codes::UNRESOLVED_MODULE.as_str());
    assert_eq!(diag.primary.file, file);
  }
}
