use std::collections::BTreeSet;
use std::sync::Arc;

use typecheck_ts::db::TypecheckDb;
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{FileId, FileKey, FileOrigin, MemoryHost, Program, PropertyKey};

#[test]
fn module_augmentation_adds_new_export() {
  let mut host = MemoryHost::new();
  let pkg = FileKey::new("pkg.ts");
  let augment = FileKey::new("augment.ts");
  let main = FileKey::new("main.ts");

  host.insert(pkg.clone(), "export const x = 1;");
  host.insert(
    augment.clone(),
    "export {};\ndeclare module \"./pkg\" { export const y: string; }",
  );
  host.insert(
    main.clone(),
    "import { y } from \"./pkg\";\nconst z: string = y;",
  );

  let program = Program::new(host, vec![main.clone(), augment.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let pkg_file = program.file_id(&pkg).expect("pkg file id");
  let exports = program.exports_of(pkg_file);
  let y_export = exports.get("y").expect("augmented export y");
  let y_ty = y_export.type_id.expect("type for y");
  assert_eq!(program.display_type(y_ty).to_string(), "string");
}

#[test]
fn module_augmentation_merges_interface_members() {
  let pkg_file = FileId(0);
  let augment_file = FileId(1);
  let pkg = FileKey::new("pkg.ts");
  let augment = FileKey::new("augment.ts");
  let mut db = TypecheckDb::default();
  db.set_file(
    pkg_file,
    pkg.clone(),
    FileKind::Ts,
    Arc::from("export interface Foo { a: number }"),
    FileOrigin::Source,
  );
  db.set_file(
    augment_file,
    augment.clone(),
    FileKind::Ts,
    Arc::from("export {};\ndeclare module \"./pkg\" { interface Foo { b: string } }"),
    FileOrigin::Source,
  );
  db.set_roots(vec![pkg.clone(), augment.clone()].into());
  db.set_module_resolution(augment_file, Arc::<str>::from("./pkg"), Some(pkg_file));

  let res = db.ts_semantics();
  assert!(
    res.diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    res.diagnostics
  );

  let sem = &res.semantics;
  let foo_symbol = sem
    .resolve_export(
      semantic_js::ts::FileId(pkg_file.0),
      "Foo",
      semantic_js::ts::Namespace::TYPE,
    )
    .expect("Foo type export");
  let decl_ids = sem.symbol_decls(foo_symbol, semantic_js::ts::Namespace::TYPE);
  let decls: Vec<_> = decl_ids
    .iter()
    .map(|decl| sem.symbols().decl(*decl))
    .collect();

  assert_eq!(decls.len(), 2, "expected two interface declarations");

  let files: BTreeSet<_> = decls.iter().map(|decl| decl.file).collect();
  assert!(
    files.contains(&pkg_file) && files.contains(&augment_file),
    "expected declarations from both pkg and augment files, got {files:?}"
  );

  for decl in decls {
    assert_eq!(decl.def_id.file(), decl.file);
  }
}

#[test]
fn declare_global_in_module_is_visible_across_files() {
  let mut host = MemoryHost::new();
  let augment = FileKey::new("augment.ts");
  let main = FileKey::new("main.ts");

  host.insert(
    augment.clone(),
    "export {};\ndeclare global { interface GlobalFoo { a: number } }",
  );
  host.insert(main.clone(), "const x: GlobalFoo = { a: 1 };");

  let program = Program::new(host, vec![main.clone(), augment.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let main_file = program.file_id(&main).expect("main file id");
  let x_def = program
    .definitions_in_file(main_file)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("x"))
    .expect("x definition");
  let ty = program.type_of_def(x_def);
  let props = program.properties_of(ty);
  assert!(
    props
      .iter()
      .any(|p| matches!(&p.key, PropertyKey::String(name) if name == "a")),
    "GlobalFoo should expose property 'a', got {props:?}"
  );
}
