use typecheck_ts::{FileKey, MemoryHost, Program, PropertyKey};

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
  let mut host = MemoryHost::new();
  let pkg = FileKey::new("pkg.ts");
  let augment = FileKey::new("augment.ts");
  let main = FileKey::new("main.ts");

  host.insert(pkg.clone(), "export interface Foo { a: number }");
  host.insert(
    augment.clone(),
    "export {};\ndeclare module \"./pkg\" { interface Foo { b: string } }",
  );
  host.insert(
    main.clone(),
    "import { Foo } from \"./pkg\";\nconst v: Foo = { a: 1, b: \"ok\" };",
  );

  let program = Program::new(host, vec![main.clone(), augment.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let main_file = program.file_id(&main).expect("main file id");
  let import_foo_def = program
    .definitions_in_file(main_file)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Foo"))
    .expect("main import Foo");
  let import_foo_ty = program.type_of_def(import_foo_def);
  let import_props = program.properties_of(import_foo_ty);
  let import_has_a =
    import_props.iter().any(|p| matches!(&p.key, PropertyKey::String(name) if name == "a"));
  let import_has_b =
    import_props.iter().any(|p| matches!(&p.key, PropertyKey::String(name) if name == "b"));
  assert!(
    import_has_a && import_has_b,
    "imported Foo should include merged members, got {import_props:?}"
  );

  let pkg_file = program.file_id(&pkg).expect("pkg file id");
  let foo_def = program
    .definitions_in_file(pkg_file)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Foo"))
    .expect("interface Foo");

  let foo_ty = program.type_of_def(foo_def);
  let props = program.properties_of(foo_ty);
  let has_a = props.iter().any(|p| matches!(&p.key, PropertyKey::String(name) if name == "a"));
  let has_b = props.iter().any(|p| matches!(&p.key, PropertyKey::String(name) if name == "b"));
  assert!(has_a && has_b, "merged interface should expose a + b, got {props:?}");
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
    props.iter().any(|p| matches!(&p.key, PropertyKey::String(name) if name == "a")),
    "GlobalFoo should expose property 'a', got {props:?}"
  );
}
