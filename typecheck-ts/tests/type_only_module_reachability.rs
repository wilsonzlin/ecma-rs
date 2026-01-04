use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program, TypeKindSummary};

#[test]
fn typeof_import_type_queries_enqueue_modules() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    ..Default::default()
  });

  let main = FileKey::new("main.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(
    main.clone(),
    r#"
type T = typeof import("./dep").value;
export const x: T = 1;
"#,
  );
  host.insert(dep.clone(), "export const value: number = 1;");
  host.link(main.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let main_id = program.file_id(&main).expect("main file id");
  let dep_id = program
    .file_id(&dep)
    .expect("dep should be discovered via typeof import() type query");
  assert_eq!(program.reachable_files(), vec![main_id, dep_id]);

  let exports = program.exports_of(main_id);
  let x_def = exports
    .get("x")
    .and_then(|entry| entry.def)
    .expect("export x should have a definition");
  assert_eq!(
    program
      .display_type(program.type_of_def_interned(x_def))
      .to_string(),
    "number"
  );

  let t_def = program
    .definitions_in_file(main_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("T"))
    .expect("type alias T definition");
  let t_ty = program.declared_type_of_def_interned(t_def);
  assert_eq!(program.type_kind(t_ty), TypeKindSummary::Number);
}

#[test]
fn import_type_in_arrow_param_enqueues_modules() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    ..Default::default()
  });

  let main = FileKey::new("main.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(
    main.clone(),
    r#"
export const f = (x: import("./dep").Thing) => x;
"#,
  );
  host.insert(dep.clone(), "export type Thing = number;");
  host.link(main.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let main_id = program.file_id(&main).expect("main file id");
  let dep_id = program
    .file_id(&dep)
    .expect("dep should be discovered via import() type in arrow param");
  assert_eq!(program.reachable_files(), vec![main_id, dep_id]);
}

#[test]
fn typeof_import_in_arrow_return_enqueues_modules() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    ..Default::default()
  });

  let main = FileKey::new("main.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(
    main.clone(),
    r#"
export const f = (): typeof import("./dep").value => 1;
"#,
  );
  host.insert(dep.clone(), "export const value: number = 1;");
  host.link(main.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let main_id = program.file_id(&main).expect("main file id");
  let dep_id = program
    .file_id(&dep)
    .expect("dep should be discovered via typeof import() in arrow return type");
  assert_eq!(program.reachable_files(), vec![main_id, dep_id]);
}

#[test]
fn typeof_import_without_qualifier_enqueues_modules() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    ..Default::default()
  });

  let main = FileKey::new("main.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(
    main.clone(),
    r#"
export type Mod = typeof import("./dep");
"#,
  );
  host.insert(dep.clone(), "export const value: number = 1;");
  host.link(main.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let main_id = program.file_id(&main).expect("main file id");
  let dep_id = program
    .file_id(&dep)
    .expect("dep should be discovered via typeof import() type query");
  assert_eq!(program.reachable_files(), vec![main_id, dep_id]);
}

#[test]
fn import_type_in_type_assertion_enqueues_modules() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    ..Default::default()
  });

  let main = FileKey::new("main.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(
    main.clone(),
    r#"
export const x = ({ value: 1 } as import("./dep").Thing).value;
"#,
  );
  host.insert(dep.clone(), "export type Thing = { value: number };");
  host.link(main.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let main_id = program.file_id(&main).expect("main file id");
  let dep_id = program
    .file_id(&dep)
    .expect("dep should be discovered via import() type assertion");
  assert_eq!(program.reachable_files(), vec![main_id, dep_id]);
}
