use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program, TypeKindSummary};

#[test]
fn typeof_import_type_queries_enqueue_modules() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    include_dom: false,
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
    "T"
  );

  let t_def = program
    .definitions_in_file(main_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("T"))
    .expect("type alias T definition");
  let t_ty = program.declared_type_of_def_interned(t_def);
  assert_eq!(program.type_kind(t_ty), TypeKindSummary::Number);
}
