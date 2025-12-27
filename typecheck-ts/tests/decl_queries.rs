use std::sync::Arc;

use hir_js::LowerResult;
use typecheck_ts::db::{queries, Database};
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{DefId, FileKey, FileOrigin, Host, MemoryHost, Program};
use types_ts_interned::TypeDisplay;

fn def_by_name(program: &Program, file: FileKey, name: &str) -> DefId {
  let file_id = program.file_id(&file).unwrap();
  program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .expect("definition found")
}

fn def_by_name_in_lower(lowered: &LowerResult, name: &str) -> DefId {
  lowered
    .defs
    .iter()
    .find(|def| lowered.names.resolve(def.name).as_deref() == Some(name))
    .map(|def| def.id)
    .expect("definition present")
}

fn seed_db(
  host: &MemoryHost,
  program: &Program,
  file_a: &FileKey,
  file_b: &FileKey,
) -> (Database, typecheck_ts::FileId, typecheck_ts::FileId) {
  let mut db = Database::new();
  db.set_compiler_options(program.compiler_options());
  db.set_roots(vec![file_b.clone()].into());

  let file_a_id = program.file_id(file_a).expect("file a id");
  let file_b_id = program.file_id(file_b).expect("file b id");

  db.set_file(
    file_a_id,
    file_a.clone(),
    FileKind::Ts,
    host.file_text(file_a).unwrap(),
    FileOrigin::Source,
  );
  db.set_file(
    file_b_id,
    file_b.clone(),
    FileKind::Ts,
    host.file_text(file_b).unwrap(),
    FileOrigin::Source,
  );
  db.set_module_resolution(file_b_id, Arc::<str>::from("./a"), Some(file_a_id));

  (db, file_a_id, file_b_id)
}

#[test]
fn decl_queries_follow_interned_types_across_files() {
  let mut host = MemoryHost::new();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(
    file_a.clone(),
    "export interface Box<T> { value: T; readonly tag?: string; }",
  );
  host.insert(
    file_b.clone(),
    "import { Box } from \"./a\";\nexport function makeBox<T>(value: T): Box<T> { return { value }; }",
  );
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host.clone(), vec![file_b.clone()]);

  let box_def = def_by_name(&program, file_a.clone(), "Box");
  let make_box_def = def_by_name(&program, file_b.clone(), "makeBox");

  let (db, _, _) = seed_db(&host, &program, &file_a, &file_b);
  let store = queries::type_store(&db);

  let decl_box = queries::decl_type(&db, box_def).expect("declared box type");
  let inferred_box = program.type_of_def_interned(box_def);
  assert_eq!(
    TypeDisplay::new(&store, decl_box).to_string(),
    program.display_type(inferred_box).to_string()
  );
  let box_params = queries::type_params(&db, box_def);
  assert_eq!(box_params.len(), 1);

  let decl_make_box = queries::decl_type(&db, make_box_def).expect("declared makeBox type");
  let inferred_make_box = program.type_of_def_interned(make_box_def);
  assert_eq!(
    TypeDisplay::new(&store, decl_make_box).to_string(),
    program.display_type(inferred_make_box).to_string()
  );
  let fn_params = queries::type_params(&db, make_box_def);
  assert_eq!(fn_params.len(), 1);

  assert_ne!(inferred_box, inferred_make_box);
}

#[test]
fn decl_type_queries_match_program_across_files() {
  let mut host = MemoryHost::new();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(
    file_a.clone(),
    "export interface Box<T> { value: T; readonly tag?: string; }",
  );
  host.insert(
    file_b.clone(),
    "import { Box } from \"./a\";\nexport function makeBox<T>(value: T): Box<T> { return { value }; }",
  );
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host.clone(), vec![file_b.clone()]);
  let box_def = def_by_name(&program, file_a.clone(), "Box");
  let make_box_def = def_by_name(&program, file_b.clone(), "makeBox");
  let (db, file_a_id, file_b_id) = seed_db(&host, &program, &file_a, &file_b);

  let box_type_program = program.type_of_def_interned(box_def);
  let make_box_type_program = program.type_of_def_interned(make_box_def);
  let program_params: std::collections::HashMap<DefId, Vec<_>> = program
    .snapshot()
    .interned_type_params
    .into_iter()
    .collect();

  let lowered_a = queries::lower_hir(&db, file_a_id);
  let lowered_b = queries::lower_hir(&db, file_b_id);
  let box_def_db =
    def_by_name_in_lower(lowered_a.lowered.as_ref().expect("lowered box file"), "Box");
  let make_box_def_db = def_by_name_in_lower(
    lowered_b.lowered.as_ref().expect("lowered makeBox file"),
    "makeBox",
  );

  assert_eq!(box_def_db, box_def);
  assert_eq!(make_box_def_db, make_box_def);

  let store = queries::type_store(&db);
  let box_decl = queries::decl_type(&db, box_def_db).expect("declared box type");
  let box_params = queries::type_params(&db, box_def_db);
  let make_box_decl = queries::decl_type(&db, make_box_def_db);
  let make_box_params = queries::type_params(&db, make_box_def_db);

  assert_eq!(
    TypeDisplay::new(&store, box_decl).to_string(),
    program.display_type(box_type_program).to_string()
  );
  assert_eq!(
    make_box_decl
      .map(|ty| TypeDisplay::new(&store, ty).to_string())
      .unwrap_or_else(|| program.display_type(make_box_type_program).to_string()),
    program.display_type(make_box_type_program).to_string()
  );
  assert_eq!(
    box_params.len(),
    program_params.get(&box_def).map(Vec::len).unwrap_or(0)
  );
  assert_eq!(
    make_box_params.len(),
    program_params.get(&make_box_def).map(Vec::len).unwrap_or(0)
  );
}
