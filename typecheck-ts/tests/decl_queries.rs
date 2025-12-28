use std::sync::Arc;

use hir_js::LowerResult;
use typecheck_ts::db::{queries, Database};
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{DefId, FileKey, FileOrigin, MemoryHost, Program};
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

  let program = Program::new(host, vec![file_b.clone()]);

  let box_def = def_by_name(&program, file_a.clone(), "Box");
  let make_box_def = def_by_name(&program, file_b.clone(), "makeBox");

  let decl_box = program.decl_type(box_def);
  let inferred_box = program.type_of_def_interned(box_def);
  let decl_box = decl_box.expect("declared type");
  assert_eq!(decl_box, inferred_box);

  let box_params = program.type_params(box_def);
  assert_eq!(box_params.len(), 1);

  let decl_make_box = program.decl_type(make_box_def);
  let inferred_make_box = program.type_of_def_interned(make_box_def);
  let decl_make_box = decl_make_box.expect("declared type");
  assert_eq!(decl_make_box, inferred_make_box);

  let fn_params = program.type_params(make_box_def);
  assert!(
    fn_params.is_empty(),
    "function type params are not tracked yet"
  );
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
  let file_a_id = program.file_id(&file_a).unwrap();
  let file_b_id = program.file_id(&file_b).unwrap();

  let box_type_program = program.type_of_def_interned(box_def);
  let make_box_type_program = program.type_of_def_interned(make_box_def);
  let box_params_program = program.type_params(box_def);

  let mut db = Database::new();
  db.set_compiler_options(program.compiler_options());
  db.set_roots(vec![file_b.clone()].into());
  db.set_file(
    file_a_id,
    file_a.clone(),
    FileKind::Ts,
    host.file_text(&file_a).unwrap(),
    FileOrigin::Source,
  );
  db.set_file(
    file_b_id,
    file_b.clone(),
    FileKind::Ts,
    host.file_text(&file_b).unwrap(),
    FileOrigin::Source,
  );
  db.set_module_resolution(file_b_id, Arc::<str>::from("./a"), Some(file_a_id));

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
  let resolver: Arc<dyn Fn(types_ts_interned::DefId) -> Option<String> + Send + Sync> = {
    let program = &program;
    Arc::new(move |def: types_ts_interned::DefId| {
      program.def_name(typecheck_ts::DefId(def.0))
    })
  };

  assert_eq!(
    TypeDisplay::new(&store, box_decl)
      .with_ref_resolver(Arc::clone(&resolver))
      .to_string(),
    program.display_type(box_type_program).to_string()
  );
  assert_eq!(
    make_box_decl
      .map(|ty| {
        TypeDisplay::new(&store, ty)
          .with_ref_resolver(Arc::clone(&resolver))
          .to_string()
      })
      .unwrap_or_else(|| program.display_type(make_box_type_program).to_string()),
    program.display_type(make_box_type_program).to_string()
  );
  assert_eq!(box_params.len(), box_params_program.len());
  assert_eq!(
    make_box_params.len(),
    program.type_params(make_box_def).len()
  );
}
