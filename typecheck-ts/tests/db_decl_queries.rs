use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use typecheck_ts::db::queries::{decl_type, type_params, type_store};
use typecheck_ts::db::Database;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, FileOrigin, MemoryHost, Program};
use types_ts_interned::{DefId, TypeDisplay, TypeParamId};

fn seed_host() -> (MemoryHost, FileKey, FileKey) {
  let mut host = MemoryHost::new();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(
    file_a.clone(),
    "export interface Box<T> { value: T; }\nexport type Alias = Box<number>;",
  );
  host.insert(
    file_b.clone(),
    "import { Box } from \"./a\";\n\
     export type MapBox<T> = (box: Box<T>) => T;\n\
     export interface Wrapper<U> extends Box<U> { wrapped: U; }",
  );
  host.link(file_b.clone(), "./a", file_a.clone());
  (host, file_a, file_b)
}

#[test]
fn decl_queries_match_program_types() {
  let (host, file_a, file_b) = seed_host();
  let program_host = host.clone();
  let program = Program::new(program_host, vec![file_b.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "program diagnostics should be empty: {diagnostics:?}"
  );

  let file_a_id = program.file_id(&file_a).expect("file a id");
  let file_b_id = program.file_id(&file_b).expect("file b id");

  let exports_a = program.exports_of(file_a_id);
  let exports_b = program.exports_of(file_b_id);
  let box_def = exports_a
    .get("Box")
    .and_then(|entry| entry.def)
    .expect("box def");
  let map_def = exports_b
    .get("MapBox")
    .and_then(|entry| entry.def)
    .expect("MapBox def");
  let wrapper_def = exports_b
    .get("Wrapper")
    .and_then(|entry| entry.def)
    .expect("wrapper def");

  let program_box_ty = program.type_of_def_interned(box_def);
  let program_map_ty = program.type_of_def_interned(map_def);
  let program_wrapper_ty = program.type_of_def_interned(wrapper_def);

  let snapshot = program.snapshot();
  let def_names: HashMap<DefId, String> = snapshot
    .def_data
    .iter()
    .map(|entry| (entry.def, entry.data.name.clone()))
    .collect();
  let program_params: HashMap<DefId, Vec<TypeParamId>> =
    snapshot.interned_type_params.into_iter().collect();

  let mut db = Database::new();
  db.set_compiler_options(CompilerOptions::default());
  db.set_roots(Arc::from([file_b.clone()]));

  let mut key_to_id = HashMap::new();
  key_to_id.insert(file_a.clone(), file_a_id);
  key_to_id.insert(file_b.clone(), file_b_id);

  for (key, id) in key_to_id.iter() {
    let text = host.file_text(key).expect("file text");
    let kind = host.file_kind(key);
    db.set_file(*id, key.clone(), kind, text, FileOrigin::Source);
  }
  db.set_module_resolution(file_b_id, Arc::<str>::from("./a"), Some(file_a_id));

  let store = type_store(&db);
  let resolver_names = Arc::new(def_names);
  let resolver = {
    let names = Arc::clone(&resolver_names);
    Arc::new(move |def: DefId| names.get(&def).cloned())
  };

  let decl_box = decl_type(&db, box_def).expect("box decl type");
  let decl_box_str = TypeDisplay::new(&store, decl_box)
    .with_ref_resolver(Arc::clone(&resolver))
    .to_string();
  let program_box_str = program.display_type(program_box_ty).to_string();
  assert_eq!(decl_box_str, program_box_str, "box type mismatch");
  assert_eq!(
    type_params(&db, box_def).as_ref(),
    program_params.get(&box_def).map(Vec::as_slice).unwrap_or(&[])
  );

  let decl_map = decl_type(&db, map_def).expect("MapBox decl type");
  let decl_map_str = TypeDisplay::new(&store, decl_map)
    .with_ref_resolver(Arc::clone(&resolver))
    .to_string();
  let program_map_str = program.display_type(program_map_ty).to_string();
  assert_eq!(decl_map_str, program_map_str, "MapBox type mismatch");
  assert_eq!(
    type_params(&db, map_def).as_ref(),
    program_params.get(&map_def).map(Vec::as_slice).unwrap_or(&[])
  );

  let decl_wrapper = decl_type(&db, wrapper_def).expect("wrapper decl type");
  let decl_wrapper_str = TypeDisplay::new(&store, decl_wrapper)
    .with_ref_resolver(resolver)
    .to_string();
  let program_wrapper_str = program.display_type(program_wrapper_ty).to_string();
  assert_eq!(
    decl_wrapper_str, program_wrapper_str,
    "wrapper interface type mismatch"
  );
  assert_eq!(
    type_params(&db, wrapper_def).as_ref(),
    program_params.get(&wrapper_def).map(Vec::as_slice).unwrap_or(&[])
  );
}
