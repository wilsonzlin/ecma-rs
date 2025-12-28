use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use typecheck_ts::db::queries::{type_of_def, type_store};
use typecheck_ts::db::{DeclInfo, DeclKind, SharedTypeStore, TypesDatabase};
use typecheck_ts::{FileId, FileKey, MemoryHost, Program};
use types_ts_interned::{DefId, TypeDisplay, TypeStore};

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
  let canonical_defs: HashMap<(FileId, String), DefId> =
    snapshot.canonical_defs.iter().cloned().collect();
  let def_names: HashMap<DefId, String> = snapshot
    .def_data
    .iter()
    .map(|entry| (entry.def, entry.data.name.clone()))
    .collect();

  let mut decls_by_file: BTreeMap<_, BTreeMap<DefId, DeclInfo>> = BTreeMap::new();
  for def in snapshot.def_data.iter() {
    if let Some(expected) = canonical_defs.get(&(def.data.file, def.data.name.clone())) {
      if *expected != def.def {
        continue;
      }
    }
    let entry = DeclInfo {
      file: def.data.file,
      name: def.data.name.clone(),
      kind: DeclKind::Var,
      declared_type: Some(program.type_of_def_interned(def.def)),
      initializer: None,
    };
    decls_by_file
      .entry(def.data.file)
      .or_default()
      .insert(def.def, entry);
  }

  let mut db = TypesDatabase::new();
  db.set_compiler_options(snapshot.compiler_options.clone());
  db.set_type_store(SharedTypeStore(TypeStore::from_snapshot(
    snapshot.interned_type_store.clone(),
  )));
  db.set_files(Arc::new(snapshot.files.iter().map(|f| f.file).collect()));
  for (file, decls) in decls_by_file {
    db.set_decl_types_in_file(file, Arc::new(decls));
  }

  let store = type_store(&db).arc();
  let resolver_names = Arc::new(def_names);
  let resolver: Arc<dyn Fn(DefId) -> Option<String> + Send + Sync> = {
    let names = Arc::clone(&resolver_names);
    Arc::new(move |def: DefId| names.get(&def).cloned())
      as Arc<dyn Fn(DefId) -> Option<String> + Send + Sync>
  };

  let decl_box = type_of_def(&db, box_def, ());
  let decl_box_str = TypeDisplay::new(store.as_ref(), decl_box)
    .with_ref_resolver(Arc::clone(&resolver))
    .to_string();
  let program_box_str = program.display_type(program_box_ty).to_string();
  assert_eq!(decl_box_str, program_box_str, "box type mismatch");

  let decl_map = type_of_def(&db, map_def, ());
  let decl_map_str = TypeDisplay::new(store.as_ref(), decl_map)
    .with_ref_resolver(Arc::clone(&resolver))
    .to_string();
  let program_map_str = program.display_type(program_map_ty).to_string();
  assert_eq!(decl_map_str, program_map_str, "MapBox type mismatch");

  let decl_wrapper = type_of_def(&db, wrapper_def, ());
  let decl_wrapper_str = TypeDisplay::new(store.as_ref(), decl_wrapper)
    .with_ref_resolver(resolver)
    .to_string();
  let program_wrapper_str = program.display_type(program_wrapper_ty).to_string();
  assert_eq!(
    decl_wrapper_str, program_wrapper_str,
    "wrapper interface type mismatch"
  );
}
