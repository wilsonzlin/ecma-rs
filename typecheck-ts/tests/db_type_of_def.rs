use std::collections::BTreeMap;
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;

use diagnostics::FileId;
use hir_js::DefId;
use typecheck_ts::db::queries::type_of_def;
use typecheck_ts::db::{DeclInfo, DeclKind, Initializer, SharedTypeStore, TypesDatabase};
use typecheck_ts::lib_support::CompilerOptions;
use types_ts_interned::{TypeId, TypeStore};

fn snapshot_types(db: &TypesDatabase, defs: &[DefId]) -> BTreeMap<DefId, TypeId> {
  let mut map = BTreeMap::new();
  for &def in defs {
    map.insert(def, type_of_def(db, def, ()));
  }
  map
}

fn parallel_snapshot(db: &TypesDatabase, defs: &[DefId]) -> BTreeMap<DefId, TypeId> {
  let (tx, rx) = mpsc::channel();
  thread::scope(|scope| {
    for &def in defs {
      let snapshot = db.snapshot();
      let tx = tx.clone();
      scope.spawn(move || {
        let ty = type_of_def(&snapshot, def, ());
        tx.send((def, ty)).unwrap();
      });
    }
  });
  drop(tx);
  let mut map = BTreeMap::new();
  for (def, ty) in rx {
    map.insert(def, ty);
  }
  map
}

fn setup_deterministic_db() -> (TypesDatabase, Arc<TypeStore>, Vec<DefId>) {
  let store = TypeStore::new();
  let mut db = TypesDatabase::default();
  db.set_compiler_options(CompilerOptions::default());
  db.set_type_store(SharedTypeStore(store.clone()));

  let file = FileId(1);
  db.set_files(Arc::new(vec![file]));

  let defs: Vec<DefId> = (0..6).map(DefId).collect();
  let primitives = store.primitive_ids();

  let mut decls = BTreeMap::new();
  // Two declarations with the same name to exercise merging logic.
  decls.insert(
    defs[0],
    DeclInfo {
      file,
      name: "over".into(),
      kind: DeclKind::Function,
      declared_type: Some(primitives.number),
      initializer: None,
      type_params: Arc::from([]),
    },
  );
  decls.insert(
    defs[1],
    DeclInfo {
      file,
      name: "over".into(),
      kind: DeclKind::Function,
      declared_type: Some(primitives.string),
      initializer: None,
      type_params: Arc::from([]),
    },
  );
  // Inferred from merged overloads.
  decls.insert(
    defs[2],
    DeclInfo {
      file,
      name: "beta".into(),
      kind: DeclKind::Var,
      declared_type: None,
      initializer: Some(Initializer::Union(vec![
        Initializer::Reference(defs[0]),
        Initializer::Reference(defs[1]),
      ])),
      type_params: Arc::from([]),
    },
  );
  decls.insert(
    defs[3],
    DeclInfo {
      file,
      name: "gamma".into(),
      kind: DeclKind::Var,
      declared_type: None,
      initializer: Some(Initializer::Union(vec![
        Initializer::Type(primitives.boolean),
        Initializer::Reference(defs[2]),
      ])),
      type_params: Arc::from([]),
    },
  );
  decls.insert(
    defs[4],
    DeclInfo {
      file,
      name: "delta".into(),
      kind: DeclKind::Var,
      declared_type: Some(primitives.undefined),
      initializer: Some(Initializer::Reference(defs[3])),
      type_params: Arc::from([]),
    },
  );
  decls.insert(
    defs[5],
    DeclInfo {
      file,
      name: "epsilon".into(),
      kind: DeclKind::Var,
      declared_type: None,
      initializer: Some(Initializer::Union(vec![
        Initializer::Reference(defs[4]),
        Initializer::Reference(defs[0]),
      ])),
      type_params: Arc::from([]),
    },
  );

  db.set_decl_types_in_file(file, Arc::new(decls));
  (db, store, defs)
}

#[test]
fn self_referential_initializer_recovers() {
  let store = TypeStore::new();
  let mut db = TypesDatabase::default();
  db.set_compiler_options(CompilerOptions::default());
  db.set_type_store(SharedTypeStore(store.clone()));

  let file = FileId(0);
  let def = DefId(0);
  db.set_files(Arc::new(vec![file]));

  let mut decls = BTreeMap::new();
  decls.insert(
    def,
    DeclInfo {
      file,
      name: "value".into(),
      kind: DeclKind::Var,
      declared_type: None,
      initializer: Some(Initializer::Reference(def)),
      type_params: Arc::from([]),
    },
  );
  db.set_decl_types_in_file(file, Arc::new(decls));

  let ty = type_of_def(&db, def, ());
  assert_eq!(
    ty,
    store.primitive_ids().any,
    "cycles should recover to a stable any type"
  );
  assert_eq!(
    type_of_def(&db, def, ()),
    ty,
    "repeat evaluations should remain stable"
  );
}

#[test]
fn type_of_def_is_deterministic_in_parallel() {
  let (db, store, defs) = setup_deterministic_db();
  let baseline = snapshot_types(&db, &defs);

  assert_eq!(
    baseline[&defs[0]], baseline[&defs[1]],
    "merged overloads should converge to the same type"
  );

  let merged = store.union(vec![
    store.primitive_ids().number,
    store.primitive_ids().string,
  ]);
  assert_eq!(
    store.type_kind(baseline[&defs[0]]),
    store.type_kind(merged),
    "merged overload type should be a stable union"
  );

  let parallel = parallel_snapshot(&db, &defs);
  assert_eq!(parallel, baseline, "parallel evaluation should be stable");

  for iteration in 0..8 {
    let repeat = parallel_snapshot(&db, &defs);
    assert_eq!(repeat, baseline, "iteration {iteration} drifted");
  }
}
