use std::collections::BTreeMap;
use std::sync::Arc;
use std::thread;

use diagnostics::FileId;
use hir_js::DefId;
use salsa::{Database, Durability};
use typecheck_ts::db::queries::{cache_stats, check_body, type_of_def};
use typecheck_ts::db::{DeclInfo, DeclKind, Initializer, SharedTypeStore, TypesDatabase};
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{CacheKind, QueryStatsCollector};
use types_ts_interned::{TypeId, TypeStore};

fn build_database(def_count: usize) -> (TypesDatabase, Arc<TypeStore>, Vec<DefId>) {
  let mut options = CompilerOptions::default();
  options.cache.max_body_cache_entries = 4;
  options.cache.max_def_cache_entries = 4;
  options.cache.cache_shards = 1;

  let store = TypeStore::new();
  let mut db = TypesDatabase::default();
  db.set_compiler_options(options);
  db.set_type_store(SharedTypeStore(store.clone()));

  let file = FileId(0);
  db.set_files(Arc::new(vec![file]));

  let primitives = store.primitive_ids();
  let mut decls = BTreeMap::new();
  for idx in 0..def_count {
    let def = DefId(idx as u32);
    let init = if idx == 0 {
      Initializer::Type(primitives.number)
    } else {
      Initializer::Union(vec![
        Initializer::Reference(DefId((idx - 1) as u32)),
        Initializer::Type(primitives.boolean),
      ])
    };
    decls.insert(
      def,
      DeclInfo {
        file,
        name: format!("v{idx}"),
        kind: DeclKind::Var,
        declared_type: None,
        initializer: Some(init),
      },
    );
  }

  db.set_decl_types_in_file(file, Arc::new(decls));

  let defs: Vec<DefId> = (0..def_count).map(|idx| DefId(idx as u32)).collect();
  (db, store, defs)
}

fn snapshot(db: &TypesDatabase, defs: &[DefId]) -> (Vec<TypeId>, Vec<TypeId>) {
  let mut body_types = Vec::new();
  for &def in defs {
    body_types.push(check_body(db, def, ()));
  }
  let mut def_types = Vec::new();
  for &def in defs {
    def_types.push(type_of_def(db, def, ()));
  }
  (body_types, def_types)
}

#[test]
fn query_caches_evict_without_affecting_results() {
  let def_count = 48;
  let (mut db, _store, defs) = build_database(def_count);
  let profiler = QueryStatsCollector::default();
  db.set_profiler(profiler.clone());

  let first = snapshot(&db, &defs);
  let second = snapshot(&db, &defs);
  assert_eq!(
    first, second,
    "repeat runs in the same revision should be stable"
  );

  let expected = first.clone();
  thread::scope(|scope| {
    for _ in 0..4 {
      let defs = defs.clone();
      let db_snapshot = db.snapshot();
      let expected = expected.clone();
      scope.spawn(move || {
        let result = snapshot(&db_snapshot, &defs);
        assert_eq!(result, expected, "parallel snapshot drifted");
      });
    }
  });

  db.synthetic_write(Durability::HIGH);
  let third = snapshot(&db, &defs);

  assert_eq!(first, third, "eviction should not change query results");

  let (body_stats, def_stats) = cache_stats(&db);
  assert!(
    body_stats.evictions > 0,
    "body cache should evict under tight bounds (stats: {body_stats:?})"
  );
  assert!(
    def_stats.evictions > 0,
    "def cache should evict under tight bounds (stats: {def_stats:?})"
  );
  assert!(
    body_stats.hits > 0 && body_stats.misses > 0,
    "body cache stats should record both hits and misses (stats: {body_stats:?})"
  );
  assert!(
    def_stats.hits > 0 && def_stats.misses > 0,
    "def cache stats should record both hits and misses (stats: {def_stats:?})"
  );

  let snapshot = profiler.snapshot();
  let body_cache = snapshot
    .caches
    .get(&CacheKind::Body)
    .cloned()
    .unwrap_or_default();
  let def_cache = snapshot
    .caches
    .get(&CacheKind::Def)
    .cloned()
    .unwrap_or_default();
  assert!(
    body_cache.evictions > 0 && def_cache.evictions > 0,
    "recorded cache stats should include evictions (body: {body_cache:?}, def: {def_cache:?})"
  );
}
