use std::collections::HashMap;
use std::sync::Arc;
use std::thread;

use ordered_float::OrderedFloat;
use typecheck_ts::check::caches::{CheckerCacheStats, CheckerCaches};
use typecheck_ts::check::instantiate::InstantiationCache;
use typecheck_ts::db::expander::{DbTypeExpander, TypeExpanderDb};
use typecheck_ts::lib_support::{CacheMode, CacheOptions, CompilerOptions};
use typecheck_ts::{CacheKind, FileKey, Host, HostError, Program, QueryKind, QueryStatsCollector};
use types_ts_interned::{
  CacheConfig, DefId, EvaluatorCaches, Param, RelateCtx, RelateTypeExpander, Signature,
  SignatureId, TypeEvaluator, TypeId, TypeKind, TypeOptions, TypeParamDecl, TypeParamId, TypeStore,
};

fn relation_round(store: &Arc<TypeStore>, caches: &CheckerCaches) -> CheckerCacheStats {
  let body = caches.for_body();
  let relate = RelateCtx::with_cache(store.clone(), TypeOptions::default(), body.relation.clone());
  let primitives = store.primitive_ids();
  assert!(relate.is_assignable(primitives.number, primitives.number));
  assert!(relate.is_assignable(primitives.number, primitives.number));
  body.stats()
}

#[test]
fn shared_caches_reuse_entries_across_bodies() {
  let store = TypeStore::new();
  let caches = CheckerCaches::new(CacheOptions {
    max_relation_cache_entries: 8,
    max_eval_cache_entries: 4,
    max_instantiation_cache_entries: 4,
    cache_shards: 1,
    mode: CacheMode::Shared,
    ..CacheOptions::default()
  });

  let first = relation_round(&store, &caches);
  let second = relation_round(&store, &caches);

  assert!(
    second.relation.hits > first.relation.hits,
    "shared caches should accumulate hits across bodies"
  );
}

#[test]
fn per_body_caches_do_not_leak_entries() {
  let store = TypeStore::new();
  let caches = CheckerCaches::new(CacheOptions {
    max_relation_cache_entries: 8,
    max_eval_cache_entries: 4,
    max_instantiation_cache_entries: 4,
    cache_shards: 1,
    mode: CacheMode::PerBody,
    ..CacheOptions::default()
  });

  let first = relation_round(&store, &caches);
  let second = relation_round(&store, &caches);

  assert_eq!(
    first.relation.hits, second.relation.hits,
    "per-body caches should start empty for each body"
  );
}

#[test]
fn instantiation_cache_eviction_is_deterministic() {
  let store = TypeStore::new();
  let t_param = TypeParamId(0);
  let param_ty = store.intern_type(TypeKind::TypeParam(t_param));
  let sig = Signature {
    params: vec![Param {
      name: None,
      ty: param_ty,
      optional: false,
      rest: false,
    }],
    ret: param_ty,
    type_params: vec![TypeParamDecl::new(t_param)],
    this_param: None,
  };
  let sig_id = store.intern_signature(sig.clone());

  let config = CacheOptions {
    max_relation_cache_entries: 0,
    max_eval_cache_entries: 0,
    max_instantiation_cache_entries: 2,
    cache_shards: 1,
    mode: CacheMode::Shared,
    ..CacheOptions::default()
  }
  .instantiation_config();

  let mut cache_a = InstantiationCache::with_config(config);
  let mut cache_b = InstantiationCache::with_config(config);

  let substitutions: Vec<HashMap<_, _>> = (0..16)
    .map(|i| {
      let lit = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(i as f64)));
      let mut map = HashMap::new();
      map.insert(t_param, lit);
      map
    })
    .collect();

  let instantiate_all = |cache: &mut InstantiationCache| -> Vec<SignatureId> {
    substitutions
      .iter()
      .map(|subst| cache.instantiate_signature(&store, sig_id, &sig, subst))
      .collect()
  };

  let first = instantiate_all(&mut cache_a);
  let second = instantiate_all(&mut cache_b);
  let instantiated = first.clone();

  assert_eq!(first, second);
  assert!(
    cache_a.stats().evictions > 0 || cache_b.stats().evictions > 0,
    "evictions should occur under tight bounds"
  );

  for (subst, sig_id) in substitutions.iter().zip(instantiated.into_iter()) {
    let resolved = store.signature(sig_id);
    assert!(
      resolved.type_params.is_empty(),
      "instantiation should remove substituted params"
    );
    let expected = *subst.get(&t_param).unwrap();
    for param in &resolved.params {
      assert_eq!(param.ty, expected, "parameter type should be substituted");
    }
    assert_eq!(resolved.ret, expected, "return type should be substituted");
  }
}

#[test]
fn relation_eviction_remains_deterministic() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let pairs: Vec<(TypeId, TypeId)> = (0..12)
    .flat_map(|i| {
      let lit = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(i as f64)));
      [
        (lit, primitives.number),
        (primitives.string, lit),
        (lit, primitives.string),
      ]
    })
    .collect();

  let caches = CheckerCaches::new(CacheOptions {
    max_relation_cache_entries: 2,
    max_eval_cache_entries: 2,
    max_instantiation_cache_entries: 2,
    cache_shards: 1,
    mode: CacheMode::PerBody,
    ..CacheOptions::default()
  });

  let run = |caches: &CheckerCaches| -> (Vec<bool>, CheckerCacheStats) {
    let body = caches.for_body();
    let relate =
      RelateCtx::with_cache(store.clone(), TypeOptions::default(), body.relation.clone());
    let results = pairs
      .iter()
      .map(|(a, b)| relate.is_assignable(*a, *b))
      .collect();
    (results, body.stats())
  };

  let (first, stats_one) = run(&caches);
  let (second, stats_two) = run(&caches);

  assert_eq!(first, second);
  assert!(
    stats_one.relation.evictions > 0 || stats_two.relation.evictions > 0,
    "small caches should evict entries without affecting results"
  );
}

#[derive(Clone)]
struct MockDb {
  store: Arc<TypeStore>,
  decl_types: HashMap<DefId, TypeId>,
  params: HashMap<DefId, Arc<[TypeParamId]>>,
}

impl MockDb {
  fn new(store: Arc<TypeStore>) -> Self {
    Self {
      store,
      decl_types: HashMap::new(),
      params: HashMap::new(),
    }
  }
}

impl TypeExpanderDb for MockDb {
  fn type_store(&self) -> Arc<TypeStore> {
    Arc::clone(&self.store)
  }

  fn decl_type(&self, def: DefId) -> Option<TypeId> {
    self.decl_types.get(&def).copied()
  }

  fn type_params(&self, def: DefId) -> Arc<[TypeParamId]> {
    self
      .params
      .get(&def)
      .cloned()
      .unwrap_or_else(|| Arc::from([]))
  }
}

#[test]
fn db_expander_handles_eviction_and_parallel_expansion() {
  let store = TypeStore::new();
  let param = TypeParamId(0);
  let declared = store.intern_type(TypeKind::TypeParam(param));
  let def = DefId(99);

  let mut db = MockDb::new(store.clone());
  db.decl_types.insert(def, declared);
  db.params
    .insert(def, Arc::from(vec![param].into_boxed_slice()));

  let caches = EvaluatorCaches::new(CacheConfig {
    max_entries: 4,
    shard_count: 1,
  });
  let expander = DbTypeExpander::new(&db, caches.clone());

  let args: Vec<TypeId> = (0..24)
    .map(|i| store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(i as f64))))
    .collect();

  let expand_all = |expander: &DbTypeExpander<'_>| -> Vec<TypeId> {
    args
      .iter()
      .map(|arg| expander.expand_ref(store.as_ref(), def, &[*arg]).unwrap())
      .collect()
  };

  let expected = expand_all(&expander);
  for (arg, expanded) in args.iter().zip(expected.iter()) {
    assert_eq!(
      store.type_kind(*expanded),
      store.type_kind(*arg),
      "type arguments should be substituted deterministically"
    );
  }

  let repeated = expand_all(&expander);
  assert_eq!(expected, repeated, "expansions should remain deterministic");
  assert!(
    caches.stats().references.evictions > 0,
    "bounded caches should evict when over capacity"
  );

  thread::scope(|scope| {
    let mut handles = Vec::new();
    for _ in 0..4 {
      let args = args.clone();
      let expander = &expander;
      let store = store.clone();
      handles.push(scope.spawn(move || {
        args
          .iter()
          .map(|arg| expander.expand_ref(store.as_ref(), def, &[*arg]).unwrap())
          .collect::<Vec<_>>()
      }));
    }

    for handle in handles {
      let result = handle.join().expect("thread panicked");
      assert_eq!(result, expected, "parallel expansions should be stable");
    }
  });
}

#[derive(Debug)]
struct NoopExpander;

impl types_ts_interned::TypeExpander for NoopExpander {
  fn expand(
    &self,
    _store: &types_ts_interned::TypeStore,
    _def: DefId,
    _args: &[TypeId],
  ) -> Option<types_ts_interned::ExpandedType> {
    None
  }
}

#[test]
fn cache_stats_are_recorded_for_profiling() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let caches = CheckerCaches::new(CacheOptions {
    max_relation_cache_entries: 8,
    max_eval_cache_entries: 8,
    max_instantiation_cache_entries: 8,
    cache_shards: 1,
    mode: CacheMode::Shared,
    ..CacheOptions::default()
  });
  let collector = QueryStatsCollector::default();

  let body = caches.for_body();
  let relate = RelateCtx::with_cache(store.clone(), TypeOptions::default(), body.relation.clone());
  assert!(relate.is_assignable(primitives.number, primitives.number));
  assert!(relate.is_assignable(primitives.number, primitives.number));

  let mut evaluator = TypeEvaluator::with_caches(store.clone(), &NoopExpander, body.eval.clone());
  let ref_ty = store.intern_type(TypeKind::Ref {
    def: DefId(1),
    args: vec![primitives.string],
  });
  evaluator.evaluate(ref_ty);
  evaluator.evaluate(ref_ty);

  let t_param = TypeParamId(0);
  let param_ty = store.intern_type(TypeKind::TypeParam(t_param));
  let sig = Signature {
    params: vec![Param {
      name: None,
      ty: param_ty,
      optional: false,
      rest: false,
    }],
    ret: param_ty,
    type_params: vec![TypeParamDecl::new(t_param)],
    this_param: None,
  };
  let mut subst = HashMap::new();
  subst.insert(t_param, primitives.number);
  let instantiation = body.instantiation.clone();
  let sig_id = store.intern_signature(sig.clone());
  let instantiated = instantiation.instantiate_signature(&store, sig_id, &sig, &subst);
  assert_eq!(
    instantiated,
    instantiation.instantiate_signature(&store, sig_id, &sig, &subst)
  );

  let stats = body.stats();
  stats.record(&collector);

  let snapshot = collector.snapshot();
  let relation = snapshot.caches.get(&CacheKind::Relation).cloned();
  let eval = snapshot.caches.get(&CacheKind::Eval).cloned();
  let refs = snapshot.caches.get(&CacheKind::RefExpansion).cloned();
  let inst = snapshot.caches.get(&CacheKind::Instantiation).cloned();

  for (name, stat) in [
    ("relation", relation),
    ("eval", eval),
    ("ref expansion", refs),
    ("instantiation", inst),
  ] {
    let stat = stat.unwrap_or_default();
    assert!(
      stat.hits > 0 || stat.misses > 0 || stat.insertions > 0,
      "{name} stats should be recorded"
    );
  }
}

#[derive(Clone)]
struct CacheHost {
  files: HashMap<FileKey, Arc<str>>,
  options: CompilerOptions,
}

impl CacheHost {
  fn new(options: CompilerOptions) -> Self {
    Self {
      files: HashMap::new(),
      options,
    }
  }

  fn insert(&mut self, file: FileKey, source: &str) {
    self.files.insert(file, Arc::from(source.to_string()));
  }
}

impl Host for CacheHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }
}

fn relation_heavy_source() -> String {
  let mut src = String::from("export function heavy(value: number): number {\n");
  for i in 0..24 {
    src.push_str(&format!("  const v{i}: number = value + {i};\n"));
  }
  src.push_str("  return value;\n}\nheavy(1);\n");
  src
}

#[test]
fn program_cache_stats_report_evictions() {
  let options = CompilerOptions {
    cache: CacheOptions {
      max_relation_cache_entries: 4,
      max_eval_cache_entries: 0,
      max_instantiation_cache_entries: 0,
      cache_shards: 1,
      mode: CacheMode::PerBody,
      ..CacheOptions::default()
    },
    ..CompilerOptions::default()
  };
  let mut host = CacheHost::new(options);
  let key = FileKey::new("entry.ts");
  host.insert(key.clone(), &relation_heavy_source());

  let program = Program::new(host, vec![key]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected clean check run: {diagnostics:#?}"
  );

  let stats = program.query_stats();
  let relation = stats
    .caches
    .get(&CacheKind::Relation)
    .cloned()
    .unwrap_or_default();
  assert!(
    relation.evictions > 0,
    "tight caches should evict when checking relation-heavy bodies (relation stats: {relation:?})"
  );
  assert!(
    relation.hits + relation.misses > 0,
    "relation cache stats should be recorded (relation stats: {relation:?})"
  );
}

#[test]
fn program_cache_evictions_are_deterministic() {
  let options = CompilerOptions {
    cache: CacheOptions {
      max_relation_cache_entries: 2,
      max_eval_cache_entries: 0,
      max_instantiation_cache_entries: 0,
      cache_shards: 1,
      mode: CacheMode::PerBody,
      ..CacheOptions::default()
    },
    ..CompilerOptions::default()
  };
  let mut host_a = CacheHost::new(options.clone());
  let key_a = FileKey::new("entry_a.ts");
  host_a.insert(key_a.clone(), &relation_heavy_source());
  let mut host_b = CacheHost::new(options);
  let key_b = FileKey::new("entry_b.ts");
  host_b.insert(key_b.clone(), &relation_heavy_source());

  let program_a = Program::new(host_a, vec![key_a]);
  let program_b = Program::new(host_b, vec![key_b]);

  let diags_a = program_a.check();
  let diags_b = program_b.check();
  assert_eq!(
    diags_a, diags_b,
    "evicting relation caches must not affect diagnostics"
  );

  let stats_a = program_a.query_stats();
  let stats_b = program_b.query_stats();
  let evictions = stats_a
    .caches
    .get(&CacheKind::Relation)
    .map(|s| s.evictions)
    .unwrap_or(0)
    + stats_b
      .caches
      .get(&CacheKind::Relation)
      .map(|s| s.evictions)
      .unwrap_or(0);
  assert!(
    evictions > 0,
    "expected relation cache eviction under tiny bounds (stats_a: {:?}, stats_b: {:?})",
    stats_a,
    stats_b
  );
}

#[derive(Clone)]
struct SingleFileHost {
  text: Arc<str>,
  options: CompilerOptions,
}

impl SingleFileHost {
  fn new(text: impl Into<Arc<str>>, options: CompilerOptions) -> Self {
    Self {
      text: text.into(),
      options,
    }
  }
}

impl Host for SingleFileHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    if file.as_str() == "entry.ts" {
      Ok(self.text.clone())
    } else {
      Err(HostError::new(format!("missing file {file:?}")))
    }
  }

  fn resolve(&self, _from: &FileKey, _spec: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }
}

fn type_aliases(count: usize) -> String {
  let mut source = String::new();
  for i in 0..count {
    source.push_str(&format!("export type T{i} = {i};\n"));
  }
  source
}

#[test]
fn program_query_stats_include_shared_caches() {
  let source = type_aliases(16);
  let cache = CacheOptions {
    max_relation_cache_entries: 0,
    max_eval_cache_entries: 4,
    max_instantiation_cache_entries: 0,
    cache_shards: 1,
    mode: CacheMode::Shared,
    ..CacheOptions::default()
  };
  let options = CompilerOptions {
    cache,
    ..Default::default()
  };
  let host = SingleFileHost::new(source, options);
  let root = FileKey::new("entry.ts");
  let program = Program::new(host, vec![root.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected clean check run: {diagnostics:#?}"
  );

  let file_id = program.file_id(&root).expect("file id");
  let defs = program.definitions_in_file(file_id);
  for def in &defs {
    let ty = program.type_of_def_interned(*def);
    let _ = program.type_kind(ty);
  }
  for def in &defs {
    let ty = program.type_of_def_interned(*def);
    let _ = program.type_kind(ty);
  }

  let stats = program.query_stats();
  let eval = stats
    .caches
    .get(&CacheKind::Eval)
    .cloned()
    .unwrap_or_default();
  assert!(
    eval.insertions > 0 && eval.misses > 0,
    "evaluation cache stats should be populated (eval stats: {eval:?})"
  );
  assert!(
    eval.evictions > 0,
    "evictions should occur when cache bounds are exceeded (eval stats: {eval:?})"
  );
}

#[test]
fn program_accumulates_per_body_cache_stats() {
  let source = type_aliases(8);
  let cache = CacheOptions {
    max_relation_cache_entries: 0,
    max_eval_cache_entries: 2,
    max_instantiation_cache_entries: 0,
    cache_shards: 1,
    mode: CacheMode::PerBody,
    ..CacheOptions::default()
  };
  let options = CompilerOptions {
    cache,
    ..Default::default()
  };
  let host = SingleFileHost::new(source, options);
  let root = FileKey::new("entry.ts");
  let program = Program::new(host, vec![root.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected clean check run: {diagnostics:#?}"
  );

  let file_id = program.file_id(&root).expect("file id");
  let defs = program.definitions_in_file(file_id);
  for _ in 0..2 {
    for def in &defs {
      let ty = program.type_of_def_interned(*def);
      let _ = program.type_kind(ty);
    }
  }

  let stats = program.query_stats();
  let eval = stats
    .caches
    .get(&CacheKind::Eval)
    .cloned()
    .unwrap_or_default();
  assert!(
    eval.misses >= (defs.len() * 2) as u64,
    "per-body cache stats should accumulate across calls"
  );
}

#[test]
fn body_check_context_is_reused_across_bodies() {
  let source = r#"
export function first(value: number): number {
  return value + 1;
}

export function second(value: number): number {
  return value + 2;
}
"#;
  let host = SingleFileHost::new(source, CompilerOptions::default());
  let root = FileKey::new("entry.ts");
  let program = Program::new(host, vec![root.clone()]);
  let file_id = program.file_id(&root).expect("file id");
  let mut bodies: Vec<_> = program
    .definitions_in_file(file_id)
    .into_iter()
    .filter_map(|def| program.body_of_def(def))
    .collect();
  bodies.sort_by_key(|body| body.0);
  bodies.dedup();
  assert!(
    bodies.len() >= 2,
    "expected at least two function bodies in test fixture"
  );

  // Multiple distinct bodies should reuse the shared `BodyCheckContext` instead
  // of rebuilding it for each cache miss.
  let _ = program.check_body(bodies[0]);
  let _ = program.check_body(bodies[1]);

  let stats = program.query_stats();
  let builds = stats
    .queries
    .get(&QueryKind::BuildBodyContext)
    .map(|stat| stat.total)
    .unwrap_or(0);
  assert_eq!(
    builds, 1,
    "expected body check context to be built once, got {builds} ({stats:?})"
  );
}
