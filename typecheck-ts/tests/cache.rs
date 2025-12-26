use std::collections::HashMap;
use std::sync::Arc;

use ordered_float::OrderedFloat;
use typecheck_ts::check::caches::{CheckerCacheStats, CheckerCaches};
use typecheck_ts::check::instantiate::InstantiationCache;
use typecheck_ts::lib_support::{CacheMode, CacheOptions, CompilerOptions};
use typecheck_ts::{CacheKind, FileKey, Host, HostError, Program, QueryStatsCollector};
use types_ts_interned::{
  DefId, Param, RelateCtx, Signature, SignatureId, TypeEvaluator, TypeId, TypeKind, TypeOptions,
  TypeParamId, TypeStore,
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
    type_params: vec![t_param],
    this_param: None,
  };
  let def = DefId(0);

  let config = CacheOptions {
    max_relation_cache_entries: 0,
    max_eval_cache_entries: 0,
    max_instantiation_cache_entries: 2,
    cache_shards: 1,
    mode: CacheMode::Shared,
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
      .map(|subst| cache.instantiate_signature(&store, def, &sig, subst))
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
    type_params: vec![t_param],
    this_param: None,
  };
  let mut subst = HashMap::new();
  subst.insert(t_param, primitives.number);
  let mut instantiation = body.instantiation.clone();
  let instantiated = instantiation.instantiate_signature(&store, DefId(0), &sig, &subst);
  assert_eq!(
    instantiated,
    instantiation.instantiate_signature(&store, DefId(0), &sig, &subst)
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
      .get(&file)
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
  let mut src = String::new();
  for i in 0..24 {
    src.push_str(&format!("const v{i}: number = {i};\n"));
  }
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
    },
    ..CompilerOptions::default()
  };
  let mut host = CacheHost::new(options);
  let file = FileKey::new("main.ts");
  host.insert(file.clone(), &relation_heavy_source());

  let program = Program::new(host, vec![file]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "expected clean check run");

  let stats = program.query_stats();
  let relation = stats
    .caches
    .get(&CacheKind::Relation)
    .cloned()
    .unwrap_or_default();
  assert!(
    relation.evictions > 0,
    "tight caches should evict when checking relation-heavy bodies"
  );
  assert!(
    relation.hits + relation.misses > 0,
    "relation cache stats should be recorded"
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
    },
    ..CompilerOptions::default()
  };
  let mut host_a = CacheHost::new(options.clone());
  let file = FileKey::new("main.ts");
  host_a.insert(file.clone(), &relation_heavy_source());
  let mut host_b = CacheHost::new(options);
  host_b.insert(file.clone(), &relation_heavy_source());

  let program_a = Program::new(host_a, vec![file.clone()]);
  let program_b = Program::new(host_b, vec![file]);

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
    "expected relation cache eviction under tiny bounds"
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
  fn file_text(&self, _file: &FileKey) -> Result<Arc<str>, HostError> {
    Ok(self.text.clone())
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
  };
  let options = CompilerOptions {
    cache,
    ..Default::default()
  };
  let host = SingleFileHost::new(source, options);
  let key = FileKey::new("file.ts");
  let program = Program::new(host, vec![key.clone()]);
  assert!(program.check().is_empty());

  let file_id = program.file_id(&key).unwrap();
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
    "evaluation cache stats should be populated"
  );
  assert!(
    eval.evictions > 0,
    "evictions should occur when cache bounds are exceeded"
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
  };
  let options = CompilerOptions {
    cache,
    ..Default::default()
  };
  let host = SingleFileHost::new(source, options);
  let key = FileKey::new("file.ts");
  let program = Program::new(host, vec![key.clone()]);
  assert!(program.check().is_empty());

  let file_id = program.file_id(&key).unwrap();
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
