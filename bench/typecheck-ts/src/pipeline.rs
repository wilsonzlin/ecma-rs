use crate::fixtures::Fixture;
use crate::fixtures::FixtureKind;
use crate::fixtures::ModuleGraphFixture;
use diagnostics::FileId as HirFileId;
use hir_js::lower_file;
use hir_js::FileKind as HirFileKind;
use hir_js::LowerResult;
use ordered_float::OrderedFloat;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::error::SyntaxResult;
use parse_js::{parse_with_options, Dialect, ParseOptions};
use semantic_js::ts::{bind_ts_program, from_hir_js::lower_to_ts_hir, HirFile, Resolver};
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};
use typecheck_ts::lib_support::{CompilerOptions, FileKind as TcFileKind, LibManager};
use typecheck_ts::FileId as TcFileId;
use typecheck_ts::FileKey;
use typecheck_ts::Host;
use typecheck_ts::HostError;
use typecheck_ts::Program;
use typecheck_ts::QueryStats;
use types_ts_interned::{
  CacheStats, Indexer, ObjectType, Param, PropData, PropKey, Property, RelateCtx, RelationCache,
  Shape, Signature, TypeId, TypeKind, TypeOptions, TypeStore,
};

#[derive(Clone, Copy, Debug)]
pub struct HirSummary {
  pub defs: usize,
  pub bodies: usize,
  pub exprs: usize,
  pub stmts: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct BindSummary {
  pub exports: usize,
  pub globals: usize,
  pub diagnostics: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct TypecheckSummary {
  pub diagnostics: usize,
  pub bodies: usize,
  pub stats: QueryStats,
}

#[derive(Clone, Debug, Serialize)]
pub struct TypeOfDefSummary {
  pub exports: usize,
  pub rendered_types: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct BodyCheckSummary {
  pub diagnostics: usize,
  pub exprs: usize,
  pub stats: QueryStats,
}

#[derive(Clone, Debug, Serialize)]
pub struct RelationStats {
  pub checks: usize,
  pub successes: usize,
  pub cache: RelationCacheSnapshot,
}

impl RelationStats {
  pub fn hit_rate(&self) -> f64 {
    self.cache.hit_rate()
  }
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct RelationCacheSnapshot {
  pub hits: u64,
  pub misses: u64,
  pub insertions: u64,
  pub evictions: u64,
}

impl RelationCacheSnapshot {
  pub fn hit_rate(&self) -> f64 {
    let lookups = self.hits + self.misses;
    if lookups == 0 {
      0.0
    } else {
      self.hits as f64 / lookups as f64
    }
  }
}

impl From<CacheStats> for RelationCacheSnapshot {
  fn from(value: CacheStats) -> Self {
    RelationCacheSnapshot {
      hits: value.hits,
      misses: value.misses,
      insertions: value.insertions,
      evictions: value.evictions,
    }
  }
}

#[derive(Clone, Debug)]
pub struct IncrementalTimings {
  pub full: Duration,
  pub edit: Duration,
  pub full_summary: TypecheckSummary,
  pub edit_summary: TypecheckSummary,
}

#[derive(Clone, Debug)]
pub struct IncrementalEdit {
  pub file: &'static str,
  pub from: &'static str,
  pub to: &'static str,
}

pub fn parse_only(fixture: &Fixture) -> SyntaxResult<Node<TopLevel>> {
  let mut opts = ParseOptions::default();
  if matches!(fixture.kind, FixtureKind::Tsx) {
    opts.dialect = Dialect::Tsx;
  }
  parse_with_options(fixture.source, opts)
}

pub fn hir_kind(kind: FixtureKind) -> HirFileKind {
  match kind {
    FixtureKind::Tsx => HirFileKind::Tsx,
    FixtureKind::Ts => HirFileKind::Ts,
  }
}

fn fixture_filename(fixture: &Fixture) -> String {
  if fixture.name.contains('.') {
    fixture.name.to_string()
  } else {
    match fixture.kind {
      FixtureKind::Tsx => format!("{}.tsx", fixture.name),
      FixtureKind::Ts => format!("{}.ts", fixture.name),
    }
  }
}

fn entries_for_fixtures(fixtures: &[&Fixture]) -> Vec<(String, Arc<str>)> {
  let mut seen = HashSet::new();
  let mut entries = Vec::new();
  let mut needs_react = false;
  for fixture in fixtures {
    let filename = fixture_filename(fixture);
    if seen.insert(filename.clone()) {
      entries.push((filename, Arc::from(fixture.source)));
    }
    if matches!(fixture.kind, FixtureKind::Tsx) {
      needs_react = true;
    }
  }
  if needs_react {
    entries.push((
      "react.d.ts".to_string(),
      Arc::from("export const FC: <T>(props: T) => any; export default {};"),
    ));
  }
  entries
}

pub fn lower_to_hir(
  file_id: HirFileId,
  kind: HirFileKind,
  top_level: &Node<TopLevel>,
) -> LowerResult {
  lower_file(file_id, kind, top_level)
}

pub fn parse_and_lower(file_id: HirFileId, fixture: &Fixture) -> HirSummary {
  let parsed = parse_only(fixture)
    .unwrap_or_else(|err| panic!("fixtures must parse ({}): {err:?}", fixture.name));
  let lowered = lower_to_hir(file_id, hir_kind(fixture.kind), &parsed);
  summarize_hir(&lowered)
}

pub fn summarize_hir(lowered: &LowerResult) -> HirSummary {
  let bodies = lowered.bodies.len();
  let mut exprs = 0;
  let mut stmts = 0;
  for body in lowered.bodies.iter() {
    exprs += body.exprs.len();
    stmts += body.stmts.len();
  }

  HirSummary {
    defs: lowered.defs.len(),
    bodies,
    exprs,
    stmts,
  }
}

pub fn bind_module_graph(graph: &ModuleGraphFixture) -> BindSummary {
  let mut files: HashMap<semantic_js::ts::FileId, Arc<HirFile>> = HashMap::new();
  let mut resolver = SemanticResolver::default();

  for (idx, fixture) in graph.files.iter().enumerate() {
    let file_id = semantic_js::ts::FileId(idx as u32);
    resolver.insert(file_id, fixture.name.to_string());
    let parsed = parse_only(fixture).expect("fixture should parse for binding");
    let lowered = lower_to_hir(file_id, hir_kind(fixture.kind), &parsed);
    let sem_hir = lower_to_ts_hir(&parsed, &lowered);
    files.insert(file_id, Arc::new(sem_hir));
  }

  let roots = vec![semantic_js::ts::FileId(0)];

  let (program, diagnostics) = bind_ts_program(&roots, &resolver, |file_id| {
    files
      .get(&file_id)
      .cloned()
      .expect("all files should be available for binding")
  });

  let exports_len: usize = files.values().map(|file| file.exports.len()).sum();

  BindSummary {
    exports: exports_len,
    globals: program.global_symbols().len(),
    diagnostics: diagnostics.len(),
  }
}

pub fn typecheck_fixture(fixture: &Fixture) -> TypecheckSummary {
  typecheck_fixture_with_options(fixture, CompilerOptions::default())
}

pub fn typecheck_fixture_with_options(
  fixture: &Fixture,
  options: CompilerOptions,
) -> TypecheckSummary {
  let filename = fixture_filename(fixture);
  let entries = entries_for_fixtures(&[fixture]);
  let host = BenchHost::with_options(entries, options);
  let root = host.key_for(&filename).expect("root file key");
  run_typecheck(host, vec![root])
}

pub fn typecheck_module_graph(graph: &ModuleGraphFixture) -> TypecheckSummary {
  typecheck_module_graph_with_options(graph, CompilerOptions::default())
}

pub fn typecheck_module_graph_with_options(
  graph: &ModuleGraphFixture,
  options: CompilerOptions,
) -> TypecheckSummary {
  let entries = entries_from_graph(graph);
  let host = BenchHost::with_options(entries, options);
  let root = host
    .key_for(graph.files[0].name)
    .expect("module graph root should exist");
  run_typecheck(host, vec![root])
}

pub fn type_of_exported_defs(graph: &ModuleGraphFixture) -> TypeOfDefSummary {
  let entries = entries_from_graph(graph);
  let host = BenchHost::new(entries);
  let root = host
    .key_for(graph.files[0].name)
    .expect("module graph root should exist");
  let keys: Vec<FileKey> = graph
    .files
    .iter()
    .filter_map(|file| host.key_for(file.name))
    .collect();
  let program = Program::new(host, vec![root]);
  let mut exports = 0usize;
  let mut rendered_types = Vec::new();

  for key in keys {
    let Some(file_id) = program.file_id(&key) else {
      continue;
    };
    for def in program.definitions_in_file(file_id) {
      exports += 1;
      let ty = program.type_of_def(def);
      rendered_types.push(program.display_type(ty).to_string());
    }
  }

  TypeOfDefSummary {
    exports,
    rendered_types,
  }
}

pub fn check_body_named(fixture: &Fixture, name: &str) -> BodyCheckSummary {
  check_body_with_warmups((fixture, name), &[], CompilerOptions::default())
}

pub fn check_body_with_warmups(
  target: (&Fixture, &str),
  warmups: &[(&Fixture, &str)],
  options: CompilerOptions,
) -> BodyCheckSummary {
  let mut fixtures: Vec<&Fixture> = Vec::with_capacity(1 + warmups.len());
  fixtures.push(target.0);
  for (fixture, _) in warmups {
    fixtures.push(*fixture);
  }
  let entries = entries_for_fixtures(&fixtures);
  let host = BenchHost::with_options(entries, options);
  let mut ids: HashMap<String, FileKey> = HashMap::new();
  let mut roots = Vec::new();
  for fixture in fixtures {
    let filename = fixture_filename(fixture);
    if let Some(key) = host.key_for(&filename) {
      if ids.insert(filename, key.clone()).is_none() {
        roots.push(key);
      }
    }
  }
  let program = Program::new(host, roots);

  for (fixture, name) in warmups {
    let filename = fixture_filename(fixture);
    let key = ids
      .get(&filename)
      .unwrap_or_else(|| panic!("missing warmup fixture {filename}"));
    let file_id = program
      .file_id(key)
      .unwrap_or_else(|| panic!("missing file id for {filename}"));
    let body = find_body_named(&program, file_id, name, fixture.name);
    let _ = program.check_body(body);
  }

  let target_filename = fixture_filename(target.0);
  let target_key = ids
    .get(&target_filename)
    .unwrap_or_else(|| panic!("missing target fixture {target_filename}"));
  let target_file = program
    .file_id(target_key)
    .unwrap_or_else(|| panic!("missing file id for {target_filename}"));
  let body = find_body_named(&program, target_file, target.1, target.0.name);
  let result = program.check_body(body);
  let stats = program.query_stats();
  BodyCheckSummary {
    diagnostics: result.diagnostics().len(),
    exprs: result.expr_spans().len(),
    stats,
  }
}

fn find_body_named(
  program: &Program,
  file: TcFileId,
  name: &str,
  fixture_name: &str,
) -> typecheck_ts::BodyId {
  let def = program
    .definitions_in_file(file)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("missing {name} definition in {fixture_name}"));
  program
    .body_of_def(def)
    .unwrap_or_else(|| panic!("missing body for {name} in {fixture_name}"))
}

pub fn incremental_recheck(
  graph: &ModuleGraphFixture,
  edit: &IncrementalEdit,
) -> IncrementalTimings {
  let entries = entries_from_graph(graph);
  let roots = vec![graph.files[0].name.to_string()];
  let manager = Arc::new(LibManager::new());

  let (full_summary, full_duration) =
    timed_typecheck(entries.clone(), roots.clone(), Arc::clone(&manager));

  let mut edited_entries = entries;
  apply_edit(&mut edited_entries, edit);

  let (edit_summary, edit_duration) = timed_typecheck(edited_entries, roots, manager);

  IncrementalTimings {
    full: full_duration,
    edit: edit_duration,
    full_summary,
    edit_summary,
  }
}

fn timed_typecheck(
  entries: Vec<(String, Arc<str>)>,
  roots: Vec<String>,
  lib_manager: Arc<LibManager>,
) -> (TypecheckSummary, Duration) {
  let started = Instant::now();
  let host = BenchHost::new(entries);
  let root_keys: Vec<FileKey> = roots
    .into_iter()
    .filter_map(|name| host.key_for(&name))
    .collect();
  let summary = run_typecheck_with_manager(host, root_keys, Some(lib_manager));
  (summary, started.elapsed())
}

fn apply_edit(entries: &mut Vec<(String, Arc<str>)>, edit: &IncrementalEdit) {
  for (name, content) in entries.iter_mut() {
    if name == edit.file {
      let replaced = content.replacen(edit.from, edit.to, 1);
      assert!(
        replaced != content.as_ref(),
        "edit text '{}' not found in {}",
        edit.from,
        edit.file
      );
      *content = Arc::from(replaced);
      return;
    }
  }
  panic!("edit target {} not found in module graph", edit.file);
}

fn entries_from_graph(graph: &ModuleGraphFixture) -> Vec<(String, Arc<str>)> {
  graph
    .files
    .iter()
    .map(|f| (f.name.to_string(), Arc::from(f.source)))
    .collect()
}

pub fn assignability_micro(iterations: usize, warm_cache: bool) -> RelationStats {
  if warm_cache {
    let (store, sample) = sample_types();
    let cache = RelationCache::default();
    let ctx = RelateCtx::with_cache(store.clone(), TypeOptions::default(), cache.clone());
    let counts = run_assignability(&ctx, iterations, &sample);
    RelationStats {
      checks: counts.checks,
      successes: counts.successes,
      cache: cache.stats().into(),
    }
  } else {
    let mut checks = 0;
    let mut successes = 0;
    let mut cache = CacheStats::default();
    for _ in 0..iterations {
      let (store, sample) = sample_types();
      let relation_cache = RelationCache::default();
      let ctx = RelateCtx::with_cache(
        store.clone(),
        TypeOptions::default(),
        relation_cache.clone(),
      );
      let stats = run_assignability(&ctx, 1, &sample);
      let cache_stats = relation_cache.stats();
      checks += stats.checks;
      successes += stats.successes;
      cache.hits += cache_stats.hits;
      cache.misses += cache_stats.misses;
      cache.insertions += cache_stats.insertions;
      cache.evictions += cache_stats.evictions;
    }
    RelationStats {
      checks,
      successes,
      cache: cache.into(),
    }
  }
}

#[derive(Default)]
struct AssignabilityCounts {
  checks: usize,
  successes: usize,
}

fn run_assignability(
  ctx: &RelateCtx<'_>,
  iterations: usize,
  sample: &SampleTypes,
) -> AssignabilityCounts {
  let mut checks = 0;
  let mut successes = 0;
  for _ in 0..iterations {
    checks += 1;
    if ctx.is_assignable(sample.narrow_union, sample.wide_union) {
      successes += 1;
    }

    checks += 1;
    if ctx.is_assignable(sample.wide_union, sample.narrow_union) {
      successes += 1;
    }

    checks += 1;
    if ctx.is_assignable(sample.tagged_object, sample.object_with_optional) {
      successes += 1;
    }

    checks += 1;
    if ctx.is_assignable(sample.fn_covariant, sample.fn_contravariant) {
      successes += 1;
    }

    checks += 1;
    if ctx.is_assignable(sample.array_of_union, sample.array_of_numbers) {
      successes += 1;
    }

    // Exercise cached path.
    let _ = ctx.explain_assignable(sample.tagged_object, sample.tagged_object);
  }

  AssignabilityCounts { checks, successes }
}

fn object_type(store: &TypeStore, shape: Shape) -> TypeId {
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj))
}

fn callable(store: &TypeStore, params: Vec<Param>, ret: TypeId) -> TypeId {
  let sig = store.intern_signature(Signature::new(params, ret));
  store.intern_type(TypeKind::Callable {
    overloads: vec![sig],
  })
}

fn sample_types() -> (Arc<TypeStore>, SampleTypes) {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let numbers: Vec<_> = (0..12)
    .map(|n| store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(n as f64))))
    .collect();
  let wide_union = store.union(numbers.clone());
  let narrow_union = store.union(numbers.iter().take(3).copied().collect());

  let string_tag = store.intern_type(TypeKind::StringLiteral(store.intern_name("tag")));
  let literal_zero = store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(0.0)));
  let optional_number = store.union(vec![primitives.number, literal_zero]);

  let tagged_object = object_type(
    &store,
    Shape {
      properties: vec![
        Property {
          key: PropKey::String(store.intern_name("kind")),
          data: PropData {
            ty: string_tag,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
        Property {
          key: PropKey::String(store.intern_name("value")),
          data: PropData {
            ty: wide_union,
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
      ],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![],
    },
  );

  let object_with_optional = object_type(
    &store,
    Shape {
      properties: vec![
        Property {
          key: PropKey::String(store.intern_name("kind")),
          data: PropData {
            ty: string_tag,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
        Property {
          key: PropKey::String(store.intern_name("value")),
          data: PropData {
            ty: optional_number,
            optional: true,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
      ],
      call_signatures: vec![],
      construct_signatures: vec![],
      indexers: vec![Indexer {
        key_type: primitives.string,
        value_type: wide_union,
        readonly: false,
      }],
    },
  );

  let fn_covariant = callable(
    &store,
    vec![Param {
      name: Some(store.intern_name("arg")),
      ty: narrow_union,
      optional: false,
      rest: false,
    }],
    wide_union,
  );

  let fn_contravariant = callable(
    &store,
    vec![Param {
      name: Some(store.intern_name("arg")),
      ty: wide_union,
      optional: false,
      rest: false,
    }],
    narrow_union,
  );

  let array_of_union = store.intern_type(TypeKind::Array {
    ty: wide_union,
    readonly: false,
  });

  let array_of_numbers = store.intern_type(TypeKind::Array {
    ty: primitives.number,
    readonly: false,
  });

  (
    store,
    SampleTypes {
      wide_union,
      narrow_union,
      tagged_object,
      object_with_optional,
      fn_covariant,
      fn_contravariant,
      array_of_union,
      array_of_numbers,
    },
  )
}

struct SampleTypes {
  wide_union: TypeId,
  narrow_union: TypeId,
  tagged_object: TypeId,
  object_with_optional: TypeId,
  fn_covariant: TypeId,
  fn_contravariant: TypeId,
  array_of_union: TypeId,
  array_of_numbers: TypeId,
}

fn run_typecheck(host: BenchHost, roots: Vec<FileKey>) -> TypecheckSummary {
  run_typecheck_with_manager(host, roots, None)
}

fn run_typecheck_with_manager(
  host: BenchHost,
  roots: Vec<FileKey>,
  lib_manager: Option<Arc<LibManager>>,
) -> TypecheckSummary {
  let program = match lib_manager {
    Some(manager) => Program::with_lib_manager(host, roots, manager),
    None => Program::new(host, roots),
  };
  let diagnostics = program.check();
  let stats = program.query_stats();

  let mut bodies = 0;
  for file in program.files() {
    if program.file_body(file).is_some() {
      bodies += 1;
    }
    for def in program.definitions_in_file(file) {
      if program.body_of_def(def).is_some() {
        bodies += 1;
      }
    }
  }

  TypecheckSummary {
    diagnostics: diagnostics.len(),
    bodies,
    stats,
  }
}

#[derive(Clone)]
struct BenchFile {
  key: FileKey,
  content: Arc<str>,
  kind: TcFileKind,
}

#[derive(Clone)]
struct BenchHost {
  files: Vec<BenchFile>,
  name_to_key: HashMap<String, FileKey>,
  key_to_name: HashMap<FileKey, String>,
  options: CompilerOptions,
}

impl BenchHost {
  fn new(entries: Vec<(String, Arc<str>)>) -> Self {
    Self::with_options(entries, CompilerOptions::default())
  }

  fn with_options(entries: Vec<(String, Arc<str>)>, options: CompilerOptions) -> Self {
    let mut files = Vec::with_capacity(entries.len());
    let mut name_to_key = HashMap::new();
    let mut key_to_name = HashMap::new();
    for (name, content) in entries.into_iter() {
      let normalized = normalize(&PathBuf::from(&name));
      let key = FileKey::new(normalized.clone());
      name_to_key.insert(normalized.clone(), key.clone());
      key_to_name.insert(key.clone(), normalized.clone());
      files.push(BenchFile {
        key,
        content,
        kind: infer_kind(&name),
      });
    }
    BenchHost {
      files,
      name_to_key,
      key_to_name,
      options,
    }
  }

  fn key_for(&self, name: &str) -> Option<FileKey> {
    self
      .name_to_key
      .get(&normalize(&PathBuf::from(name)))
      .cloned()
  }

  fn name_for_key(&self, key: &FileKey) -> Option<String> {
    self.key_to_name.get(key).cloned()
  }
}

impl Host for BenchHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .iter()
      .find(|f| &f.key == file)
      .map(|f| f.content.clone())
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn file_kind(&self, file: &FileKey) -> TcFileKind {
    self
      .files
      .iter()
      .find(|f| &f.key == file)
      .map(|f| f.kind)
      .unwrap_or(TcFileKind::Ts)
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    let from_name = self.name_for_key(from)?;
    for cand in candidate_paths(&from_name, specifier) {
      if let Some(key) = self.name_to_key.get(&cand) {
        return Some(key.clone());
      }
    }
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }
}

#[derive(Default)]
struct SemanticResolver {
  id_to_name: Vec<String>,
  name_to_id: HashMap<String, semantic_js::ts::FileId>,
}

impl SemanticResolver {
  fn insert(&mut self, id: semantic_js::ts::FileId, name: String) {
    let idx = id.0 as usize;
    if self.id_to_name.len() <= idx {
      self.id_to_name.resize(idx + 1, String::new());
    }
    self.id_to_name[idx] = normalize(&PathBuf::from(&name));
    self.name_to_id.insert(normalize(&PathBuf::from(name)), id);
  }
}

impl Resolver for SemanticResolver {
  fn resolve(
    &self,
    from: semantic_js::ts::FileId,
    specifier: &str,
  ) -> Option<semantic_js::ts::FileId> {
    let from_name = self
      .id_to_name
      .get(from.0 as usize)
      .map(|s| s.as_str())
      .unwrap_or_default();
    for cand in candidate_paths(from_name, specifier) {
      if let Some(id) = self.name_to_id.get(&cand) {
        return Some(*id);
      }
    }
    None
  }
}

fn infer_kind(name: &str) -> TcFileKind {
  if name.ends_with(".d.ts") {
    return TcFileKind::Dts;
  }
  match Path::new(name).extension().and_then(|ext| ext.to_str()) {
    Some("tsx") => TcFileKind::Tsx,
    Some("jsx") => TcFileKind::Jsx,
    Some("js") => TcFileKind::Js,
    _ => TcFileKind::Ts,
  }
}

fn candidate_paths(from_name: &str, specifier: &str) -> Vec<String> {
  let from_path = Path::new(from_name);
  let base_dir = from_path.parent().unwrap_or_else(|| Path::new(""));
  let joined = if specifier.starts_with("./") || specifier.starts_with("../") {
    base_dir.join(specifier)
  } else {
    PathBuf::from(specifier)
  };

  let mut candidates = Vec::new();
  push_candidates(&joined, &mut candidates);
  candidates
}

fn push_candidates(path: &Path, candidates: &mut Vec<String>) {
  let normalized = normalize(path);
  candidates.push(normalized.clone());

  let has_ext = path.extension().is_some();
  if !has_ext {
    for ext in ["ts", "tsx", "d.ts", "js", "jsx"] {
      let mut with_ext = path.to_path_buf();
      with_ext.set_extension(ext);
      candidates.push(normalize(&with_ext));
    }
  } else if path.extension().and_then(|e| e.to_str()) == Some("js") {
    let mut ts = path.to_path_buf();
    ts.set_extension("ts");
    candidates.push(normalize(&ts));
    let mut tsx = path.to_path_buf();
    tsx.set_extension("tsx");
    candidates.push(normalize(&tsx));
  }
}

fn normalize(path: &Path) -> String {
  path.to_string_lossy().replace('\\', "/")
}
