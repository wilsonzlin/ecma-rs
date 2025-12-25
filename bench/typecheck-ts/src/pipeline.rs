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
use semantic_js::ts::{
  bind_ts_program,
  from_hir_js::lower_to_ts_hir,
  HirFile,
  Resolver,
};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};
use typecheck_ts::lib_support::{FileKind as TcFileKind, LibManager};
use typecheck_ts::FileId as TcFileId;
use typecheck_ts::Host;
use typecheck_ts::HostError;
use typecheck_ts::Program;
use types_ts_interned::{
  Indexer, ObjectType, Param, PropData, PropKey, Property, RelateCtx, Shape, Signature, TypeId,
  TypeKind, TypeOptions, TypeStore,
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

#[derive(Clone, Copy, Debug)]
pub struct TypecheckSummary {
  pub diagnostics: usize,
  pub bodies: usize,
}

#[derive(Clone, Debug)]
pub struct TypeOfDefSummary {
  pub exports: usize,
  pub rendered_types: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct BodyCheckSummary {
  pub diagnostics: usize,
  pub exprs: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct RelationStats {
  pub checks: usize,
  pub successes: usize,
}

#[derive(Clone, Debug)]
pub struct IncrementalTimings {
  pub full: Duration,
  pub edit: Duration,
  pub full_diagnostics: usize,
  pub edit_diagnostics: usize,
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

pub fn lower_to_hir(file_id: HirFileId, top_level: &Node<TopLevel>) -> LowerResult {
  lower_file(file_id, HirFileKind::Ts, top_level)
}

pub fn parse_and_lower(file_id: HirFileId, fixture: &Fixture) -> HirSummary {
  let parsed = parse_only(fixture)
    .unwrap_or_else(|err| panic!("fixtures must parse ({}): {err:?}", fixture.name));
  let lowered = lower_to_hir(file_id, &parsed);
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
    let lowered = lower_to_hir(file_id, &parsed);
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
  let mut entries = vec![(fixture.name.to_string(), fixture.source)];
  if matches!(fixture.kind, FixtureKind::Tsx) {
    entries.push((
      "react.d.ts".to_string(),
      "export const FC: <T>(props: T) => any; export default {};",
    ));
  }
  let host = BenchHost::from_static(entries);
  let root = host.id_for(fixture.name).expect("root file id");
  run_typecheck(host, vec![root])
}

pub fn typecheck_module_graph(graph: &ModuleGraphFixture) -> TypecheckSummary {
  let entries = entries_from_graph(graph);
  let host = BenchHost::new(entries);
  let root = host
    .id_for(graph.files[0].name)
    .expect("module graph root should exist");
  run_typecheck(host, vec![root])
}

pub fn type_of_exported_defs(graph: &ModuleGraphFixture) -> TypeOfDefSummary {
  let entries = entries_from_graph(graph);
  let host = BenchHost::new(entries);
  let root = host
    .id_for(graph.files[0].name)
    .expect("module graph root should exist");
  let program = Program::new(host, vec![root]);
  let mut exports = 0usize;
  let mut rendered_types = Vec::new();

  for (idx, _) in graph.files.iter().enumerate() {
    let file_id = TcFileId(idx as u32);
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
  let host = BenchHost::from_static(vec![(fixture.name.to_string(), fixture.source)]);
  let root = host.id_for(fixture.name).expect("fixture root file id");
  let program = Program::new(host, vec![root]);
  let def = program
    .definitions_in_file(root)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("missing {name} definition in {}", fixture.name));
  let body = program
    .body_of_def(def)
    .unwrap_or_else(|| panic!("missing body for {name} in {}", fixture.name));
  let result = program.check_body(body);
  BodyCheckSummary {
    diagnostics: result.diagnostics().len(),
    exprs: result.expr_spans().len(),
  }
}

pub fn incremental_recheck(
  graph: &ModuleGraphFixture,
  edit: &IncrementalEdit,
) -> IncrementalTimings {
  let entries = entries_from_graph(graph);
  let roots = vec![TcFileId(0)];
  let manager = Arc::new(LibManager::new());

  let (full_summary, full_duration) =
    timed_typecheck(entries.clone(), roots.clone(), Arc::clone(&manager));

  let mut edited_entries = entries;
  apply_edit(&mut edited_entries, edit);

  let (edit_summary, edit_duration) = timed_typecheck(edited_entries, roots, manager);

  IncrementalTimings {
    full: full_duration,
    edit: edit_duration,
    full_diagnostics: full_summary.diagnostics,
    edit_diagnostics: edit_summary.diagnostics,
  }
}

fn timed_typecheck(
  entries: Vec<(String, Arc<str>)>,
  roots: Vec<TcFileId>,
  lib_manager: Arc<LibManager>,
) -> (TypecheckSummary, Duration) {
  let started = Instant::now();
  let host = BenchHost::new(entries);
  let summary = run_typecheck_with_manager(host, roots, Some(lib_manager));
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
    let ctx = RelateCtx::new(store.clone(), TypeOptions::default());
    run_assignability(&ctx, iterations, &sample)
  } else {
    let mut checks = 0;
    let mut successes = 0;
    for _ in 0..iterations {
      let (store, sample) = sample_types();
      let ctx = RelateCtx::new(store.clone(), TypeOptions::default());
      let stats = run_assignability(&ctx, 1, &sample);
      checks += stats.checks;
      successes += stats.successes;
    }
    RelationStats { checks, successes }
  }
}

fn run_assignability(
  ctx: &RelateCtx<'_>,
  iterations: usize,
  sample: &SampleTypes,
) -> RelationStats {
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

  RelationStats { checks, successes }
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

fn run_typecheck(host: BenchHost, roots: Vec<TcFileId>) -> TypecheckSummary {
  run_typecheck_with_manager(host, roots, None)
}

fn run_typecheck_with_manager(
  host: BenchHost,
  roots: Vec<TcFileId>,
  lib_manager: Option<Arc<LibManager>>,
) -> TypecheckSummary {
  let all_files = host.all_file_ids();
  let program = match lib_manager {
    Some(manager) => Program::with_lib_manager(host, roots, manager),
    None => Program::new(host, roots),
  };
  let diagnostics = program.check();

  let mut bodies = 0;
  for file in all_files {
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
  }
}

#[derive(Clone)]
struct BenchFile {
  name: String,
  content: Arc<str>,
  kind: TcFileKind,
}

#[derive(Clone)]
struct BenchHost {
  files: Vec<BenchFile>,
  name_to_id: HashMap<String, TcFileId>,
}

impl BenchHost {
  fn new(entries: Vec<(String, Arc<str>)>) -> Self {
    let mut files = Vec::with_capacity(entries.len());
    let mut name_to_id = HashMap::new();
    for (idx, (name, content)) in entries.into_iter().enumerate() {
      let id = TcFileId(idx as u32);
      name_to_id.insert(normalize(&PathBuf::from(&name)), id);
      files.push(BenchFile {
        name: name.clone(),
        content,
        kind: infer_kind(&name),
      });
    }
    BenchHost { files, name_to_id }
  }

  fn from_static(entries: Vec<(String, &'static str)>) -> Self {
    let owned = entries
      .into_iter()
      .map(|(name, content)| (name, Arc::from(content)))
      .collect();
    BenchHost::new(owned)
  }

  fn id_for(&self, name: &str) -> Option<TcFileId> {
    self
      .name_to_id
      .get(&normalize(&PathBuf::from(name)))
      .copied()
  }

  fn all_file_ids(&self) -> Vec<TcFileId> {
    (0..self.files.len())
      .map(|idx| TcFileId(idx as u32))
      .collect()
  }
}

impl Host for BenchHost {
  fn file_text(&self, file: TcFileId) -> Result<Arc<str>, HostError> {
    let idx = file.0 as usize;
    self
      .files
      .get(idx)
      .map(|f| f.content.clone())
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn file_kind(&self, file: TcFileId) -> TcFileKind {
    self
      .files
      .get(file.0 as usize)
      .map(|f| f.kind)
      .unwrap_or(TcFileKind::Ts)
  }

  fn resolve(&self, from: TcFileId, specifier: &str) -> Option<TcFileId> {
    let from_name = self
      .files
      .get(from.0 as usize)
      .map(|f| f.name.as_str())
      .unwrap_or_default();
    for cand in candidate_paths(from_name, specifier) {
      if let Some(id) = self.name_to_id.get(&cand) {
        return Some(*id);
      }
    }
    None
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
