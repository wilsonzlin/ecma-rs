use crate::fixtures::Fixture;
use crate::fixtures::FixtureKind;
use crate::fixtures::ModuleGraphFixture;
use diagnostics::FileId as HirFileId;
use hir_js::lower_file;
use hir_js::FileKind as HirFileKind;
use hir_js::LowerResult;
use parse_js::ast::expr::pat::Pat as AstPat;
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::error::SyntaxResult;
use parse_js::parse;
use semantic_js::ts::{
  bind_ts_program, Decl, DeclKind, Export, ExportAll, Exported, HirFile, Import, ImportDefault,
  ImportNamed, ImportNamespace, NamedExport, Resolver, TextRange,
};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use typecheck_ts::FileId as TcFileId;
use typecheck_ts::Host;
use typecheck_ts::HostError;
use typecheck_ts::Program;
use types_ts::{
  FnParam, FunctionType, IndexKind, IndexSignature, MemberVisibility, ObjectType, Property,
  RelateCtx, TypeKind, TypeOptions, TypeStore,
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

#[derive(Clone, Copy, Debug)]
pub struct RelationStats {
  pub checks: usize,
  pub successes: usize,
}

pub fn parse_only(fixture: &Fixture) -> SyntaxResult<Node<TopLevel>> {
  parse(fixture.source)
}

pub fn lower_to_hir(file_id: HirFileId, top_level: &Node<TopLevel>) -> LowerResult {
  lower_file(file_id, HirFileKind::Ts, top_level)
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
    let hir = lower_semantic_hir(file_id, &parsed);
    files.insert(file_id, Arc::new(hir));
  }

  let roots = vec![semantic_js::ts::FileId(0)];

  let (program, diagnostics) = bind_ts_program(&roots, &resolver, |file_id| {
    files
      .get(&file_id)
      .cloned()
      .expect("all files should be available for binding")
  });

  let mut exports_len = 0usize;
  for idx in 0..graph.files.len() {
    let file = semantic_js::ts::FileId(idx as u32);
    exports_len += program.exports_of(file).len();
  }

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
  let host = BenchHost::new(entries);
  let root = host.id_for(fixture.name).expect("root file id");
  run_typecheck(host, vec![root])
}

pub fn typecheck_module_graph(graph: &ModuleGraphFixture) -> TypecheckSummary {
  let entries: Vec<_> = graph
    .files
    .iter()
    .map(|f| (f.name.to_string(), f.source))
    .collect();
  let host = BenchHost::new(entries);
  let root = host
    .id_for(graph.files[0].name)
    .expect("module graph root should exist");
  run_typecheck(host, vec![root])
}

pub fn assignability_micro(iterations: usize, warm_cache: bool) -> RelationStats {
  if warm_cache {
    let (store, sample) = sample_types();
    let ctx = RelateCtx::new(&store, TypeOptions::default());
    run_assignability(&ctx, iterations, &sample)
  } else {
    let mut checks = 0;
    let mut successes = 0;
    for _ in 0..iterations {
      let (store, sample) = sample_types();
      let ctx = RelateCtx::new(&store, TypeOptions::default());
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

fn sample_types() -> (TypeStore, SampleTypes) {
  let mut store = TypeStore::new();

  let numbers: Vec<_> = (0..12).map(|n| store.literal_number(n as i64)).collect();
  let wide_union = store.intern(TypeKind::Union(numbers.clone()));
  let narrow_union = store.intern(TypeKind::Union(numbers.iter().take(3).copied().collect()));

  let string_tag = store.literal_string("tag");
  let literal_zero = store.literal_number(0);
  let optional_number = store.intern(TypeKind::Union(vec![store.number(), literal_zero]));

  let tagged_object = store.intern(TypeKind::Object(ObjectType::new(
    vec![
      Property {
        name: "kind".into(),
        ty: string_tag,
        optional: false,
        readonly: true,
        is_method: false,
        visibility: MemberVisibility::Public,
        origin_id: None,
      },
      Property {
        name: "value".into(),
        ty: wide_union,
        optional: false,
        readonly: false,
        is_method: false,
        visibility: MemberVisibility::Public,
        origin_id: None,
      },
    ],
    vec![],
  )));

  let object_with_optional = store.intern(TypeKind::Object(ObjectType::new(
    vec![
      Property {
        name: "kind".into(),
        ty: string_tag,
        optional: false,
        readonly: true,
        is_method: false,
        visibility: MemberVisibility::Public,
        origin_id: None,
      },
      Property {
        name: "value".into(),
        ty: optional_number,
        optional: true,
        readonly: false,
        is_method: false,
        visibility: MemberVisibility::Public,
        origin_id: None,
      },
    ],
    vec![IndexSignature {
      kind: IndexKind::String,
      ty: wide_union,
      readonly: false,
    }],
  )));

  let fn_covariant = store.intern(TypeKind::Function(FunctionType {
    params: vec![FnParam {
      name: Some("arg".into()),
      ty: narrow_union,
      optional: false,
      rest: false,
    }],
    ret: wide_union,
    is_method: false,
    this_param: None,
  }));

  let fn_contravariant = store.intern(TypeKind::Function(FunctionType {
    params: vec![FnParam {
      name: Some("arg".into()),
      ty: wide_union,
      optional: false,
      rest: false,
    }],
    ret: narrow_union,
    is_method: false,
    this_param: None,
  }));

  let number_ty = store.number();

  let array_of_union = store.intern(TypeKind::Object(ObjectType::new(
    vec![Property {
      name: "length".into(),
      ty: number_ty,
      optional: false,
      readonly: false,
      is_method: false,
      visibility: MemberVisibility::Public,
      origin_id: None,
    }],
    vec![IndexSignature {
      kind: IndexKind::Number,
      ty: wide_union,
      readonly: false,
    }],
  )));

  let array_of_numbers = store.intern(TypeKind::Object(ObjectType::new(
    vec![Property {
      name: "length".into(),
      ty: number_ty,
      optional: false,
      readonly: false,
      is_method: false,
      visibility: MemberVisibility::Public,
      origin_id: None,
    }],
    vec![IndexSignature {
      kind: IndexKind::Number,
      ty: number_ty,
      readonly: false,
    }],
  )));

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
  wide_union: types_ts::TypeId,
  narrow_union: types_ts::TypeId,
  tagged_object: types_ts::TypeId,
  object_with_optional: types_ts::TypeId,
  fn_covariant: types_ts::TypeId,
  fn_contravariant: types_ts::TypeId,
  array_of_union: types_ts::TypeId,
  array_of_numbers: types_ts::TypeId,
}

fn run_typecheck(host: BenchHost, roots: Vec<TcFileId>) -> TypecheckSummary {
  let all_files = host.all_file_ids();
  let program = Program::new(host, roots);
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
}

#[derive(Clone)]
struct BenchHost {
  files: Vec<BenchFile>,
  name_to_id: HashMap<String, TcFileId>,
}

impl BenchHost {
  fn new(entries: Vec<(String, &'static str)>) -> Self {
    let mut files = Vec::with_capacity(entries.len());
    let mut name_to_id = HashMap::new();
    for (idx, (name, content)) in entries.into_iter().enumerate() {
      let id = TcFileId(idx as u32);
      name_to_id.insert(normalize(&PathBuf::from(&name)), id);
      files.push(BenchFile {
        name: name.clone(),
        content: Arc::from(content),
      });
    }
    BenchHost { files, name_to_id }
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

fn lower_semantic_hir(file: semantic_js::ts::FileId, ast: &Node<TopLevel>) -> HirFile {
  let mut hir = HirFile::module(file);
  let mut next_def = 0u32;

  for stmt in ast.stx.body.iter() {
    match &*stmt.stx {
      Stmt::VarDecl(var) => {
        lower_var_decl(&mut hir, &mut next_def, &var.stx);
      }
      Stmt::FunctionDecl(func) => {
        lower_function_decl(&mut hir, &mut next_def, &func.stx);
      }
      Stmt::Import(import_stmt) => {
        hir.imports.push(lower_import(&import_stmt.stx));
      }
      Stmt::ExportDefaultExpr(_) => {
        hir.decls.push(Decl {
          def_id: semantic_js::ts::DefId(next_def),
          name: "default".to_string(),
          kind: DeclKind::Var,
          is_ambient: false,
          is_global: false,
          exported: Exported::Default,
          span: TextRange::new(0, 0),
        });
        next_def += 1;
      }
      Stmt::ExportList(export_list) => match &export_list.stx.names {
        parse_js::ast::import_export::ExportNames::All(_) => {
          let specifier = export_list
            .stx
            .from
            .as_ref()
            .map(|s| s.to_string())
            .unwrap_or_default();
          hir.exports.push(Export::All(ExportAll {
            specifier,
            is_type_only: export_list.stx.type_only,
            specifier_span: TextRange::new(0, 0),
          }));
        }
        parse_js::ast::import_export::ExportNames::Specific(list) => {
          let mut named = NamedExport {
            specifier: export_list.stx.from.clone(),
            specifier_span: export_list.stx.from.as_ref().map(|_| TextRange::new(0, 0)),
            items: Vec::new(),
            is_type_only: export_list.stx.type_only,
          };
          for export_name in list.iter() {
            let exported = export_name.stx.alias.stx.name.to_string();
            named.items.push(semantic_js::ts::ExportSpecifier {
              local: export_name.stx.exportable.as_str().to_string(),
              exported: Some(exported),
              local_span: TextRange::new(0, 0),
              exported_span: Some(TextRange::new(0, 0)),
            });
          }
          hir.exports.push(Export::Named(named));
        }
      },
      _ => {}
    }
  }

  hir
}

fn lower_var_decl(hir: &mut HirFile, next_def: &mut u32, var: &VarDecl) {
  let exported = if var.export {
    Exported::Named
  } else {
    Exported::No
  };

  for declarator in var.declarators.iter() {
    for name in collect_pat_names(&declarator.pattern) {
      hir.decls.push(Decl {
        def_id: semantic_js::ts::DefId(*next_def),
        name,
        kind: DeclKind::Var,
        is_ambient: false,
        is_global: false,
        exported: exported.clone(),
        span: TextRange::new(0, 0),
      });
      *next_def += 1;
    }
  }
}

fn lower_function_decl(hir: &mut HirFile, next_def: &mut u32, func: &FuncDecl) {
  let name = func
    .name
    .as_ref()
    .map(|n| n.stx.name.clone())
    .unwrap_or_else(|| "default".to_string());
  let exported = if func.export_default {
    Exported::Default
  } else if func.export {
    Exported::Named
  } else {
    Exported::No
  };

  hir.decls.push(Decl {
    def_id: semantic_js::ts::DefId(*next_def),
    name,
    kind: DeclKind::Function,
    is_ambient: false,
    is_global: false,
    exported,
    span: TextRange::new(0, 0),
  });
  *next_def += 1;
}

fn collect_pat_names(pat: &Node<parse_js::ast::stmt::decl::PatDecl>) -> Vec<String> {
  let mut names = Vec::new();
  collect_pat_names_inner(&pat.stx.pat, &mut names);
  names
}

fn collect_pat_names_inner(pat: &Node<AstPat>, out: &mut Vec<String>) {
  match &*pat.stx {
    AstPat::Id(id) => out.push(id.stx.name.clone()),
    AstPat::Obj(obj) => {
      for prop in obj.stx.properties.iter() {
        collect_pat_names_inner(&prop.stx.target, out);
      }
      if let Some(rest) = &obj.stx.rest {
        collect_pat_names_inner(rest, out);
      }
    }
    AstPat::Arr(arr) => {
      for elem in arr.stx.elements.iter().flatten() {
        collect_pat_names_inner(&elem.target, out);
        if let Some(default) = &elem.default_value {
          if let AstExpr::Id(id) = &*default.stx {
            out.push(id.stx.name.clone());
          }
        }
      }
      if let Some(rest) = &arr.stx.rest {
        collect_pat_names_inner(rest, out);
      }
    }
    AstPat::AssignTarget(expr) => {
      if let AstExpr::Id(id) = &*expr.stx {
        out.push(id.stx.name.clone());
      }
    }
  }
}

fn lower_import(import_stmt: &parse_js::ast::stmt::ImportStmt) -> Import {
  let mut imp = Import {
    specifier: import_stmt.module.clone(),
    specifier_span: TextRange::new(0, 0),
    default: None,
    namespace: None,
    named: Vec::new(),
    is_type_only: import_stmt.type_only,
  };

  if let Some(default) = &import_stmt.default {
    let local = collect_pat_names(default)
      .into_iter()
      .next()
      .unwrap_or_else(|| "default".to_string());
    imp.default = Some(ImportDefault {
      local,
      local_span: TextRange::new(0, 0),
      is_type_only: import_stmt.type_only,
    });
  }

  if let Some(names) = &import_stmt.names {
    match names {
      parse_js::ast::import_export::ImportNames::All(pat) => {
        let local = collect_pat_names(pat)
          .into_iter()
          .next()
          .unwrap_or_else(|| "*".to_string());
        imp.namespace = Some(ImportNamespace {
          local,
          local_span: TextRange::new(0, 0),
          is_type_only: import_stmt.type_only,
        });
      }
      parse_js::ast::import_export::ImportNames::Specific(list) => {
        for item in list.iter() {
          let local = collect_pat_names(&item.stx.alias)
            .into_iter()
            .next()
            .unwrap_or_else(|| item.stx.importable.as_str().to_string());
          imp.named.push(ImportNamed {
            imported: item.stx.importable.as_str().to_string(),
            local,
            is_type_only: item.stx.type_only || import_stmt.type_only,
            imported_span: TextRange::new(0, 0),
            local_span: TextRange::new(0, 0),
          });
        }
      }
    }
  }

  imp
}
