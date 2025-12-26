use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;
use std::thread;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::semantic_js;
use typecheck_ts::{
  BodyId, DefId, Diagnostic, ExprId, FileId, Host, HostError, PatId, Program, TextRange, TypeId,
};

const ITERATIONS: usize = 128;
const ROOT_MAIN: FileId = FileId(0);
const ROOT_DEP: FileId = FileId(1);
const LIB_ID: FileId = FileId(1000);

#[derive(Clone)]
struct DeterministicHost {
  files: Arc<HashMap<FileId, Arc<str>>>,
  edges: Arc<HashMap<(FileId, String), FileId>>,
  libs: Arc<Vec<LibFile>>,
}

impl DeterministicHost {
  fn new() -> Self {
    let mut files = HashMap::new();
    files.insert(
      ROOT_MAIN,
      Arc::from(
        r#"
          import { value, makeLabel } from "./b";

          export function combine(a: number, b: string) {
            return makeLabel(a) + b;
          }

          export const folded = {
            total: value,
            label: makeLabel(value),
          };

          export const mismatch: number = "not a number";
        "#,
      ),
    );
    files.insert(
      ROOT_DEP,
      Arc::from(
        r#"
          export const value: number = 41;
          export function makeLabel(input: number): string {
            return "" + input;
          }
        "#,
      ),
    );

    let mut edges = HashMap::new();
    edges.insert((ROOT_MAIN, "./b".to_string()), ROOT_DEP);

    let libs = vec![LibFile {
      id: LIB_ID,
      name: Arc::from("deterministic.d.ts"),
      kind: FileKind::Dts,
      text: Arc::from("declare const implicit: any;"),
    }];

    DeterministicHost {
      files: Arc::new(files),
      edges: Arc::new(edges),
      libs: Arc::new(libs),
    }
  }
}

impl Host for DeterministicHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    self.edges.get(&(from, specifier.to_string())).copied()
  }

  fn compiler_options(&self) -> CompilerOptions {
    CompilerOptions {
      no_default_lib: true,
      ..CompilerOptions::default()
    }
  }

  fn lib_files(&self) -> Vec<LibFile> {
    (*self.libs).clone()
  }

  fn file_kind(&self, file: FileId) -> FileKind {
    if self.libs.iter().any(|lib| lib.id == file) {
      FileKind::Dts
    } else {
      FileKind::Ts
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExportSnapshot {
  symbol: semantic_js::SymbolId,
  def: Option<DefId>,
  type_id: Option<TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ExportSpacesSnapshot {
  values: BTreeMap<String, ExportSnapshot>,
  types: BTreeMap<String, ExportSnapshot>,
  namespaces: BTreeMap<String, ExportSnapshot>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BodySnapshot {
  diagnostics: Vec<Diagnostic>,
  expr_types: Vec<Option<TypeId>>,
  pat_types: Vec<Option<TypeId>>,
  expr_spans: Vec<TextRange>,
  pat_spans: Vec<TextRange>,
  return_types: Vec<TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DeterministicSnapshot {
  diagnostics: Vec<Diagnostic>,
  exports: BTreeMap<FileId, ExportSpacesSnapshot>,
  def_types: BTreeMap<DefId, TypeId>,
  interned_types: BTreeMap<DefId, TypeId>,
  bodies: BTreeMap<BodyId, BodySnapshot>,
}

fn collect_body_ids(program: &Program, files: &[FileId]) -> Vec<BodyId> {
  let mut ids = BTreeSet::new();
  for &file in files {
    if let Some(body) = program.file_body(file) {
      ids.insert(body);
    }
    let mut defs = program.definitions_in_file(file);
    defs.sort_by_key(|d| d.0);
    for def in defs {
      if let Some(body) = program.body_of_def(def) {
        ids.insert(body);
      }
    }
  }
  ids.into_iter().collect()
}

fn snapshot_body(program: &Program, body: BodyId) -> BodySnapshot {
  let result = program.check_body(body);
  let mut diagnostics = result.diagnostics().to_vec();
  codes::normalize_diagnostics(&mut diagnostics);
  let expr_spans = result.expr_spans().to_vec();
  let expr_types = expr_spans
    .iter()
    .enumerate()
    .map(|(idx, _)| result.expr_type(ExprId(idx as u32)))
    .collect();
  let mut pat_spans = Vec::new();
  let mut pat_types = Vec::new();
  for idx in 0u32.. {
    let pat = PatId(idx);
    match result.pat_span(pat) {
      Some(span) => {
        pat_spans.push(span);
        pat_types.push(result.pat_type(pat));
      }
      None => break,
    }
  }
  BodySnapshot {
    diagnostics,
    expr_types,
    pat_types,
    expr_spans,
    pat_spans,
    return_types: result.return_types().to_vec(),
  }
}

fn snapshot_program(program: &Program, files: &[FileId]) -> DeterministicSnapshot {
  let mut diagnostics = program.check();
  codes::normalize_diagnostics(&mut diagnostics);

  let mut exports = BTreeMap::new();
  for &file in files {
    let map = program.exports_of(file);
    let converted = ExportSpacesSnapshot {
      values: convert_exports(&map.values),
      types: convert_exports(&map.types),
      namespaces: convert_exports(&map.namespaces),
    };
    exports.insert(file, converted);
  }

  let mut def_types = BTreeMap::new();
  let mut interned_types = BTreeMap::new();
  for &file in files {
    let mut defs = program.definitions_in_file(file);
    defs.sort_by_key(|d| d.0);
    for def in defs {
      def_types.insert(def, program.type_of_def(def));
      interned_types.insert(def, program.type_of_def_interned(def));
    }
  }

  let mut bodies = BTreeMap::new();
  for body in collect_body_ids(program, files) {
    bodies.insert(body, snapshot_body(program, body));
  }

  DeterministicSnapshot {
    diagnostics,
    exports,
    def_types,
    interned_types,
    bodies,
  }
}

fn convert_exports(map: &typecheck_ts::ExportMap) -> BTreeMap<String, ExportSnapshot> {
  map
    .iter()
    .map(|(name, entry)| {
      (
        name.clone(),
        ExportSnapshot {
          symbol: entry.symbol,
          def: entry.def,
          type_id: entry.type_id,
        },
      )
    })
    .collect()
}

fn run_parallel_bodies(program: &Arc<Program>, bodies: &[BodyId]) {
  thread::scope(|scope| {
    for &body in bodies {
      let program = Arc::clone(program);
      scope.spawn(move || {
        let _ = program.check_body(body);
      });
    }
  });
}

#[test]
fn outputs_remain_deterministic() {
  let files = [ROOT_MAIN, ROOT_DEP];
  let host = DeterministicHost::new();
  let roots = vec![ROOT_MAIN, ROOT_DEP];
  let reversed_roots = vec![ROOT_DEP, ROOT_MAIN];

  let baseline_program = Arc::new(Program::new(host.clone(), roots.clone()));
  let baseline_bodies = collect_body_ids(&baseline_program, &files);
  run_parallel_bodies(&baseline_program, &baseline_bodies);
  let baseline = snapshot_program(&baseline_program, &files);
  let repeat = snapshot_program(&baseline_program, &files);
  assert_eq!(
    repeat, baseline,
    "same program should remain stable across multiple checks"
  );

  for iteration in 0..ITERATIONS {
    let program = Arc::new(Program::new(
      host.clone(),
      if iteration % 2 == 0 {
        roots.clone()
      } else {
        reversed_roots.clone()
      },
    ));
    let body_ids = collect_body_ids(&program, &files);
    run_parallel_bodies(&program, &body_ids);
    let snapshot = snapshot_program(&program, &files);
    assert_eq!(snapshot, baseline, "iteration {iteration} drifted");
  }
}
