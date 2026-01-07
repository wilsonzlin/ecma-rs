//! Emit a small, deterministic JSON payload describing a `typecheck-ts` run.
//!
//! This example is intended as a template for downstream tooling (CLIs, language
//! servers, snapshot-based tests). It avoids filesystem I/O by using
//! [`typecheck_ts::MemoryHost`] and prints a stable JSON schema.
//!
//! ## Schema
//!
//! ```text
//! {
//!   schema_version: 1,
//!   diagnostics: Diagnostic[],
//!   queries: {
//!     exports_of: { "<file>": { "<export_name>": "<display_type>" } },
//!     type_at: [{ file, offset, type }],
//!     symbol_at: [{ file, offset, symbol_id, name, def_id, type }]
//!   }
//! }
//! ```
//!
//! All collections use stable ordering so that redirecting stdout to a file
//! produces a deterministic snapshot.

use std::collections::BTreeMap;

use diagnostics::{sort_diagnostics, Diagnostic, FileId, Label, Severity, Span, TextRange};
use serde::Serialize;
use typecheck_ts::{FileKey, MemoryHost, Program, TypeId};

const INDEX_TS: &str = r#"import { add } from "./math";

export const total = add(1, 2);
export const message = `total=${total}`;

const bad: number = "oops";
"#;

const MATH_TS: &str = r#"export function add(a: number, b: number) {
  return a + b;
}
"#;

#[derive(Serialize)]
struct Snapshot {
  schema_version: u32,
  diagnostics: Vec<DiagnosticSnapshot>,
  queries: QueriesSnapshot,
}

#[derive(Serialize)]
struct DiagnosticSnapshot {
  code: String,
  severity: String,
  message: String,
  primary: SpanSnapshot,
  labels: Vec<LabelSnapshot>,
  notes: Vec<String>,
}

#[derive(Serialize)]
struct SpanSnapshot {
  file: String,
  range: RangeSnapshot,
}

#[derive(Serialize)]
struct RangeSnapshot {
  start: u32,
  end: u32,
}

#[derive(Serialize)]
struct LabelSnapshot {
  span: SpanSnapshot,
  message: String,
  is_primary: bool,
}

#[derive(Serialize)]
struct QueriesSnapshot {
  exports_of: BTreeMap<String, BTreeMap<String, String>>,
  type_at: Vec<TypeAtSnapshot>,
  symbol_at: Vec<SymbolAtSnapshot>,
}

#[derive(Serialize)]
struct TypeAtSnapshot {
  file: String,
  offset: u32,
  #[serde(rename = "type")]
  ty: String,
}

#[derive(Serialize)]
struct SymbolAtSnapshot {
  file: String,
  offset: u32,
  symbol_id: u64,
  name: Option<String>,
  def_id: Option<u32>,
  #[serde(rename = "type")]
  ty: Option<String>,
}

fn main() {
  let index_key = FileKey::new("index.ts");
  let math_key = FileKey::new("math.ts");

  let mut host = MemoryHost::new();
  host.insert(index_key.clone(), INDEX_TS);
  host.insert(math_key.clone(), MATH_TS);
  host.link(index_key.clone(), "./math", math_key.clone());

  let program = Program::new(host, vec![index_key.clone()]);

  let mut diagnostics = program.check();
  sort_diagnostics(&mut diagnostics);

  let index_file = program.file_id(&index_key).expect("index.ts is loaded");
  let math_file = program.file_id(&math_key).expect("math.ts is loaded");

  let exports_of = BTreeMap::from([
    (
      index_key.as_str().to_string(),
      exports_to_snapshot(&program, index_file),
    ),
    (
      math_key.as_str().to_string(),
      exports_to_snapshot(&program, math_file),
    ),
  ]);

  let add_offset = INDEX_TS.rfind("add(1, 2)").expect("add call exists") as u32;
  let add_ty = program.type_at(index_file, add_offset).expect("type_at succeeded");

  let total_offset = INDEX_TS
    .find("total =")
    .expect("total declaration exists") as u32;
  let symbol_id = program.symbol_at(index_file, total_offset).expect("symbol_at succeeded");
  let symbol_info = program.symbol_info(symbol_id);
  let symbol_ty = symbol_info
    .as_ref()
    .and_then(|info| info.type_id.or(info.def.map(|def| program.type_of_def(def))))
    .map(|ty| program.display_type(ty).to_string());

  let snapshot = Snapshot {
    schema_version: 1,
    diagnostics: diagnostics
      .into_iter()
      .map(|diag| diagnostic_to_snapshot(&program, diag))
      .collect(),
    queries: QueriesSnapshot {
      exports_of,
      type_at: vec![TypeAtSnapshot {
        file: index_key.as_str().to_string(),
        offset: add_offset,
        ty: program.display_type(add_ty).to_string(),
      }],
      symbol_at: vec![SymbolAtSnapshot {
        file: index_key.as_str().to_string(),
        offset: total_offset,
        symbol_id: symbol_id.0,
        name: symbol_info.as_ref().and_then(|info| info.name.clone()),
        def_id: symbol_info.as_ref().and_then(|info| info.def.map(|def| def.0)),
        ty: symbol_ty,
      }],
    },
  };

  println!(
    "{}",
    serde_json::to_string_pretty(&snapshot).expect("serialize snapshot")
  );
}

fn exports_to_snapshot(program: &Program, file: FileId) -> BTreeMap<String, String> {
  program
    .exports_of(file)
    .into_iter()
    .map(|(name, entry)| {
      let ty: Option<TypeId> = entry.type_id.or(entry.def.map(|def| program.type_of_def(def)));
      let ty = ty.map(|ty| program.display_type(ty).to_string());
      (name, ty.unwrap_or_else(|| "<unknown>".to_string()))
    })
    .collect()
}

fn diagnostic_to_snapshot(program: &Program, diagnostic: Diagnostic) -> DiagnosticSnapshot {
  DiagnosticSnapshot {
    code: diagnostic.code.as_str().to_string(),
    severity: severity_to_string(diagnostic.severity),
    message: diagnostic.message,
    primary: span_to_snapshot(program, diagnostic.primary),
    labels: diagnostic
      .labels
      .into_iter()
      .map(|label| label_to_snapshot(program, label))
      .collect(),
    notes: diagnostic.notes,
  }
}

fn label_to_snapshot(program: &Program, label: Label) -> LabelSnapshot {
  LabelSnapshot {
    span: span_to_snapshot(program, label.span),
    message: label.message,
    is_primary: label.is_primary,
  }
}

fn span_to_snapshot(program: &Program, span: Span) -> SpanSnapshot {
  SpanSnapshot {
    file: file_name(program, span.file),
    range: range_to_snapshot(span.range),
  }
}

fn range_to_snapshot(range: TextRange) -> RangeSnapshot {
  RangeSnapshot {
    start: range.start,
    end: range.end,
  }
}

fn file_name(program: &Program, file: FileId) -> String {
  program
    .file_key(file)
    .map(|key| key.to_string())
    .unwrap_or_else(|| format!("<FileId {}>", file.0))
}

fn severity_to_string(severity: Severity) -> String {
  severity.as_str().to_string()
}
