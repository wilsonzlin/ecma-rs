use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{sort_diagnostics, Diagnostic, FileId};
use typecheck_ts::{FileKey, MemoryHost, Program, TypeId};

const INDEX_TS: &str = r#"import { add } from "./math";

export const total = add(1, 2);
export const message = `total=${total}`;

// Intentional type error to demonstrate diagnostics.
const bad: number = "oops";
"#;

const MATH_TS: &str = r#"export function add(a: number, b: number) {
  return a + b;
}
"#;

struct ProgramSourceProvider {
  names: BTreeMap<FileId, String>,
  texts: BTreeMap<FileId, Arc<str>>,
}

impl ProgramSourceProvider {
  fn new(program: &Program, diagnostics: &[Diagnostic]) -> Self {
    let mut file_ids = BTreeSet::new();
    for diagnostic in diagnostics {
      file_ids.insert(diagnostic.primary.file);
      for label in &diagnostic.labels {
        file_ids.insert(label.span.file);
      }
    }

    let mut names = BTreeMap::new();
    let mut texts = BTreeMap::new();
    for file in file_ids {
      let name = program
        .file_key(file)
        .map(|key| key.to_string())
        .unwrap_or_else(|| format!("<FileId {}>", file.0));
      names.insert(file, name);
      if let Some(text) = program.file_text(file) {
        texts.insert(file, text);
      }
    }

    Self { names, texts }
  }
}

impl SourceProvider for ProgramSourceProvider {
  fn file_name(&self, file: FileId) -> Option<&str> {
    self.names.get(&file).map(|name| name.as_str())
  }

  fn file_text(&self, file: FileId) -> Option<&str> {
    self.texts.get(&file).map(|text| text.as_ref())
  }
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

  if diagnostics.is_empty() {
    println!("No diagnostics.");
  } else {
    let sources = ProgramSourceProvider::new(&program, &diagnostics);
    for diagnostic in &diagnostics {
      print!("{}", render_diagnostic(&sources, diagnostic));
    }
  }

  let index_file = program.file_id(&index_key).expect("index.ts is loaded");
  let math_file = program.file_id(&math_key).expect("math.ts is loaded");

  println!();
  println!("== Program queries ==");

  // 1) exports_of
  println!();
  print_exports(&program, index_key.as_str(), index_file);
  print_exports(&program, math_key.as_str(), math_file);

  // 2) type_of_def + display_type
  let index_exports = program.exports_of(index_file);
  let total_def = index_exports
    .get("total")
    .and_then(|entry| entry.def)
    .expect("total is an exported definition");
  let total_ty = program.type_of_def(total_def);
  println!();
  println!("type_of_def(total) = {}", program.display_type(total_ty));

  // 3) type_at + display_type
  let add_offset = INDEX_TS
    .rfind("add(1, 2)")
    .expect("add call exists") as u32;
  let add_ty = program
    .type_at(index_file, add_offset)
    .expect("type_at should find an expression");
  println!();
  println!("type_at(index.ts@{add_offset}) = {}", program.display_type(add_ty));

  // 4) symbol_at
  let total_ref_offset = INDEX_TS
    .find("total =")
    .expect("total declaration exists") as u32;
  let symbol = program
    .symbol_at(index_file, total_ref_offset)
    .expect("symbol_at should find `total`");
  let symbol_info = program.symbol_info(symbol).expect("symbol info exists");
  println!();
  println!("symbol_at(index.ts@{total_ref_offset}) = {symbol:?}");
  println!("  name: {:?}", symbol_info.name);
  println!("  def: {:?}", symbol_info.def);
  if let Some(ty) = symbol_info.type_id.or(symbol_info.def.map(|def| program.type_of_def(def))) {
    println!("  type: {}", program.display_type(ty));
  }
}

fn print_exports(program: &Program, file_name: &str, file: FileId) {
  println!("exports_of({file_name}):");
  for (name, entry) in program.exports_of(file) {
    let ty: Option<TypeId> = entry.type_id.or(entry.def.map(|def| program.type_of_def(def)));
    let ty_display = ty
      .map(|ty| program.display_type(ty).to_string())
      .unwrap_or_else(|| "<unknown>".to_string());
    println!("  {name}: {ty_display}");
  }
}
