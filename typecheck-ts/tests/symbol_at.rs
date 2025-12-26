use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::semantic_js::SymbolId;
use typecheck_ts::{FileId, Host, HostError, Program, TextRange};

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileId, Arc<str>>,
  edges: HashMap<(FileId, String), FileId>,
}

impl MemoryHost {
  fn insert(&mut self, id: FileId, text: &str) {
    self.files.insert(id, Arc::from(text.to_string()));
  }

  fn link(&mut self, from: FileId, spec: &str, to: FileId) {
    self.edges.insert((from, spec.to_string()), to);
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: FileId, spec: &str) -> Option<FileId> {
    self.edges.get(&(from, spec.to_string())).copied()
  }
}

fn positions_of(source: &str, needle: &str) -> Vec<u32> {
  let mut positions = Vec::new();
  let mut start = 0usize;
  while let Some(found) = source[start..].find(needle) {
    let pos = start + found;
    positions.push(pos as u32);
    start = pos + needle.len();
  }
  positions
}

fn symbol_for_occurrence(
  program: &Program,
  file: FileId,
  source: &str,
  needle: &str,
  occurrence: usize,
) -> SymbolId {
  let positions = positions_of(source, needle);
  let start = *positions
    .get(occurrence)
    .unwrap_or_else(|| panic!("missing occurrence {occurrence} of '{needle}'"));
  let end = start + needle.len() as u32;
  let search_start = start.saturating_sub(8);
  let search_end = (end + 8).min(source.len() as u32);
  let mut offsets: Vec<u32> = (start..end).collect();
  offsets.extend(end..search_end);
  offsets.extend(search_start..start);
  offsets
    .into_iter()
    .find_map(|offset| program.symbol_at(file, offset))
    .unwrap_or_else(|| {
      panic!(
        "no symbol for '{needle}' occurrence {occurrence} in range {search_start}..{search_end}"
      )
    })
}

#[test]
fn expr_at_prefers_innermost_span() {
  let mut host = MemoryHost::default();
  let source = "const value = 1 + (2 + 3);";
  let file = FileId(0);
  host.insert(file, source);

  let program = Program::new(host, vec![file]);
  let main_body = program.file_body(file).expect("body for file");
  let result = program.check_body(main_body);
  let mut spans = Vec::new();
  let mut idx = 0;
  loop {
    let expr_id = typecheck_ts::ExprId(idx);
    if let Some(span) = result.expr_span(expr_id) {
      spans.push((expr_id, span));
      idx += 1;
    } else {
      break;
    }
  }

  let mut target: Option<(typecheck_ts::ExprId, TextRange)> = None;
  'outer: for (outer_id, outer_span) in spans.iter() {
    for (inner_id, inner_span) in spans.iter() {
      if outer_id == inner_id {
        continue;
      }
      if outer_span.start <= inner_span.start
        && inner_span.end <= outer_span.end
        && outer_span.end > outer_span.start
        && inner_span.end > inner_span.start
      {
        target = Some((*inner_id, *inner_span));
        break 'outer;
      }
    }
  }

  let (_expected_expr, expected_span) = target.expect("nested expressions");
  let offset = expected_span.start;

  let (found_body, expr) = program.expr_at(file, offset).expect("expression at offset");
  assert_eq!(found_body, main_body);
  let span = result.expr_span(expr).expect("expr span");
  assert_eq!(span, expected_span);

  let ty = program.type_at(file, offset).expect("type at offset");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn symbol_at_resolves_imports() {
  let mut host = MemoryHost::default();
  let file_a = FileId(0);
  let file_b = FileId(1);
  let source_a = "export function foo() { return 1; }";
  let source_b = "import { foo } from \"./a\";\nexport const result = foo();\n";

  host.insert(file_a, source_a);
  host.insert(file_b, source_b);
  host.link(file_b, "./a", file_a);

  let program = Program::new(host, vec![file_b]);
  let decl_symbol = symbol_for_occurrence(&program, file_a, source_a, "foo", 0);
  let import_symbol = symbol_for_occurrence(&program, file_b, source_b, "foo", 0);
  let use_symbol = symbol_for_occurrence(&program, file_b, source_b, "foo", 1);

  assert_eq!(decl_symbol, import_symbol);
  assert_eq!(decl_symbol, use_symbol);
}

#[test]
fn symbol_at_import_binding_with_alias() {
  let mut host = MemoryHost::default();
  let file_a = FileId(0);
  let file_b = FileId(1);
  let source_a = "export const original = 1;";
  let source_b = "import { original as alias } from \"./a\";\nconst value = alias;";

  host.insert(file_a, source_a);
  host.insert(file_b, source_b);
  host.link(file_b, "./a", file_a);

  let program = Program::new(host, vec![file_b]);

  let decl_symbol = symbol_for_occurrence(&program, file_a, source_a, "original", 0);
  let import_symbol = symbol_for_occurrence(&program, file_b, source_b, "alias", 0);
  let use_symbol = symbol_for_occurrence(&program, file_b, source_b, "alias", 1);

  assert_eq!(decl_symbol, import_symbol);
  assert_eq!(import_symbol, use_symbol);
}

#[test]
fn symbol_at_respects_local_shadowing() {
  let mut host = MemoryHost::default();
  let file = FileId(0);
  let source = "const foo = 1; function wrap() { const foo = 2; return foo; } const again = foo;";
  host.insert(file, source);

  let program = Program::new(host, vec![file]);
  let outer_symbol = symbol_for_occurrence(&program, file, source, "foo", 0);
  let inner_symbol = symbol_for_occurrence(&program, file, source, "foo", 1);
  let inner_use_symbol = symbol_for_occurrence(&program, file, source, "foo", 2);
  let outer_use_symbol = symbol_for_occurrence(&program, file, source, "foo", 3);

  assert_eq!(
    inner_symbol, inner_use_symbol,
    "inner binding should resolve"
  );
  assert_ne!(inner_symbol, outer_symbol, "shadowed symbols should differ");
  assert_eq!(
    outer_symbol, outer_use_symbol,
    "outer usage should see outer binding"
  );
}

#[test]
fn symbol_at_resolves_type_only_imports() {
  let mut host = MemoryHost::default();
  let file_a = FileId(0);
  let file_b = FileId(1);
  let source_a = "export type Foo = { value: number };";
  let source_b = "import type { Foo } from \"./a\";\ntype Bar = Foo;";

  host.insert(file_a, source_a);
  host.insert(file_b, source_b);
  host.link(file_b, "./a", file_a);

  let program = Program::new(host, vec![file_b]);
  let decl_symbol = symbol_for_occurrence(&program, file_a, source_a, "Foo", 0);
  let import_symbol = symbol_for_occurrence(&program, file_b, source_b, "Foo", 0);
  let use_symbol = symbol_for_occurrence(&program, file_b, source_b, "Foo", 1);

  assert_eq!(decl_symbol, import_symbol);
  assert_eq!(import_symbol, use_symbol);
}
