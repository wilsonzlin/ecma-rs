use std::collections::HashMap;
use std::sync::Arc;

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
  let decl_offset = source_a.find("foo").unwrap() as u32;
  let import_offset = source_b.find("{ foo }").unwrap() as u32 + 2;
  let use_offset = source_b.find("foo()").unwrap() as u32;

  let decl_symbol = program
    .symbol_at(file_a, decl_offset)
    .expect("decl symbol");
  let import_symbol = program
    .symbol_at(file_b, import_offset)
    .expect("import symbol");
  let use_symbol = program.symbol_at(file_b, use_offset).unwrap();

  assert_eq!(decl_symbol, import_symbol);
  assert_eq!(decl_symbol, use_symbol);
}
