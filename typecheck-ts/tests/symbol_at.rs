use std::sync::Arc;

use typecheck_ts::semantic_js::SymbolId;
use typecheck_ts::{FileId, FileKey, MemoryHost, Program, TextRange};

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
  let (offset, symbol) = offsets
    .into_iter()
    .find_map(|offset| program.symbol_at(file, offset).map(|sym| (offset, sym)))
    .unwrap_or_else(|| {
      panic!(
        "no symbol for '{needle}' occurrence {occurrence} in range {search_start}..{search_end}"
      )
    });
  for _ in 0..3 {
    assert_eq!(
      Some(symbol),
      program.symbol_at(file, offset),
      "symbol_at should be deterministic for {needle} at offset {offset}"
    );
  }
  symbol
}

#[test]
fn expr_at_prefers_innermost_span() {
  let mut host = MemoryHost::default();
  let source = "const value = 1 + (2 + 3);";
  let file = FileKey::new("file.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let main_body = program.file_body(file_id).expect("body for file");
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

  let (found_body, expr) = program
    .expr_at(file_id, offset)
    .expect("expression at offset");
  assert_eq!(found_body, main_body);
  let span = result.expr_span(expr).expect("expr span");
  assert_eq!(span, expected_span);

  let ty = program.type_at(file_id, offset).expect("type at offset");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn symbol_at_local_variable() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file.ts");
  let source = "let value = 1;\nconst copy = value;";
  host.insert(file.clone(), source);

  let program = Program::new(host, vec![file.clone()]);
  let file = program.file_id(&file).expect("file id");
  let decl_symbol = symbol_for_occurrence(&program, file, source, "value", 0);
  let use_symbol = symbol_for_occurrence(&program, file, source, "value", 1);

  assert_eq!(decl_symbol, use_symbol);
}

#[test]
fn symbol_at_function_parameter() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file.ts");
  let source = "function wrap(param: number) { const inner = param; return param; }";
  host.insert(file.clone(), source);

  let program = Program::new(host, vec![file.clone()]);
  let file = program.file_id(&file).expect("file id");
  let decl_symbol = symbol_for_occurrence(&program, file, source, "param", 0);
  let first_use = symbol_for_occurrence(&program, file, source, "param", 1);
  let second_use = symbol_for_occurrence(&program, file, source, "param", 2);

  assert_eq!(decl_symbol, first_use);
  assert_eq!(first_use, second_use);
}

#[test]
fn symbol_at_resolves_imports() {
  let mut host = MemoryHost::default();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  let source_a = "export function foo() { return 1; }";
  let source_b = "import { foo } from \"./a\";\nexport const result = foo();\n";

  host.insert(file_a.clone(), Arc::from(source_a.to_string()));
  host.insert(file_b.clone(), Arc::from(source_b.to_string()));
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host, vec![file_b.clone()]);
  let file_a = program.file_id(&file_a).unwrap();
  let file_b = program.file_id(&file_b).unwrap();
  let decl_symbol = symbol_for_occurrence(&program, file_a, source_a, "foo", 0);
  let import_symbol = symbol_for_occurrence(&program, file_b, source_b, "foo", 0);
  let use_symbol = symbol_for_occurrence(&program, file_b, source_b, "foo", 1);

  assert_eq!(decl_symbol, import_symbol);
  assert_eq!(decl_symbol, use_symbol);
}

#[test]
fn symbol_at_type_reference_in_annotation() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file.ts");
  let source = "type Foo = { value: number };\nfunction use(arg: Foo): Foo { const local: Foo = arg; return local; }";
  host.insert(file.clone(), source);

  let program = Program::new(host, vec![file.clone()]);
  let file = program.file_id(&file).expect("file id");
  let decl_symbol = symbol_for_occurrence(&program, file, source, "Foo", 0);
  let param_symbol = symbol_for_occurrence(&program, file, source, "Foo", 1);
  let return_symbol = symbol_for_occurrence(&program, file, source, "Foo", 2);
  let local_symbol = symbol_for_occurrence(&program, file, source, "Foo", 3);

  assert_eq!(decl_symbol, param_symbol);
  assert_eq!(param_symbol, return_symbol);
  assert_eq!(return_symbol, local_symbol);
}

#[test]
fn symbol_at_import_binding_with_alias() {
  let mut host = MemoryHost::default();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  let source_a = "export const original = 1;";
  let source_b = "import { original as alias } from \"./a\";\nconst value = alias;";

  host.insert(file_a.clone(), Arc::from(source_a.to_string()));
  host.insert(file_b.clone(), Arc::from(source_b.to_string()));
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host, vec![file_b.clone()]);
  let file_a = program.file_id(&file_a).unwrap();
  let file_b = program.file_id(&file_b).unwrap();

  let decl_symbol = symbol_for_occurrence(&program, file_a, source_a, "original", 0);
  let import_symbol = symbol_for_occurrence(&program, file_b, source_b, "alias", 0);
  let use_symbol = symbol_for_occurrence(&program, file_b, source_b, "alias", 1);

  assert_eq!(decl_symbol, import_symbol);
  assert_eq!(import_symbol, use_symbol);
}

#[test]
fn symbol_at_respects_local_shadowing() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file.ts");
  let source = "const foo = 1; { const foo = 2; { const foo = 3; foo; } foo; } const again = foo;";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file = program.file_id(&file).unwrap();
  let outer_symbol = symbol_for_occurrence(&program, file, source, "foo", 0);
  let mid_symbol = symbol_for_occurrence(&program, file, source, "foo", 1);
  let inner_symbol = symbol_for_occurrence(&program, file, source, "foo", 2);
  let inner_use_symbol = symbol_for_occurrence(&program, file, source, "foo", 3);
  let mid_use_symbol = symbol_for_occurrence(&program, file, source, "foo", 4);
  let outer_use_symbol = symbol_for_occurrence(&program, file, source, "foo", 5);

  assert_eq!(
    inner_symbol, inner_use_symbol,
    "inner binding should resolve"
  );
  assert_eq!(mid_symbol, mid_use_symbol, "mid binding should resolve");
  assert_ne!(inner_symbol, outer_symbol, "shadowed symbols should differ");
  assert_ne!(
    inner_symbol, mid_symbol,
    "nested blocks should shadow parents"
  );
  assert_eq!(
    outer_symbol, outer_use_symbol,
    "outer usage should see outer binding"
  );
}

#[test]
fn symbol_at_resolves_type_only_imports() {
  let mut host = MemoryHost::default();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  let source_a = "export type Foo = { value: number };";
  let source_b = "import type { Foo } from \"./a\";\ntype Bar = Foo;";

  host.insert(file_a.clone(), Arc::from(source_a.to_string()));
  host.insert(file_b.clone(), Arc::from(source_b.to_string()));
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host, vec![file_b.clone()]);
  let file_a = program.file_id(&file_a).unwrap();
  let file_b = program.file_id(&file_b).unwrap();
  let decl_symbol = symbol_for_occurrence(&program, file_a, source_a, "Foo", 0);
  let import_symbol = symbol_for_occurrence(&program, file_b, source_b, "Foo", 0);
  let use_symbol = symbol_for_occurrence(&program, file_b, source_b, "Foo", 1);

  assert_eq!(decl_symbol, import_symbol);
  assert_eq!(import_symbol, use_symbol);
}
