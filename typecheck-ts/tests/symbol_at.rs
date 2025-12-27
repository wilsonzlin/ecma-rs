use std::sync::Arc;

use ordered_float::OrderedFloat;
use parse_js::{Dialect, ParseOptions, SourceType};
use semantic_js::ts::locals;
use typecheck_ts::semantic_js::SymbolId;
use typecheck_ts::{FileId, FileKey, MemoryHost, Program, TextRange, TypeKindSummary};

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
  let span = program
    .expr_span(found_body, expr)
    .map(|s| s.range)
    .or_else(|| result.expr_span(expr))
    .expect("expr span");
  assert_eq!(span, expected_span);

  let ty = program.type_at(file_id, offset).expect("type at offset");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn type_at_prefers_innermost_conditional_branch() {
  let mut host = MemoryHost::default();
  let source = "const value = true ? 1 : \"two\";";
  let file = FileKey::new("file.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).unwrap();

  let one_offset = source.find('1').expect("literal offset") as u32;
  let one_type = program.type_at(file_id, one_offset).expect("type at 1");
  match program.type_kind(one_type) {
    TypeKindSummary::NumberLiteral(val) => assert_eq!(val, OrderedFloat(1.0)),
    other => panic!("expected number literal, got {other:?}"),
  }

  let string_offset = source.find("\"two\"").expect("string offset") as u32 + 1;
  let string_type = program
    .type_at(file_id, string_offset)
    .expect("type at string");
  match program.type_kind(string_type) {
    TypeKindSummary::StringLiteral(text) => assert_eq!(text, "two"),
    other => panic!("expected string literal, got {other:?}"),
  }

  let outer_offset = source.find('?').expect("conditional") as u32 + 1;
  assert_eq!(
    program.type_kind(program.type_at(file_id, outer_offset).expect("outer type")),
    TypeKindSummary::Union { members: 2 }
  );
}

#[test]
fn type_at_handles_nested_bodies() {
  let mut host = MemoryHost::default();
  let source =
    "function outer() { function inner() { return true ? 1 : \"two\"; } return inner(); }";
  let file = FileKey::new("file.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).unwrap();
  let offset = source.find("\"two\"").expect("inner string") as u32 + 1;
  let ty = program
    .type_at(file_id, offset)
    .expect("type at inner string");
  match program.type_kind(ty) {
    TypeKindSummary::StringLiteral(text) => assert_eq!(text, "two"),
    other => panic!("expected string literal, got {other:?}"),
  }
}

#[test]
fn type_at_picks_inner_expression_for_nested_call() {
  let mut host = MemoryHost::default();
  let source = "function choose(value: number): boolean { return value > 0; }\nconst result = choose(true ? 1 : 2);";
  let file = FileKey::new("file.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).unwrap();
  let offset = source
    .find('?')
    .map(|idx| idx as u32 + 1)
    .expect("conditional");
  let ty = program.type_at(file_id, offset).expect("type at offset");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn span_of_expr_returns_covering_span() {
  let mut host = MemoryHost::default();
  let source = "const value = 1 + 2;";
  let file = FileKey::new("file.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).unwrap();
  let plus_offset = source.find('+').expect("plus position") as u32;
  let (body, expr) = program
    .expr_at(file_id, plus_offset)
    .expect("expression at +");
  let span = program.span_of_expr(body, expr).expect("expr span");
  assert!(span.range.start <= plus_offset && plus_offset <= span.range.end);
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
  let source = "const foo = 1; function wrap() { const foo = 2; return foo; } const again = foo;";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file = program.file_id(&file).unwrap();
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

#[test]
fn symbol_at_resolves_function_parameter_uses() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file.ts");
  let source = "function add(param: number) { return param + 1; }";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).unwrap();

  let decl_symbol = symbol_for_occurrence(&program, file_id, source, "param", 0);
  let use_symbol = symbol_for_occurrence(&program, file_id, source, "param", 1);

  assert_eq!(
    decl_symbol, use_symbol,
    "parameter declaration and use should resolve to the same symbol"
  );
}

#[test]
fn symbol_at_prefers_innermost_binding_in_nested_functions() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file.ts");
  let source =
    "const value = 1; const factory = () => { const value = 2; return () => value + 1; }; const result = factory()();";
  host.insert(file.clone(), Arc::from(source.to_string()));

  // Ensure the local semantics consider the inner arrow to reference the innermost
  // `value` binding rather than the outer one.
  let mut ast = parse_js::parse_with_options(
    &source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let locals = locals::bind_ts_locals(&mut ast, FileId(0), true);
  let value_symbols: Vec<_> = locals
    .symbols
    .values()
    .filter(|sym| locals.names.get(&sym.name).map(|n| n.as_str()) == Some("value"))
    .collect();
  assert_eq!(
    value_symbols.len(),
    2,
    "expected outer and inner value bindings"
  );
  let positions = positions_of(source, "value");
  // Occurrence order: outer decl, inner decl, inner use.
  let outer_decl = positions[0];
  let inner_decl = positions[1];
  let inner_use = positions[2];
  let inner_symbol = locals
    .resolve_expr_at_offset(inner_use)
    .map(|(_, id)| id)
    .expect("inner use should resolve");
  let outer_symbol = locals
    .resolve_expr_at_offset(outer_decl)
    .map(|(_, id)| id)
    .expect("outer decl should resolve");
  let inner_decl_symbol = locals
    .resolve_expr_at_offset(inner_decl)
    .map(|(_, id)| id)
    .expect("inner decl should resolve");
  assert_ne!(
    inner_symbol, outer_symbol,
    "inner use should resolve to inner binding"
  );
  assert_eq!(
    inner_symbol, inner_decl_symbol,
    "inner use should match inner decl"
  );

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let snapshot = program.snapshot();
  if let Some((_, occs)) = snapshot
    .symbol_occurrences
    .iter()
    .find(|(id, _)| *id == file_id)
  {
    for occ in occs {
      let text = &source[occ.range.start as usize..occ.range.end as usize];
      println!("{:?} -> {:?} ({text})", occ.range, occ.symbol);
    }
  }
  let outer_decl_symbol = program
    .symbol_at(file_id, outer_decl)
    .expect("outer declaration");
  let inner_decl_symbol = program
    .symbol_at(file_id, inner_decl)
    .expect("inner declaration");
  let inner_use_symbol = program
    .symbol_at(file_id, inner_use)
    .expect("inner use");

  assert_ne!(
    outer_decl_symbol, inner_decl_symbol,
    "inner binding should shadow outer binding"
  );
  assert_eq!(
    inner_decl_symbol, inner_use_symbol,
    "should resolve to innermost binding"
  );
}
