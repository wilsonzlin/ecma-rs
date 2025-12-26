use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn nested_body_expr_lookup_prefers_innermost_span() {
  let mut host = MemoryHost::default();
  let source =
    "const top = 0; function outer() { const shadow = 1; function inner() { const value = 2 + 3; return value; } return inner(); }";
  let file = FileKey::new("entry.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source
    .rfind("inner")
    .expect("offset of nested call")
    .try_into()
    .expect("offset fits in u32");

  let (body, expr) = program.expr_at(file_id, offset).expect("expr at offset");
  let top_body = program.file_body(file_id).expect("top-level body");
  assert_ne!(body, top_body, "should select inner function body");

  let span = program.span_of_expr(body, expr).expect("span of expr");
  assert_eq!(
    &source[span.range.start as usize..span.range.end as usize],
    "inner"
  );

  let ty = program.type_at(file_id, offset).expect("type at offset");
  assert!(
    program.display_type(ty).to_string().len() > 0,
    "expected a type for identifier"
  );
}

#[test]
fn nested_expression_prefers_smallest_covering_span() {
  let mut host = MemoryHost::default();
  let source = "const value = 1 + (2 * (3 + 4));";
  let file = FileKey::new("expr.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source.find("3 + 4").expect("inner literal") as u32;

  let (body, expr) = program.expr_at(file_id, offset).expect("expr at offset");
  let top_body = program.file_body(file_id).expect("top-level body");
  assert_eq!(body, top_body);

  let span = program.span_of_expr(body, expr).expect("span of expr");
  assert_eq!(
    &source[span.range.start as usize..span.range.end as usize],
    "3"
  );
  let ty = program.type_at(file_id, offset).expect("type at offset");
  let display = program.display_type(ty).to_string();
  assert!(
    display == "number" || display == "3",
    "expected number-like display, got {display}"
  );
}

#[test]
fn type_at_prefers_innermost_parenthesized_expression() {
  let mut host = MemoryHost::default();
  let source = "const result = ((1 + 2) * (3 + (4 + 5)));";
  let file = FileKey::new("paren.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source.find("4 + 5").expect("inner addition") as u32;

  let ty = program.type_at(file_id, offset).expect("type at offset");
  let display = program.display_type(ty).to_string();
  assert!(
    display == "number" || display == "4",
    "expected number-like display, got {display}"
  );

  let (body, expr) = program.expr_at(file_id, offset).expect("expr at offset");
  let span = program.span_of_expr(body, expr).expect("span of expr");
  assert_eq!(
    &source[span.range.start as usize..span.range.end as usize],
    "4"
  );
}

#[test]
fn body_result_expr_lookup_prefers_innermost_literal() {
  let mut host = MemoryHost::default();
  let source = "const value = ((1 + 2) * 3);";
  let file = FileKey::new("body.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let body = program.file_body(file_id).expect("body id");
  let result = program.check_body(body);

  let offset = source.find('1').expect("literal offset") as u32;
  let (expr, ty) = result.expr_at(offset).expect("expr at literal");
  let span = result.expr_span(expr).expect("expr span");

  assert_eq!(
    &source[span.start as usize..span.end as usize],
    "1",
    "should pick innermost literal span",
  );
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn span_of_def_returns_declaration_span() {
  let mut host = MemoryHost::default();
  let source = "function outer() { return 1; }\nconst value = outer();";
  let file = FileKey::new("defs.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let outer_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("outer"))
    .expect("outer definition");

  let span = program.span_of_def(outer_def).expect("span of def");
  let snippet = &source[span.range.start as usize..span.range.end as usize];
  assert!(
    snippet.contains("outer()"),
    "definition span should include function name, got {snippet}"
  );
}
