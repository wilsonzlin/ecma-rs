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

#[test]
fn type_at_prefers_innermost_in_nested_arrows() {
  let mut host = MemoryHost::default();
  let source = "const nested = (() => () => 1 + 2)();";
  let file = FileKey::new("arrows.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source.rfind('2').expect("offset of literal") as u32;

  let ty = program.type_at(file_id, offset).expect("type at literal");
  assert_eq!(program.display_type(ty).to_string(), "number");

  let (body, expr) = program.expr_at(file_id, offset).expect("expr at literal");
  let span = program.span_of_expr(body, expr).expect("span of expr");
  assert_eq!(
    &source[span.range.start as usize..span.range.end as usize],
    "2",
    "should select innermost literal in nested arrow body"
  );
}

#[test]
fn type_at_prefers_inner_identifier_in_nested_arrows() {
  let mut host = MemoryHost::default();
  let source = "const run = ((value: number) => () => value + 1)(41)();";
  let file = FileKey::new("arrow_capture.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source
    .rfind("value")
    .expect("inner identifier")
    .try_into()
    .expect("offset fits");

  let (body, expr) = program.expr_at(file_id, offset).expect("expr at offset");
  let span = program.span_of_expr(body, expr).expect("span of expr");
  assert_eq!(
    &source[span.range.start as usize..span.range.end as usize],
    "value",
    "innermost captured identifier should be selected"
  );

  let param_offset = source.find("value: number").unwrap() as u32;
  let param_ty = program
    .type_at(file_id, param_offset)
    .expect("type at param");
  assert_eq!(
    program.display_type(param_ty).to_string(),
    "number",
    "parameter annotation should be respected"
  );

  let ty = program
    .type_at(file_id, offset)
    .expect("type at inner identifier");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn type_at_prefers_innermost_member_access() {
  let mut host = MemoryHost::default();
  let source =
    "const obj = { nested: { value: 42 } } as const; const total = obj.nested.value + 1;";
  let file = FileKey::new("members.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source
    .rfind("value + 1")
    .expect("offset of innermost member") as u32;

  let ty = program.type_at(file_id, offset).expect("type at member");
  if std::env::var("DEBUG_SPAN").is_ok() {
    if let Some(obj_def) = program
      .definitions_in_file(file_id)
      .into_iter()
      .find(|d| program.def_name(*d).as_deref() == Some("obj"))
    {
      eprintln!(
        "DEBUG obj type {}",
        program.display_type(program.type_of_def(obj_def))
      );
    }
    eprintln!("DEBUG type_at {}", program.display_type(ty));
  }
  let (body, expr) = program.expr_at(file_id, offset).expect("expr at offset");
  let span = program.span_of_expr(body, expr).expect("expr span");
  let snippet = &source[span.range.start as usize..span.range.end as usize];
  assert!(
    snippet.contains("value"),
    "expected member access containing 'value', got {snippet}"
  );
  assert_eq!(program.display_type(ty).to_string(), "42");
}

#[test]
fn type_at_includes_undefined_for_optional_chain_member() {
  let mut host = MemoryHost::default();
  let source = "function g(x: { v: number } | null) { const y = x?.v; return y; }";
  let file = FileKey::new("optional_member.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source.find("?.").expect("optional chain operator") as u32;

  let ty = program
    .type_at(file_id, offset)
    .expect("type at optional member");
  assert_eq!(program.display_type(ty).to_string(), "undefined | number");
}

#[test]
fn type_at_includes_undefined_for_optional_chain_call() {
  let mut host = MemoryHost::default();
  let source = "function g(cb: (() => number) | undefined) { const y = cb?.(); return y; }";
  let file = FileKey::new("optional_call.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source.find("?.(").expect("optional call operator") as u32;

  let ty = program
    .type_at(file_id, offset)
    .expect("type at optional call");
  assert_eq!(program.display_type(ty).to_string(), "undefined | number");
}

#[test]
fn type_at_prefers_inner_body_expression_in_nested_functions() {
  let mut host = MemoryHost::default();
  let source =
    "function outer() { return (function inner(arg: string) { return arg + \"!\"; })(\"hi\"); }";
  let file = FileKey::new("nested_funcs.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source
    .rfind("arg +")
    .expect("inner arg")
    .try_into()
    .unwrap();

  let ty = program.type_at(file_id, offset).expect("type at offset");
  assert_eq!(program.display_type(ty).to_string(), "string");

  let (body, expr) = program.expr_at(file_id, offset).expect("expr at arg");
  let span = program.span_of_expr(body, expr).expect("expr span");
  assert_eq!(
    &source[span.range.start as usize..span.range.end as usize],
    "arg"
  );
}

#[test]
fn nested_body_lookup_uses_span_map() {
  let mut host = MemoryHost::default();
  let source = "function outer() { function inner() { return 1 + 2; } return inner(); }";
  let file = FileKey::new("nested.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source.find('1').expect("literal offset") as u32;

  let top_body = program.file_body(file_id).expect("top-level body");
  let (body, expr) = program.expr_at(file_id, offset).expect("expr at literal");
  assert_ne!(
    body, top_body,
    "lookup should select inner body from span map"
  );

  let span = program.span_of_expr(body, expr).expect("span of expr");
  assert_eq!(
    &source[span.range.start as usize..span.range.end as usize],
    "1",
    "innermost literal span should be returned"
  );

  let ty = program.type_at(file_id, offset).expect("type at literal");
  let display = program.display_type(ty).to_string();
  assert!(
    display == "number" || display == "1",
    "expected numeric literal type, got {display}"
  );
}

#[test]
fn type_at_handles_construct_signatures() {
  let mut host = MemoryHost::default();
  let source =
    "class Greeter { constructor(public msg: string) {} }\nconst g = new Greeter(\"hi\");\nconst m = g.msg;";
  let file = FileKey::new("new_expr.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  let offset = source
    .rfind("m = g.msg")
    .expect("offset for binding")
    .try_into()
    .expect("offset fits");

  let ty = program.type_at(file_id, offset).expect("type at m");
  assert_eq!(program.display_type(ty).to_string(), "string");
}

#[test]
fn type_at_recovers_from_trivia_offsets() {
  let mut host = MemoryHost::default();
  let source =
    "declare function m(this: { x: number }, y: number): number;\nconst r = m.call({ x: 1 }, 2);";
  let file = FileKey::new("trivia.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");

  let offset = source.find("= m").expect("assignment operator") as u32 + 1;

  let ty = program.type_at(file_id, offset).expect("type at trivia");
  assert_eq!(program.display_type(ty).to_string(), "number");
}
