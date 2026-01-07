use hir_js::{lower_from_source_with_kind, BodyKind, DefKind, FileKind, StmtKind};

#[test]
fn span_map_body_at_offset_prefers_initializer_body() {
  let source = "function f(){ if(true){ const x = 1; } return 2; }";
  let lowered = lower_from_source_with_kind(FileKind::Ts, source).expect("lower source");

  let declarator = lowered
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::VarDeclarator && lowered.names.resolve(def.name) == Some("x"))
    .expect("x declarator");
  let init_body = declarator.body.expect("initializer body");
  assert_eq!(
    lowered
      .body(init_body)
      .expect("initializer body exists")
      .kind,
    BodyKind::Initializer,
    "expected x initializer body"
  );

  let offset = source.find('1').expect("initializer literal") as u32;
  assert_eq!(lowered.hir.span_map.body_at_offset(offset), Some(init_body));
}

#[test]
fn span_map_stmt_at_offset_returns_innermost_statement() {
  let source = "function f(){ if(true){ const x = 1; } return 2; }";
  let lowered = lower_from_source_with_kind(FileKind::Ts, source).expect("lower source");

  let func = lowered
    .defs
    .iter()
    .find(|def| def.path.kind == DefKind::Function && lowered.names.resolve(def.name) == Some("f"))
    .expect("function f");
  let func_body = func.body.expect("f body");

  let var_offset = source.find("const x").expect("var decl") as u32;
  let var_stmt = lowered
    .hir
    .span_map
    .stmt_span_at_offset(var_offset)
    .expect("stmt at var decl");
  assert_eq!(var_stmt.id.0, func_body);
  let body = lowered.body(var_stmt.id.0).expect("stmt body");
  assert!(
    matches!(body.stmts[var_stmt.id.1 .0 as usize].kind, StmtKind::Var(_)),
    "expected var statement"
  );
  assert_eq!(
    lowered.hir.span_map.stmt_span(var_stmt.id.0, var_stmt.id.1),
    Some(var_stmt.range)
  );

  let return_offset = source.find('2').expect("return literal") as u32;
  let ret_stmt = lowered
    .hir
    .span_map
    .stmt_span_at_offset(return_offset)
    .expect("stmt at return");
  assert_eq!(ret_stmt.id.0, func_body);
  let body = lowered.body(ret_stmt.id.0).expect("return body");
  assert!(
    matches!(body.stmts[ret_stmt.id.1 .0 as usize].kind, StmtKind::Return(_)),
    "expected return statement"
  );
}

