use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId;
use hir_js::{lower_from_source, BodyKind};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use typecheck_ts::check::caches::CheckerCaches;
use typecheck_ts::check::hir_body::check_body;
use typecheck_ts::{
  parse_call_count, reset_parse_call_count, BodyId, ExprId, FileKey, Program, TypeKindSummary,
};
use types_ts_interned::{TypeKind, TypeStore};

#[derive(Clone)]
struct NoLibHost {
  text: &'static str,
}

impl typecheck_ts::Host for NoLibHost {
  fn file_text(&self, _file: &FileKey) -> Result<std::sync::Arc<str>, typecheck_ts::HostError> {
    Ok(std::sync::Arc::from(self.text))
  }

  fn resolve(&self, _from: &FileKey, _spec: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> typecheck_ts::lib_support::CompilerOptions {
    let mut opts = typecheck_ts::lib_support::CompilerOptions::default();
    opts.no_default_lib = true;
    opts
  }
}

#[test]
fn infers_basic_literals_and_identifiers() {
  let source = "function f(a) { return a; }";
  let lowered = lower_from_source(source).expect("lower");
  let (body_id, body) = lowered
    .bodies
    .iter()
    .enumerate()
    .find(|(_, b)| matches!(b.kind, BodyKind::Function))
    .map(|(idx, b)| (BodyId(idx as u32), b.as_ref()))
    .expect("function body");
  let ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let store = TypeStore::new();
  let caches = CheckerCaches::new(Default::default()).for_body();
  let bindings = HashMap::new();
  let mut next_symbol = 0;
  let (result, _, _) = check_body(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    &ast,
    Arc::clone(&store),
    &caches,
    &bindings,
    &mut next_symbol,
    None,
    None,
    None,
  );

  // parameter, const binding, return expression
  assert_eq!(result.expr_types().len(), body.exprs.len());
  assert_eq!(result.pat_types().len(), body.pats.len());
  assert!(
    !result.return_types().is_empty(),
    "return statement should be recorded"
  );
  assert!(result.diagnostics().is_empty());
}

#[test]
fn expression_spans_match_body_indices() {
  let source = "function g(x: number) { const y = x + 1; return y; }";
  let lowered = lower_from_source(source).expect("lower");
  let (body_id, body) = lowered
    .bodies
    .iter()
    .enumerate()
    .find(|(_, b)| matches!(b.kind, BodyKind::Function))
    .map(|(idx, b)| (BodyId(idx as u32), b.as_ref()))
    .expect("function body");
  let ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let store = TypeStore::new();
  let caches = CheckerCaches::new(Default::default()).for_body();
  let bindings = HashMap::new();
  let mut next_symbol = 0;
  let (result, _, _) = check_body(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    &ast,
    store.clone(),
    &caches,
    &bindings,
    &mut next_symbol,
    None,
    None,
    None,
  );

  for (idx, expr) in body.exprs.iter().enumerate() {
    assert_eq!(
      expr.span,
      result.expr_spans()[idx],
      "ExprId {idx} span should match body expression span"
    );
  }
}

#[test]
fn expr_at_returns_innermost_type() {
  let source = "function h(v: number) { return (v + 1) * 2; }";
  let lowered = lower_from_source(source).expect("lower");
  let (body_id, body) = lowered
    .bodies
    .iter()
    .enumerate()
    .find(|(_, b)| matches!(b.kind, BodyKind::Function))
    .map(|(idx, b)| (BodyId(idx as u32), b.as_ref()))
    .expect("function body");
  let ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let store = TypeStore::new();
  let caches = CheckerCaches::new(Default::default()).for_body();
  let bindings = HashMap::new();
  let mut next_symbol = 0;
  let (result, _, _) = check_body(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    &ast,
    store.clone(),
    &caches,
    &bindings,
    &mut next_symbol,
    None,
    None,
    None,
  );

  for (_idx, span) in result.expr_spans().iter().enumerate() {
    if span.is_empty() {
      continue;
    }
    let mid = span.start + (span.len() / 2);
    let found = result.expr_at(mid).expect("expression at offset");
    let found_span = result
      .expr_span(found.0)
      .expect("expr span for located expression");
    assert!(
      span.start <= found_span.start && found_span.end <= span.end,
      "ExprId {} span {:?} should be contained in {:?}",
      found.0 .0,
      found_span,
      span
    );
    assert_eq!(
      found.1,
      result
        .expr_type(found.0)
        .expect("expr type for located expression")
    );
  }
}

#[test]
fn program_expr_at_matches_body_checker() {
  reset_parse_call_count();
  let source = "export function h(v: number) { return (v + 1) * 2; }";
  let host = NoLibHost { text: source };
  let key = FileKey::new("entry.ts");
  let program = Program::new(host.clone(), vec![key.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);
  let body = program
    .body_of_def(exports.get("h").and_then(|e| e.def).expect("def for h"))
    .expect("body for h");
  let result = program.check_body(body);
  let offset = source.find("v + 1").unwrap() as u32 + 1;

  let (_res_expr, res_ty) = result.expr_at(offset).expect("body result expr");
  let (found_body, found_expr) = program.expr_at(file_id, offset).expect("program expr");
  assert_eq!(found_body, body);
  let found_span = result
    .expr_span(found_expr)
    .expect("span for program expr_at result");
  assert!(
    found_span.start <= offset
      && (offset < found_span.end || (found_span.is_empty() && offset == found_span.start))
  );

  let ty_at = program.type_at(file_id, offset).expect("program type at");
  assert_eq!(ty_at, res_ty);
  assert_eq!(
    Some(res_ty),
    result.expr_type(found_expr),
    "program expr_at should line up with body checker type"
  );
}

#[test]
fn diagnostics_are_stably_sorted() {
  let source = "function bad() { return missing + also_missing; }";
  let lowered = lower_from_source(source).expect("lower");
  let (body_id, body) = lowered
    .bodies
    .iter()
    .enumerate()
    .find(|(_, b)| matches!(b.kind, BodyKind::Function))
    .map(|(idx, b)| (BodyId(idx as u32), b.as_ref()))
    .expect("function body");
  let ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let store = TypeStore::new();
  let caches = CheckerCaches::new(Default::default()).for_body();
  let bindings = HashMap::new();
  let mut next_symbol = 0;
  let (result, _, _) = check_body(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    &ast,
    store.clone(),
    &caches,
    &bindings,
    &mut next_symbol,
    None,
    None,
    None,
  );
  let starts: Vec<u32> = result
    .diagnostics()
    .iter()
    .map(|d| d.primary.range.start)
    .collect();
  let mut sorted = starts.clone();
  sorted.sort();
  assert_eq!(starts, sorted, "diagnostics should be sorted by span start");
}

#[test]
fn call_with_missing_arguments_types_arguments_once() {
  let source =
    "function add(a: number, b: number): number { return a + b; }\nconst result = add(1);";
  let lowered = lower_from_source(source).expect("lower");
  let (body_id, body) = lowered
    .bodies
    .iter()
    .enumerate()
    .find(|(_, b)| matches!(b.kind, BodyKind::Initializer | BodyKind::TopLevel))
    .map(|(idx, b)| (BodyId(idx as u32), b.as_ref()))
    .expect("initializer body");
  let ast = parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse");
  let store = TypeStore::new();
  let caches = CheckerCaches::new(Default::default()).for_body();
  let mut next_symbol = 0;
  let (result, _, _) = check_body(
    body_id,
    body,
    &lowered.names,
    FileId(0),
    &ast,
    Arc::clone(&store),
    &caches,
    &HashMap::new(),
    &mut next_symbol,
    None,
    None,
    None,
  );

  assert_eq!(
    result.diagnostics().len(),
    1,
    "should emit a single overload diagnostic"
  );
  let offset = result
    .expr_spans()
    .get(1)
    .map(|span| span.start)
    .expect("literal span");
  let (expr, ty) = result.expr_at(offset).expect("expression at literal");
  assert_eq!(expr, ExprId(1), "should select the literal expression");
  match store.type_kind(ty) {
    TypeKind::NumberLiteral(_) | TypeKind::Number => {}
    other => panic!("expected number literal type, got {:?}", other),
  }
}

#[test]
fn program_check_body_avoids_reparse() {
  reset_parse_call_count();
  let host = NoLibHost {
    text: "export function f(a: number) { return a + 1; }",
  };
  let key = FileKey::new("entry.ts");
  let program = typecheck_ts::Program::new(host, vec![key.clone()]);
  let _ = program.check();
  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);
  let body = program
    .body_of_def(exports.get("f").and_then(|e| e.def).expect("def"))
    .expect("body");
  let parsed_once = parse_call_count();
  let _ = program.check_body(body);
  let after_first = parse_call_count();
  let _ = program.check_body(body);
  let after_second = parse_call_count();
  assert_eq!(parsed_once, after_first);
  assert_eq!(after_first, after_second);
}

#[test]
fn program_type_at_prefers_literal_in_call_arguments() {
  let source =
    "function add(a: number, b: number): number { return a + b; }\nconst result = add(1);";
  let host = NoLibHost { text: source };
  let key = FileKey::new("entry.ts");
  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  let call_diags: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == "TC2000")
    .collect();
  assert_eq!(call_diags.len(), 1, "should report one overload error");
  let start = source.find("(1)").expect("argument snippet start") as u32;
  let offset = start + (("(1)").len() as u32 / 2);
  let file_id = program.file_id(&key).expect("file id");
  let ty = program.type_at(file_id, offset).expect("type at argument");
  let rendered = program.display_type(ty).to_string();
  assert_eq!(rendered, "number");
}

#[test]
fn program_type_of_expr_returns_interned_unknown_for_missing_expr() {
  let host = NoLibHost {
    text: "export const value = 1;",
  };
  let key = FileKey::new("entry.ts");
  let program = Program::new(host, vec![key.clone()]);
  let _ = program.check();
  let file_id = program.file_id(&key).expect("file id");
  let body = program.file_body(file_id).expect("top-level body");
  let ty = program.type_of_expr(body, ExprId(9999));
  assert_eq!(program.type_kind(ty), TypeKindSummary::Unknown);
}
