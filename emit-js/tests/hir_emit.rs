use emit_js::{emit_hir_file_to_string, EmitOptions};
use hir_js::{lower_from_source_with_kind, Body, ExprKind, FileKind, PatKind, StmtKind};
use parse_js::parse;
use serde_json::Value;
use std::collections::HashSet;

mod util;

fn syntax_value(source: &str) -> Value {
  let ast = parse(source).expect("parse source");
  util::serialize_without_locs(&ast)
}

fn roundtrip(source: &str) {
  let lowered = lower_from_source_with_kind(FileKind::Js, source)
    .unwrap_or_else(|err| panic!("failed to lower {source}: {err:?}"));
  assert_no_missing(&lowered);
  let emitted =
    emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit lowered program");
  let original = syntax_value(source);
  let reparsed = syntax_value(&emitted);
  assert_eq!(
    original, reparsed,
    "roundtrip via HIR changed syntax\nsource: {source}\nemitted: {emitted}"
  );
}

#[test]
fn roundtrip_matrix() {
  let cases = [
    "function add(a,b){ return a + b * 2; }",
    "const pick = (arr = [1,2]) => arr?.[0] ?? null;",
    "function loops(flag){ for (let i = 0; i < 3; i++) items[i] = i; while(flag){ if(flag){ break; } } do action(); while(check()); }",
    "function branch(v){ switch(v){ case 1: return 'one'+v; default: return String(v||0); } }",
    "const obj = {value:1,get v(){ return this.value; },set v(x){ this.value = x; },['x'+1]:2,...rest};",
    "export const x = 1;",
    "export const {a,b} = foo();",
  ];
  for case in cases {
    roundtrip(case);
  }
}

#[test]
fn deterministic_emission() {
  let source = "const pick = (arr = [1,2]) => arr?.[0] ?? null;";
  let lowered = lower_from_source_with_kind(FileKind::Js, source).expect("lower source");
  assert_no_missing(&lowered);
  let emitted1 =
    emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit first pass");
  let emitted2 =
    emit_hir_file_to_string(&lowered, EmitOptions::minified()).expect("emit second pass");
  assert_eq!(emitted1, emitted2, "HIR emission must be deterministic");
}

fn assert_no_missing(lowered: &hir_js::LowerResult) {
  for body in lowered.bodies.iter() {
    let body = body.as_ref();
    let mut visited = HashSet::new();
    for stmt in &body.root_stmts {
      visit_stmt(body, *stmt, &mut visited);
    }
  }
}

fn visit_stmt(body: &Body, stmt_id: hir_js::StmtId, visited: &mut HashSet<hir_js::ExprId>) {
  let stmt = &body.stmts[stmt_id.0 as usize];
  match &stmt.kind {
    StmtKind::Expr(expr) => visit_expr(body, *expr, visited),
    StmtKind::Return(expr) => {
      if let Some(expr) = expr {
        visit_expr(body, *expr, visited);
      }
    }
    StmtKind::Block(stmts) => {
      for stmt in stmts {
        visit_stmt(body, *stmt, visited);
      }
    }
    StmtKind::If {
      test,
      consequent,
      alternate,
    } => {
      visit_expr(body, *test, visited);
      visit_stmt(body, *consequent, visited);
      if let Some(alt) = alternate {
        visit_stmt(body, *alt, visited);
      }
    }
    StmtKind::While { test, body: inner } => {
      visit_expr(body, *test, visited);
      visit_stmt(body, *inner, visited);
    }
    StmtKind::DoWhile { test, body: inner } => {
      visit_expr(body, *test, visited);
      visit_stmt(body, *inner, visited);
    }
    StmtKind::For {
      init,
      test,
      update,
      body: inner,
    } => {
      if let Some(init) = init {
        match init {
          hir_js::ForInit::Expr(expr) => visit_expr(body, *expr, visited),
          hir_js::ForInit::Var(decl) => visit_var_decl(body, decl, visited),
        }
      }
      if let Some(test) = test {
        visit_expr(body, *test, visited);
      }
      if let Some(update) = update {
        visit_expr(body, *update, visited);
      }
      visit_stmt(body, *inner, visited);
    }
    StmtKind::ForIn {
      left,
      right,
      body: inner,
      ..
    } => {
      match left {
        hir_js::ForHead::Pat(pat) => visit_pat(body, *pat, visited),
        hir_js::ForHead::Var(decl) => visit_var_decl(body, decl, visited),
      }
      visit_expr(body, *right, visited);
      visit_stmt(body, *inner, visited);
    }
    StmtKind::Switch {
      discriminant,
      cases,
    } => {
      visit_expr(body, *discriminant, visited);
      for case in cases {
        if let Some(test) = case.test {
          visit_expr(body, test, visited);
        }
        for stmt in &case.consequent {
          visit_stmt(body, *stmt, visited);
        }
      }
    }
    StmtKind::Try {
      block,
      catch,
      finally_block,
    } => {
      visit_stmt(body, *block, visited);
      if let Some(catch) = catch {
        if let Some(param) = catch.param {
          visit_pat(body, param, visited);
        }
        visit_stmt(body, catch.body, visited);
      }
      if let Some(finally_block) = finally_block {
        visit_stmt(body, *finally_block, visited);
      }
    }
    StmtKind::Throw(expr) => visit_expr(body, *expr, visited),
    StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Empty => {}
    StmtKind::Var(decl) => visit_var_decl(body, decl, visited),
    StmtKind::Labeled { body: inner, .. } => visit_stmt(body, *inner, visited),
    StmtKind::With {
      object,
      body: inner,
    } => {
      visit_expr(body, *object, visited);
      visit_stmt(body, *inner, visited);
    }
    StmtKind::Decl(_) => {}
  }
}

fn visit_var_decl(body: &Body, decl: &hir_js::VarDecl, visited: &mut HashSet<hir_js::ExprId>) {
  for declarator in &decl.declarators {
    visit_pat(body, declarator.pat, visited);
    if let Some(init) = declarator.init {
      visit_expr(body, init, visited);
    }
  }
}

fn visit_pat(body: &Body, pat_id: hir_js::PatId, visited: &mut HashSet<hir_js::ExprId>) {
  let pat = &body.pats[pat_id.0 as usize];
  match &pat.kind {
    PatKind::Ident(_) | PatKind::AssignTarget(_) => {}
    PatKind::Rest(inner) => visit_pat(body, **inner, visited),
    PatKind::Array(arr) => {
      for elem in &arr.elements {
        if let Some(elem) = elem {
          visit_pat(body, elem.pat, visited);
          if let Some(default) = elem.default_value {
            visit_expr(body, default, visited);
          }
        }
      }
      if let Some(rest) = arr.rest {
        visit_pat(body, rest, visited);
      }
    }
    PatKind::Object(obj) => {
      for prop in &obj.props {
        visit_pat(body, prop.value, visited);
        if let Some(default) = prop.default_value {
          visit_expr(body, default, visited);
        }
      }
      if let Some(rest) = obj.rest {
        visit_pat(body, rest, visited);
      }
    }
    PatKind::Assign {
      target,
      default_value,
    } => {
      visit_pat(body, *target, visited);
      visit_expr(body, *default_value, visited);
    }
  }
}

fn visit_expr(body: &Body, expr_id: hir_js::ExprId, visited: &mut HashSet<hir_js::ExprId>) {
  if !visited.insert(expr_id) {
    return;
  }
  let expr = &body.exprs[expr_id.0 as usize];
  assert!(
    !matches!(expr.kind, ExprKind::Missing),
    "body {:?} contains missing expression {expr_id:?}",
    body.kind
  );
  match &expr.kind {
    ExprKind::Unary { expr, .. } | ExprKind::Update { expr, .. } | ExprKind::Await { expr } => {
      visit_expr(body, *expr, visited);
    }
    ExprKind::Binary { left, right, .. } => {
      visit_expr(body, *left, visited);
      visit_expr(body, *right, visited);
    }
    ExprKind::Assignment { target, value, .. } => {
      visit_pat(body, *target, visited);
      visit_expr(body, *value, visited);
    }
    ExprKind::Call(call) => {
      visit_expr(body, call.callee, visited);
      for arg in &call.args {
        visit_expr(body, arg.expr, visited);
      }
    }
    ExprKind::Member(member) => {
      visit_expr(body, member.object, visited);
      if let hir_js::ObjectKey::Computed(expr) = member.property {
        visit_expr(body, expr, visited);
      }
    }
    ExprKind::Conditional {
      test,
      consequent,
      alternate,
    } => {
      visit_expr(body, *test, visited);
      visit_expr(body, *consequent, visited);
      visit_expr(body, *alternate, visited);
    }
    ExprKind::Array(arr) => {
      for el in &arr.elements {
        match el {
          hir_js::ArrayElement::Expr(expr) | hir_js::ArrayElement::Spread(expr) => {
            visit_expr(body, *expr, visited)
          }
          hir_js::ArrayElement::Empty => {}
        }
      }
    }
    ExprKind::Object(obj) => {
      for prop in &obj.properties {
        match prop {
          hir_js::ObjectProperty::KeyValue { key, value, .. } => {
            if let hir_js::ObjectKey::Computed(expr) = key {
              visit_expr(body, *expr, visited);
            }
            visit_expr(body, *value, visited);
          }
          hir_js::ObjectProperty::Getter { body: _, .. }
          | hir_js::ObjectProperty::Setter { body: _, .. } => {}
          hir_js::ObjectProperty::Spread(expr) => visit_expr(body, *expr, visited),
        }
      }
    }
    ExprKind::Template(tmpl) => {
      for span in &tmpl.spans {
        visit_expr(body, span.expr, visited);
      }
    }
    ExprKind::TaggedTemplate { tag, template: _ } => visit_expr(body, *tag, visited),
    ExprKind::Yield { expr, .. } => {
      if let Some(expr) = expr {
        visit_expr(body, *expr, visited);
      }
    }
    ExprKind::ImportCall {
      argument,
      attributes,
    } => {
      visit_expr(body, *argument, visited);
      if let Some(attrs) = attributes {
        visit_expr(body, *attrs, visited);
      }
    }
    ExprKind::Literal(_)
    | ExprKind::Ident(_)
    | ExprKind::This
    | ExprKind::Super
    | ExprKind::ImportMeta
    | ExprKind::NewTarget
    | ExprKind::FunctionExpr { .. }
    | ExprKind::ClassExpr { .. }
    | ExprKind::TypeAssertion { .. }
    | ExprKind::NonNull { .. }
    | ExprKind::Satisfies { .. }
    | ExprKind::Jsx(_) => {}
    ExprKind::Missing => unreachable!("missing expressions should be caught earlier"),
  }
}
