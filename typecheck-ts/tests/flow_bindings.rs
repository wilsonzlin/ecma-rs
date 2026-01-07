use std::collections::HashSet;

use diagnostics::{FileId, TextRange};
use parse_js::{Dialect, ParseOptions, SourceType};
use semantic_js::ts::locals::bind_ts_locals;
use typecheck_ts::check::flow_bindings::FlowBindings;

#[test]
fn flow_bindings_distinguish_shadowed_bindings() {
  let source = "let x = 1; { let x = 2; x; } x;";
  let mut ast = parse_js::parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse source");
  let sem = bind_ts_locals(&mut ast, FileId(0));
  let lowered = hir_js::lower_file(FileId(0), hir_js::FileKind::Ts, &ast);
  let body = lowered.body(lowered.root_body()).expect("root body");

  let bindings = FlowBindings::new(body, &sem);
  let names = lowered.names.clone();

  let mut pat_ids = Vec::new();
  for (idx, pat) in body.pats.iter().enumerate() {
    if let hir_js::PatKind::Ident(name) = pat.kind {
      if names.resolve(name).as_deref() == Some("x") {
        pat_ids.push(hir_js::PatId(idx as u32));
      }
    }
  }
  assert_eq!(pat_ids.len(), 2, "expected two x patterns");
  let first_binding = bindings
    .binding_for_pat(pat_ids[0])
    .expect("binding for outer x");
  let second_binding = bindings
    .binding_for_pat(pat_ids[1])
    .expect("binding for inner x");
  assert_ne!(
    first_binding, second_binding,
    "shadowed declarations should resolve to different bindings"
  );

  let mut expr_bindings = Vec::new();
  for (idx, expr) in body.exprs.iter().enumerate() {
    if let hir_js::ExprKind::Ident(name) = expr.kind {
      if names.resolve(name).as_deref() == Some("x") {
        let binding = bindings
          .binding_for_expr(hir_js::ExprId(idx as u32))
          .unwrap_or_else(|| panic!("no binding for expr {idx}"));
        expr_bindings.push(binding);
      }
    }
  }
  assert_eq!(expr_bindings.len(), 2, "expected two x expressions");
  let unique: HashSet<_> = expr_bindings.iter().copied().collect();
  assert_eq!(unique.len(), 2, "references should target both bindings");
  assert!(unique.contains(&first_binding));
  assert!(unique.contains(&second_binding));
}

#[test]
fn flow_bindings_fall_back_to_offset_resolution() {
  let source = "const longName = longName;";
  let mut ast = parse_js::parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("parse source");
  let sem = bind_ts_locals(&mut ast, FileId(0));
  let lowered = hir_js::lower_file(FileId(0), hir_js::FileKind::Ts, &ast);
  let names = lowered.names.clone();
  let body = lowered.body(lowered.root_body()).expect("root body");

  let mut pat_info = None;
  for (idx, pat) in body.pats.iter().enumerate() {
    if let hir_js::PatKind::Ident(name_id) = pat.kind {
      if names.resolve(name_id).as_deref() == Some("longName") {
        let span = pat.span;
        let sym = sem
          .resolve_expr_span(span)
          .expect("locals should resolve pattern span");
        pat_info = Some((hir_js::PatId(idx as u32), span, sym));
        break;
      }
    }
  }
  let (pat_id, pat_span, pat_symbol) = pat_info.expect("identifier pattern");

  let mut expr_info = None;
  for (idx, expr) in body.exprs.iter().enumerate() {
    if let hir_js::ExprKind::Ident(name_id) = expr.kind {
      if names.resolve(name_id).as_deref() == Some("longName") {
        let span = expr.span;
        let sym = sem
          .resolve_expr_span(span)
          .expect("locals should resolve expression span");
        expr_info = Some((hir_js::ExprId(idx as u32), span, sym));
        break;
      }
    }
  }
  let (expr_id, expr_span, expr_symbol) = expr_info.expect("identifier expression");

  let shrink = |span: TextRange| {
    let len = span.end - span.start;
    assert!(
      len > 2,
      "expected span for fallback test to have room to shrink"
    );
    TextRange::new(span.start + 1, span.end - 1)
  };

  let mut modified_body = body.clone();
  let shrunk_expr_span = shrink(expr_span);
  assert!(
    sem.resolve_expr_span(shrunk_expr_span).is_none(),
    "shrunk expression span should miss exact lookup"
  );
  modified_body.exprs[expr_id.0 as usize].span = shrunk_expr_span;

  assert!(
    pat_span.start > 0,
    "pattern span should start after file start"
  );
  let shifted_pat_span = TextRange::new(pat_span.start - 1, pat_span.end - 1);
  assert!(
    sem.resolve_expr_span(shifted_pat_span).is_none(),
    "shifted pattern span should miss exact lookup"
  );
  modified_body.pats[pat_id.0 as usize].span = shifted_pat_span;

  assert_eq!(
    sem
      .resolve_expr_at_offset(shrunk_expr_span.start)
      .map(|(_, id)| id),
    Some(expr_symbol),
    "expression should resolve via offset fallback"
  );
  assert!(
    sem.resolve_expr_at_offset(shifted_pat_span.start).is_none(),
    "pattern start offset should not resolve so end-offset fallback is exercised"
  );
  assert_eq!(
    sem
      .resolve_expr_at_offset(shifted_pat_span.end - 1)
      .map(|(_, id)| id),
    Some(pat_symbol),
    "pattern should resolve via end-offset fallback"
  );

  let bindings = FlowBindings::new(&modified_body, &sem);

  assert_eq!(
    bindings.binding_for_expr(expr_id),
    Some(expr_symbol),
    "flow bindings should fall back for expression spans"
  );
  assert_eq!(
    bindings.binding_for_pat(pat_id),
    Some(pat_symbol),
    "flow bindings should fall back for pattern spans"
  );
}
