use std::collections::HashSet;

use diagnostics::FileId;
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
  let sem = bind_ts_locals(&mut ast, FileId(0), true);
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
