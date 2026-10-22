use hir_js::lower_from_source;
use hir_js::StmtKind;

#[test]
fn namespace_interface_lowers_to_decl_stmt() {
  let source = r#"
namespace N {
  interface Base { a: number }
  var b: Base;
}
"#;
  let lowered = lower_from_source(source).expect("lower");
  let body = lowered.body(lowered.hir.root_body).expect("top body");
  let mut found_iface = false;
  let mut kinds = Vec::new();
  fn walk(
    body: &hir_js::Body,
    stmts: &[hir_js::StmtId],
    lowered: &hir_js::LowerResult,
    found: &mut bool,
    kinds: &mut Vec<String>,
  ) {
    for id in stmts {
      let stmt = &body.stmts[id.0 as usize];
      match &stmt.kind {
        StmtKind::Decl(def) => {
          if let Some(d) = lowered.def(*def) {
            let name = lowered.names.resolve(d.name).unwrap_or("?");
            kinds.push(format!("Decl({name})"));
            if name == "Base" {
              *found = true;
            }
          }
        }
        StmtKind::Block(inner) => {
          kinds.push("Block".into());
          walk(body, inner, lowered, found, kinds);
        }
        StmtKind::Empty => kinds.push("Empty".into()),
        StmtKind::Var(_) => kinds.push("Var".into()),
        _ => kinds.push("Other".into()),
      }
    }
  }
  walk(
    body,
    &body.root_stmts,
    &lowered,
    &mut found_iface,
    &mut kinds,
  );
  assert!(
    found_iface,
    "expected Interface Base as StmtKind::Decl; kinds={kinds:?}"
  );
}
