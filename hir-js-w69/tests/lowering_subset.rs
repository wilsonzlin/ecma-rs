use hir_js_w69::lower_top_level;
use hir_js_w69::BodyRoot;
use hir_js_w69::ExprKind;
use hir_js_w69::HirProgram;
use hir_js_w69::ObjPatKey;
use hir_js_w69::PatKind;
use hir_js_w69::StmtKind;
use parse_js::parse;
use symbol_js::compute_symbols;
use symbol_js::TopLevelMode;

fn lower_checked(source: &str) -> HirProgram {
  let mut parsed = parse(source).expect("parse input");
  compute_symbols(&mut parsed, TopLevelMode::Module);
  lower_top_level(&parsed).expect("lowering to succeed")
}

fn assert_ids_valid(hir: &HirProgram) {
  let check_body = |id: &hir_js_w69::BodyId| {
    assert!(id.index() < hir.bodies.len());
  };
  let check_stmt = |id: &hir_js_w69::StmtId| {
    assert!(id.index() < hir.stmts.len());
  };
  let check_expr = |id: &hir_js_w69::ExprId| {
    assert!(id.index() < hir.exprs.len());
  };
  let check_pat = |id: &hir_js_w69::PatId| {
    assert!(id.index() < hir.pats.len());
  };

  for (idx, body) in hir.bodies.iter().enumerate() {
    assert!(
      !body.loc.is_empty(),
      "body {idx} had empty loc with root {:?}",
      body.root
    );
    match &body.root {
      BodyRoot::Block(stmts) => stmts.iter().for_each(&check_stmt),
      BodyRoot::Expr(expr) => check_expr(expr),
    }
  }

  for (idx, stmt) in hir.stmts.iter().enumerate() {
    assert!(
      !stmt.loc.is_empty(),
      "stmt {idx} had empty loc with kind {:?}",
      stmt.kind
    );
    match &stmt.kind {
      StmtKind::Block(stmts) => stmts.iter().for_each(&check_stmt),
      StmtKind::Break { .. } => {}
      StmtKind::Expr { expr } => check_expr(expr),
      StmtKind::ForTriple {
        init,
        cond,
        post,
        body,
      } => {
        match init {
          hir_js_w69::ForInit::None => {}
          hir_js_w69::ForInit::Expr(e) => check_expr(e),
          hir_js_w69::ForInit::VarDecl(s) => check_stmt(s),
        }
        cond.iter().for_each(&check_expr);
        post.iter().for_each(&check_expr);
        body.iter().for_each(&check_stmt);
      }
      StmtKind::If {
        test,
        consequent,
        alternate,
      } => {
        check_expr(test);
        check_stmt(consequent);
        alternate.iter().for_each(&check_stmt);
      }
      StmtKind::VarDecl(var) => {
        for decl in var.declarators.iter() {
          check_pat(&decl.pat);
          decl.init.iter().for_each(&check_expr);
        }
      }
      StmtKind::While { cond, body } => {
        check_expr(cond);
        check_stmt(body);
      }
    }
  }

  for (idx, expr) in hir.exprs.iter().enumerate() {
    assert!(
      !expr.loc.is_empty(),
      "expr {idx} had empty loc with kind {:?}",
      expr.kind
    );
    match &expr.kind {
      ExprKind::ArrowFunc(func) => {
        check_body(&func.body);
        for param in func.params.iter() {
          assert!(!param.loc.is_empty(), "param in expr {idx} missing loc");
          check_pat(&param.pat);
          param.default.iter().for_each(&check_expr);
        }
      }
      ExprKind::Binary { left, right, .. } => {
        check_expr(left);
        check_expr(right);
      }
      ExprKind::Call { callee, args, .. } => {
        check_expr(callee);
        args.iter().for_each(&check_expr);
      }
      ExprKind::Member { object, .. } => check_expr(object),
      ExprKind::ComputedMember { object, member, .. } => {
        check_expr(object);
        check_expr(member);
      }
      ExprKind::Cond {
        test,
        consequent,
        alternate,
      } => {
        check_expr(test);
        check_expr(consequent);
        check_expr(alternate);
      }
      ExprKind::Unary { arg, .. } => check_expr(arg),
      ExprKind::UnaryPostfix { arg, .. } => check_expr(arg),
      ExprKind::Id(_) | ExprKind::LitBool(_) | ExprKind::LitNum(_) | ExprKind::LitStr(_) => {}
    }
  }

  for (idx, pat) in hir.pats.iter().enumerate() {
    assert!(
      !pat.loc.is_empty(),
      "pat {idx} had empty loc with kind {:?}",
      pat.kind
    );
    match &pat.kind {
      PatKind::Id(_) => {}
      PatKind::AssignTarget(expr) => check_expr(expr),
      PatKind::Arr { elements, rest } => {
        for element in elements.iter().flatten() {
          check_pat(&element.target);
          element.default_value.iter().for_each(&check_expr);
        }
        rest.iter().for_each(&check_pat);
      }
      PatKind::Obj { properties, rest } => {
        for prop in properties.iter() {
          match &prop.key {
            ObjPatKey::Computed(expr) => check_expr(expr),
            ObjPatKey::Direct(_) => {}
          }
          check_pat(&prop.target);
          prop.default_value.iter().for_each(&check_expr);
        }
        rest.iter().for_each(&check_pat);
      }
    }
  }
}

#[test]
fn lowers_nested_arrows_and_control_flow() {
  let source = r#"
    const make = (a) => (b) => a + b;
    const outer = (v) => {
      var i = 0;
      while (i < 3) {
        if (v) {
          i++;
        } else {
          i += 2;
        }
        for (var j = i; j < 5; j++) {
          foo?.bar?.(j);
        }
        for (i = i; i < 10; i++) {}
      }
      make(v)(i);
    };
  "#;

  let hir = lower_checked(source);
  let arrow_funcs = hir
    .exprs
    .iter()
    .filter(|e| matches!(e.kind, ExprKind::ArrowFunc(_)))
    .count();
  assert_eq!(hir.bodies.len(), arrow_funcs + 1);
  assert_ids_valid(&hir);
}

#[test]
fn lowers_destructuring_and_computed_keys() {
  let source = r#"
    var { a: { b = fallback }, [key()]: c = other, d = value, ...restObj } = input;
    var [first = 1, , second, ...restArr] = items;
    const pick = ({ inner = 1 }) => inner;
  "#;

  let hir = lower_checked(source);
  assert_ids_valid(&hir);

  // Ensure patterns made it through lowering.
  let obj_pat = hir
    .pats
    .iter()
    .find(|p| matches!(p.kind, PatKind::Obj { .. }))
    .expect("object pattern present");
  assert!(!obj_pat.loc.is_empty());
}
