use derive_visitor::DriveMut;
use derive_visitor::VisitorMut;
use hir_js_w72::lower_top_level_and_attach_ids;
use hir_js_w72::BodyId;
use hir_js_w72::ExprId;
use hir_js_w72::HirProgram;
use hir_js_w72::PatId;
use hir_js_w72::StmtId;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::ArrowFuncExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::func::Func;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::parse;
use symbol_js::compute_symbols;
use symbol_js::TopLevelMode;

type StmtNode = Node<Stmt>;
type ExprNode = Node<Expr>;
type PatNode = Node<Pat>;
type FuncNode = Node<Func>;
type ArrowFuncExprNode = Node<ArrowFuncExpr>;

#[derive(VisitorMut)]
#[visitor(
  StmtNode(enter),
  ExprNode(enter),
  PatNode(enter),
  FuncNode(exit),
  ArrowFuncExprNode(exit)
)]
struct AssocChecker<'a> {
  program: &'a HirProgram,
  stmt_count: usize,
  expr_count: usize,
  pat_count: usize,
  func_body_ids: Vec<BodyId>,
  arrow_expr_body_ids: Vec<BodyId>,
}

impl<'a> AssocChecker<'a> {
  fn new(program: &'a HirProgram) -> Self {
    Self {
      program,
      stmt_count: 0,
      expr_count: 0,
      pat_count: 0,
      func_body_ids: Vec::new(),
      arrow_expr_body_ids: Vec::new(),
    }
  }

  fn assert_stmt(&mut self, node: &StmtNode) {
    let id = node
      .assoc
      .get::<StmtId>()
      .copied()
      .expect("expected stmt id attached");
    assert!(self.program.stmts.get(id.index()).is_some());
    self.stmt_count += 1;
  }

  fn assert_expr(&mut self, node: &ExprNode) {
    let id = node
      .assoc
      .get::<ExprId>()
      .copied()
      .expect("expected expr id attached");
    assert!(self.program.exprs.get(id.index()).is_some());
    self.expr_count += 1;
  }

  fn assert_pat(&mut self, node: &PatNode) {
    let id = node
      .assoc
      .get::<PatId>()
      .copied()
      .expect("expected pattern id attached");
    assert!(self.program.pats.get(id.index()).is_some());
    self.pat_count += 1;
  }
}

impl<'a> AssocChecker<'a> {
  fn exit_func_node(&mut self, node: &mut FuncNode) {
    if node.stx.body.is_some() && node.stx.arrow {
      let body_id = node
        .assoc
        .get::<BodyId>()
        .copied()
        .expect("expected arrow function to have body id");
      assert!(self.program.bodies.get(body_id.index()).is_some());
      self.func_body_ids.push(body_id);
    }
  }

  fn exit_arrow_func_expr_node(&mut self, node: &mut ArrowFuncExprNode) {
    if node.stx.func.stx.body.is_some() {
      let arrow_id = node
        .assoc
        .get::<BodyId>()
        .copied()
        .expect("expected arrow expr to carry body id");
      let func_id = node.stx.func.assoc.get::<BodyId>().copied();
      assert_eq!(func_id, Some(arrow_id));
      self.arrow_expr_body_ids.push(arrow_id);
    }
  }

  fn enter_stmt_node(&mut self, node: &mut StmtNode) {
    self.assert_stmt(node);
  }

  fn enter_expr_node(&mut self, node: &mut ExprNode) {
    self.assert_expr(node);
  }

  fn enter_pat_node(&mut self, node: &mut PatNode) {
    self.assert_pat(node);
  }
}

fn assert_assoc_ids(ast: &mut Node<TopLevel>, program: &HirProgram) {
  // Top-level order must be preserved.
  assert_eq!(program.top_level.len(), ast.stx.body.len());
  for (stmt, stmt_id) in ast.stx.body.iter().zip(program.top_level.iter()) {
    let attached = stmt.assoc.get::<StmtId>().copied().unwrap();
    assert_eq!(&attached, stmt_id);
  }

  let mut visitor = AssocChecker::new(program);
  ast.drive_mut(&mut visitor);

  assert_eq!(visitor.stmt_count, program.stmts.len());
  assert_eq!(visitor.expr_count, program.exprs.len());
  assert_eq!(visitor.pat_count, program.pats.len());

  // Every arrow function should have exactly one body id shared with its arrow expression.
  assert_eq!(
    visitor.func_body_ids.len(),
    visitor.arrow_expr_body_ids.len()
  );
  for body_id in visitor.func_body_ids.iter() {
    assert!(visitor.arrow_expr_body_ids.contains(body_id));
  }
}

#[test]
fn attaches_ids_during_lowering() {
  let source = r#"
    const [a, b] = call();
    const obj = { nested: 1 };
    const makeAdder = (x) => (y) => x + y + obj.nested;
    const double = (value) => { return value * 2; };
  "#;

  let mut ast = parse(source).expect("parse should succeed");
  compute_symbols(&mut ast, TopLevelMode::Module);

  let program = lower_top_level_and_attach_ids(&mut ast).expect("lowering failed");
  assert_assoc_ids(&mut ast, &program);

  // Lowering again should deterministically overwrite existing assoc entries.
  let program_again = lower_top_level_and_attach_ids(&mut ast).expect("second lowering failed");
  assert_assoc_ids(&mut ast, &program_again);
}
