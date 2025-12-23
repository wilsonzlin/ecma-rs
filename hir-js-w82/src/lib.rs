use parse_js::ast::expr::pat;
use parse_js::ast::expr::{self};
use parse_js::ast::func::Func as AstFunc;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::ParamDecl;
use parse_js::ast::stmt::Stmt as AstStmt;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PatId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StmtId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BodyId(pub usize);

#[derive(Debug, Clone, Default)]
pub struct Hir {
  pub exprs: Vec<Expr>,
  pub pats: Vec<Pat>,
  pub stmts: Vec<Stmt>,
  pub bodies: Vec<Body>,
}

impl Hir {
  pub fn expr(&self, id: ExprId) -> &Expr {
    &self.exprs[id.0]
  }

  pub fn pat(&self, id: PatId) -> &Pat {
    &self.pats[id.0]
  }

  pub fn stmt(&self, id: StmtId) -> &Stmt {
    &self.stmts[id.0]
  }

  pub fn body(&self, id: BodyId) -> &Body {
    &self.bodies[id.0]
  }
}

#[derive(Debug, Clone)]
pub struct Expr {
  pub loc: Loc,
  pub kind: ExprKind,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
  ArrowFunc(Func),
  Binary {
    op: OperatorName,
    left: ExprId,
    right: ExprId,
  },
  Bool(bool),
  Id {
    name: String,
  },
  Member {
    object: ExprId,
    property: String,
    optional_chaining: bool,
  },
  Null,
  Number(JsNumber),
  Pattern(PatId),
  String(String),
  Super,
  This,
  Unsupported,
}

#[derive(Debug, Clone)]
pub struct Func {
  pub arrow: bool,
  pub async_: bool,
  pub generator: bool,
  pub params: Vec<Param>,
  pub body: BodyId,
}

#[derive(Debug, Clone)]
pub struct Param {
  pub pat: PatId,
  pub default: Option<ExprId>,
  pub rest: bool,
  pub optional: bool,
}

#[derive(Debug, Clone)]
pub struct Body {
  pub root: BodyRoot,
}

#[derive(Debug, Clone)]
pub enum BodyRoot {
  Block(Vec<StmtId>),
  Expr(ExprId),
  Empty,
}

#[derive(Debug, Clone)]
pub struct Stmt {
  pub loc: Loc,
  pub kind: StmtKind,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
  Block(Vec<StmtId>),
  Empty,
  Expr(ExprId),
  Return(Option<ExprId>),
  Unsupported,
}

#[derive(Debug, Clone)]
pub struct Pat {
  pub loc: Loc,
  pub kind: PatKind,
}

#[derive(Debug, Clone)]
pub enum PatKind {
  Array {
    elements: Vec<Option<ArrayPatElement>>,
    rest: Option<PatId>,
  },
  AssignTarget(ExprId),
  Id {
    name: String,
  },
  Object {
    props: Vec<ObjectPatProp>,
    rest: Option<PatId>,
  },
}

#[derive(Debug, Clone)]
pub struct ArrayPatElement {
  pub pat: PatId,
  pub default: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub enum ObjPatKey {
  Direct(String),
  Computed(ExprId),
}

#[derive(Debug, Clone)]
pub struct ObjectPatProp {
  pub key: ObjPatKey,
  pub pat: PatId,
  pub default: Option<ExprId>,
  pub shorthand: bool,
}

#[derive(Default)]
pub struct Lowerer {
  hir: Hir,
}

impl Lowerer {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn finish(self) -> Hir {
    self.hir
  }

  fn alloc_expr(&mut self, loc: Loc, kind: ExprKind) -> ExprId {
    let id = ExprId(self.hir.exprs.len());
    self.hir.exprs.push(Expr { loc, kind });
    id
  }

  fn alloc_pat(&mut self, loc: Loc, kind: PatKind) -> PatId {
    let id = PatId(self.hir.pats.len());
    self.hir.pats.push(Pat { loc, kind });
    id
  }

  fn alloc_stmt(&mut self, loc: Loc, kind: StmtKind) -> StmtId {
    let id = StmtId(self.hir.stmts.len());
    self.hir.stmts.push(Stmt { loc, kind });
    id
  }

  fn alloc_body(&mut self, root: BodyRoot) -> BodyId {
    let id = BodyId(self.hir.bodies.len());
    self.hir.bodies.push(Body { root });
    id
  }

  pub fn lower_expr(&mut self, expr: &Node<expr::Expr>) -> ExprId {
    let loc = expr.loc;
    let kind = match &*expr.stx {
      expr::Expr::ArrowFunc(func) => ExprKind::ArrowFunc(self.lower_func(&func.stx.func)),
      expr::Expr::Binary(binary) => {
        let left = self.lower_expr(&binary.stx.left);
        let right = self.lower_expr(&binary.stx.right);
        ExprKind::Binary {
          op: binary.stx.operator,
          left,
          right,
        }
      }
      expr::Expr::Id(id) => ExprKind::Id {
        name: id.stx.name.clone(),
      },
      expr::Expr::Member(member) => ExprKind::Member {
        object: self.lower_expr(&member.stx.left),
        property: member.stx.right.clone(),
        optional_chaining: member.stx.optional_chaining,
      },
      expr::Expr::LitBool(b) => ExprKind::Bool(b.stx.value),
      expr::Expr::LitNull(_) => ExprKind::Null,
      expr::Expr::LitNum(n) => ExprKind::Number(n.stx.value),
      expr::Expr::LitStr(s) => ExprKind::String(s.stx.value.clone()),
      expr::Expr::This(_) => ExprKind::This,
      expr::Expr::Super(_) => ExprKind::Super,
      expr::Expr::ArrPat(pat) => ExprKind::Pattern(self.lower_arr_pat(pat)),
      expr::Expr::IdPat(pat) => ExprKind::Pattern(self.lower_id_pat(pat)),
      expr::Expr::ObjPat(pat) => ExprKind::Pattern(self.lower_obj_pat(pat)),
      _ => ExprKind::Unsupported,
    };
    self.alloc_expr(loc, kind)
  }

  fn lower_func(&mut self, func: &Node<AstFunc>) -> Func {
    let params = func
      .stx
      .parameters
      .iter()
      .map(|p| self.lower_param(p))
      .collect();
    let body = self.lower_body(func.stx.body.as_ref());
    Func {
      arrow: func.stx.arrow,
      async_: func.stx.async_,
      generator: func.stx.generator,
      params,
      body,
    }
  }

  fn lower_param(&mut self, param: &Node<ParamDecl>) -> Param {
    Param {
      pat: self.lower_pat(&param.stx.pattern.stx.pat),
      default: param.stx.default_value.as_ref().map(|d| self.lower_expr(d)),
      rest: param.stx.rest,
      optional: param.stx.optional,
    }
  }

  fn lower_body(&mut self, body: Option<&FuncBody>) -> BodyId {
    let root = match body {
      Some(FuncBody::Block(stmts)) => {
        BodyRoot::Block(stmts.iter().map(|s| self.lower_stmt(s)).collect())
      }
      Some(FuncBody::Expression(expr)) => BodyRoot::Expr(self.lower_expr(expr)),
      None => BodyRoot::Empty,
    };
    self.alloc_body(root)
  }

  pub fn lower_stmt(&mut self, stmt: &Node<AstStmt>) -> StmtId {
    let loc = stmt.loc;
    let kind = match &*stmt.stx {
      AstStmt::Block(block) => {
        let stmts = block.stx.body.iter().map(|s| self.lower_stmt(s)).collect();
        StmtKind::Block(stmts)
      }
      AstStmt::Empty(_) => StmtKind::Empty,
      AstStmt::Expr(expr_stmt) => StmtKind::Expr(self.lower_expr(&expr_stmt.stx.expr)),
      AstStmt::Return(ret) => StmtKind::Return(ret.stx.value.as_ref().map(|v| self.lower_expr(v))),
      _ => StmtKind::Unsupported,
    };
    self.alloc_stmt(loc, kind)
  }

  pub fn lower_pat(&mut self, pat: &Node<pat::Pat>) -> PatId {
    match &*pat.stx {
      pat::Pat::Arr(arr) => self.lower_arr_pat(arr),
      pat::Pat::Id(id) => self.lower_id_pat(id),
      pat::Pat::Obj(obj) => self.lower_obj_pat(obj),
      pat::Pat::AssignTarget(expr) => {
        let expr_id = self.lower_expr(expr);
        self.alloc_pat(pat.loc, PatKind::AssignTarget(expr_id))
      }
    }
  }

  fn lower_arr_pat(&mut self, arr: &Node<pat::ArrPat>) -> PatId {
    let elements = arr
      .stx
      .elements
      .iter()
      .map(|elem| {
        elem.as_ref().map(|elem| ArrayPatElement {
          pat: self.lower_pat(&elem.target),
          default: elem.default_value.as_ref().map(|d| self.lower_expr(d)),
        })
      })
      .collect();
    let rest = arr.stx.rest.as_ref().map(|r| self.lower_pat(r));
    self.alloc_pat(arr.loc, PatKind::Array { elements, rest })
  }

  fn lower_id_pat(&mut self, id: &Node<pat::IdPat>) -> PatId {
    self.alloc_pat(id.loc, PatKind::Id {
      name: id.stx.name.clone(),
    })
  }

  fn lower_obj_pat(&mut self, obj: &Node<pat::ObjPat>) -> PatId {
    let props = obj
      .stx
      .properties
      .iter()
      .map(|p| ObjectPatProp {
        key: match &p.stx.key {
          parse_js::ast::class_or_object::ClassOrObjKey::Direct(direct) => {
            ObjPatKey::Direct(direct.stx.key.clone())
          }
          parse_js::ast::class_or_object::ClassOrObjKey::Computed(expr) => {
            ObjPatKey::Computed(self.lower_expr(expr))
          }
        },
        pat: self.lower_pat(&p.stx.target),
        default: p.stx.default_value.as_ref().map(|d| self.lower_expr(d)),
        shorthand: p.stx.shorthand,
      })
      .collect();
    let rest = obj.stx.rest.as_ref().map(|r| self.lower_pat(r));
    self.alloc_pat(obj.loc, PatKind::Object { props, rest })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use parse_js::parse;

  #[test]
  fn lowers_arrow_function_params_with_defaults_and_rest() {
    let src = "(a = 1, ...b) => a + b.length";
    let top = parse(src).expect("parse");
    let expr = match &*top.stx.body[0].stx {
      AstStmt::Expr(expr_stmt) => &expr_stmt.stx.expr,
      other => panic!("unexpected stmt: {other:?}"),
    };

    let mut lowerer = Lowerer::new();
    let expr_id = lowerer.lower_expr(expr);
    let hir = lowerer.finish();

    let func = match &hir.expr(expr_id).kind {
      ExprKind::ArrowFunc(func) => func,
      other => panic!("expected arrow function, got {other:?}"),
    };

    assert!(func.arrow);
    assert!(!func.async_);
    assert!(!func.generator);
    assert_eq!(func.params.len(), 2);

    let first = &func.params[0];
    assert!(!first.rest);
    assert!(!first.optional);
    let first_pat = hir.pat(first.pat);
    match &first_pat.kind {
      PatKind::Id { name } => assert_eq!(name, "a"),
      other => panic!("unexpected first param pattern: {other:?}"),
    }
    let default_expr = first.default.expect("expected default expression");
    match &hir.expr(default_expr).kind {
      ExprKind::Number(n) => assert_eq!(*n, JsNumber(1.0)),
      other => panic!("unexpected default expr: {other:?}"),
    }

    let second = &func.params[1];
    assert!(second.rest);
    assert!(!second.optional);
    match &hir.pat(second.pat).kind {
      PatKind::Id { name } => assert_eq!(name, "b"),
      other => panic!("unexpected second param pattern: {other:?}"),
    }
    assert!(second.default.is_none());

    let body = hir.body(func.body);
    let body_expr = match body.root {
      BodyRoot::Expr(id) => id,
      ref other => panic!("unexpected body root: {other:?}"),
    };
    match &hir.expr(body_expr).kind {
      ExprKind::Binary { op, left, right } => {
        assert_eq!(*op, OperatorName::Addition);
        match &hir.expr(*left).kind {
          ExprKind::Id { name } => assert_eq!(name, "a"),
          other => panic!("unexpected left expr: {other:?}"),
        }
        match &hir.expr(*right).kind {
          ExprKind::Member {
            object,
            property,
            optional_chaining,
          } => {
            assert_eq!(property, "length");
            assert!(!optional_chaining);
            match &hir.expr(*object).kind {
              ExprKind::Id { name } => assert_eq!(name, "b"),
              other => panic!("unexpected member object: {other:?}"),
            }
          }
          other => panic!("unexpected right expr: {other:?}"),
        }
      }
      other => panic!("unexpected body expr: {other:?}"),
    }
  }
}
