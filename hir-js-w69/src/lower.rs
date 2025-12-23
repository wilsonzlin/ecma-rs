use crate::hir::*;
use crate::ids::*;
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::ArrPat;
use parse_js::ast::expr::pat::ObjPat;
use parse_js::ast::expr::pat::ObjPatProp as AstObjPatProp;
use parse_js::ast::expr::pat::Pat as AstPat;
use parse_js::ast::expr::ArrowFuncExpr;
use parse_js::ast::expr::BinaryExpr;
use parse_js::ast::expr::CallArg;
use parse_js::ast::expr::CallExpr;
use parse_js::ast::expr::ComputedMemberExpr;
use parse_js::ast::expr::CondExpr;
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::expr::MemberExpr;
use parse_js::ast::expr::UnaryExpr;
use parse_js::ast::expr::UnaryPostfixExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::decl::ParamDecl;
use parse_js::ast::stmt::decl::VarDecl as AstVarDecl;
use parse_js::ast::stmt::Stmt as AstStmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use std::fmt;
use symbol_js::symbol::Scope;

#[derive(Debug, Clone)]
pub struct LowerError {
  pub loc: Loc,
  pub unsupported: String,
}

impl LowerError {
  fn unsupported(loc: Loc, unsupported: impl Into<String>) -> Self {
    Self {
      loc,
      unsupported: unsupported.into(),
    }
  }
}

impl fmt::Display for LowerError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{0:?}: {1}", self.loc, self.unsupported)
  }
}

impl std::error::Error for LowerError {}

#[derive(Default)]
struct LowerCtx {
  bodies: Vec<Body>,
  exprs: Vec<Expr>,
  stmts: Vec<Stmt>,
  pats: Vec<Pat>,
}

impl LowerCtx {
  fn push_body(&mut self, body: Body) -> BodyId {
    let id = BodyId::from_index(self.bodies.len());
    self.bodies.push(body);
    id
  }

  fn push_expr(&mut self, expr: Expr) -> ExprId {
    let id = ExprId::from_index(self.exprs.len());
    self.exprs.push(expr);
    id
  }

  fn push_stmt(&mut self, stmt: Stmt) -> StmtId {
    let id = StmtId::from_index(self.stmts.len());
    self.stmts.push(stmt);
    id
  }

  fn push_pat(&mut self, pat: Pat) -> PatId {
    let id = PatId::from_index(self.pats.len());
    self.pats.push(pat);
    id
  }

  fn lower_top_level_body(&mut self, top: &Node<TopLevel>) -> Result<BodyId, LowerError> {
    let stmts = self.lower_stmt_list(&top.stx.body)?;
    Ok(self.push_body(Body {
      loc: top.loc,
      root: BodyRoot::Block(stmts),
    }))
  }

  fn lower_stmt_list(&mut self, stmts: &[Node<AstStmt>]) -> Result<Vec<StmtId>, LowerError> {
    stmts.iter().map(|s| self.lower_stmt(s)).collect()
  }

  fn lower_stmt(&mut self, stmt: &Node<AstStmt>) -> Result<StmtId, LowerError> {
    let loc = stmt.loc;
    let kind = match stmt.stx.as_ref() {
      AstStmt::Block(n) => {
        let body = self.lower_stmt_list(&n.stx.body)?;
        StmtKind::Block(body)
      }
      AstStmt::Break(n) => StmtKind::Break {
        label: n.stx.label.clone(),
      },
      AstStmt::Expr(n) => StmtKind::Expr {
        expr: self.lower_expr(&n.stx.expr, loc)?,
      },
      AstStmt::ForTriple(n) => StmtKind::ForTriple {
        init: self.lower_for_init(&n.stx.init, loc)?,
        cond: match &n.stx.cond {
          Some(c) => Some(self.lower_expr(c, loc)?),
          None => None,
        },
        post: match &n.stx.post {
          Some(p) => Some(self.lower_expr(p, loc)?),
          None => None,
        },
        body: self.lower_stmt_list(&n.stx.body.stx.body)?,
      },
      AstStmt::If(n) => StmtKind::If {
        test: self.lower_expr(&n.stx.test, loc)?,
        consequent: self.lower_stmt(&n.stx.consequent)?,
        alternate: match &n.stx.alternate {
          Some(a) => Some(self.lower_stmt(a)?),
          None => None,
        },
      },
      AstStmt::VarDecl(n) => StmtKind::VarDecl(self.lower_var_decl(n, loc)?),
      AstStmt::While(n) => StmtKind::While {
        cond: self.lower_expr(&n.stx.condition, loc)?,
        body: self.lower_stmt(&n.stx.body)?,
      },
      _ => {
        return Err(LowerError::unsupported(
          loc,
          format!("unsupported statement: {:?}", stmt.stx),
        ))
      }
    };

    Ok(self.push_stmt(Stmt { loc, kind }))
  }

  fn lower_for_init(
    &mut self,
    init: &parse_js::ast::stmt::ForTripleStmtInit,
    fallback: Loc,
  ) -> Result<ForInit, LowerError> {
    Ok(match init {
      parse_js::ast::stmt::ForTripleStmtInit::None => ForInit::None,
      parse_js::ast::stmt::ForTripleStmtInit::Expr(e) => {
        ForInit::Expr(self.lower_expr(e, fallback)?)
      }
      parse_js::ast::stmt::ForTripleStmtInit::Decl(d) => {
        let decl = self.lower_var_decl(d, d.loc)?;
        let stmt = self.push_stmt(Stmt {
          loc: d.loc,
          kind: StmtKind::VarDecl(decl),
        });
        ForInit::VarDecl(stmt)
      }
    })
  }

  fn lower_var_decl(
    &mut self,
    var: &Node<AstVarDecl>,
    fallback: Loc,
  ) -> Result<crate::hir::VarDecl, LowerError> {
    let mut declarators = Vec::new();
    for decl in var.stx.declarators.iter() {
      let pat = self.lower_pat(&decl.pattern.stx.pat, decl.pattern.loc)?;
      let init = match &decl.initializer {
        Some(init) => Some(self.lower_expr(init, fallback)?),
        None => None,
      };
      declarators.push(VarDeclarator {
        pat,
        init,
        has_type_annotation: decl.type_annotation.is_some(),
      });
    }

    Ok(crate::hir::VarDecl {
      export: var.stx.export,
      mode: var.stx.mode,
      declarators,
    })
  }

  fn lower_expr(&mut self, expr: &Node<AstExpr>, fallback: Loc) -> Result<ExprId, LowerError> {
    let loc = if expr.loc.is_empty() {
      fallback
    } else {
      expr.loc
    };
    let kind = match expr.stx.as_ref() {
      AstExpr::ArrowFunc(n) => ExprKind::ArrowFunc(self.lower_arrow_func(n, loc)?),
      AstExpr::Binary(n) => {
        let BinaryExpr {
          operator,
          left,
          right,
        } = n.stx.as_ref();
        ExprKind::Binary {
          op: *operator,
          left: self.lower_expr(left, loc)?,
          right: self.lower_expr(right, loc)?,
        }
      }
      AstExpr::Call(n) => {
        let CallExpr {
          optional_chaining,
          callee,
          arguments,
        } = n.stx.as_ref();
        let mut args = Vec::new();
        for arg in arguments.iter() {
          let CallArg { spread, value } = arg.stx.as_ref();
          if *spread {
            return Err(LowerError::unsupported(
              arg.loc,
              "spread call arguments are not supported",
            ));
          }
          args.push(self.lower_expr(value, loc)?);
        }
        ExprKind::Call {
          optional_chaining: *optional_chaining,
          callee: self.lower_expr(callee, loc)?,
          args,
        }
      }
      AstExpr::Member(n) => {
        let MemberExpr {
          optional_chaining,
          left,
          right,
        } = n.stx.as_ref();
        ExprKind::Member {
          optional_chaining: *optional_chaining,
          object: self.lower_expr(left, loc)?,
          property: right.clone(),
        }
      }
      AstExpr::ComputedMember(n) => {
        let ComputedMemberExpr {
          optional_chaining,
          object,
          member,
        } = n.stx.as_ref();
        ExprKind::ComputedMember {
          optional_chaining: *optional_chaining,
          object: self.lower_expr(object, loc)?,
          member: self.lower_expr(member, loc)?,
        }
      }
      AstExpr::Cond(n) => {
        let CondExpr {
          test,
          consequent,
          alternate,
        } = n.stx.as_ref();
        ExprKind::Cond {
          test: self.lower_expr(test, loc)?,
          consequent: self.lower_expr(consequent, loc)?,
          alternate: self.lower_expr(alternate, loc)?,
        }
      }
      AstExpr::Unary(n) => {
        let UnaryExpr { operator, argument } = n.stx.as_ref();
        ExprKind::Unary {
          op: *operator,
          arg: self.lower_expr(argument, loc)?,
        }
      }
      AstExpr::UnaryPostfix(n) => {
        let UnaryPostfixExpr { operator, argument } = n.stx.as_ref();
        ExprKind::UnaryPostfix {
          op: *operator,
          arg: self.lower_expr(argument, loc)?,
        }
      }
      AstExpr::IdPat(n) => ExprKind::Id(self.lower_ident(&n.stx.name, &n.assoc)),
      AstExpr::Id(n) => ExprKind::Id(self.lower_ident(&n.stx.name, &n.assoc)),
      AstExpr::LitBool(n) => ExprKind::LitBool(n.stx.value),
      AstExpr::LitNum(n) => ExprKind::LitNum(n.stx.value),
      AstExpr::LitStr(n) => ExprKind::LitStr(n.stx.value.clone()),
      _ => {
        return Err(LowerError::unsupported(
          loc,
          format!("unsupported expression: {:?}", expr.stx),
        ))
      }
    };

    Ok(self.push_expr(Expr { loc, kind }))
  }

  fn lower_arrow_func(
    &mut self,
    func: &Node<ArrowFuncExpr>,
    fallback: Loc,
  ) -> Result<FuncExpr, LowerError> {
    let func_node: &Node<Func> = &func.stx.func;
    let Func {
      arrow: _,
      async_,
      generator,
      parameters,
      body,
      ..
    } = func_node.stx.as_ref();
    let params = self.lower_params(parameters)?;
    let root = match body {
      Some(FuncBody::Block(stmts)) => BodyRoot::Block(self.lower_stmt_list(stmts)?),
      Some(FuncBody::Expression(expr)) => BodyRoot::Expr(self.lower_expr(expr, func_node.loc)?),
      None => {
        return Err(LowerError::unsupported(
          func_node.loc,
          "arrow function without body",
        ))
      }
    };
    let body_id = self.push_body(Body {
      loc: if func_node.loc.is_empty() {
        fallback
      } else {
        func_node.loc
      },
      root,
    });

    Ok(FuncExpr {
      params,
      body: body_id,
      async_: *async_,
      generator: *generator,
    })
  }

  fn lower_params(&mut self, params: &[Node<ParamDecl>]) -> Result<Vec<Param>, LowerError> {
    let mut out = Vec::new();
    for param in params.iter() {
      let pat = self.lower_pat(&param.stx.pattern.stx.pat, param.loc)?;
      let default = match &param.stx.default_value {
        Some(expr) => Some(self.lower_expr(expr, param.loc)?),
        None => None,
      };
      out.push(Param {
        loc: param.loc,
        pat,
        default,
        rest: param.stx.rest,
      });
    }
    Ok(out)
  }

  fn lower_pat(&mut self, pat: &Node<AstPat>, fallback: Loc) -> Result<PatId, LowerError> {
    let loc = pat.loc;
    let loc = if loc.is_empty() { fallback } else { loc };
    let kind = match pat.stx.as_ref() {
      AstPat::Id(n) => PatKind::Id(self.lower_ident(&n.stx.name, &n.assoc)),
      AstPat::Arr(n) => self.lower_arr_pat(n.stx.as_ref(), loc)?,
      AstPat::Obj(n) => self.lower_obj_pat(n.stx.as_ref(), loc)?,
      AstPat::AssignTarget(expr) => PatKind::AssignTarget(self.lower_expr(expr, loc)?),
    };
    Ok(self.push_pat(Pat { loc, kind }))
  }

  fn lower_arr_pat(&mut self, pat: &ArrPat, fallback: Loc) -> Result<PatKind, LowerError> {
    let mut elements = Vec::with_capacity(pat.elements.len());
    for elem in pat.elements.iter() {
      let elem = match elem {
        None => None,
        Some(e) => Some(ArrPatElem {
          target: self.lower_pat(&e.target, fallback)?,
          default_value: match &e.default_value {
            Some(d) => Some(self.lower_expr(d, fallback)?),
            None => None,
          },
        }),
      };
      elements.push(elem);
    }
    let rest = match &pat.rest {
      Some(rest) => Some(self.lower_pat(rest, fallback)?),
      None => None,
    };
    Ok(PatKind::Arr { elements, rest })
  }

  fn lower_obj_pat(&mut self, pat: &ObjPat, fallback: Loc) -> Result<PatKind, LowerError> {
    let mut properties = Vec::new();
    for prop in pat.properties.iter() {
      properties.push(self.lower_obj_pat_prop(prop, fallback)?);
    }
    let rest = match &pat.rest {
      Some(rest) => Some(self.lower_pat(rest, fallback)?),
      None => None,
    };
    Ok(PatKind::Obj { properties, rest })
  }

  fn lower_obj_pat_prop(
    &mut self,
    prop: &Node<AstObjPatProp>,
    fallback: Loc,
  ) -> Result<ObjPatProp, LowerError> {
    let prop_loc = if prop.loc.is_empty() {
      fallback
    } else {
      prop.loc
    };
    Ok(ObjPatProp {
      key: self.lower_obj_pat_key(&prop.stx.key, prop_loc)?,
      target: self.lower_pat(&prop.stx.target, prop_loc)?,
      shorthand: prop.stx.shorthand,
      default_value: match &prop.stx.default_value {
        Some(v) => Some(self.lower_expr(v, prop_loc)?),
        None => None,
      },
    })
  }

  fn lower_obj_pat_key(
    &mut self,
    key: &ClassOrObjKey,
    fallback: Loc,
  ) -> Result<ObjPatKey, LowerError> {
    Ok(match key {
      ClassOrObjKey::Direct(k) => ObjPatKey::Direct(k.stx.key.clone()),
      ClassOrObjKey::Computed(expr) => ObjPatKey::Computed(self.lower_expr(expr, fallback)?),
    })
  }

  fn lower_ident(&self, name: &str, assoc: &NodeAssocData) -> Ident {
    let name = name.to_string();
    let symbol = assoc
      .get::<Scope>()
      .and_then(|scope| scope.find_symbol(name.clone()));
    Ident { name, symbol }
  }
}

pub fn lower_top_level(top: &Node<TopLevel>) -> Result<HirProgram, LowerError> {
  let mut ctx = LowerCtx::default();
  let top_level_body = ctx.lower_top_level_body(top)?;
  Ok(HirProgram {
    top_level_body,
    bodies: ctx.bodies,
    exprs: ctx.exprs,
    stmts: ctx.stmts,
    pats: ctx.pats,
  })
}
