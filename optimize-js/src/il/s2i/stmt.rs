use parse_js::{ast::{class_or_object::ClassOrObjKey, expr::{pat::{ArrPat, IdPat, ObjPat, ObjPatProp, Pat}, Expr}, node::Node, stmt::{decl::{VarDecl, VarDeclarator}, BlockStmt, BreakStmt, ExprStmt, ForTripleStmt, ForTripleStmtInit, IfStmt, Stmt, WhileStmt}}, num::JsNumber};

use crate::il::inst::{Arg, BinOp, Const, Inst};

use super::{SourceToInst, VarType, DUMMY_LABEL};


impl<'p> SourceToInst<'p> {
  // Handle `[a = 1] = x;` or `{b: c = 2} = y;`.
  pub fn compile_destructuring_via_prop(
    &mut self,
    obj: Arg,
    prop: Arg,
    target: Node<Pat>,
    default_value: Option<Node<Expr>>,
  ) {
    let tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(
      tmp_var,
      obj,
      BinOp::GetProp,
      prop,
    ));
    if let Some(dv) = default_value {
      // Compile default value. If `%tmp` is undefined, we need to assign `e.default_value` to it.
      let after_label_id = self.c_label.bump();
      let is_undefined_tmp_var = self.c_temp.bump();
      self.out.push(Inst::bin(
        is_undefined_tmp_var,
        Arg::Var(tmp_var),
        BinOp::StrictEq,
        Arg::Const(Const::Undefined),
      ));
      self.out.push(Inst::cond_goto( Arg::Var(is_undefined_tmp_var), DUMMY_LABEL,  after_label_id));
      let dv_arg = self.compile_expr(dv);
      self.out.push(Inst::var_assign(
        tmp_var,
        dv_arg,
      ));
      self.out.push(Inst::label( after_label_id));
    };
    self.compile_destructuring(target, Arg::Var(tmp_var));
  }

  pub fn compile_destructuring(&mut self, pat: Node<Pat>, rval: Arg) {
    match *pat.stx {
      Pat::Arr(n) => {
        let ArrPat {elements, rest} = *n.stx;
        for (i, e) in elements.into_iter().enumerate() {
          let Some(e) = e else {
            continue;
          };
          self.compile_destructuring_via_prop(
            rval.clone(),
            Arg::Const(Const::Num(JsNumber(i as f64))),
            e.target,
            e.default_value,
          );
        }
        // TODO `rest`.
      }
      Pat::Obj(n) => {
        let ObjPat { properties, rest } = *n.stx;
        for p in properties {
          let ObjPatProp {
            key,
            target,
            default_value,
            ..
          } = *p.stx;
          let prop = match key {
            ClassOrObjKey::Direct(d) => Arg::Const(Const::Str(d.stx.key)),
            ClassOrObjKey::Computed(c) => self.compile_expr(c),
          };
          self.compile_destructuring_via_prop(rval.clone(), prop, target, default_value);
        }
        // TODO `rest`.
      }
      Pat::Id(n) => {
        let IdPat { name } = *n.stx;
        // NOTE: It's possible to destructure-assign to ancestor scope vars (including globals), so just because this is a pattern doesn't mean it's for a local var.
        let inst = match self.var_type(pat.assoc, name.clone()) {
          VarType::Local(local) => Inst::var_assign(
            self.symbol_to_temp(local),
            rval.clone(),
          ),
          VarType::Foreign(foreign) => Inst::foreign_store(
            foreign,
            rval.clone(),
          ),
          VarType::Unknown(unknown) => Inst::unknown_store(
            unknown,
            rval.clone(),
          ),
          VarType::Builtin(builtin) => panic!("assignment to builtin {builtin}"),
        };
        self.out.push(inst);
      }
      _ => unreachable!(),
    };
  }

  pub fn compile_stmts(&mut self, stmts: Vec<Node<Stmt>>) {
    for stmt in stmts {
      self.compile_stmt(stmt);
    }
  }

  pub fn compile_break_stmt(&mut self, BreakStmt { label }: BreakStmt) {
    // TODO Label.
    self.out.push(Inst::goto(*self.break_stack.last().unwrap()));
  }

  pub fn compile_for_triple_stmt(&mut self, ForTripleStmt { init, cond, post, body }: ForTripleStmt) {
    match init {
      ForTripleStmtInit::None => {}
      ForTripleStmtInit::Expr(e) => {
        self.compile_expr(e);
      }
      ForTripleStmtInit::Decl(d) => {
        self.compile_var_decl(*d.stx);
      }
    };
    let loop_entry_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label( loop_entry_label));
    if let Some(cond) = cond {
      let cond_arg = self.compile_expr(cond);
      self.out.push(Inst::cond_goto(cond_arg, DUMMY_LABEL,  after_loop_label));
    };
    self.break_stack.push(after_loop_label);
    self.compile_stmts(body.stx.body);
    self.break_stack.pop().unwrap();
    if let Some(post) = post {
      self.compile_expr(post);
    };
    self.out.push(Inst::goto( loop_entry_label,));
    self.out.push(Inst::label( after_loop_label));
  }

  pub fn compile_if_stmt(&mut self, IfStmt { test, consequent, alternate }: IfStmt) {
    let test_arg = self.compile_expr(test);
    match alternate {
      Some(alternate) => {
        let cons_label_id = self.c_label.bump();
        let after_label_id = self.c_label.bump();
        self.out.push(Inst::cond_goto( test_arg,  cons_label_id, DUMMY_LABEL));
        self.compile_stmt(alternate);
        self.out.push(Inst::goto( after_label_id,));
        self.out.push(Inst::label( cons_label_id));
        self.compile_stmt(consequent);
        self.out.push(Inst::label( after_label_id));
      }
      None => {
        let after_label_id = self.c_label.bump();
        self.out.push(Inst::cond_goto( test_arg, DUMMY_LABEL,  after_label_id));
        self.compile_stmt(consequent);
        self.out.push(Inst::label( after_label_id));
      }
    };
  }

  pub fn compile_var_decl(&mut self, VarDecl { export, mode, declarators }: VarDecl) {
    // TODO export.
    for VarDeclarator { initializer, pattern, type_annotation, definite_assignment: _ } in declarators
    {
      // TODO `initializer` must exist if `pattern` isn't IdentifierPattern (e.g. `var [a]; var {b};`).
      let Some(init) = initializer else {
        continue;
      };
      let tmp = self.c_temp.bump();
      let rval = self.compile_expr(init);
      self.out.push(Inst::var_assign(tmp, rval));
      self.compile_destructuring(pattern.stx.pat, Arg::Var(tmp));
    }
  }

  pub fn compile_while_stmt(&mut self, WhileStmt { condition, body }: WhileStmt) {
    let before_test_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label( before_test_label));
    let test_arg = self.compile_expr(condition);
    self.out.push(Inst::cond_goto( test_arg, DUMMY_LABEL,  after_loop_label));
    self.break_stack.push(after_loop_label);
    self.compile_stmt(body);
    self.break_stack.pop();
    self.out.push(Inst::goto( before_test_label));
    self.out.push(Inst::label( after_loop_label));
  }

  pub fn compile_expr_stmt(&mut self, ExprStmt { expr }: ExprStmt) {
    self.compile_expr(expr);
  }

  pub fn compile_stmt(&mut self, n: Node<Stmt>) {
    match *n.stx {
      Stmt::Block(n) => self.compile_stmts(n.stx.body),
      Stmt::Break(n) => self.compile_break_stmt(*n.stx),
      Stmt::Expr(n) => self.compile_expr_stmt(*n.stx),
      Stmt::ForTriple(n) => self.compile_for_triple_stmt(*n.stx),
      Stmt::If(n) => self.compile_if_stmt(*n.stx),
      Stmt::VarDecl(n) => self.compile_var_decl(*n.stx),
      Stmt::While(n) => self.compile_while_stmt(*n.stx),
      _ => unreachable!(),
    };
  }
}
