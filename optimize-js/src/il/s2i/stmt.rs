use super::{HirSourceToInst, VarType, DUMMY_LABEL};
use crate::il::inst::{Arg, BinOp, Const, Inst};
use crate::unsupported_syntax_range;
use crate::util::counter::Counter;
use crate::OptimizeResult;
use crate::ProgramCompiler;
use hir_js::{
  Body, BodyId, BodyKind, ExprId, ForInit, ObjectKey, PatId, PatKind, StmtId, StmtKind, VarDecl,
  VarDeclarator,
};
use parse_js::loc::Loc;
use parse_js::num::JsNumber;

pub fn key_arg(compiler: &mut HirSourceToInst<'_>, key: &ObjectKey) -> OptimizeResult<Arg> {
  Ok(match key {
    ObjectKey::Ident(name) => Arg::Const(Const::Str(compiler.name_for(*name))),
    ObjectKey::String(s) => Arg::Const(Const::Str(s.clone())),
    ObjectKey::Number(n) => Arg::Const(Const::Str(n.clone())),
    ObjectKey::Computed(expr) => compiler.compile_expr(*expr)?,
  })
}

fn root_statements(body: &Body) -> Vec<StmtId> {
  let mut referenced = vec![false; body.stmts.len()];
  for stmt in body.stmts.iter() {
    match &stmt.kind {
      StmtKind::Block(stmts) => {
        for id in stmts {
          referenced[id.0 as usize] = true;
        }
      }
      StmtKind::If {
        consequent,
        alternate,
        ..
      } => {
        referenced[consequent.0 as usize] = true;
        if let Some(alt) = alternate {
          referenced[alt.0 as usize] = true;
        }
      }
      StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } => {
        referenced[body.0 as usize] = true;
      }
      StmtKind::For { body, .. } | StmtKind::ForIn { body, .. } => {
        referenced[body.0 as usize] = true;
      }
      StmtKind::Switch { cases, .. } => {
        for case in cases {
          for stmt in case.consequent.iter() {
            referenced[stmt.0 as usize] = true;
          }
        }
      }
      StmtKind::Try {
        block,
        catch,
        finally_block,
      } => {
        referenced[block.0 as usize] = true;
        if let Some(catch) = catch {
          referenced[catch.body.0 as usize] = true;
        }
        if let Some(finally) = finally_block {
          referenced[finally.0 as usize] = true;
        }
      }
      StmtKind::Labeled { body, .. } | StmtKind::With { body, .. } => {
        referenced[body.0 as usize] = true;
      }
      _ => {}
    }
  }
  let mut roots: Vec<_> = body
    .stmts
    .iter()
    .enumerate()
    .filter_map(|(idx, _)| (!referenced[idx]).then_some(StmtId(idx as u32)))
    .collect();
  roots.sort_by_key(|id| body.stmts[id.0 as usize].span.start);
  roots
}

impl<'p> HirSourceToInst<'p> {
  pub fn compile_destructuring_via_prop(
    &mut self,
    obj: Arg,
    prop: Arg,
    target: PatId,
    default_value: Option<ExprId>,
  ) -> OptimizeResult<()> {
    let tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(tmp_var, obj, BinOp::GetProp, prop));
    if let Some(dv) = default_value {
      let after_label_id = self.c_label.bump();
      let is_undefined_tmp_var = self.c_temp.bump();
      self.out.push(Inst::bin(
        is_undefined_tmp_var,
        Arg::Var(tmp_var),
        BinOp::StrictEq,
        Arg::Const(Const::Undefined),
      ));
      self.out.push(Inst::cond_goto(
        Arg::Var(is_undefined_tmp_var),
        DUMMY_LABEL,
        after_label_id,
      ));
      let dv_arg = self.compile_expr(dv)?;
      self.out.push(Inst::var_assign(tmp_var, dv_arg));
      self.out.push(Inst::label(after_label_id));
    };
    self.compile_destructuring(target, Arg::Var(tmp_var))
  }

  pub fn compile_destructuring(&mut self, pat: PatId, rval: Arg) -> OptimizeResult<()> {
    match &self.body.pats[pat.0 as usize].kind {
      PatKind::Array(arr) => {
        for (i, e) in arr.elements.iter().enumerate() {
          let Some(e) = e else {
            continue;
          };
          self.compile_destructuring_via_prop(
            rval.clone(),
            Arg::Const(Const::Num(JsNumber(i as f64))),
            e.pat,
            e.default_value,
          )?;
        }
      }
      PatKind::Object(obj) => {
        for p in obj.props.iter() {
          let prop = key_arg(self, &p.key)?;
          self.compile_destructuring_via_prop(rval.clone(), prop, p.value, p.default_value)?;
        }
      }
      PatKind::Ident(name) => {
        let var_type = self.classify_symbol(self.symbol_for_pat(pat), self.name_for(*name));
        let inst = match var_type {
          VarType::Local(local) => Inst::var_assign(self.symbol_to_temp(local), rval.clone()),
          VarType::Foreign(foreign) => Inst::foreign_store(foreign, rval.clone()),
          VarType::Unknown(unknown) => Inst::unknown_store(unknown, rval.clone()),
          VarType::Builtin(builtin) => {
            return Err(unsupported_syntax_range(
              self.body.pats[pat.0 as usize].span,
              format!("assignment to builtin {builtin}"),
            ))
          }
        };
        self.out.push(inst);
      }
      _ => {
        return Err(unsupported_syntax_range(
          self.body.pats[pat.0 as usize].span,
          "unsupported destructuring pattern",
        ))
      }
    };
    Ok(())
  }

  pub fn compile_var_decl(&mut self, decl: &VarDecl) -> OptimizeResult<()> {
    for VarDeclarator { pat, init, .. } in decl.declarators.iter() {
      let Some(init) = init else {
        continue;
      };
      let tmp = self.c_temp.bump();
      let rval = self.compile_expr(*init)?;
      self.out.push(Inst::var_assign(tmp, rval));
      self.compile_destructuring(*pat, Arg::Var(tmp))?;
    }
    Ok(())
  }

  fn compile_for_stmt(
    &mut self,
    _span: Loc,
    init: &Option<ForInit>,
    cond: &Option<ExprId>,
    post: &Option<ExprId>,
    body: StmtId,
  ) -> OptimizeResult<()> {
    match init {
      Some(ForInit::Expr(e)) => {
        self.compile_expr(*e)?;
      }
      Some(ForInit::Var(d)) => {
        self.compile_var_decl(d)?;
      }
      None => {}
    };
    let loop_entry_label = self.c_label.bump();
    let loop_continue_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label(loop_entry_label));
    if let Some(cond) = cond {
      let cond_arg = self.compile_expr(*cond)?;
      self
        .out
        .push(Inst::cond_goto(cond_arg, DUMMY_LABEL, after_loop_label));
    };
    self.break_stack.push(after_loop_label);
    self.continue_stack.push(loop_continue_label);
    self.compile_stmt(body)?;
    self.continue_stack.pop();
    self.break_stack.pop().unwrap();
    self.out.push(Inst::label(loop_continue_label));
    if let Some(post) = post {
      self.compile_expr(*post)?;
    };
    self.out.push(Inst::goto(loop_entry_label));
    self.out.push(Inst::label(after_loop_label));
    Ok(())
  }

  fn compile_if_stmt(
    &mut self,
    _span: Loc,
    test: ExprId,
    consequent: StmtId,
    alternate: Option<StmtId>,
  ) -> OptimizeResult<()> {
    let known = self.bool_literal_expr(test);
    let test_arg = self.compile_expr(test)?;
    if let Some(value) = known {
      if value {
        self.compile_stmt(consequent)?;
      } else if let Some(alternate) = alternate {
        self.compile_stmt(alternate)?;
      }
      return Ok(());
    }
    match alternate {
      Some(alternate) => {
        let cons_label_id = self.c_label.bump();
        let after_label_id = self.c_label.bump();
        self
          .out
          .push(Inst::cond_goto(test_arg, cons_label_id, DUMMY_LABEL));
        self.compile_stmt(alternate)?;
        self.out.push(Inst::goto(after_label_id));
        self.out.push(Inst::label(cons_label_id));
        self.compile_stmt(consequent)?;
        self.out.push(Inst::label(after_label_id));
      }
      None => {
        let after_label_id = self.c_label.bump();
        self
          .out
          .push(Inst::cond_goto(test_arg, DUMMY_LABEL, after_label_id));
        self.compile_stmt(consequent)?;
        self.out.push(Inst::label(after_label_id));
      }
    };
    Ok(())
  }

  fn compile_switch_stmt(
    &mut self,
    span: Loc,
    discriminant: ExprId,
    cases: &[hir_js::hir::SwitchCase],
  ) -> OptimizeResult<()> {
    let discriminant_tmp_var = self.c_temp.bump();
    let discriminant_arg = self.compile_expr(discriminant)?;
    self
      .out
      .push(Inst::var_assign(discriminant_tmp_var, discriminant_arg));

    if cases.is_empty() {
      return Ok(());
    }

    let after_switch_label = self.c_label.bump();
    self.break_stack.push(after_switch_label);

    let mut case_labels = Vec::with_capacity(cases.len());
    let mut default_label = None;
    for case in cases.iter() {
      let label = self.c_label.bump();
      if case.test.is_none() && default_label.is_none() {
        default_label = Some(label);
      }
      case_labels.push(label);
    }

    let default_or_after = default_label.unwrap_or(after_switch_label);
    let test_indices: Vec<usize> = cases
      .iter()
      .enumerate()
      .filter_map(|(idx, case)| case.test.map(|_| idx))
      .collect();

    for (pos, &idx) in test_indices.iter().enumerate() {
      let test_expr = cases[idx].test.expect("case has test");
      let test_arg = self.compile_expr(test_expr)?;
      let cmp_tmp_var = self.c_temp.bump();
      self.out.push(Inst::bin(
        cmp_tmp_var,
        Arg::Var(discriminant_tmp_var),
        BinOp::StrictEq,
        test_arg,
      ));
      let fallthrough = if pos == test_indices.len() - 1 {
        default_or_after
      } else {
        DUMMY_LABEL
      };
      self.out.push(Inst::cond_goto(
        Arg::Var(cmp_tmp_var),
        case_labels[idx],
        fallthrough,
      ));
    }

    if test_indices.is_empty() {
      // Only a `default` clause can exist in this scenario, so always jump to it.
      self.out.push(Inst::goto(default_or_after));
    }

    for (idx, case) in cases.iter().enumerate() {
      self.out.push(Inst::label(case_labels[idx]));
      for stmt in case.consequent.iter() {
        self.compile_stmt(*stmt)?;
      }
    }

    self.break_stack.pop();
    self.out.push(Inst::label(after_switch_label));

    let _ = span;
    Ok(())
  }

  fn compile_do_while_stmt(
    &mut self,
    test: ExprId,
    body: StmtId,
    _span: Loc,
  ) -> OptimizeResult<()> {
    let loop_entry_label = self.c_label.bump();
    let loop_continue_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label(loop_entry_label));
    self.break_stack.push(after_loop_label);
    self.continue_stack.push(loop_continue_label);
    self.compile_stmt(body)?;
    self.continue_stack.pop();
    self.break_stack.pop();
    self.out.push(Inst::label(loop_continue_label));
    let test_arg = self.compile_expr(test)?;
    self
      .out
      .push(Inst::cond_goto(test_arg, loop_entry_label, after_loop_label));
    self.out.push(Inst::label(after_loop_label));
    Ok(())
  }

  fn compile_while_stmt(&mut self, test: ExprId, body: StmtId, _span: Loc) -> OptimizeResult<()> {
    let before_test_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label(before_test_label));
    let test_arg = self.compile_expr(test)?;
    self
      .out
      .push(Inst::cond_goto(test_arg, DUMMY_LABEL, after_loop_label));
    self.break_stack.push(after_loop_label);
    self.continue_stack.push(before_test_label);
    self.compile_stmt(body)?;
    self.continue_stack.pop();
    self.break_stack.pop();
    self.out.push(Inst::goto(before_test_label));
    self.out.push(Inst::label(after_loop_label));
    Ok(())
  }

  pub fn compile_stmt(&mut self, stmt_id: StmtId) -> OptimizeResult<()> {
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    let span = Loc(stmt.span.start as usize, stmt.span.end as usize);
    match &stmt.kind {
      StmtKind::Block(stmts) => {
        for stmt in stmts {
          self.compile_stmt(*stmt)?;
        }
        Ok(())
      }
      StmtKind::Break(_) => {
        if !matches!(&stmt.kind, StmtKind::Break(None)) {
          return Err(unsupported_syntax_range(
            stmt.span,
            "labeled break is not supported",
          ));
        }
        let target = self
          .break_stack
          .last()
          .copied()
          .ok_or_else(|| unsupported_syntax_range(stmt.span, "break statement outside loop"))?;
        self.out.push(Inst::goto(target));
        Ok(())
      }
      StmtKind::Continue(_) => {
        if !matches!(&stmt.kind, StmtKind::Continue(None)) {
          return Err(unsupported_syntax_range(
            stmt.span,
            "labeled continue is not supported",
          ));
        }
        let target =
          self.continue_stack.last().copied().ok_or_else(|| {
            unsupported_syntax_range(stmt.span, "continue statement outside loop")
          })?;
        self.out.push(Inst::goto(target));
        Ok(())
      }
      StmtKind::Return(value) => {
        if let Some(value) = value {
          let _ = self.compile_expr(*value)?;
        }
        let target = self
          .return_label
          .ok_or_else(|| unsupported_syntax_range(stmt.span, "return statement outside function"))?;
        self.out.push(Inst::goto(target));
        Ok(())
      }
      StmtKind::Expr(expr) => {
        self.compile_expr(*expr)?;
        Ok(())
      }
      StmtKind::For {
        init,
        test,
        update,
        body,
      } => self.compile_for_stmt(span, init, test, update, *body),
      StmtKind::If {
        test,
        consequent,
        alternate,
      } => self.compile_if_stmt(span, *test, *consequent, *alternate),
      StmtKind::Switch {
        discriminant,
        cases,
      } => self.compile_switch_stmt(span, *discriminant, cases),
      StmtKind::Var(decl) => self.compile_var_decl(decl),
      StmtKind::While { test, body } => self.compile_while_stmt(*test, *body, span),
      StmtKind::DoWhile { test, body } => self.compile_do_while_stmt(*test, *body, span),
      StmtKind::Debugger => Err(unsupported_syntax_range(
        stmt.span,
        "debugger statements are not supported",
      )),
      StmtKind::Empty => Ok(()),
      StmtKind::Decl(_) => Ok(()),
      StmtKind::With { .. } => Err(unsupported_syntax_range(
        stmt.span,
        "with statements introduce dynamic scope and are not supported",
      )),
      other => Err(unsupported_syntax_range(
        stmt.span,
        format!("unsupported statement {other:?}"),
      )),
    }
  }
}

pub fn translate_body(
  program: &ProgramCompiler,
  body_id: BodyId,
) -> OptimizeResult<(Vec<Inst>, Counter, Counter)> {
  let mut compiler = HirSourceToInst::new(program, body_id);
  if compiler.body.kind == BodyKind::Function {
    compiler.return_label = Some(compiler.c_label.bump());
  }
  for stmt in root_statements(compiler.body) {
    compiler.compile_stmt(stmt)?;
  }
  if let Some(label) = compiler.return_label {
    compiler.out.push(Inst::label(label));
  }
  Ok((compiler.out, compiler.c_label, compiler.c_temp))
}
