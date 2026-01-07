use super::{HirSourceToInst, LabeledTarget, VarType, DUMMY_LABEL};
use crate::il::inst::{Arg, BinOp, Const, Inst};
use crate::symbol::semantics::SymbolId;
use crate::unsupported_syntax_range;
use crate::util::counter::Counter;
use crate::OptimizeResult;
use crate::ProgramCompiler;
use crate::TextRange;
use hir_js::{
  Body, BodyId, BodyKind, ExprId, ExprKind, ForHead, ForInit, NameId, ObjectKey, PatId, PatKind,
  StmtId, StmtKind, VarDecl, VarDeclKind, VarDeclarator,
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
  fn collect_pat_binding_symbols(&self, pat: PatId, out: &mut Vec<SymbolId>) {
    match &self.body.pats[pat.0 as usize].kind {
      PatKind::Ident(_) => {
        if let Some(sym) = self.symbol_for_pat(pat) {
          out.push(sym);
        }
      }
      PatKind::Array(arr) => {
        for element in arr.elements.iter().flatten() {
          self.collect_pat_binding_symbols(element.pat, out);
        }
        if let Some(rest) = arr.rest {
          self.collect_pat_binding_symbols(rest, out);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.collect_pat_binding_symbols(prop.value, out);
        }
        if let Some(rest) = obj.rest {
          self.collect_pat_binding_symbols(rest, out);
        }
      }
      PatKind::Rest(inner) => self.collect_pat_binding_symbols(**inner, out),
      PatKind::Assign { target, .. } => self.collect_pat_binding_symbols(*target, out),
      PatKind::AssignTarget(_) => {}
    }
  }

  fn hoist_var_decls(&mut self) {
    let mut declared = Vec::<SymbolId>::new();
    for stmt in self.body.stmts.iter() {
      match &stmt.kind {
        StmtKind::Var(decl) if decl.kind == VarDeclKind::Var => {
          for declarator in decl.declarators.iter() {
            self.collect_pat_binding_symbols(declarator.pat, &mut declared);
          }
        }
        StmtKind::For {
          init: Some(ForInit::Var(decl)),
          ..
        } if decl.kind == VarDeclKind::Var => {
          for declarator in decl.declarators.iter() {
            self.collect_pat_binding_symbols(declarator.pat, &mut declared);
          }
        }
        StmtKind::ForIn {
          left: ForHead::Var(decl),
          ..
        } if decl.kind == VarDeclKind::Var => {
          for declarator in decl.declarators.iter() {
            self.collect_pat_binding_symbols(declarator.pat, &mut declared);
          }
        }
        _ => {}
      }
    }

    if declared.is_empty() {
      return;
    }

    let mut params = Vec::<SymbolId>::new();
    if let Some(function) = &self.body.function {
      for param in function.params.iter() {
        self.collect_pat_binding_symbols(param.pat, &mut params);
      }
    }
    params.sort_by_key(|sym| sym.raw_id());
    params.dedup();

    declared.retain(|sym| params.binary_search(sym).is_err());
    declared.sort_by_key(|sym| sym.raw_id());
    declared.dedup();

    for sym in declared {
      if self.program.foreign_vars.contains(&sym) {
        self
          .out
          .push(Inst::foreign_store(sym, Arg::Const(Const::Undefined)));
      } else {
        let tmp = self.symbol_to_temp(sym);
        self
          .out
          .push(Inst::var_assign(tmp, Arg::Const(Const::Undefined)));
      }
    }
  }

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
              self.program.lower.hir.file,
              self.body.pats[pat.0 as usize].span,
              format!("assignment to builtin {builtin}"),
            ))
          }
        };
        self.out.push(inst);
      }
      PatKind::AssignTarget(expr_id) => {
        let expr = &self.body.exprs[expr_id.0 as usize];
        let inst = match &expr.kind {
          ExprKind::Member(member) => {
            if member.optional {
              return Err(unsupported_syntax_range(
                self.program.lower.hir.file,
                expr.span,
                "optional chaining in assignment target",
              ));
            }
            let obj = self.compile_expr(member.object)?;
            let prop = key_arg(self, &member.property)?;
            Inst::prop_assign(obj, prop, rval.clone())
          }
          other => {
            return Err(unsupported_syntax_range(
              self.program.lower.hir.file,
              expr.span,
              format!("unsupported assignment target {other:?}"),
            ))
          }
        };
        self.out.push(inst);
      }
      _ => {
        return Err(unsupported_syntax_range(
          self.program.lower.hir.file,
          self.body.pats[pat.0 as usize].span,
          "unsupported destructuring pattern",
        ))
      }
    };
    Ok(())
  }

  pub fn compile_var_decl(&mut self, decl: &VarDecl) -> OptimizeResult<()> {
    for VarDeclarator { pat, init, .. } in decl.declarators.iter() {
      let pat_span = self.body.pats[pat.0 as usize].span;
      match init {
        Some(init) => {
          let tmp = self.c_temp.bump();
          let rval = self.compile_expr(*init)?;
          self.out.push(Inst::var_assign(tmp, rval));
          self.compile_destructuring(*pat, Arg::Var(tmp))?;
        }
        None => match decl.kind {
          VarDeclKind::Const | VarDeclKind::Using | VarDeclKind::AwaitUsing => {
            return Err(unsupported_syntax_range(
              self.program.lower.hir.file,
              pat_span,
              format!("{:?} declarations must have initializers", decl.kind),
            ));
          }
          VarDeclKind::Let => match self.body.pats[pat.0 as usize].kind {
            PatKind::Ident(_) => {
              self.compile_destructuring(*pat, Arg::Const(Const::Undefined))?;
            }
            _ => {
              return Err(unsupported_syntax_range(
                self.program.lower.hir.file,
                pat_span,
                "destructuring declarations must have initializers",
              ));
            }
          },
          VarDeclKind::Var => {
            // `var x;` is hoisted and has no runtime effect at the declaration site, so
            // we do not emit an explicit assignment here.
          }
        },
      }
    }
    Ok(())
  }

  fn compile_for_head(
    &mut self,
    span: TextRange,
    head: &ForHead,
    value: Arg,
  ) -> OptimizeResult<()> {
    match head {
      ForHead::Pat(pat) => self.compile_destructuring(*pat, value),
      ForHead::Var(decl) => {
        if decl.declarators.len() != 1 {
          return Err(unsupported_syntax_range(
            self.program.lower.hir.file,
            span,
            "for-in/of variable declarations must have a single declarator",
          ));
        }
        self.compile_destructuring(decl.declarators[0].pat, value)
      }
    }
  }

  fn compile_for_in_of_stmt(
    &mut self,
    span: TextRange,
    left: &ForHead,
    right: ExprId,
    body: StmtId,
    is_for_of: bool,
    await_: bool,
    label: Option<NameId>,
  ) -> OptimizeResult<()> {
    if await_ && !is_for_of {
      return Err(unsupported_syntax_range(
        self.program.lower.hir.file,
        span,
        "for-in statements do not support await",
      ));
    }

    let iterable_tmp_var = if is_for_of {
      let iterable_tmp_var = self.c_temp.bump();
      let iterable_arg = self.compile_expr(right)?;
      self
        .out
        .push(Inst::var_assign(iterable_tmp_var, iterable_arg));
      iterable_tmp_var
    } else {
      let obj_tmp_var = self.c_temp.bump();
      let obj_arg = self.compile_expr(right)?;
      self.out.push(Inst::var_assign(obj_tmp_var, obj_arg));

      let keys_tmp_var = self.c_temp.bump();
      self.out.push(Inst::call(
        keys_tmp_var,
        Arg::Builtin("Object.keys".to_string()),
        Arg::Const(Const::Undefined),
        vec![Arg::Var(obj_tmp_var)],
        Vec::new(),
      ));
      keys_tmp_var
    };

    let iterator_method_tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(
      iterator_method_tmp_var,
      Arg::Var(iterable_tmp_var),
      BinOp::GetProp,
      Arg::Builtin(
        if await_ {
          "Symbol.asyncIterator"
        } else {
          "Symbol.iterator"
        }
        .to_string(),
      ),
    ));

    let iterator_tmp_var = self.c_temp.bump();
    self.out.push(Inst::call(
      iterator_tmp_var,
      Arg::Var(iterator_method_tmp_var),
      Arg::Var(iterable_tmp_var),
      Vec::new(),
      Vec::new(),
    ));

    let loop_entry_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label(loop_entry_label));

    let next_method_tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(
      next_method_tmp_var,
      Arg::Var(iterator_tmp_var),
      BinOp::GetProp,
      Arg::Const(Const::Str("next".to_string())),
    ));
    let next_result_tmp_var = self.c_temp.bump();
    self.out.push(Inst::call(
      next_result_tmp_var,
      Arg::Var(next_method_tmp_var),
      Arg::Var(iterator_tmp_var),
      Vec::new(),
      Vec::new(),
    ));

    let iter_result_tmp_var = if await_ {
      let awaited_tmp_var = self.c_temp.bump();
      self.out.push(Inst::call(
        awaited_tmp_var,
        Arg::Builtin("__optimize_js_await".to_string()),
        Arg::Const(Const::Undefined),
        vec![Arg::Var(next_result_tmp_var)],
        Vec::new(),
      ));
      awaited_tmp_var
    } else {
      next_result_tmp_var
    };

    let done_tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(
      done_tmp_var,
      Arg::Var(iter_result_tmp_var),
      BinOp::GetProp,
      Arg::Const(Const::Str("done".to_string())),
    ));
    self.out.push(Inst::cond_goto(
      Arg::Var(done_tmp_var),
      after_loop_label,
      DUMMY_LABEL,
    ));

    let value_tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(
      value_tmp_var,
      Arg::Var(iter_result_tmp_var),
      BinOp::GetProp,
      Arg::Const(Const::Str("value".to_string())),
    ));
    self.compile_for_head(span, left, Arg::Var(value_tmp_var))?;

    self.break_stack.push(after_loop_label);
    self.continue_stack.push(loop_entry_label);
    if let Some(label) = label {
      self.label_stack.push(LabeledTarget {
        label,
        break_target: after_loop_label,
        continue_target: Some(loop_entry_label),
      });
    }
    let res = self.compile_stmt(body);
    if label.is_some() {
      self.label_stack.pop();
    }
    self.continue_stack.pop();
    self.break_stack.pop();
    res?;

    self.out.push(Inst::goto(loop_entry_label));
    self.out.push(Inst::label(after_loop_label));
    Ok(())
  }

  fn compile_for_stmt(
    &mut self,
    _span: Loc,
    init: &Option<ForInit>,
    cond: &Option<ExprId>,
    post: &Option<ExprId>,
    body: StmtId,
    label: Option<NameId>,
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
    if let Some(label) = label {
      self.label_stack.push(LabeledTarget {
        label,
        break_target: after_loop_label,
        continue_target: Some(loop_continue_label),
      });
    }
    let res = self.compile_stmt(body);
    if label.is_some() {
      self.label_stack.pop();
    }
    self.continue_stack.pop();
    self.break_stack.pop().unwrap();
    res?;
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
    let known = self.expr_truthiness(test);
    let test_arg = self.compile_expr(test)?;
    if let Some(truthiness) = known {
      match truthiness {
        crate::types::Truthiness::AlwaysTruthy => {
          self.compile_stmt(consequent)?;
        }
        crate::types::Truthiness::AlwaysFalsy => {
          if let Some(alternate) = alternate {
            self.compile_stmt(alternate)?;
          }
        }
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
    label: Option<NameId>,
  ) -> OptimizeResult<()> {
    let loop_entry_label = self.c_label.bump();
    let loop_continue_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label(loop_entry_label));
    self.break_stack.push(after_loop_label);
    self.continue_stack.push(loop_continue_label);
    if let Some(label) = label {
      self.label_stack.push(LabeledTarget {
        label,
        break_target: after_loop_label,
        continue_target: Some(loop_continue_label),
      });
    }
    let res = self.compile_stmt(body);
    if label.is_some() {
      self.label_stack.pop();
    }
    self.continue_stack.pop();
    self.break_stack.pop();
    res?;
    self.out.push(Inst::label(loop_continue_label));
    let test_arg = self.compile_expr(test)?;
    self.out.push(Inst::cond_goto(
      test_arg,
      loop_entry_label,
      after_loop_label,
    ));
    self.out.push(Inst::label(after_loop_label));
    Ok(())
  }

  fn compile_while_stmt(
    &mut self,
    test: ExprId,
    body: StmtId,
    _span: Loc,
    label: Option<NameId>,
  ) -> OptimizeResult<()> {
    let before_test_label = self.c_label.bump();
    let after_loop_label = self.c_label.bump();
    self.out.push(Inst::label(before_test_label));
    let test_arg = self.compile_expr(test)?;
    self
      .out
      .push(Inst::cond_goto(test_arg, DUMMY_LABEL, after_loop_label));
    self.break_stack.push(after_loop_label);
    self.continue_stack.push(before_test_label);
    if let Some(label) = label {
      self.label_stack.push(LabeledTarget {
        label,
        break_target: after_loop_label,
        continue_target: Some(before_test_label),
      });
    }
    let res = self.compile_stmt(body);
    if label.is_some() {
      self.label_stack.pop();
    }
    self.continue_stack.pop();
    self.break_stack.pop();
    res?;
    self.out.push(Inst::goto(before_test_label));
    self.out.push(Inst::label(after_loop_label));
    Ok(())
  }

  pub fn compile_stmt(&mut self, stmt_id: StmtId) -> OptimizeResult<()> {
    let file = self.program.lower.hir.file;
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    let span = Loc(stmt.span.start as usize, stmt.span.end as usize);
    match &stmt.kind {
      StmtKind::Block(stmts) => {
        for stmt in stmts {
          self.compile_stmt(*stmt)?;
        }
        Ok(())
      }
      StmtKind::Break(label) => {
        let target = if let Some(label) = label {
          self
            .label_stack
            .iter()
            .rev()
            .find(|entry| entry.label == *label)
            .map(|entry| entry.break_target)
            .ok_or_else(|| {
              unsupported_syntax_range(
                file,
                stmt.span,
                format!("break to unknown label {}", self.name_for(*label)),
              )
            })?
        } else {
          self.break_stack.last().copied().ok_or_else(|| {
            unsupported_syntax_range(file, stmt.span, "break statement outside loop")
          })?
        };
        self.out.push(Inst::goto(target));
        Ok(())
      }
      StmtKind::Continue(label) => {
        let target = if let Some(label) = label {
          let entry = self
            .label_stack
            .iter()
            .rev()
            .find(|entry| entry.label == *label)
            .ok_or_else(|| {
              unsupported_syntax_range(
                file,
                stmt.span,
                format!("continue to unknown label {}", self.name_for(*label)),
              )
            })?;
          entry.continue_target.ok_or_else(|| {
            unsupported_syntax_range(
              file,
              stmt.span,
              format!("continue to non-loop label {}", self.name_for(*label)),
            )
          })?
        } else {
          self.continue_stack.last().copied().ok_or_else(|| {
            unsupported_syntax_range(file, stmt.span, "continue statement outside loop")
          })?
        };
        self.out.push(Inst::goto(target));
        Ok(())
      }
      StmtKind::Labeled { label, body } => {
        let body_kind = self.body.stmts[body.0 as usize].kind.clone();
        match body_kind {
          StmtKind::While { test, body } => self.compile_while_stmt(test, body, span, Some(*label)),
          StmtKind::DoWhile { test, body } => {
            self.compile_do_while_stmt(test, body, span, Some(*label))
          }
          StmtKind::For {
            init,
            test,
            update,
            body,
          } => self.compile_for_stmt(span, &init, &test, &update, body, Some(*label)),
          StmtKind::ForIn {
            left,
            right,
            body,
            is_for_of,
            await_,
          } => self.compile_for_in_of_stmt(
            stmt.span,
            &left,
            right,
            body,
            is_for_of,
            await_,
            Some(*label),
          ),
          _ => {
            let after_label = self.c_label.bump();
            self.label_stack.push(LabeledTarget {
              label: *label,
              break_target: after_label,
              continue_target: None,
            });
            let res = self.compile_stmt(*body);
            self.label_stack.pop();
            res?;
            self.out.push(Inst::label(after_label));
            Ok(())
          }
        }
      }
      StmtKind::Return(value) => {
        if let Some(value) = value {
          let _ = self.compile_expr(*value)?;
        }
        let target = self.return_label.ok_or_else(|| {
          unsupported_syntax_range(file, stmt.span, "return statement outside function")
        })?;
        self.out.push(Inst::goto(target));
        Ok(())
      }
      StmtKind::Throw(value) => {
        let _ = self.compile_expr(*value)?;
        let target = self.return_label.ok_or_else(|| {
          unsupported_syntax_range(file, stmt.span, "throw statement outside function")
        })?;
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
      } => self.compile_for_stmt(span, init, test, update, *body, None),
      StmtKind::ForIn {
        left,
        right,
        body,
        is_for_of,
        await_,
      } => self.compile_for_in_of_stmt(stmt.span, left, *right, *body, *is_for_of, *await_, None),
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
      StmtKind::While { test, body } => self.compile_while_stmt(*test, *body, span, None),
      StmtKind::DoWhile { test, body } => self.compile_do_while_stmt(*test, *body, span, None),
      StmtKind::Debugger => Ok(()),
      StmtKind::Empty => Ok(()),
      StmtKind::Decl(_) => Ok(()),
      StmtKind::With { .. } => Err(unsupported_syntax_range(
        file,
        stmt.span,
        "with statements introduce dynamic scope and are not supported",
      )),
      other => Err(unsupported_syntax_range(
        file,
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
  compiler.hoist_var_decls();
  for stmt in root_statements(compiler.body) {
    compiler.compile_stmt(stmt)?;
  }
  if let Some(label) = compiler.return_label {
    compiler.out.push(Inst::label(label));
  }
  Ok((compiler.out, compiler.c_label, compiler.c_temp))
}
