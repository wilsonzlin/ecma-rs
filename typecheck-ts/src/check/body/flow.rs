use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use diagnostics::{FileId, Span, TextRange};
use hir_js::{
  ArrayElement, AssignOp, BinaryOp, Body, ExprId, ExprKind, ForHead, ForInit, MemberExpr, NameId,
  NameInterner, ObjectKey, StmtId, StmtKind, UnaryOp,
};
use types_ts_interned::{PredicateParam, RelateCtx, TypeDisplay, TypeId, TypeKind, TypeStore};

use super::super::super::cfg::{BlockId, BlockKind, ControlFlowGraph};
use super::super::super::expr::{resolve_call, resolve_construct};
use super::super::super::flow::{BindingKey, Env, FlowKey, InitState};
use super::super::super::flow_bindings::{FlowBindingId, FlowBindings};
use super::super::super::flow_narrow::{
  and_facts, narrow_by_assignability, narrow_by_discriminant_path, narrow_by_in_check,
  narrow_by_instanceof_rhs, narrow_by_literal, narrow_by_nullish_equality, narrow_by_private_in,
  narrow_by_typeof, narrow_non_nullish, nullish_coalesce_facts, or_facts, truthy_falsy_types,
  Facts, LiteralValue,
};
use super::super::super::instantiate::InstantiationCache;
use super::super::super::overload::CallArgType;
use crate::{codes, BodyId};

use super::super::awaited_type;

use super::super::BodyCheckResult;
use super::bindings::DaTypeAliasMap;
use super::{BindingCollector, BindingMode, FlowBodyChecker};

impl<'a> FlowBodyChecker<'a> {
  pub(crate) fn new(
    body_id: BodyId,
    body: &'a Body,
    names: &'a NameInterner,
    store: Arc<TypeStore>,
    file: FileId,
    initial: &HashMap<NameId, TypeId>,
    flow_bindings: Option<&'a FlowBindings>,
    relate: RelateCtx<'a>,
    ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
    type_arenas: Option<&'a hir_js::TypeArenas>,
    type_aliases: Option<&'a DaTypeAliasMap<'a>>,
    private_in_targets: HashMap<String, TypeId>,
    type_resolver: Option<Arc<dyn crate::check::type_expr::TypeResolver>>,
    no_implicit_any: bool,
  ) -> Self {
    let prim = store.primitive_ids();
    let expr_types = vec![prim.unknown; body.exprs.len()];
    let optional_chain_exec_types = vec![None; body.exprs.len()];
    let mut bindings = BindingCollector::collect(body, flow_bindings);
    let mut pat_types = vec![prim.unknown; body.pats.len()];
    for binding in bindings.param_bindings.iter() {
      let BindingKey::Local { pat, name } = *binding else {
        continue;
      };
      if let Some(ty) = initial.get(&name) {
        if let Some(slot) = pat_types.get_mut(pat.0 as usize) {
          *slot = *ty;
        }
      }
    }
    let mut initial_flow = HashMap::new();
    for (name, ty) in initial.iter() {
      // Seed the type onto the flow binding the body actually uses: params
      // first, then the same-named *body-root* local (module-level
      // `declare const` is a local of the top-level body, not an external;
      // never a shadowed block-scoped local of the same name), then external.
      let id = bindings
        .param_bindings
        .iter()
        .find(|b| matches!(b, BindingKey::Local { name: n, .. } if *n == *name))
        .or_else(|| bindings.root_bindings.get(name))
        .and_then(|b| bindings.flow_binding_for_key(*b))
        .unwrap_or_else(|| bindings.flow_binding_for_external(*name));
      initial_flow.insert(id, *ty);
    }

    let mut returns: Vec<(StmtId, u32)> = body
      .stmts
      .iter()
      .enumerate()
      .filter_map(|(idx, stmt)| {
        if matches!(stmt.kind, StmtKind::Return(_)) {
          Some((StmtId(idx as u32), stmt.span.start))
        } else {
          None
        }
      })
      .collect();
    returns.sort_by_key(|(_, start)| *start);
    let mut return_indices = HashMap::new();
    let mut return_types = Vec::new();
    for (idx, (stmt_id, _)) in returns.into_iter().enumerate() {
      return_indices.insert(stmt_id, idx);
      return_types.push(prim.unknown);
    }

    let expr_spans: Vec<TextRange> = body.exprs.iter().map(|e| e.span).collect();
    let pat_spans: Vec<TextRange> = body.pats.iter().map(|p| p.span).collect();
    let types_at_start = store.type_count();
    Self {
      body_id,
      body,
      names,
      store,
      file,
      relate,
      instantiation_cache: InstantiationCache::default(),
      expr_types,
      optional_chain_exec_types,
      pat_types,
      expr_spans,
      pat_spans,
      diagnostics: Vec::new(),
      reported_unassigned: HashSet::new(),
      da_exempt_bindings: HashSet::new(),
      type_arenas,
      type_aliases,
      return_types,
      return_indices,
      widen_object_literals: true,
      ref_expander,
      type_resolver,
      initial: initial_flow,
      param_bindings: bindings.param_bindings.clone(),
      bindings,
      flow_steps: 0,
      flow_step_limit: Self::DEFAULT_FLOW_STEP_LIMIT,
      budget_diagnostic_emitted: false,
      private_in_targets,
      no_implicit_any,
      types_at_start,
      max_type_growth: Self::DEFAULT_MAX_TYPE_GROWTH,
    }
  }

  pub(crate) fn into_result(self) -> BodyCheckResult {
    BodyCheckResult {
      body: self.body_id,
      expr_types: self.expr_types,
      pat_types: self.pat_types,
      expr_spans: self.expr_spans,
      pat_spans: self.pat_spans,
      diagnostics: self.diagnostics,
      return_types: self.return_types,
      yield_types: Vec::new(),
    }
  }

  fn emit_budget_diagnostic(&mut self) {
    if self.budget_diagnostic_emitted {
      return;
    }
    self.budget_diagnostic_emitted = true;
    let span = self
      .body
      .stmts
      .first()
      .map(|s| Span::new(self.file, s.span))
      .unwrap_or_else(|| Span::new(self.file, TextRange::new(0, 0)));
    self
      .diagnostics
      .push(codes::ENGINE_BUDGET_EXCEEDED.error("engine budget exceeded", span));
  }

  pub(crate) fn run(&mut self) {
    let cfg = ControlFlowGraph::from_body(self.body);
    let mut in_envs: Vec<Option<Env>> = vec![None; cfg.blocks.len()];
    let mut initial_env: Vec<(FlowBindingId, BindingKey, TypeId)> = Vec::new();
    for (id, ty) in self.initial.iter() {
      if let Some(key) = self.bindings.binding_for_flow(*id) {
        initial_env.push((*id, key, *ty));
      }
    }
    for binding in self.param_bindings.iter() {
      if let Some(id) = self.bindings.flow_binding_for_key(*binding) {
        initial_env.push((id, *binding, self.binding_type(*binding)));
      }
    }
    in_envs[cfg.entry.0] = Some(Env::with_initial(&initial_env));
    let mut worklist: VecDeque<BlockId> = VecDeque::new();
    worklist.push_back(cfg.entry);

    while let Some(block_id) = worklist.pop_front() {
      // Cooperative cancel + step budget: CFA merges can fail to stabilize on
      // pathological bodies (e.g. many indexed assigns with unresolved names),
      // growing RSS without ever returning to the outer checker.
      if self.relate.stop_requested() {
        std::panic::panic_any(crate::FatalError::Cancelled);
      }
      if self.relate.budget_exceeded()
        || self.store.type_count().saturating_sub(self.types_at_start) > self.max_type_growth
      {
        self.emit_budget_diagnostic();
        break;
      }
      self.flow_steps += 1;
      if self.flow_steps > self.flow_step_limit {
        self.emit_budget_diagnostic();
        break;
      }
      let env = match in_envs[block_id.0].clone() {
        Some(env) => env,
        None => continue,
      };
      let outgoing = self.process_block(block_id, env, &cfg);
      for (succ, out_env) in outgoing {
        if let Some(existing) = in_envs[succ.0].as_mut() {
          if existing.merge_from(&out_env, &self.store) {
            worklist.push_back(succ);
          }
        } else {
          in_envs[succ.0] = Some(out_env);
          worklist.push_back(succ);
        }
      }
    }
  }

  pub(crate) fn binding_type(&self, binding: BindingKey) -> TypeId {
    let prim = self.store.primitive_ids();
    match binding {
      BindingKey::Local { pat, .. } => self
        .pat_types
        .get(pat.0 as usize)
        .copied()
        .unwrap_or(prim.unknown),
      BindingKey::External(_) => self
        .bindings
        .flow_binding_for_key(binding)
        .and_then(|id| self.initial.get(&id).copied())
        .unwrap_or(prim.unknown),
    }
  }

  pub(crate) fn process_block(
    &mut self,
    block_id: BlockId,
    mut env: Env,
    cfg: &ControlFlowGraph,
  ) -> Vec<(BlockId, Env)> {
    let block = &cfg.blocks[block_id.0];

    match &block.kind {
      BlockKind::ForInit { init } => {
        if let Some(init) = init {
          match init {
            ForInit::Expr(expr_id) => {
              let (_, facts) = self.eval_expr(*expr_id, &mut env);
              env.apply_map(&facts.assertions);
            }
            ForInit::Var(var) => {
              self.bind_var_declarators(var, &mut env);
            }
          }
        }
        return block
          .successors
          .iter()
          .map(|succ| (*succ, env.clone()))
          .collect();
      }
      BlockKind::ForTest { test } => {
        let facts = test
          .map(|t| self.eval_expr(t, &mut env).1)
          .unwrap_or_default();
        let mut then_env = env.clone();
        then_env.apply_facts(&facts);
        let mut else_env = env.clone();
        else_env.apply_falsy(&facts);
        match test.and_then(|t| self.bare_boolean_literal(t)) {
          Some(true) => else_env.set_suppress_da(true),
          Some(false) => then_env.set_suppress_da(true),
          None => {}
        }

        let mut outgoing = Vec::new();
        if let Some(succ) = block.successors.get(0) {
          outgoing.push((*succ, then_env));
        }
        if let Some(succ) = block.successors.get(1) {
          outgoing.push((*succ, else_env));
        }
        return outgoing;
      }
      BlockKind::ForUpdate { update } => {
        if let Some(expr_id) = update {
          let (_, facts) = self.eval_expr(*expr_id, &mut env);
          env.apply_map(&facts.assertions);
        }
        return block
          .successors
          .iter()
          .map(|succ| (*succ, env.clone()))
          .collect();
      }
      BlockKind::DoWhileTest { test } => {
        let facts = self.eval_expr(*test, &mut env).1;
        let mut body_env = env.clone();
        body_env.apply_facts(&facts);
        let mut after_env = env.clone();
        after_env.apply_falsy(&facts);
        match self.bare_boolean_literal(*test) {
          Some(true) => after_env.set_suppress_da(true),
          Some(false) => body_env.set_suppress_da(true),
          None => {}
        }
        let mut outgoing = Vec::new();
        if let Some(succ) = block.successors.get(0) {
          outgoing.push((*succ, body_env));
        }
        if let Some(succ) = block.successors.get(1) {
          outgoing.push((*succ, after_env));
        }
        return outgoing;
      }
      BlockKind::Normal => {}
    }

    if block.stmts.is_empty() {
      return block
        .successors
        .iter()
        .map(|succ| (*succ, env.clone()))
        .collect();
    }

    let mut outgoing = Vec::new();
    for stmt_id in block.stmts.iter() {
      let stmt = &self.body.stmts[stmt_id.0 as usize];
      match &stmt.kind {
        StmtKind::Expr(expr) => {
          let (_, facts) = self.eval_expr(*expr, &mut env);
          env.apply_map(&facts.assertions);
        }
        StmtKind::Return(expr) => {
          let expr_ty = match expr {
            Some(id) => self.eval_expr(*id, &mut env).0,
            None => self.store.primitive_ids().undefined,
          };
          let ty = if self.body.function.as_ref().is_some_and(|f| f.async_) {
            awaited_type(self.store.as_ref(), expr_ty, self.ref_expander)
          } else {
            expr_ty
          };
          self.record_return(*stmt_id, ty);
          // return/throw terminate flow; no successors.
          return Vec::new();
        }
        StmtKind::Throw(expr) => {
          let _ = self.eval_expr(*expr, &mut env);
          return Vec::new();
        }
        StmtKind::Var(decl) => {
          self.bind_var_declarators(decl, &mut env);
        }
        StmtKind::If {
          test,
          consequent: _,
          alternate: _,
        } => {
          let facts = self.eval_expr(*test, &mut env).1;
          let mut then_env = env.clone();
          then_env.apply_facts(&facts);
          let mut else_env = env.clone();
          else_env.apply_falsy(&facts);
          match self.bare_boolean_literal(*test) {
            Some(true) => else_env.set_suppress_da(true),
            Some(false) => then_env.set_suppress_da(true),
            None => {}
          }

          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, then_env));
          }
          if let Some(succ) = block.successors.get(1) {
            outgoing.push((*succ, else_env));
          }
          return outgoing;
        }
        StmtKind::While { test, .. } => {
          let facts = self.eval_expr(*test, &mut env).1;
          let mut body_env = env.clone();
          body_env.apply_facts(&facts);
          let mut after_env = env.clone();
          after_env.apply_falsy(&facts);
          match self.bare_boolean_literal(*test) {
            Some(true) => after_env.set_suppress_da(true),
            Some(false) => body_env.set_suppress_da(true),
            None => {}
          }
          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, body_env));
          }
          if let Some(succ) = block.successors.get(1) {
            outgoing.push((*succ, after_env));
          }
          return outgoing;
        }
        StmtKind::DoWhile { .. } => {
          unreachable!("do...while statements are lowered into synthetic blocks");
        }
        StmtKind::For { .. } => {
          unreachable!("for statements are lowered into synthetic blocks");
        }
        StmtKind::ForIn {
          left,
          right,
          is_for_of,
          ..
        } => {
          let iter_ty = self.eval_expr(*right, &mut env).0;
          let right_ty = if *is_for_of {
            self.for_of_element_type(iter_ty)
          } else {
            self.store.primitive_ids().string
          };
          let mut loop_env = env.clone();
          match left {
            ForHead::Pat(pat) => self.assign_pat(*pat, right_ty, &mut loop_env),
            ForHead::Var(var) => {
              let mode = match var.kind {
                hir_js::VarDeclKind::Const
                | hir_js::VarDeclKind::Using
                | hir_js::VarDeclKind::AwaitUsing => BindingMode::Declare,
                _ => BindingMode::Assign,
              };
              for declarator in var.declarators.iter() {
                self.note_da_exempt_annotation(declarator.pat, declarator.type_annotation);
                self.bind_pat_with_mode(declarator.pat, right_ty, &mut loop_env, mode);
                self.mark_pat_state(declarator.pat, &mut loop_env, InitState::Assigned);
              }
            }
          }
          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, loop_env.clone()));
          }
          if let Some(succ) = block.successors.get(1) {
            outgoing.push((*succ, env.clone()));
          }
          return outgoing;
        }
        StmtKind::Switch {
          discriminant,
          cases,
        } => {
          let discriminant_ty = self.eval_expr(*discriminant, &mut env).0;
          let target = self.switch_discriminant_target(*discriminant, discriminant_ty, &env);
          let default_remaining = target
            .as_ref()
            .and_then(|t| self.switch_default_remaining(t, cases));

          let mut case_envs = Vec::with_capacity(cases.len());
          for case in cases.iter() {
            let mut case_env = env.clone();
            if let Some(test) = case.test {
              let _ = self.eval_expr(test, &mut case_env);
              if let Some(target) = target.as_ref() {
                let _ = self.apply_switch_narrowing(target, test, &mut case_env);
              }
            } else if let (Some(target), Some(default_ty)) = (target.as_ref(), default_remaining) {
              self.apply_switch_result(target, default_ty, &mut case_env);
            }
            case_envs.push(case_env);
          }

          for (idx, case_env) in case_envs.iter().enumerate() {
            if let Some(succ) = block.successors.get(idx) {
              outgoing.push((*succ, case_env.clone()));
              if self.switch_case_falls_through(cases.get(idx)) {
                for later in (idx + 1)..cases.len() {
                  if let Some(later_succ) = block.successors.get(later) {
                    outgoing.push((*later_succ, case_env.clone()));
                  }
                }
              }
            }
          }
          // If there is an implicit default edge (no default case), use the final successor.
          if block.successors.len() > cases.len() {
            if let Some(succ) = block.successors.last() {
              let mut default_env = env.clone();
              if let (Some(target), Some(default_ty)) = (target.as_ref(), default_remaining) {
                self.apply_switch_result(target, default_ty, &mut default_env);
              }
              outgoing.push((*succ, default_env));
            }
          }
          return outgoing;
        }
        StmtKind::Try {
          block: _,
          catch,
          finally_block,
        } => {
          if let Some(succ) = block.successors.get(0) {
            outgoing.push((*succ, env.clone()));
          }
          if let Some((idx, catch_clause)) = catch.as_ref().map(|c| (1, c)) {
            let mut catch_env = env.clone();
            if let Some(param) = catch_clause.param {
              self.bind_pat(param, self.store.primitive_ids().unknown, &mut catch_env);
              self.mark_pat_state(param, &mut catch_env, InitState::Assigned);
            }
            if let Some(succ) = block.successors.get(idx) {
              outgoing.push((*succ, catch_env));
            }
          }
          if let Some(_) = finally_block {
            if let Some(pos) = catch.as_ref().map(|_| 2).or_else(|| Some(1)) {
              if let Some(succ) = block.successors.get(pos) {
                outgoing.push((*succ, env.clone()));
              }
            }
          }
          return outgoing;
        }
        _ => {}
      }
    }

    if outgoing.is_empty() {
      outgoing.extend(block.successors.iter().map(|succ| (*succ, env.clone())));
    }
    outgoing
  }

  pub(crate) fn record_return(&mut self, stmt: StmtId, ty: TypeId) {
    let prim = self.store.primitive_ids();
    if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
      eprintln!(
        "DEBUG record_return {:?} ty {}",
        stmt,
        TypeDisplay::new(&self.store, ty)
      );
    }
    let idx = *self.return_indices.entry(stmt).or_insert_with(|| {
      self.return_types.push(prim.unknown);
      self.return_types.len() - 1
    });
    let slot = self.return_types.get_mut(idx).unwrap();
    if *slot == prim.unknown {
      *slot = ty;
    } else {
      *slot = self.store.union(vec![*slot, ty]);
    }
  }

  pub(crate) fn eval_expr(&mut self, expr_id: ExprId, env: &mut Env) -> (TypeId, Facts) {
    self.eval_expr_inner(expr_id, env, false)
  }

  pub(crate) fn eval_expr_inner(
    &mut self,
    expr_id: ExprId,
    env: &mut Env,
    suppress_uninit: bool,
  ) -> (TypeId, Facts) {
    if self.relate.stop_requested() {
      std::panic::panic_any(crate::FatalError::Cancelled);
    }
    // Count every expression visit — a single CFG block can evaluate an
    // unbounded amount of work without returning to the worklist loop.
    self.flow_steps += 1;
    let type_growth =
      self.store.type_count().saturating_sub(self.types_at_start) > self.max_type_growth;
    if self.relate.budget_exceeded() || self.flow_steps > self.flow_step_limit || type_growth {
      self.emit_budget_diagnostic();
      let prim = self.store.primitive_ids();
      return (prim.unknown, Facts::default());
    }
    let prim = self.store.primitive_ids();
    let expr = &self.body.exprs[expr_id.0 as usize];
    let mut facts = Facts::default();
    let ty = match &expr.kind {
      ExprKind::Ident(name) => {
        let flow_binding = self.bindings.binding_for_expr(expr_id);
        let binding_key = self.bindings.binding_key_for_expr(expr_id);
        let ty = flow_binding
          .and_then(|id| env.get(id).or_else(|| self.initial.get(&id).copied()))
          .unwrap_or(prim.unknown);
        if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
          let name_text = self.hir_name(*name);
          eprintln!(
            "DEBUG ident {name_text} flow {:?} ty {} initial {:?}",
            flow_binding,
            TypeDisplay::new(&self.store, ty),
            flow_binding.and_then(
              |id| self
                .initial
                .get(&id)
                .copied()
                .map(|t| TypeDisplay::new(&self.store, t).to_string())
            )
          );
        }
        if let Some(binding) = binding_key {
          let span = Span {
            file: self.file,
            range: expr.span,
          };
          let name_text = self.hir_name(*name);
          if !suppress_uninit
            && self.bindings.used_before_declaration.contains(&expr_id)
            && self.reported_unassigned.insert(expr_id)
          {
            // TS2448 (TDZ). For for-in/of RHS, tsc reports only this code
            // (`for-of55.ts`); variable self-init may also get TS2454 below.
            self
              .diagnostics
              .push(codes::BLOCK_SCOPED_USED_BEFORE_DECLARATION.error(
                format!("Block-scoped variable '{name_text}' used before its declaration"),
                span,
              ));
            // Re-allow a second insert for optional TS2454 on self-init.
            if !self
              .bindings
              .suppress_use_before_assignment
              .contains(&expr_id)
            {
              self.reported_unassigned.remove(&expr_id);
            }
          }
          if !suppress_uninit
            && !self
              .bindings
              .suppress_use_before_assignment
              .contains(&expr_id)
            && !self.param_bindings.contains(&binding)
            && self.should_report_use_before_assignment(binding, env)
            && self.reported_unassigned.insert(expr_id)
          {
            self.diagnostics.push(
              codes::USE_BEFORE_ASSIGNMENT
                .error(format!("{name_text} is used before being assigned"), span),
            );
          }
        }
        let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
        if let Some(id) = flow_binding {
          let key = FlowKey::root(id);
          facts.truthy.insert(key.clone(), truthy);
          facts.falsy.insert(key, falsy);
        }
        ty
      }
      ExprKind::Literal(lit) => match lit {
        hir_js::Literal::Number(num) => self.store.intern_type(TypeKind::NumberLiteral(
          num.parse::<f64>().unwrap_or(0.0).into(),
        )),
        hir_js::Literal::String(s) => self.store.intern_type(TypeKind::StringLiteral(
          self.store.intern_name(s.lossy.clone()),
        )),
        hir_js::Literal::Boolean(b) => self.store.intern_type(TypeKind::BooleanLiteral(*b)),
        hir_js::Literal::Null => prim.null,
        hir_js::Literal::Undefined => prim.undefined,
        hir_js::Literal::BigInt(v) => self.store.intern_type(TypeKind::BigIntLiteral(
          v.parse::<i128>().unwrap_or(0).into(),
        )),
        // Regex literals are `RegExp` (tsc), falling back to `string` when the
        // global interface is unavailable (e.g. `no-default-lib`).
        hir_js::Literal::Regex(_) => self.regexp_literal_type().unwrap_or(prim.string),
      },
      ExprKind::Unary { op, expr } => match op {
        UnaryOp::Not => {
          let (_, inner_facts) = self.eval_expr(*expr, env);
          facts.truthy = inner_facts.falsy;
          facts.falsy = inner_facts.truthy;
          facts.assertions = inner_facts.assertions;
          prim.boolean
        }
        UnaryOp::Typeof => {
          let _ = self.eval_expr_inner(*expr, env, true);
          prim.string
        }
        UnaryOp::Void => prim.undefined,
        UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => {
          let _ = self.eval_expr(*expr, env);
          prim.number
        }
        _ => prim.unknown,
      },
      ExprKind::Update { expr, .. } => {
        let operand_ty = self.eval_expr(*expr, env).0;
        let result_ty = if self.is_bigint_like(self.base_type(operand_ty)) {
          prim.bigint
        } else {
          prim.number
        };
        self.write_assign_target_expr(*expr, result_ty, env, BindingMode::Assign);
        self.mark_expr_state(*expr, env, InitState::Assigned);
        if let Some(root) = self.assignment_target_root_expr(*expr) {
          self.record_assignment_facts(Some(root), result_ty, &mut facts);
        }
        result_ty
      }
      ExprKind::Binary { op, left, right } => match op {
        BinaryOp::LogicalAnd | BinaryOp::LogicalOr | BinaryOp::NullishCoalescing => {
          self.eval_logical(*op, *left, *right, env, &mut facts)
        }
        BinaryOp::Equality
        | BinaryOp::Inequality
        | BinaryOp::StrictEquality
        | BinaryOp::StrictInequality => {
          self.eval_equality(*op, *left, *right, env, &mut facts);
          prim.boolean
        }
        BinaryOp::LessThan
        | BinaryOp::LessEqual
        | BinaryOp::GreaterThan
        | BinaryOp::GreaterEqual => {
          let _ = self.eval_expr(*left, env);
          let _ = self.eval_expr(*right, env);
          prim.boolean
        }
        BinaryOp::Add => {
          let (l_ty, _) = self.eval_expr(*left, env);
          let (r_ty, _) = self.eval_expr(*right, env);
          match (self.store.type_kind(l_ty), self.store.type_kind(r_ty)) {
            (TypeKind::String | TypeKind::StringLiteral(_), _)
            | (_, TypeKind::String | TypeKind::StringLiteral(_)) => prim.string,
            (
              TypeKind::Number | TypeKind::NumberLiteral(_),
              TypeKind::Number | TypeKind::NumberLiteral(_),
            ) => prim.number,
            _ => self.store.union(vec![l_ty, r_ty]),
          }
        }
        BinaryOp::Subtract
        | BinaryOp::Multiply
        | BinaryOp::Divide
        | BinaryOp::Remainder
        | BinaryOp::Exponent
        | BinaryOp::ShiftLeft
        | BinaryOp::ShiftRight
        | BinaryOp::ShiftRightUnsigned
        | BinaryOp::BitOr
        | BinaryOp::BitAnd
        | BinaryOp::BitXor => {
          let _ = self.eval_expr(*left, env);
          let _ = self.eval_expr(*right, env);
          prim.number
        }
        BinaryOp::Instanceof => {
          let left_expr = *left;
          let left_ty = self.eval_expr(left_expr, env).0;
          let right_ty = self.eval_expr(*right, env).0;
          if let Some(binding) = self.ident_binding(left_expr) {
            let (yes, no) = narrow_by_instanceof_rhs(
              left_ty,
              right_ty,
              &self.store,
              &self.relate,
              self.ref_expander,
            );
            let key = FlowKey::root(binding);
            facts.truthy.insert(key.clone(), yes);
            facts.falsy.insert(key, no);
          }
          prim.boolean
        }
        BinaryOp::In => {
          let right_ty = self.eval_expr(*right, env).0;
          let private_prop = self.private_ident_name(*left);
          let _ = self.eval_expr(*left, env);
          // Flow-aware RHS checks for `k in x` when `x` is a bare identifier:
          // tsc `checkInExpression` uses the *flow type* of the reference, so
          // the AST pass defers to CFA (`u !== null` must silence TS18047).
          let rhs_is_ident = matches!(self.body.exprs[right.0 as usize].kind, ExprKind::Ident(_));
          if rhs_is_ident {
            self.check_in_rhs_flow(*right, right_ty);
          }
          if let (Some(prop), Some(binding)) = (private_prop, self.ident_binding(*right)) {
            if let Some(class_ty) = self.private_in_targets.get(&prop).copied() {
              let (yes, no) = narrow_by_private_in(right_ty, class_ty, &self.store, &self.relate);
              let key = FlowKey::root(binding);
              facts.truthy.insert(key.clone(), yes);
              facts.falsy.insert(key, no);
            }
          } else if let (Some(prop), Some(binding)) =
            (self.literal_prop(*left), self.ident_binding(*right))
          {
            let (yes, no) = narrow_by_in_check(right_ty, &prop, &self.store, self.ref_expander);
            let key = FlowKey::root(binding);
            facts.truthy.insert(key.clone(), yes);
            facts.falsy.insert(key, no);
          }
          prim.boolean
        }
        BinaryOp::Comma => {
          let _ = self.eval_expr(*left, env);
          self.eval_expr(*right, env).0
        }
      },
      ExprKind::Assignment { op, target, value } => {
        let (left_ty, root, _) = self.assignment_target_info(*target, env);
        match op {
          AssignOp::Assign => {
            let val_ty = self.eval_expr(*value, env).0;
            self.assign_pat(*target, val_ty, env);
            let assigned_ty = self.apply_binding_mode(val_ty, BindingMode::Assign);
            self.record_assignment_facts(root, assigned_ty, &mut facts);
            assigned_ty
          }
          AssignOp::AddAssign => {
            let val_ty = self.eval_expr(*value, env).0;
            let result_ty = self.add_assign_result(left_ty, val_ty);
            self.assign_pat(*target, result_ty, env);
            self.record_assignment_facts(root, result_ty, &mut facts);
            result_ty
          }
          AssignOp::LogicalAndAssign => {
            self.logical_and_assign(*target, left_ty, *value, root, env, &mut facts)
          }
          AssignOp::LogicalOrAssign => {
            self.logical_or_assign(*target, left_ty, *value, root, env, &mut facts)
          }
          AssignOp::NullishAssign => {
            self.nullish_assign(*target, left_ty, *value, root, env, &mut facts)
          }
          _ => {
            let val_ty = self.eval_expr(*value, env).0;
            let result_ty = self.numeric_assign_result(left_ty, val_ty);
            self.assign_pat(*target, result_ty, env);
            self.record_assignment_facts(root, result_ty, &mut facts);
            result_ty
          }
        }
      }
      ExprKind::Call(call) => {
        let (ret_ty, chain_short_circuit) = self.eval_call(expr_id, call, env, &mut facts);
        if call.optional || chain_short_circuit {
          self.record_optional_chain_exec_type(expr_id, ret_ty);
        }
        if chain_short_circuit {
          self.store.union(vec![ret_ty, prim.undefined])
        } else {
          ret_ty
        }
      }
      ExprKind::Member(mem) => {
        let obj_ty = self.eval_expr(mem.object, env).0;
        let chain_short_circuit = self.optional_chain_short_circuits(expr_id, env);
        if !mem.optional && !chain_short_circuit {
          let obj_exec_ty = self.expand_ref(obj_ty);
          if self.type_contains_undefined(obj_exec_ty) {
            let span = *self
              .expr_spans
              .get(mem.object.0 as usize)
              .unwrap_or(&TextRange::new(0, 0));
            self.diagnostics.push(codes::POSSIBLY_UNDEFINED.error(
              "identifier is possibly undefined",
              Span::new(self.file, span),
            ));
          }
        }
        let obj_exec_ty = if chain_short_circuit {
          self.optional_chain_exec_type_for(mem.object, obj_ty)
        } else {
          obj_ty
        };

        let (obj_non_nullish, obj_nullish) = if mem.optional {
          narrow_non_nullish(obj_ty, &self.store)
        } else {
          (obj_exec_ty, prim.never)
        };

        if mem.optional && obj_non_nullish == prim.never {
          self.record_optional_chain_exec_type(expr_id, prim.never);
          // Optional chaining (`x?.y`) short-circuits on a nullish base; if
          // the base is always nullish, the whole expression is `undefined`
          // and the property expression is not evaluated.
          prim.undefined
        } else if chain_short_circuit && !mem.optional && obj_exec_ty == prim.never {
          self.record_optional_chain_exec_type(expr_id, prim.never);
          prim.undefined
        } else {
          if let ObjectKey::Computed(expr) = &mem.property {
            let _ = self.eval_expr(*expr, env);
          }
          let obj_ty_for_member = if mem.optional {
            obj_non_nullish
          } else if chain_short_circuit {
            obj_exec_ty
          } else {
            obj_ty
          };
          let prop_ty = match (
            self.ident_binding(mem.object),
            self.member_path_segment(&mem.property),
          ) {
            (Some(binding), Some(segment)) => {
              let key = FlowKey::root(binding).with_segment(segment);
              let derived = self.member_type(obj_ty_for_member, mem);
              match env.get_path(&key) {
                Some(stored) => {
                  let (overlap, _) =
                    narrow_by_assignability(stored, derived, &self.store, &self.relate);
                  if overlap == prim.never {
                    derived
                  } else {
                    overlap
                  }
                }
                None => derived,
              }
            }
            _ => self.member_type(obj_ty_for_member, mem),
          };

          if mem.optional || chain_short_circuit {
            self.record_optional_chain_exec_type(expr_id, prop_ty);
          }
          if chain_short_circuit {
            self.insert_optional_chain_truthy_facts(expr_id, env, &mut facts);
          }

          if mem.optional {
            if let Some(key) = self.flow_key_for_expr(mem.object) {
              if obj_non_nullish != prim.never {
                facts.truthy.insert(key, obj_non_nullish);
              }
            }
            if obj_nullish != prim.never {
              self.store.union(vec![prop_ty, prim.undefined])
            } else {
              prop_ty
            }
          } else if chain_short_circuit {
            self.store.union(vec![prop_ty, prim.undefined])
          } else {
            prop_ty
          }
        }
      }
      ExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => {
        let cond_facts = self.eval_expr(*test, env).1;
        let mut then_env = env.clone();
        then_env.apply_facts(&cond_facts);
        let mut else_env = env.clone();
        else_env.apply_falsy(&cond_facts);
        // Bare `true`/`false`: opposite branch is UnreachableFlow in tsc (no TS2454).
        match self.bare_boolean_literal(*test) {
          Some(true) => else_env.set_suppress_da(true),
          Some(false) => then_env.set_suppress_da(true),
          None => {}
        }
        let then_ty = self.eval_expr(*consequent, &mut then_env).0;
        let else_ty = self.eval_expr(*alternate, &mut else_env).0;
        self.store.union(vec![then_ty, else_ty])
      }
      ExprKind::Array(arr) => {
        let mut elem_tys = Vec::new();
        for elem in arr.elements.iter() {
          match elem {
            ArrayElement::Expr(id) | ArrayElement::Spread(id) => {
              let elem_ty = self.eval_expr(*id, env).0;
              let widened = match self.store.type_kind(elem_ty) {
                TypeKind::NumberLiteral(_) => prim.number,
                TypeKind::StringLiteral(_) => prim.string,
                TypeKind::BooleanLiteral(_) => prim.boolean,
                _ => elem_ty,
              };
              elem_tys.push(widened);
            }
            ArrayElement::Empty => {}
          }
        }
        // Align with AST `array_literal_type` / tsc: empty `[]` is `never[]`
        // under `strictNullChecks`, else `undefined[]` (not `any[]`).
        let elem_ty = if elem_tys.is_empty() {
          if self.store.options().strict_null_checks {
            prim.never
          } else {
            prim.undefined
          }
        } else {
          self.store.union(elem_tys)
        };
        self.store.intern_type(TypeKind::Array {
          ty: elem_ty,
          readonly: false,
        })
      }
      ExprKind::Object(obj) => self.object_type(obj, env),
      ExprKind::FunctionExpr { .. } => prim.unknown,
      ExprKind::ClassExpr { .. } => prim.unknown,
      ExprKind::Template(_) => prim.string,
      // Evaluate the tag (TS2454 DA) and substitutions; leave the tagged-template
      // result type to the AST checker (TemplateStringsArray packing / overloads).
      ExprKind::TaggedTemplate { tag, template } => {
        let _ = self.eval_expr(*tag, env);
        for span in template.spans.iter() {
          let _ = self.eval_expr(span.expr, env);
        }
        prim.unknown
      }
      ExprKind::Await { expr } => {
        let inner = self.eval_expr(*expr, env).0;
        awaited_type(self.store.as_ref(), inner, self.ref_expander)
      }
      ExprKind::Yield { expr, .. } => expr
        .map(|id| self.eval_expr(id, env).0)
        .unwrap_or(prim.undefined),
      ExprKind::TypeAssertion {
        expr,
        const_assertion,
        ..
      } => {
        let inner = self.eval_expr(*expr, env).0;
        if *const_assertion {
          inner
        } else {
          // The flow checker intentionally does not attempt to fully lower the
          // type annotation (it would require access to declaration/type arenas).
          // However, it must not treat `x as number` / `x as string` as a
          // narrowing operation by propagating literal types through the graph.
          //
          // Widen primitive literals so that `1 as number` behaves like `number`
          // during flow-based type recomputation, keeping results aligned with
          // the main checker (and `tsc`).
          match self.store.type_kind(inner) {
            TypeKind::NumberLiteral(_) => prim.number,
            TypeKind::StringLiteral(_) | TypeKind::TemplateLiteral(_) => prim.string,
            TypeKind::BooleanLiteral(_) => prim.boolean,
            _ => inner,
          }
        }
      }
      ExprKind::NonNull {
        expr,
        operand_parenthesized,
      } => {
        // tsc `assumeInitialized` when `node.parent.kind === NonNullExpression`.
        // A ParenthesizedExpression between the use and `!` (`(x)!`) must NOT
        // suppress TS2454; bare `x!` / `(x!)` still do.
        let suppress_da = !*operand_parenthesized;
        let (inner_ty, _) = self.eval_expr_inner(*expr, env, suppress_da);
        let (_, nonnull) = narrow_by_nullish_equality(
          inner_ty,
          BinaryOp::Equality,
          &LiteralValue::Null,
          &self.store,
        );
        nonnull
      }
      ExprKind::Satisfies { expr, .. } => {
        let prev = self.widen_object_literals;
        self.widen_object_literals = false;
        let ty = self.eval_expr(*expr, env).0;
        self.widen_object_literals = prev;
        ty
      }
      // Instantiation type args are applied in the AST `check_expr` path; flow
      // only needs the value-side structure (transparent wrapper).
      ExprKind::Instantiation { expr, .. } => self.eval_expr(*expr, env).0,
      ExprKind::Jsx(elem) => {
        for attr in elem.attributes.iter() {
          match attr {
            hir_js::JsxAttr::Named { value, .. } => {
              if let Some(value) = value {
                match value {
                  hir_js::JsxAttrValue::Expression(container) => {
                    if let Some(expr) = container.expr {
                      let _ = self.eval_expr(expr, env);
                    }
                  }
                  hir_js::JsxAttrValue::Element(expr) => {
                    let _ = self.eval_expr(*expr, env);
                  }
                  hir_js::JsxAttrValue::Text(_) => {}
                }
              }
            }
            hir_js::JsxAttr::Spread { expr } => {
              let _ = self.eval_expr(*expr, env);
            }
          }
        }
        for child in elem.children.iter() {
          match child {
            hir_js::JsxChild::Text(_) => {}
            hir_js::JsxChild::Expr(container) => {
              if let Some(expr) = container.expr {
                let _ = self.eval_expr(expr, env);
              }
            }
            hir_js::JsxChild::Element(expr) => {
              let _ = self.eval_expr(*expr, env);
            }
          }
        }
        prim.unknown
      }
      _ => prim.unknown,
    };

    let slot = &mut self.expr_types[expr_id.0 as usize];
    *slot = if *slot == prim.unknown {
      ty
    } else {
      self.store.union(vec![*slot, ty])
    };
    (ty, facts)
  }

  pub(crate) fn eval_logical(
    &mut self,
    op: BinaryOp,
    left: ExprId,
    right: ExprId,
    env: &mut Env,
    out: &mut Facts,
  ) -> TypeId {
    let (left_ty, mut left_facts) = self.eval_expr(left, env);
    match op {
      BinaryOp::LogicalAnd => {
        let mut right_env = env.clone();
        right_env.apply_facts(&left_facts);
        // `false && rhs`: rhs is unreachable for TS2454 (bare FalseKeyword only).
        if self.bare_boolean_literal(left) == Some(false) {
          right_env.set_suppress_da(true);
        }
        let (right_ty, right_facts) = self.eval_expr(right, &mut right_env);
        *out = and_facts(left_facts, right_facts, &self.store);
        self.store.union(vec![left_ty, right_ty])
      }
      BinaryOp::LogicalOr => {
        let mut right_env = env.clone();
        right_env.apply_falsy(&left_facts);
        // `true || rhs`: rhs is unreachable for TS2454 (bare TrueKeyword only).
        if self.bare_boolean_literal(left) == Some(true) {
          right_env.set_suppress_da(true);
        }
        let (right_ty, right_facts) = self.eval_expr(right, &mut right_env);
        let mut combined = or_facts(left_facts.clone(), right_facts, &self.store);
        for (key, ty) in combined.truthy.iter_mut() {
          if !left_facts.truthy.contains_key(key) {
            if let Some(orig) = env
              .get(key.root)
              .or_else(|| self.initial.get(&key.root).copied())
            {
              *ty = self.store.union(vec![*ty, orig]);
            }
          }
        }
        *out = combined;
        self.store.union(vec![left_ty, right_ty])
      }
      BinaryOp::NullishCoalescing => {
        let prim = self.store.primitive_ids();
        let (nonnullish, nullish) = narrow_non_nullish(left_ty, &self.store);

        // `tsc` currently does not propagate narrowing derived from optional chaining across
        // nullish coalescing (`x?.y ?? z`). This keeps our flow facts aligned with the baseline
        // diagnostics (notably TS18048 for `x?.y ?? false`).
        let mut optional_bases = Vec::new();
        self.optional_chain_base_keys(left, &mut optional_bases);
        for base in optional_bases {
          left_facts.truthy.remove(&base);
          left_facts.falsy.remove(&base);
        }

        let mut right_env = env.clone();
        right_env.apply_map(&left_facts.assertions);

        let mut left_nullish = HashMap::new();
        if let Some(binding) = self.nullish_coalesce_binding(left) {
          let key = FlowKey::root(binding);
          left_nullish.insert(key.clone(), nullish);
          right_env.set(binding, nullish);
        }

        let (right_ty, right_facts) = self.eval_expr(right, &mut right_env);
        if nullish == prim.never {
          // The RHS is unreachable at runtime; still type-check it, but do not
          // incorporate its narrowing facts into the current environment.
          *out = left_facts;
          nonnullish
        } else {
          *out = nullish_coalesce_facts(left_facts, right_facts, left_nullish, &self.store);
          self.store.union(vec![nonnullish, right_ty])
        }
      }
      _ => {
        let right_ty = self.eval_expr(right, env).0;
        self.store.union(vec![left_ty, right_ty])
      }
    }
  }

  pub(crate) fn eval_equality(
    &mut self,
    op: BinaryOp,
    left: ExprId,
    right: ExprId,
    env: &mut Env,
    out: &mut Facts,
  ) {
    let left_ty = self.eval_expr(left, env).0;
    let right_ty = self.eval_expr(right, env).0;
    let negate = matches!(op, BinaryOp::Inequality | BinaryOp::StrictInequality);

    pub(crate) fn apply_narrowing(
      out: &mut Facts,
      negate: bool,
      target: FlowBindingId,
      yes: TypeId,
      no: TypeId,
    ) {
      let key = FlowKey::root(target);
      if negate {
        out.truthy.insert(key.clone(), no);
        out.falsy.insert(key, yes);
      } else {
        out.truthy.insert(key.clone(), yes);
        out.falsy.insert(key, no);
      }
    }

    let mut apply_literal_narrow =
      |target: FlowBindingId, target_ty: TypeId, lit: &LiteralValue| {
        if matches!(lit, LiteralValue::Null | LiteralValue::Undefined) {
          let (yes, no) = narrow_by_nullish_equality(target_ty, op, lit, &self.store);
          apply_narrowing(out, negate, target, yes, no);
        } else {
          let (yes, no) = narrow_by_literal(target_ty, lit, &self.store);
          apply_narrowing(out, negate, target, yes, no);
        }
      };

    if let Some(target) = self.ident_binding(left) {
      if let Some(lit) = self.literal_value(right) {
        apply_literal_narrow(target, left_ty, &lit);
        return;
      }
    }
    if let Some(target) = self.ident_binding(right) {
      if let Some(lit) = self.literal_value(left) {
        apply_literal_narrow(target, right_ty, &lit);
        return;
      }
    }

    if let Some((target, path, object_expr, optional_bases)) = self.discriminant_member(left) {
      if let Some(lit) = self.literal_value(right) {
        self.optional_chain_equality_facts(left, right, right_ty, op, env, out);
        self.optional_chain_equality_facts(right, left, left_ty, op, env, out);

        let target_ty = env
          .get(target)
          .or_else(|| self.initial.get(&target).copied())
          .unwrap_or_else(|| self.expr_types[object_expr.0 as usize]);
        let has_nested_optional = !optional_bases.is_empty();
        if let Some(prop_ty) = self.object_prop_type_path(target_ty, &path) {
          let (prop_yes, prop_no) = match lit {
            LiteralValue::Null | LiteralValue::Undefined => {
              narrow_by_nullish_equality(prop_ty, op, &lit, &self.store)
            }
            _ => narrow_by_literal(prop_ty, &lit, &self.store),
          };
          let mut flow_key = FlowKey::root(target);
          for seg in path.iter() {
            flow_key = flow_key.with_segment(seg.clone());
          }
          if has_nested_optional && !matches!(lit, LiteralValue::Null | LiteralValue::Undefined) {
            if negate {
              out.falsy.insert(flow_key, prop_yes);
            } else {
              out.truthy.insert(flow_key, prop_yes);
            }
          } else if negate {
            out.truthy.insert(flow_key.clone(), prop_no);
            out.falsy.insert(flow_key, prop_yes);
          } else {
            out.truthy.insert(flow_key.clone(), prop_yes);
            out.falsy.insert(flow_key, prop_no);
          }
        }
        match lit {
          LiteralValue::Null | LiteralValue::Undefined => {
            if let Some(prop_ty) = self.object_prop_type_path(target_ty, &path) {
              let (yes_prop, no_prop) = narrow_by_nullish_equality(prop_ty, op, &lit, &self.store);
              let yes = self.narrow_object_by_path_assignability(target_ty, &path, yes_prop);
              let no = self.narrow_object_by_path_assignability(target_ty, &path, no_prop);
              apply_narrowing(out, negate, target, yes, no);
              return;
            }
          }
          _ => {
            let (yes, no) =
              narrow_by_discriminant_path(target_ty, &path, &lit, &self.store, self.ref_expander);
            if has_nested_optional {
              let key = FlowKey::root(target);
              if negate {
                out.falsy.insert(key, yes);
              } else {
                out.truthy.insert(key, yes);
              }
            } else {
              apply_narrowing(out, negate, target, yes, no);
            }
            return;
          }
        }
      }
    }
    if let Some((target, path, object_expr, optional_bases)) = self.discriminant_member(right) {
      if let Some(lit) = self.literal_value(left) {
        self.optional_chain_equality_facts(left, right, right_ty, op, env, out);
        self.optional_chain_equality_facts(right, left, left_ty, op, env, out);

        let target_ty = env
          .get(target)
          .or_else(|| self.initial.get(&target).copied())
          .unwrap_or_else(|| self.expr_types[object_expr.0 as usize]);
        let has_nested_optional = !optional_bases.is_empty();
        if let Some(prop_ty) = self.object_prop_type_path(target_ty, &path) {
          let (prop_yes, prop_no) = match lit {
            LiteralValue::Null | LiteralValue::Undefined => {
              narrow_by_nullish_equality(prop_ty, op, &lit, &self.store)
            }
            _ => narrow_by_literal(prop_ty, &lit, &self.store),
          };
          let mut flow_key = FlowKey::root(target);
          for seg in path.iter() {
            flow_key = flow_key.with_segment(seg.clone());
          }
          if has_nested_optional && !matches!(lit, LiteralValue::Null | LiteralValue::Undefined) {
            if negate {
              out.falsy.insert(flow_key, prop_yes);
            } else {
              out.truthy.insert(flow_key, prop_yes);
            }
          } else if negate {
            out.truthy.insert(flow_key.clone(), prop_no);
            out.falsy.insert(flow_key, prop_yes);
          } else {
            out.truthy.insert(flow_key.clone(), prop_yes);
            out.falsy.insert(flow_key, prop_no);
          }
        }
        match lit {
          LiteralValue::Null | LiteralValue::Undefined => {
            if let Some(prop_ty) = self.object_prop_type_path(target_ty, &path) {
              let (yes_prop, no_prop) = narrow_by_nullish_equality(prop_ty, op, &lit, &self.store);
              let yes = self.narrow_object_by_path_assignability(target_ty, &path, yes_prop);
              let no = self.narrow_object_by_path_assignability(target_ty, &path, no_prop);
              apply_narrowing(out, negate, target, yes, no);
              return;
            }
          }
          _ => {
            let (yes, no) =
              narrow_by_discriminant_path(target_ty, &path, &lit, &self.store, self.ref_expander);
            if has_nested_optional {
              let key = FlowKey::root(target);
              if negate {
                out.falsy.insert(key, yes);
              } else {
                out.truthy.insert(key, yes);
              }
            } else {
              apply_narrowing(out, negate, target, yes, no);
            }
            return;
          }
        }
      }
    }

    if !negate {
      if let (Some(left_ref), Some(right_ref)) = (
        self.reference_from_expr(left, left_ty),
        self.reference_from_expr(right, right_ty),
      ) {
        let left_yes = self.narrow_reference_against(&left_ref, right_ref.value_ty());
        let right_yes = self.narrow_reference_against(&right_ref, left_ref.value_ty());
        if left_ref.target() == right_ref.target() {
          let combined = self.store.intersection(vec![left_yes, right_yes]);
          apply_narrowing(
            out,
            negate,
            left_ref.target(),
            combined,
            left_ref.target_ty(),
          );
        } else {
          apply_narrowing(
            out,
            negate,
            left_ref.target(),
            left_yes,
            left_ref.target_ty(),
          );
          apply_narrowing(
            out,
            negate,
            right_ref.target(),
            right_yes,
            right_ref.target_ty(),
          );
        }
        return;
      }
    }

    if let Some((target, target_ty, lit)) = self.typeof_comparison(left, right) {
      let (yes, no) = narrow_by_typeof(target_ty, &lit, &self.store, self.ref_expander);
      apply_narrowing(out, negate, target, yes, no);
    }

    self.optional_chain_equality_facts(left, right, right_ty, op, env, out);
    self.optional_chain_equality_facts(right, left, left_ty, op, env, out);
  }

  pub(crate) fn eval_call(
    &mut self,
    expr_id: ExprId,
    call: &hir_js::CallExpr,
    env: &mut Env,
    out: &mut Facts,
  ) -> (TypeId, bool) {
    let prim = self.store.primitive_ids();
    let _ = self.eval_expr(call.callee, env);
    let callee_base = self.expand_ref(self.expr_types[call.callee.0 as usize]);
    self.expr_types[call.callee.0 as usize] = callee_base;

    let chain_short_circuit = self.optional_chain_short_circuits(expr_id, env);
    if chain_short_circuit {
      self.insert_optional_chain_truthy_facts(expr_id, env, out);
    } else if call.optional {
      if let Some(key) = self.flow_key_for_expr(call.callee) {
        let (non_nullish, _) = narrow_non_nullish(self.flow_key_type(env, &key), &self.store);
        if non_nullish != prim.never {
          out.truthy.insert(key, non_nullish);
        }
      }
    }
    let callee_exec_ty = if chain_short_circuit {
      self.optional_chain_exec_type_for(call.callee, callee_base)
    } else {
      callee_base
    };
    if chain_short_circuit && callee_exec_ty == prim.never {
      return (prim.never, chain_short_circuit);
    }

    let (callee_non_nullish, _) = if call.optional {
      narrow_non_nullish(callee_exec_ty, &self.store)
    } else {
      (callee_exec_ty, prim.never)
    };
    if call.optional && callee_non_nullish == prim.never {
      return (prim.never, chain_short_circuit);
    }

    let mut arg_bases: Vec<CallArgType> = Vec::new();
    for arg in call.args.iter() {
      let _ = self.eval_expr(arg.expr, env);
      let expanded = self.expand_ref(self.expr_types[arg.expr.0 as usize]);
      self.expr_types[arg.expr.0 as usize] = expanded;
      let arg_span = self
        .expr_spans
        .get(arg.expr.0 as usize)
        .copied()
        .map(|range| Span::new(self.file, range));
      let base = if arg.spread {
        CallArgType::spread(expanded)
      } else {
        CallArgType::new(expanded)
      };
      arg_bases.push(match arg_span {
        Some(span) => base.with_span(span),
        None => base,
      });
    }

    let this_arg = match &self.body.exprs[call.callee.0 as usize].kind {
      ExprKind::Member(MemberExpr { object, .. }) => {
        let mut ty = self.expr_types[object.0 as usize];
        if chain_short_circuit {
          ty = self.optional_chain_exec_type_for(*object, ty);
        }
        Some(ty)
      }
      _ => None,
    };

    let span = Span::new(
      self.file,
      *self
        .expr_spans
        .get(expr_id.0 as usize)
        .unwrap_or(&TextRange::new(0, 0)),
    );
    let resolution = if call.is_new {
      resolve_construct(
        &self.store,
        &self.relate,
        &self.instantiation_cache,
        callee_non_nullish,
        &arg_bases,
        None,
        None,
        None,
        span,
        self.ref_expander,
      )
    } else {
      resolve_call(
        &self.store,
        &self.relate,
        &self.instantiation_cache,
        callee_non_nullish,
        &arg_bases,
        None,
        this_arg,
        None,
        span,
        self.ref_expander,
      )
    };
    if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
      eprintln!(
        "DEBUG call resolution sig {:?} ret {}",
        resolution.signature,
        TypeDisplay::new(&self.store, resolution.return_type)
      );
    }

    let mut ret_ty = resolution.return_type;
    if !call.is_new {
      if let Some(sig_id) = resolution.signature {
        let sig = self.store.signature(sig_id);
        if let TypeKind::Predicate {
          asserted,
          asserts,
          parameter,
        } = self.store.type_kind(sig.ret)
        {
          if let Some(asserted) = asserted {
            match parameter.unwrap_or(PredicateParam::Param(0)) {
              PredicateParam::Param(target_idx) => {
                let target_idx = target_idx as usize;
                if let Some(arg_expr) = call.args.get(target_idx).map(|a| a.expr) {
                  if let Some(binding) = self.ident_binding(arg_expr) {
                    let arg_ty = arg_bases
                      .get(target_idx)
                      .map(|arg| arg.ty)
                      .unwrap_or(prim.unknown);
                    let (yes, no) =
                      narrow_by_assignability(arg_ty, asserted, &self.store, &self.relate);
                    if asserts {
                      if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
                        eprintln!(
                          "DEBUG asserts narrowing arg {} to {} (no {}) in file {:?}",
                          TypeDisplay::new(&self.store, arg_ty),
                          TypeDisplay::new(&self.store, yes),
                          TypeDisplay::new(&self.store, no),
                          self.file
                        );
                      }
                      env.set(binding, yes);
                      out.assertions.insert(FlowKey::root(binding), yes);
                    } else {
                      let key = FlowKey::root(binding);
                      out.truthy.insert(key.clone(), yes);
                      out.falsy.insert(key, no);
                      if std::env::var("DEBUG_ASSERT_NARROW").is_ok() {
                        eprintln!(
                          "DEBUG predicate narrowing arg {} to {} (no {}) in file {:?}",
                          TypeDisplay::new(&self.store, arg_ty),
                          TypeDisplay::new(&self.store, yes),
                          TypeDisplay::new(&self.store, no),
                          self.file
                        );
                      }
                    }
                  }
                }
              }
              PredicateParam::This => {
                if let Some(this_expr) = match &self.body.exprs[call.callee.0 as usize].kind {
                  ExprKind::Member(MemberExpr { object, .. }) => Some(*object),
                  _ => None,
                } {
                  if let Some(binding) = self.ident_binding(this_expr) {
                    let arg_ty = this_arg.unwrap_or(prim.unknown);
                    let (yes, no) =
                      narrow_by_assignability(arg_ty, asserted, &self.store, &self.relate);
                    if asserts {
                      env.set(binding, yes);
                      out.assertions.insert(FlowKey::root(binding), yes);
                    } else {
                      let key = FlowKey::root(binding);
                      out.truthy.insert(key.clone(), yes);
                      out.falsy.insert(key, no);
                    }
                  }
                }
              }
            }
          }
          ret_ty = if asserts {
            prim.undefined
          } else {
            prim.boolean
          };
        } else {
          ret_ty = sig.ret;
        }
      }
    }

    (ret_ty, chain_short_circuit)
  }
}
