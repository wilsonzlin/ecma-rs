use crate::flow::cfg::BasicBlock;
use crate::flow::cfg::BlockId;
use crate::flow::cfg::ControlFlowGraph;
use crate::flow::cfg::Terminator;
use crate::hir::*;
use crate::types::SimpleType;
use crate::types::Type;
use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub struct FlowResult {
  pub expr_types: Vec<Type>,
}

#[derive(Clone, Debug)]
struct TypeEnv {
  vars: Vec<Type>,
  unreachable: bool,
}

impl TypeEnv {
  fn new_from_body(body: &Body) -> Self {
    Self {
      vars: body.vars.iter().map(|v| v.declared_type.clone()).collect(),
      unreachable: false,
    }
  }

  fn for_unreachable(vars_len: usize) -> Self {
    Self {
      vars: vec![Type::never(); vars_len],
      unreachable: true,
    }
  }

  fn var(&self, var: VarId) -> &Type {
    &self.vars[var.idx()]
  }

  fn set_var(&mut self, var: VarId, ty: Type) {
    self.vars[var.idx()] = ty;
  }

  fn narrow_var(&mut self, var: VarId, ty: Type) {
    let new_ty = self.vars[var.idx()].intersect(&ty);
    self.vars[var.idx()] = new_ty;
  }

  fn exclude_var(&mut self, var: VarId, ty: Type) {
    let new_ty = self.vars[var.idx()].exclude(&ty);
    self.vars[var.idx()] = new_ty;
  }

  fn merge_with(&self, other: &TypeEnv) -> (TypeEnv, bool) {
    if self.unreachable {
      return (other.clone(), !other.unreachable);
    }
    if other.unreachable {
      return (self.clone(), false);
    }

    let mut changed = false;
    let mut vars = Vec::with_capacity(self.vars.len());
    for (a, b) in self.vars.iter().zip(other.vars.iter()) {
      let merged = a.union(b);
      if &merged != a {
        changed = true;
      }
      vars.push(merged);
    }
    (
      TypeEnv {
        vars,
        unreachable: false,
      },
      changed,
    )
  }
}

pub fn solve_flow(body: &Body, cfg: &ControlFlowGraph) -> FlowResult {
  let mut expr_types = vec![Type::never(); body.exprs.len()];
  let mut in_states: Vec<Option<TypeEnv>> = vec![None; cfg.blocks.len()];
  let mut worklist = VecDeque::new();

  let entry_env = TypeEnv::new_from_body(body);
  in_states[cfg.entry] = Some(entry_env);
  worklist.push_back(cfg.entry);

  while let Some(block_id) = worklist.pop_front() {
    let in_env = match &in_states[block_id] {
      Some(env) => env.clone(),
      None => continue,
    };
    let block = &cfg.blocks[block_id];
    let out_env = evaluate_block(block, &in_env, body, &mut expr_types);

    match block.terminator {
      Terminator::Goto(target) => {
        push_state(target, out_env, &mut in_states, &mut worklist);
      }
      Terminator::If {
        cond,
        then_bb,
        else_bb,
      } => {
        let (then_env, else_env) = apply_condition(cond, &out_env, body, &mut expr_types);
        push_state(then_bb, then_env, &mut in_states, &mut worklist);
        push_state(else_bb, else_env, &mut in_states, &mut worklist);
      }
      Terminator::Return | Terminator::End => {}
    }
  }

  FlowResult { expr_types }
}

fn push_state(
  target: BlockId,
  env: TypeEnv,
  states: &mut [Option<TypeEnv>],
  worklist: &mut VecDeque<BlockId>,
) {
  if let Some(existing) = &states[target] {
    let (merged, changed) = existing.merge_with(&env);
    if changed {
      states[target] = Some(merged);
      worklist.push_back(target);
    }
  } else {
    states[target] = Some(env);
    worklist.push_back(target);
  }
}

fn evaluate_block(
  block: &BasicBlock,
  in_env: &TypeEnv,
  body: &Body,
  expr_types: &mut [Type],
) -> TypeEnv {
  let mut env = in_env.clone();
  if env.unreachable {
    return env;
  }

  for stmt_id in &block.stmts {
    let stmt = &body.stmts[stmt_id.idx()];
    match &stmt.kind {
      StmtKind::Var { id, init } => {
        if let Some(expr) = init {
          let init_ty = eval_expr(*expr, &env, body, expr_types);
          let declared = body.vars[id.idx()].declared_type.clone();
          env.set_var(*id, declared.union(&init_ty));
        }
      }
      StmtKind::Expr(expr) => {
        let _ = eval_expr(*expr, &env, body, expr_types);
        // Assertion functions affect environment.
        if let Expr::Call { callee, args } = &body.exprs[expr.idx()] {
          if let Some(arg) = args.first() {
            if let Expr::Var(var) = body.exprs[arg.idx()] {
              match &body.functions[callee.idx()].ret {
                FunctionReturn::Asserts { narrows, to } => {
                  if *narrows == var {
                    env.narrow_var(var, to.clone());
                  }
                }
                FunctionReturn::AssertsTruthy { narrows } => {
                  if *narrows == var {
                    let truthy = env.var(var).truthy_part();
                    env.set_var(var, truthy);
                  }
                }
                FunctionReturn::TypeGuard { .. } | FunctionReturn::Value(_) => {}
              }
            }
          }
        }
      }
      StmtKind::Return(expr) => {
        if let Some(expr) = expr {
          let _ = eval_expr(*expr, &env, body, expr_types);
        }
        env.unreachable = true;
        break;
      }
      // Control-flow statements are lowered into separate blocks by CFG builder.
      StmtKind::Block(_) | StmtKind::If { .. } | StmtKind::While { .. } | StmtKind::Try { .. } => {}
    }
  }

  env
}

fn record_expr_type(expr_id: ExprId, ty: Type, expr_types: &mut [Type]) {
  let slot = &mut expr_types[expr_id.idx()];
  let merged = slot.union(&ty);
  *slot = merged;
}

fn eval_expr(expr_id: ExprId, env: &TypeEnv, body: &Body, expr_types: &mut [Type]) -> Type {
  let ty = match &body.exprs[expr_id.idx()] {
    Expr::Var(v) => env.var(*v).clone(),
    Expr::Literal(lit) => match lit {
      Literal::Boolean(v) => Type::boolean_literal(*v),
      Literal::Number(v) => Type::number_literal(*v),
      Literal::String(v) => Type::string_literal(v.clone()),
      Literal::Null => Type::null(),
      Literal::Undefined => Type::undefined(),
    },
    Expr::Unary(UnaryOp::Not, inner) => {
      let _ = eval_expr(*inner, env, body, expr_types);
      Type::boolean()
    }
    Expr::Unary(UnaryOp::Typeof, inner) => {
      let inner_ty = eval_expr(*inner, env, body, expr_types);
      let mut tags = Type::never();
      for atom in inner_ty.atoms() {
        let tag = match atom {
          SimpleType::String | SimpleType::StringLit(_) => Some("string"),
          SimpleType::Number | SimpleType::NumberLit(_) => Some("number"),
          SimpleType::Boolean | SimpleType::BooleanLit(_) => Some("boolean"),
          SimpleType::Undefined => Some("undefined"),
          SimpleType::Null | SimpleType::Object(_) | SimpleType::Class(_) => Some("object"),
          SimpleType::Function => Some("function"),
          _ => None,
        };
        if let Some(tag) = tag {
          tags = tags.union(&Type::string_literal(tag));
        }
      }
      if tags.is_never() {
        Type::string()
      } else {
        tags
      }
    }
    Expr::Binary(op, left, right) => {
      let _ = eval_expr(*left, env, body, expr_types);
      let _ = eval_expr(*right, env, body, expr_types);
      match op {
        BinaryOp::Equals | BinaryOp::StrictEquals | BinaryOp::InstanceOf => Type::boolean(),
      }
    }
    Expr::Logical(op, left, right) => {
      let left_ty = eval_expr(*left, env, body, expr_types);
      let right_ty = eval_expr(*right, env, body, expr_types);
      match op {
        LogicalOp::And => left_ty.falsy_part().union(&right_ty),
        LogicalOp::Or => left_ty.truthy_part().union(&right_ty),
      }
    }
    Expr::Conditional {
      cond,
      when_true,
      when_false,
    } => {
      let _ = eval_expr(*cond, env, body, expr_types);
      let t_ty = eval_expr(*when_true, env, body, expr_types);
      let f_ty = eval_expr(*when_false, env, body, expr_types);
      t_ty.union(&f_ty)
    }
    Expr::Call { callee, .. } => match &body.functions[callee.idx()].ret {
      FunctionReturn::Value(ty) => ty.clone(),
      FunctionReturn::TypeGuard { .. } => Type::boolean(),
      FunctionReturn::Asserts { .. } | FunctionReturn::AssertsTruthy { .. } => Type::boolean(),
    },
    Expr::Property { obj, name } => {
      let obj_ty = eval_expr(*obj, env, body, expr_types);
      obj_ty.property_type(name)
    }
    Expr::In { .. } => Type::boolean(),
  };

  record_expr_type(expr_id, ty.clone(), expr_types);
  ty
}

fn apply_condition(
  expr_id: ExprId,
  env: &TypeEnv,
  body: &Body,
  expr_types: &mut [Type],
) -> (TypeEnv, TypeEnv) {
  match &body.exprs[expr_id.idx()] {
    Expr::Unary(UnaryOp::Not, inner) => {
      let (t, f) = apply_condition(*inner, env, body, expr_types);
      (f, t)
    }
    Expr::Logical(LogicalOp::And, left, right) => {
      let (left_t, left_f) = apply_condition(*left, env, body, expr_types);
      let (right_t, right_f) = apply_condition(*right, &left_t, body, expr_types);
      let false_env = merge_envs(left_f, right_f);
      (right_t, false_env)
    }
    Expr::Logical(LogicalOp::Or, left, right) => {
      let (left_t, left_f) = apply_condition(*left, env, body, expr_types);
      let (right_t, right_f) = apply_condition(*right, &left_f, body, expr_types);
      let true_env = merge_envs(left_t, right_t);
      (true_env, right_f)
    }
    Expr::Conditional {
      cond,
      when_true,
      when_false,
    } => {
      let (cond_t, cond_f) = apply_condition(*cond, env, body, expr_types);
      let (true_branch_t, true_branch_f) = apply_condition(*when_true, &cond_t, body, expr_types);
      let (false_branch_t, false_branch_f) =
        apply_condition(*when_false, &cond_f, body, expr_types);

      let merged_true = merge_envs(true_branch_t, false_branch_t);
      let merged_false = merge_envs(true_branch_f, false_branch_f);
      (merged_true, merged_false)
    }
    Expr::Binary(op, left, right) => match op {
      BinaryOp::Equals | BinaryOp::StrictEquals => {
        let left_expr = &body.exprs[left.idx()];
        let right_expr = &body.exprs[right.idx()];
        match (left_expr, right_expr) {
          // typeof x === "string"
          (Expr::Unary(UnaryOp::Typeof, inner), Expr::Literal(Literal::String(tag))) => {
            apply_typeof_compare(*inner, tag, env, body, expr_types)
          }
          (Expr::Literal(Literal::String(tag)), Expr::Unary(UnaryOp::Typeof, inner)) => {
            apply_typeof_compare(*inner, tag, env, body, expr_types)
          }
          // property discriminant check
          (Expr::Property { obj, name }, Expr::Literal(Literal::String(value))) => {
            apply_discriminant(*obj, name, value, env, body, expr_types)
          }
          (Expr::Literal(Literal::String(value)), Expr::Property { obj, name }) => {
            apply_discriminant(*obj, name, value, env, body, expr_types)
          }
          _ => {
            let _ = eval_expr(expr_id, env, body, expr_types);
            (env.clone(), env.clone())
          }
        }
      }
      BinaryOp::InstanceOf => {
        let left_expr = &body.exprs[left.idx()];
        if let (Expr::Var(var), Expr::Literal(Literal::String(class))) =
          (left_expr, &body.exprs[right.idx()])
        {
          apply_instanceof(*var, class, env)
        } else {
          let _ = eval_expr(expr_id, env, body, expr_types);
          (env.clone(), env.clone())
        }
      }
    },
    Expr::Var(v) => {
      let mut t_env = env.clone();
      let mut f_env = env.clone();
      t_env.set_var(*v, env.var(*v).truthy_part());
      f_env.set_var(*v, env.var(*v).falsy_part());
      (t_env, f_env)
    }
    Expr::Literal(lit) => {
      let val_truthy = match lit {
        Literal::Boolean(v) => *v,
        Literal::Number(v) => *v != 0,
        Literal::String(s) => !s.is_empty(),
        Literal::Null | Literal::Undefined => false,
      };
      if val_truthy {
        (env.clone(), TypeEnv::for_unreachable(env.vars.len()))
      } else {
        (TypeEnv::for_unreachable(env.vars.len()), env.clone())
      }
    }
    Expr::Call { callee, args } => {
      let func = &body.functions[callee.idx()];
      if let Some(arg) = args.first() {
        if let Expr::Var(var) = body.exprs[arg.idx()] {
          match &func.ret {
            FunctionReturn::TypeGuard { narrows, to } => {
              if *narrows == var {
                let mut t_env = env.clone();
                t_env.narrow_var(var, to.clone());
                let mut f_env = env.clone();
                f_env.exclude_var(var, to.clone());
                return (t_env, f_env);
              }
            }
            FunctionReturn::Asserts { narrows, to } => {
              if *narrows == var {
                let mut t_env = env.clone();
                t_env.narrow_var(var, to.clone());
                return (t_env, TypeEnv::for_unreachable(env.vars.len()));
              }
            }
            FunctionReturn::AssertsTruthy { narrows } => {
              if *narrows == var {
                let mut t_env = env.clone();
                let narrowed = env.var(var).truthy_part();
                t_env.set_var(var, narrowed);
                return (t_env, TypeEnv::for_unreachable(env.vars.len()));
              }
            }
            FunctionReturn::Value(_) => {}
          }
        }
      }
      let _ = eval_expr(expr_id, env, body, expr_types);
      (env.clone(), env.clone())
    }
    Expr::In { property, obj } => {
      let obj_expr = &body.exprs[obj.idx()];
      if let Expr::Var(var) = obj_expr {
        let mut t_env = env.clone();
        t_env.narrow_var(*var, env.var(*var).narrow_by_property(property));
        let mut f_env = env.clone();
        f_env.exclude_var(*var, env.var(*var).narrow_by_property(property));
        (t_env, f_env)
      } else {
        let _ = eval_expr(expr_id, env, body, expr_types);
        (env.clone(), env.clone())
      }
    }
    Expr::Property { obj, .. } => {
      if let Expr::Var(var) = &body.exprs[obj.idx()] {
        let mut t_env = env.clone();
        t_env.set_var(*var, env.var(*var).truthy_part());
        let mut f_env = env.clone();
        f_env.set_var(*var, env.var(*var).falsy_part());
        (t_env, f_env)
      } else {
        (env.clone(), env.clone())
      }
    }
    _ => {
      let _ = eval_expr(expr_id, env, body, expr_types);
      (env.clone(), env.clone())
    }
  }
}

fn apply_typeof_compare(
  inner: ExprId,
  tag: &str,
  env: &TypeEnv,
  body: &Body,
  expr_types: &mut [Type],
) -> (TypeEnv, TypeEnv) {
  if let Expr::Var(var) = body.exprs[inner.idx()] {
    let mut t_env = env.clone();
    let mut f_env = env.clone();
    t_env.narrow_var(var, env.var(var).narrow_by_typeof(tag));
    f_env.set_var(var, env.var(var).exclude_typeof(tag));
    (t_env, f_env)
  } else {
    let _ = eval_expr(inner, env, body, expr_types);
    (env.clone(), env.clone())
  }
}

fn apply_instanceof(var: VarId, class: &str, env: &TypeEnv) -> (TypeEnv, TypeEnv) {
  let mut t_env = env.clone();
  t_env.narrow_var(var, env.var(var).narrow_by_instanceof(class));
  let mut f_env = env.clone();
  f_env.exclude_var(var, env.var(var).narrow_by_instanceof(class));
  (t_env, f_env)
}

fn apply_discriminant(
  obj_expr: ExprId,
  prop: &str,
  value: &str,
  env: &TypeEnv,
  body: &Body,
  expr_types: &mut [Type],
) -> (TypeEnv, TypeEnv) {
  if let Expr::Var(var) = body.exprs[obj_expr.idx()] {
    let mut t_env = env.clone();
    let narrowed = env.var(var).narrow_by_discriminant(prop, value);
    t_env.narrow_var(var, narrowed.clone());
    let mut f_env = env.clone();
    f_env.exclude_var(var, narrowed);
    (t_env, f_env)
  } else {
    let _ = eval_expr(obj_expr, env, body, expr_types);
    (env.clone(), env.clone())
  }
}

fn merge_envs(a: TypeEnv, b: TypeEnv) -> TypeEnv {
  if a.unreachable {
    return b;
  }
  if b.unreachable {
    return a;
  }
  let mut merged = TypeEnv {
    vars: Vec::with_capacity(a.vars.len()),
    unreachable: false,
  };
  for (x, y) in a.vars.iter().zip(b.vars.iter()) {
    merged.vars.push(x.union(y));
  }
  merged
}
