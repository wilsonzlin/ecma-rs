use super::stmt::key_arg;
use super::{Chain, HirSourceToInst, VarType, DUMMY_LABEL};
use crate::il::inst::{Arg, BinOp, Const, Inst, InstTyp, UnOp};
use crate::unsupported_syntax;
use crate::unsupported_syntax_range;
use crate::OptimizeResult;
use hir_js::{
  AssignOp, BinaryOp, CallExpr, ExprId, ExprKind, MemberExpr, NameId, PatId, UnaryOp, UpdateOp,
};
use num_bigint::BigInt;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use std::sync::atomic::Ordering;

pub struct CompiledMemberExpr {
  pub left: Arg,
  pub res: Arg,
}

impl<'p> HirSourceToInst<'p> {
  const INTERNAL_IN_CALLEE: &'static str = "__optimize_js_in";
  const INTERNAL_INSTANCEOF_CALLEE: &'static str = "__optimize_js_instanceof";
  const INTERNAL_DELETE_CALLEE: &'static str = "__optimize_js_delete";
  const INTERNAL_NEW_CALLEE: &'static str = "__optimize_js_new";
  const INTERNAL_REGEX_CALLEE: &'static str = "__optimize_js_regex";
  const INTERNAL_ARRAY_CALLEE: &'static str = "__optimize_js_array";
  const INTERNAL_ARRAY_HOLE: &'static str = "__optimize_js_array_hole";

  pub fn temp_var_arg(&mut self, f: impl FnOnce(u32) -> Inst) -> Arg {
    let tgt = self.c_temp.bump();
    self.out.push(f(tgt));
    Arg::Var(tgt)
  }

  /// Gets the existing chain or sets one up. This must be called at the beginning of any possible chain node e.g. Call, ComputedMember, Member.
  /// See `Chain` for more details.
  fn maybe_setup_chain(&mut self, chain: impl Into<Option<Chain>>) -> (bool, Chain) {
    match chain.into() {
      Some(chain) => (false, chain),
      None => (
        true,
        Chain {
          is_nullish_label: self.c_label.bump(),
        },
      ),
    }
  }

  /// Jumps to the on-nullish chain label if the `left_arg` value to the left of the operator with `optional_chaining` is null or undefined.
  /// Does nothing if the operator is not `optional_chaining`.
  /// See `Chain` for more details.
  fn conditional_chain_jump(&mut self, optional_chaining: bool, left_arg: &Arg, chain: Chain) {
    if optional_chaining {
      let is_undefined_tmp_var = self.c_temp.bump();
      self.out.push(Inst::bin(
        is_undefined_tmp_var,
        left_arg.clone(),
        BinOp::LooseEq,
        Arg::Const(Const::Null),
      ));
      self.out.push(Inst::cond_goto(
        Arg::Var(is_undefined_tmp_var),
        chain.is_nullish_label,
        DUMMY_LABEL,
      ));
    }
  }

  /// If a chain was set up by the current node, add the jump target and action for on-nullish for the entire chain.
  /// This must be called at the end of any node that called `maybe_setup_chain`.
  /// See `Chain` for more details.
  fn complete_chain_setup(&mut self, did_chain_setup: bool, res_tmp_var: u32, chain: Chain) {
    if did_chain_setup {
      let after_chain_label = self.c_label.bump();
      // This is for when our chain was fully evaluated i.e. there was no short-circuiting due to optional chaining.
      self.out.push(Inst::goto(after_chain_label));
      self.out.push(Inst::label(chain.is_nullish_label));
      self
        .out
        .push(Inst::var_assign(res_tmp_var, Arg::Const(Const::Undefined)));
      self.out.push(Inst::goto(after_chain_label));
      self.out.push(Inst::label(after_chain_label));
    }
  }

  fn classify_ident(&self, expr: ExprId, name: NameId) -> VarType {
    let symbol = self.symbol_for_expr(expr);
    let name = self.name_for(name);
    self.classify_symbol(symbol, name)
  }

  fn literal_arg(&mut self, span: Loc, lit: &hir_js::Literal) -> OptimizeResult<Arg> {
    Ok(match lit {
      hir_js::Literal::Boolean(v) => Arg::Const(Const::Bool(*v)),
      hir_js::Literal::Number(v) => {
        Arg::Const(Const::Num(JsNumber(v.parse::<f64>().unwrap_or_default())))
      }
      hir_js::Literal::String(v) => Arg::Const(Const::Str(v.clone())),
      hir_js::Literal::Null => Arg::Const(Const::Null),
      hir_js::Literal::Undefined => Arg::Const(Const::Undefined),
      hir_js::Literal::BigInt(v) => {
        let value = BigInt::parse_bytes(v.as_bytes(), 10)
          .ok_or_else(|| unsupported_syntax(span, format!("invalid bigint literal {v:?}")))?;
        Arg::Const(Const::BigInt(value))
      }
      hir_js::Literal::Regex(v) => {
        let tmp = self.c_temp.bump();
        self.out.push(Inst::call(
          tmp,
          Arg::Builtin(Self::INTERNAL_REGEX_CALLEE.to_string()),
          Arg::Const(Const::Undefined),
          vec![Arg::Const(Const::Str(v.clone()))],
          Vec::new(),
        ));
        Arg::Var(tmp)
      }
    })
  }

  pub fn compile_func(
    &mut self,
    def: hir_js::DefId,
    body: hir_js::BodyId,
    name: Option<NameId>,
  ) -> OptimizeResult<Arg> {
    let _ = def;
    let pg = self.program.clone();
    let id = pg.next_fn_id.fetch_add(1, Ordering::Relaxed);
    let func = crate::compile_hir_body(&pg, body)?;
    if let Some(name) = name {
      let _ = def;
      let _ = name;
    }
    pg.functions.insert(id, func);
    Ok(Arg::Fn(id))
  }

  fn compile_id_expr(&mut self, expr: ExprId, name: NameId) -> OptimizeResult<Arg> {
    Ok(match self.classify_ident(expr, name) {
      VarType::Local(local) => Arg::Var(self.symbol_to_temp(local)),
      VarType::Builtin(builtin) => Arg::Builtin(builtin),
      VarType::Foreign(foreign) => self.temp_var_arg(|tgt| Inst::foreign_load(tgt, foreign)),
      VarType::Unknown(name) => self.temp_var_arg(|tgt| Inst::unknown_load(tgt, name)),
    })
  }

  pub fn compile_assignment(
    &mut self,
    span: Loc,
    operator: AssignOp,
    target: PatId,
    value: ExprId,
  ) -> OptimizeResult<Arg> {
    use hir_js::PatKind;

    let pat = &self.body.pats[target.0 as usize];
    match pat.kind {
      PatKind::Array(_) | PatKind::Object(_) => {
        if operator != AssignOp::Assign {
          return Err(unsupported_syntax_range(
            self.body.pats[target.0 as usize].span,
            format!("unsupported destructuring assignment operator {operator:?}"),
          ));
        }
        let value_tmp_var = self.c_temp.bump();
        let value_arg = self.compile_expr(value)?;
        self.out.push(Inst::var_assign(value_tmp_var, value_arg));
        self.compile_destructuring(target, Arg::Var(value_tmp_var))?;
        Ok(Arg::Var(value_tmp_var))
      }
      PatKind::Ident(name_id) => {
        let dummy_val = Arg::Const(Const::Num(JsNumber(0xdeadbeefu32 as f64)));
        let var_type = self.classify_symbol(self.symbol_for_pat(target), self.name_for(name_id));
        let mut assign_inst = match var_type {
          VarType::Local(local) => Inst::var_assign(self.symbol_to_temp(local), dummy_val),
          VarType::Foreign(foreign) => Inst::foreign_store(foreign, dummy_val),
          VarType::Unknown(name) => Inst::unknown_store(name, dummy_val),
          VarType::Builtin(builtin) => {
            return Err(unsupported_syntax(
              span,
              format!("assignment to builtin {builtin}"),
            ))
          }
        };
        let value_tmp_var = self.c_temp.bump();
        match operator {
          AssignOp::Assign => {
            let value_arg = self.compile_expr(value)?;
            self
              .out
              .push(Inst::var_assign(value_tmp_var, value_arg.clone()));
            *assign_inst.args.last_mut().unwrap() = value_arg;
            self.out.push(assign_inst);
            Ok(Arg::Var(value_tmp_var))
          }
          AssignOp::LogicalAndAssign | AssignOp::LogicalOrAssign | AssignOp::NullishAssign => {
            let left_arg = match assign_inst.t {
              InstTyp::VarAssign => Arg::Var(assign_inst.tgts[0]),
              InstTyp::ForeignStore => {
                let left_tmp_var = self.c_temp.bump();
                self
                  .out
                  .push(Inst::foreign_load(left_tmp_var, assign_inst.foreign));
                Arg::Var(left_tmp_var)
              }
              InstTyp::UnknownStore => {
                let left_tmp_var = self.c_temp.bump();
                self.out.push(Inst::unknown_load(
                  left_tmp_var,
                  assign_inst.unknown.clone(),
                ));
                Arg::Var(left_tmp_var)
              }
              _ => return Err(unsupported_syntax(span, "unsupported assignment target")),
            };

            self
              .out
              .push(Inst::var_assign(value_tmp_var, left_arg.clone()));
            let converge_label_id = self.c_label.bump();

            match operator {
              AssignOp::LogicalAndAssign => self.out.push(Inst::cond_goto(
                Arg::Var(value_tmp_var),
                DUMMY_LABEL,
                converge_label_id,
              )),
              AssignOp::LogicalOrAssign => self.out.push(Inst::cond_goto(
                Arg::Var(value_tmp_var),
                converge_label_id,
                DUMMY_LABEL,
              )),
              AssignOp::NullishAssign => {
                let is_nullish_tmp_var = self.c_temp.bump();
                self.out.push(Inst::bin(
                  is_nullish_tmp_var,
                  Arg::Var(value_tmp_var),
                  BinOp::LooseEq,
                  Arg::Const(Const::Null),
                ));
                self.out.push(Inst::cond_goto(
                  Arg::Var(is_nullish_tmp_var),
                  DUMMY_LABEL,
                  converge_label_id,
                ));
              }
              _ => unreachable!(),
            }

            let rhs = self.compile_expr(value)?;
            self.out.push(Inst::var_assign(value_tmp_var, rhs.clone()));
            *assign_inst.args.last_mut().unwrap() = rhs;
            self.out.push(assign_inst);
            self.out.push(Inst::label(converge_label_id));

            Ok(Arg::Var(value_tmp_var))
          }
          _ => {
            let value_arg = self.compile_expr(value)?;
            let op = match operator {
              AssignOp::AddAssign => BinOp::Add,
              AssignOp::SubAssign => BinOp::Sub,
              AssignOp::MulAssign => BinOp::Mul,
              AssignOp::DivAssign => BinOp::Div,
              AssignOp::RemAssign => BinOp::Mod,
              AssignOp::ShiftLeftAssign => BinOp::Shl,
              AssignOp::ShiftRightAssign => BinOp::Shr,
              AssignOp::ShiftRightUnsignedAssign => BinOp::UShr,
              AssignOp::BitAndAssign => BinOp::BitAnd,
              AssignOp::BitOrAssign => BinOp::BitOr,
              AssignOp::BitXorAssign => BinOp::BitXor,
              AssignOp::ExponentAssign => BinOp::Exp,
              _ => {
                return Err(unsupported_syntax(
                  span,
                  format!("unsupported assignment operator {operator:?}"),
                ))
              }
            };
            let left_arg = match assign_inst.t {
              InstTyp::VarAssign => Arg::Var(assign_inst.tgts[0]),
              InstTyp::ForeignStore => {
                let left_tmp_var = self.c_temp.bump();
                self
                  .out
                  .push(Inst::foreign_load(left_tmp_var, assign_inst.foreign));
                Arg::Var(left_tmp_var)
              }
              InstTyp::UnknownStore => {
                let left_tmp_var = self.c_temp.bump();
                self.out.push(Inst::unknown_load(
                  left_tmp_var,
                  assign_inst.unknown.clone(),
                ));
                Arg::Var(left_tmp_var)
              }
              _ => return Err(unsupported_syntax(span, "unsupported assignment target")),
            };
            let rhs_inst = Inst::bin(value_tmp_var, left_arg, op, value_arg);
            self.out.push(rhs_inst);
            *assign_inst.args.last_mut().unwrap() = Arg::Var(value_tmp_var);
            self.out.push(assign_inst);
            Ok(Arg::Var(value_tmp_var))
          }
        }
      }
      PatKind::AssignTarget(expr_id) => {
        let target_expr = &self.body.exprs[expr_id.0 as usize];
        let dummy_val = Arg::Const(Const::Num(JsNumber(0xdeadbeefu32 as f64)));
        let mut assign_inst = match target_expr.kind {
          ExprKind::Member(ref member) => {
            if member.optional {
              return Err(unsupported_syntax(
                span,
                "optional chaining in assignment target",
              ));
            }
            let left_arg = self.compile_expr(member.object)?;
            let member_arg = key_arg(self, &member.property)?;
            Inst::prop_assign(left_arg, member_arg, dummy_val)
          }
          _ => return Err(unsupported_syntax(span, "unsupported assignment target")),
        };
        let value_tmp_var = self.c_temp.bump();
        match operator {
          AssignOp::Assign => {
            let value_arg = self.compile_expr(value)?;
            self
              .out
              .push(Inst::var_assign(value_tmp_var, value_arg.clone()));
            *assign_inst.args.last_mut().unwrap() = value_arg;
            self.out.push(assign_inst);
            Ok(Arg::Var(value_tmp_var))
          }
          AssignOp::LogicalAndAssign | AssignOp::LogicalOrAssign | AssignOp::NullishAssign => {
            let (obj, prop, _) = assign_inst.as_prop_assign();
            let left_tmp_var = self.c_temp.bump();
            self.out.push(Inst::bin(
              left_tmp_var,
              obj.clone(),
              BinOp::GetProp,
              prop.clone(),
            ));
            self
              .out
              .push(Inst::var_assign(value_tmp_var, Arg::Var(left_tmp_var)));

            let converge_label_id = self.c_label.bump();

            match operator {
              AssignOp::LogicalAndAssign => self.out.push(Inst::cond_goto(
                Arg::Var(value_tmp_var),
                DUMMY_LABEL,
                converge_label_id,
              )),
              AssignOp::LogicalOrAssign => self.out.push(Inst::cond_goto(
                Arg::Var(value_tmp_var),
                converge_label_id,
                DUMMY_LABEL,
              )),
              AssignOp::NullishAssign => {
                let is_nullish_tmp_var = self.c_temp.bump();
                self.out.push(Inst::bin(
                  is_nullish_tmp_var,
                  Arg::Var(value_tmp_var),
                  BinOp::LooseEq,
                  Arg::Const(Const::Null),
                ));
                self.out.push(Inst::cond_goto(
                  Arg::Var(is_nullish_tmp_var),
                  DUMMY_LABEL,
                  converge_label_id,
                ));
              }
              _ => unreachable!(),
            }

            let rhs = self.compile_expr(value)?;
            self.out.push(Inst::var_assign(value_tmp_var, rhs.clone()));
            *assign_inst.args.last_mut().unwrap() = rhs;
            self.out.push(assign_inst);
            self.out.push(Inst::label(converge_label_id));

            Ok(Arg::Var(value_tmp_var))
          }
          _ => {
            let value_arg = self.compile_expr(value)?;
            let op = match operator {
              AssignOp::AddAssign => BinOp::Add,
              AssignOp::SubAssign => BinOp::Sub,
              AssignOp::MulAssign => BinOp::Mul,
              AssignOp::DivAssign => BinOp::Div,
              AssignOp::RemAssign => BinOp::Mod,
              AssignOp::ShiftLeftAssign => BinOp::Shl,
              AssignOp::ShiftRightAssign => BinOp::Shr,
              AssignOp::ShiftRightUnsignedAssign => BinOp::UShr,
              AssignOp::BitAndAssign => BinOp::BitAnd,
              AssignOp::BitOrAssign => BinOp::BitOr,
              AssignOp::BitXorAssign => BinOp::BitXor,
              AssignOp::ExponentAssign => BinOp::Exp,
              _ => {
                return Err(unsupported_syntax(
                  span,
                  format!("unsupported assignment operator {operator:?}"),
                ))
              }
            };
            let (obj, prop, _) = assign_inst.as_prop_assign();
            let left_tmp_var = self.c_temp.bump();
            self.out.push(Inst::bin(
              left_tmp_var,
              obj.clone(),
              BinOp::GetProp,
              prop.clone(),
            ));
            let rhs_inst = Inst::bin(value_tmp_var, Arg::Var(left_tmp_var), op, value_arg);
            self.out.push(rhs_inst);
            *assign_inst.args.last_mut().unwrap() = Arg::Var(value_tmp_var);
            self.out.push(assign_inst);
            Ok(Arg::Var(value_tmp_var))
          }
        }
      }
      _ => Err(unsupported_syntax(span, "unsupported assignment target")),
    }
  }

  pub fn compile_logical_expr(
    &mut self,
    span: Loc,
    operator: BinaryOp,
    left: ExprId,
    right: ExprId,
  ) -> OptimizeResult<Arg> {
    let converge_label_id = self.c_label.bump();
    let res_tmp_var = self.c_temp.bump();
    let left = self.compile_expr(left)?;
    self.out.push(Inst::var_assign(res_tmp_var, left.clone()));
    self.out.push(match operator {
      BinaryOp::LogicalAnd => Inst::cond_goto(left, DUMMY_LABEL, converge_label_id),
      BinaryOp::LogicalOr => Inst::cond_goto(left, converge_label_id, DUMMY_LABEL),
      other => {
        return Err(unsupported_syntax(
          span,
          format!("unsupported logical operator {other:?}"),
        ))
      }
    });
    let right = self.compile_expr(right)?;
    self.out.push(Inst::var_assign(res_tmp_var, right));
    self.out.push(Inst::label(converge_label_id));
    Ok(Arg::Var(res_tmp_var))
  }

  pub fn compile_nullish_coalescing_expr(
    &mut self,
    left: ExprId,
    right: ExprId,
  ) -> OptimizeResult<Arg> {
    if self.expr_excludes_nullish(left) {
      return self.compile_expr(left);
    }

    let converge_label_id = self.c_label.bump();
    let res_tmp_var = self.c_temp.bump();

    let left_arg = self.compile_expr(left)?;
    self.out.push(Inst::var_assign(res_tmp_var, left_arg));

    let is_nullish_tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(
      is_nullish_tmp_var,
      Arg::Var(res_tmp_var),
      BinOp::LooseEq,
      Arg::Const(Const::Null),
    ));
    self.out.push(Inst::cond_goto(
      Arg::Var(is_nullish_tmp_var),
      DUMMY_LABEL,
      converge_label_id,
    ));

    let right_arg = self.compile_expr(right)?;
    self.out.push(Inst::var_assign(res_tmp_var, right_arg));
    self.out.push(Inst::label(converge_label_id));

    Ok(Arg::Var(res_tmp_var))
  }

  pub fn compile_comma_expr(&mut self, left: ExprId, right: ExprId) -> OptimizeResult<Arg> {
    let _ = self.compile_expr(left)?;
    self.compile_expr(right)
  }

  pub fn compile_binary_expr(
    &mut self,
    span: Loc,
    operator: BinaryOp,
    left: ExprId,
    right: ExprId,
  ) -> OptimizeResult<Arg> {
    if matches!(operator, BinaryOp::LogicalAnd | BinaryOp::LogicalOr) {
      return self.compile_logical_expr(span, operator, left, right);
    }
    if operator == BinaryOp::NullishCoalescing {
      return self.compile_nullish_coalescing_expr(left, right);
    }
    if operator == BinaryOp::Comma {
      return self.compile_comma_expr(left, right);
    }
    if matches!(operator, BinaryOp::In | BinaryOp::Instanceof) {
      let left = self.compile_expr(left)?;
      let right = self.compile_expr(right)?;
      let res_tmp_var = self.c_temp.bump();
      let callee = match operator {
        BinaryOp::In => Self::INTERNAL_IN_CALLEE,
        BinaryOp::Instanceof => Self::INTERNAL_INSTANCEOF_CALLEE,
        _ => unreachable!(),
      };
      self.out.push(Inst::call(
        res_tmp_var,
        Arg::Builtin(callee.to_string()),
        Arg::Const(Const::Undefined),
        vec![left, right],
        Vec::new(),
      ));
      return Ok(Arg::Var(res_tmp_var));
    }

    let left_expr = &self.body.exprs[left.0 as usize];
    let right_expr = &self.body.exprs[right.0 as usize];
    let is_nullish = |expr_id: ExprId, expr: &hir_js::Expr| match expr.kind {
      ExprKind::Literal(hir_js::Literal::Null | hir_js::Literal::Undefined) => true,
      ExprKind::Unary {
        op: UnaryOp::Void, ..
      } => true,
      ExprKind::Ident(name) => {
        self.symbol_for_expr(expr_id).is_none()
          && self.program.names.resolve(name) == Some("undefined")
      }
      _ => false,
    };
    let left_nullish = is_nullish(left, left_expr);
    let right_nullish = is_nullish(right, right_expr);

    if matches!(
      operator,
      BinaryOp::StrictEquality
        | BinaryOp::StrictInequality
        | BinaryOp::Equality
        | BinaryOp::Inequality
    ) {
      if (left_nullish && self.expr_excludes_nullish(right))
        || (right_nullish && self.expr_excludes_nullish(left))
      {
        let _ = self.compile_expr(left)?;
        let _ = self.compile_expr(right)?;
        let is_inequality = matches!(operator, BinaryOp::StrictInequality | BinaryOp::Inequality);
        return Ok(Arg::Const(Const::Bool(is_inequality)));
      }

      let typeof_left = match left_expr.kind {
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        } => Some((left, expr)),
        _ => None,
      };
      let typeof_right = match right_expr.kind {
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        } => Some((right, expr)),
        _ => None,
      };

      // Type-driven folding for `typeof` equality is only valid for strict
      // equality/inequality. The optimizer doesn't currently lower non-nullish
      // loose equality operators because they can trigger ToPrimitive coercions
      // (and user-defined side effects) on objects.
      if matches!(
        operator,
        BinaryOp::StrictEquality | BinaryOp::StrictInequality
      ) {
        if let Some(((typeof_expr, typeof_operand), typeof_on_left)) =
          match (typeof_left, typeof_right) {
            (Some((expr, operand)), None) => Some(((expr, operand), true)),
            (None, Some((expr, operand))) => Some(((expr, operand), false)),
            _ => None,
          }
        {
          let literal = if typeof_on_left {
            match &right_expr.kind {
              ExprKind::Literal(hir_js::Literal::String(value)) => Some(value.as_str()),
              _ => None,
            }
          } else {
            match &left_expr.kind {
              ExprKind::Literal(hir_js::Literal::String(value)) => Some(value.as_str()),
              _ => None,
            }
          };
          if let Some(literal) = literal {
            if let Some(known) = self.typeof_string_expr(typeof_operand) {
              let _ = self.compile_expr(typeof_expr)?;
              let eq = known == literal;
              let value = if operator == BinaryOp::StrictEquality {
                eq
              } else {
                !eq
              };
              return Ok(Arg::Const(Const::Bool(value)));
            }
          }
        }
      }
    }

    let op = match operator {
      BinaryOp::Add => BinOp::Add,
      BinaryOp::BitAnd => BinOp::BitAnd,
      BinaryOp::BitOr => BinOp::BitOr,
      BinaryOp::BitXor => BinOp::BitXor,
      BinaryOp::Divide => BinOp::Div,
      BinaryOp::LessThan => BinOp::Lt,
      BinaryOp::LessEqual => BinOp::Leq,
      BinaryOp::Multiply => BinOp::Mul,
      BinaryOp::Remainder => BinOp::Mod,
      BinaryOp::Exponent => BinOp::Exp,
      BinaryOp::ShiftLeft => BinOp::Shl,
      BinaryOp::ShiftRight => BinOp::Shr,
      BinaryOp::ShiftRightUnsigned => BinOp::UShr,
      BinaryOp::StrictEquality => BinOp::StrictEq,
      BinaryOp::StrictInequality => BinOp::NotStrictEq,
      BinaryOp::Subtract => BinOp::Sub,
      BinaryOp::GreaterThan => BinOp::Gt,
      BinaryOp::GreaterEqual => BinOp::Geq,
      BinaryOp::Equality if left_nullish || right_nullish => BinOp::LooseEq,
      BinaryOp::Inequality if left_nullish || right_nullish => BinOp::NotLooseEq,
      _ => {
        return Err(unsupported_syntax(
          span,
          format!("unsupported binary operator {operator:?}"),
        ))
      }
    };
    let left = self.compile_expr(left)?;
    let right = self.compile_expr(right)?;
    let res_tmp_var = self.c_temp.bump();
    self.out.push(Inst::bin(res_tmp_var, left, op, right));
    Ok(Arg::Var(res_tmp_var))
  }

  pub fn compile_cond_expr(
    &mut self,
    test: ExprId,
    consequent: ExprId,
    alternate: ExprId,
  ) -> OptimizeResult<Arg> {
    let known = self.bool_literal_expr(test);
    let _test_arg = self.compile_expr(test)?;
    if let Some(value) = known {
      if value {
        return self.compile_expr(consequent);
      }
      return self.compile_expr(alternate);
    }
    let res_tmp_var = self.c_temp.bump();
    let test_arg = _test_arg;
    let cons_label_id = self.c_label.bump();
    let after_label_id = self.c_label.bump();
    self
      .out
      .push(Inst::cond_goto(test_arg, cons_label_id, DUMMY_LABEL));
    let alt_res = self.compile_expr(alternate)?;
    self.out.push(Inst::var_assign(res_tmp_var, alt_res));
    self.out.push(Inst::goto(after_label_id));
    self.out.push(Inst::label(cons_label_id));
    let cons_res = self.compile_expr(consequent)?;
    self.out.push(Inst::var_assign(res_tmp_var, cons_res));
    self.out.push(Inst::label(after_label_id));
    Ok(Arg::Var(res_tmp_var))
  }

  pub fn compile_update_expr(
    &mut self,
    _span: Loc,
    operator: UpdateOp,
    argument: ExprId,
    prefix: bool,
  ) -> OptimizeResult<Arg> {
    let arg = self.compile_expr(argument)?;
    match operator {
      UpdateOp::Decrement | UpdateOp::Increment => {
        let rhs = match operator {
          UpdateOp::Decrement => BinOp::Sub,
          UpdateOp::Increment => BinOp::Add,
        };
        if prefix {
          self.out.push(Inst::bin(
            arg.to_var(),
            arg.clone(),
            rhs,
            Arg::Const(Const::Num(JsNumber(1.0))),
          ));
          Ok(arg)
        } else {
          let tmp_var = self.c_temp.bump();
          self.out.push(Inst::var_assign(tmp_var, arg.clone()));
          self.out.push(Inst::bin(
            arg.clone().to_var(),
            arg,
            rhs,
            Arg::Const(Const::Num(JsNumber(1.0))),
          ));
          Ok(Arg::Var(tmp_var))
        }
      }
    }
  }

  pub fn compile_unary_expr(
    &mut self,
    span: Loc,
    operator: UnaryOp,
    argument: ExprId,
  ) -> OptimizeResult<Arg> {
    match operator {
      UnaryOp::Not => {
        let arg = self.compile_expr(argument)?;
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, UnOp::Not, arg));
        Ok(Arg::Var(tmp))
      }
      UnaryOp::BitNot => {
        let arg = self.compile_expr(argument)?;
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, UnOp::BitNot, arg));
        Ok(Arg::Var(tmp))
      }
      UnaryOp::Minus => {
        let arg = self.compile_expr(argument)?;
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, UnOp::Neg, arg));
        Ok(Arg::Var(tmp))
      }
      UnaryOp::Plus => {
        let arg = self.compile_expr(argument)?;
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, UnOp::Plus, arg));
        Ok(Arg::Var(tmp))
      }
      UnaryOp::Typeof => {
        let arg = match self.body.exprs[argument.0 as usize].kind {
          ExprKind::Ident(name) => match self.classify_ident(argument, name) {
            VarType::Unknown(name) => Arg::Builtin(name),
            _ => self.compile_expr(argument)?,
          },
          _ => self.compile_expr(argument)?,
        };
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, UnOp::Typeof, arg));
        Ok(Arg::Var(tmp))
      }
      UnaryOp::Void => {
        let arg = self.compile_expr(argument)?;
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, UnOp::Void, arg));
        Ok(Arg::Var(tmp))
      }
      UnaryOp::Delete => {
        let arg_expr = &self.body.exprs[argument.0 as usize];
        match &arg_expr.kind {
          ExprKind::Member(member) => {
            if member.optional {
              return Err(unsupported_syntax(
                span,
                "optional chaining in delete operand",
              ));
            }
            let object_arg = self.compile_expr(member.object)?;
            let prop_arg = key_arg(self, &member.property)?;
            let tmp = self.c_temp.bump();
            self.out.push(Inst::call(
              tmp,
              Arg::Builtin(Self::INTERNAL_DELETE_CALLEE.to_string()),
              Arg::Const(Const::Undefined),
              vec![object_arg, prop_arg],
              Vec::new(),
            ));
            Ok(Arg::Var(tmp))
          }
          _ => Err(unsupported_syntax(span, "unsupported delete operand")),
        }
      }
      _ => Err(unsupported_syntax(
        span,
        format!("unsupported unary operator {operator:?}"),
      )),
    }
  }

  pub fn compile_member_expr(
    &mut self,
    member: &MemberExpr,
    chain: impl Into<Option<Chain>>,
  ) -> OptimizeResult<CompiledMemberExpr> {
    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    let left_arg = self.compile_expr_with_chain(member.object, chain)?;
    let optional = member.optional && !self.expr_excludes_nullish(member.object);
    self.conditional_chain_jump(optional, &left_arg, chain);
    let res_tmp_var = self.c_temp.bump();
    let right_arg = key_arg(self, &member.property)?;
    self.out.push(Inst::bin(
      res_tmp_var,
      left_arg.clone(),
      BinOp::GetProp,
      right_arg,
    ));
    self.complete_chain_setup(did_chain_setup, res_tmp_var, chain);
    Ok(CompiledMemberExpr {
      res: Arg::Var(res_tmp_var),
      left: left_arg.clone(),
    })
  }

  pub fn compile_call_expr(
    &mut self,
    span: Loc,
    call: &CallExpr,
    chain: impl Into<Option<Chain>>,
  ) -> OptimizeResult<Arg> {
    if !call.is_new {
      if let ExprKind::Ident(name) = self.body.exprs[call.callee.0 as usize].kind {
        if self.name_for(name) == "eval" && self.symbol_for_expr(call.callee).is_none() {
          return Err(unsupported_syntax(span, "direct eval is not supported"));
        }
      }
    }

    if call.is_new {
      if call.optional {
        return Err(unsupported_syntax(
          span,
          "optional chaining in new expressions is not supported",
        ));
      }

      let (did_chain_setup, chain) = self.maybe_setup_chain(chain);

      let ctor_arg = self.compile_expr(call.callee)?;
      let res_tmp_var = self.c_temp.bump();

      let mut args = Vec::new();
      let mut spreads = Vec::new();
      for a in call.args.iter() {
        let arg = self.compile_expr(a.expr)?;
        let arg_idx = args.len();
        args.push(arg);
        if a.spread {
          spreads.push(arg_idx + 2);
        }
      }

      self.out.push(Inst::call(
        res_tmp_var,
        Arg::Builtin(Self::INTERNAL_NEW_CALLEE.to_string()),
        ctor_arg,
        args,
        spreads,
      ));

      self.complete_chain_setup(did_chain_setup, res_tmp_var, chain);
      return Ok(Arg::Var(res_tmp_var));
    }

    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    let (this_arg, callee_arg) = match self.body.exprs[call.callee.0 as usize].kind.clone() {
      ExprKind::Member(m) => {
        let c = self.compile_member_expr(&m, chain)?;
        (c.left, c.res)
      }
      _ => {
        let c = self.compile_expr_with_chain(call.callee, chain)?;
        let this = Arg::Const(Const::Undefined);
        (this, c)
      }
    };
    let res_tmp_var = self.c_temp.bump();
    let optional = call.optional && !self.expr_excludes_nullish(call.callee);
    self.conditional_chain_jump(optional, &callee_arg, chain);

    let mut args = Vec::new();
    let mut spreads = Vec::new();
    for a in call.args.iter() {
      let arg = self.compile_expr(a.expr)?;
      let arg_idx = args.len();
      args.push(arg);
      if a.spread {
        spreads.push(arg_idx + 2);
      }
    }
    self
      .out
      .push(Inst::call(res_tmp_var, callee_arg, this_arg, args, spreads));
    self.complete_chain_setup(did_chain_setup, res_tmp_var, chain);
    Ok(Arg::Var(res_tmp_var))
  }

  pub fn compile_expr_with_chain(
    &mut self,
    expr_id: ExprId,
    chain: impl Into<Option<Chain>>,
  ) -> OptimizeResult<Arg> {
    let expr = &self.body.exprs[expr_id.0 as usize];
    let span = Loc(expr.span.start as usize, expr.span.end as usize);
    match &expr.kind {
      ExprKind::Binary { op, left, right } => self.compile_binary_expr(span, *op, *left, *right),
      ExprKind::Call(call) => self.compile_call_expr(span, call, chain),
      ExprKind::Member(member) => Ok(self.compile_member_expr(member, chain)?.res),
      ExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => self.compile_cond_expr(*test, *consequent, *alternate),
      ExprKind::Array(array) => {
        let mut args = Vec::new();
        let mut spreads = Vec::new();
        for element in array.elements.iter() {
          match element {
            hir_js::ArrayElement::Expr(expr) => {
              args.push(self.compile_expr(*expr)?);
            }
            hir_js::ArrayElement::Spread(expr) => {
              let arg = self.compile_expr(*expr)?;
              let idx = args.len();
              args.push(arg);
              spreads.push(idx + 2);
            }
            hir_js::ArrayElement::Empty => {
              args.push(Arg::Builtin(Self::INTERNAL_ARRAY_HOLE.to_string()));
            }
          }
        }
        let tmp = self.c_temp.bump();
        self.out.push(Inst::call(
          tmp,
          Arg::Builtin(Self::INTERNAL_ARRAY_CALLEE.to_string()),
          Arg::Const(Const::Undefined),
          args,
          spreads,
        ));
        Ok(Arg::Var(tmp))
      }
      ExprKind::Ident(name) => self.compile_id_expr(expr_id, *name),
      ExprKind::Literal(lit) => self.literal_arg(span, lit),
      ExprKind::This => Ok(Arg::Builtin("this".to_string())),
      ExprKind::ImportMeta => Ok(Arg::Builtin("import.meta".to_string())),
      ExprKind::NewTarget => Ok(Arg::Builtin("new.target".to_string())),
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr }
      | ExprKind::Satisfies { expr, .. } => self.compile_expr(*expr),
      ExprKind::Unary { op, expr } => self.compile_unary_expr(span, *op, *expr),
      ExprKind::Update { op, expr, prefix } => self.compile_update_expr(span, *op, *expr, *prefix),
      ExprKind::Assignment { op, target, value } => {
        self.compile_assignment(span, *op, *target, *value)
      }
      ExprKind::FunctionExpr {
        def,
        body,
        name,
        is_arrow: _,
      } => self.compile_func(*def, *body, *name),
      other => Err(unsupported_syntax(
        span,
        format!("unsupported expression {other:?}"),
      )),
    }
  }

  pub fn compile_expr(&mut self, expr_id: ExprId) -> OptimizeResult<Arg> {
    self.compile_expr_with_chain(expr_id, None)
  }
}
