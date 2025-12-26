use super::compile_js_statements;
use super::Chain;
use super::SourceToInst;
use super::VarType;
use super::DUMMY_LABEL;
use crate::il::inst::Arg;
use crate::il::inst::BinOp;
use crate::il::inst::Const;
use crate::il::inst::Inst;
use crate::il::inst::InstTyp;
use crate::il::inst::UnOp;
use crate::symbol::semantics::{assoc_declared_symbol, assoc_resolved_symbol};
use crate::unsupported_syntax;
use crate::OptimizeResult;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::BinaryExpr;
use parse_js::ast::expr::CallArg;
use parse_js::ast::expr::CallExpr;
use parse_js::ast::expr::ComputedMemberExpr;
use parse_js::ast::expr::CondExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::expr::MemberExpr;
use parse_js::ast::expr::UnaryExpr;
use parse_js::ast::expr::UnaryPostfixExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use std::sync::atomic::Ordering;

fn assoc_has_resolved_symbol(assoc: &NodeAssocData) -> bool {
  assoc_resolved_symbol(assoc).is_some() || assoc_declared_symbol(assoc).is_some()
}

pub struct CompiledMemberExpr {
  pub left: Arg,
  pub res: Arg,
}

impl<'p> SourceToInst<'p> {
  /// Creates a new temp var, emits a new Inst derived from it using provided callback, and returns the temp var as an Arg.
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

  pub fn compile_func(&mut self, Func { body, .. }: Func) -> OptimizeResult<Arg> {
    let pg = self.program.clone();
    let id = pg.next_fn_id.fetch_add(1, Ordering::Relaxed);
    // TODO params, arrow, async, etc.
    let func = match body {
      Some(FuncBody::Block(stmts)) => compile_js_statements(&pg, stmts)?,
      Some(FuncBody::Expression(node)) => {
        return Err(unsupported_syntax(
          node.loc,
          "expression-bodied functions are not supported",
        ))
      }
      None => compile_js_statements(&pg, Vec::new())?,
    };
    pg.functions.insert(id, func);
    Ok(Arg::Fn(id))
  }

  pub fn compile_id_expr(
    &mut self,
    assoc: NodeAssocData,
    IdExpr { name }: IdExpr,
  ) -> OptimizeResult<Arg> {
    Ok(match self.var_type(assoc, name) {
      VarType::Local(local) => Arg::Var(self.symbol_to_temp(local)),
      VarType::Builtin(builtin) => Arg::Builtin(builtin),
      VarType::Foreign(foreign) => self.temp_var_arg(|tgt| Inst::foreign_load(tgt, foreign)),
      VarType::Unknown(name) => self.temp_var_arg(|tgt| Inst::unknown_load(tgt, name)),
    })
  }

  pub fn compile_assignment(
    &mut self,
    span: Loc,
    operator: OperatorName,
    target: Node<Expr>,
    value: Node<Expr>,
  ) -> OptimizeResult<Arg> {
    let Node { loc, assoc, stx } = target;
    match *stx {
      Expr::ArrPat(pat) => {
        if operator != OperatorName::Assignment {
          return Err(unsupported_syntax(
            span,
            format!("unsupported destructuring assignment operator {operator:?}"),
          ));
        }
        let value_tmp_var = self.c_temp.bump();
        let value_arg = self.compile_expr(value)?;
        self.out.push(Inst::var_assign(value_tmp_var, value_arg));
        let pat = Node {
          loc,
          assoc,
          stx: Box::new(Pat::Arr(pat)),
        };
        self.compile_destructuring(pat, Arg::Var(value_tmp_var))?;
        Ok(Arg::Var(value_tmp_var))
      }
      Expr::ObjPat(pat) => {
        if operator != OperatorName::Assignment {
          return Err(unsupported_syntax(
            span,
            format!("unsupported destructuring assignment operator {operator:?}"),
          ));
        }
        let value_tmp_var = self.c_temp.bump();
        let value_arg = self.compile_expr(value)?;
        self.out.push(Inst::var_assign(value_tmp_var, value_arg));
        let pat = Node {
          loc,
          assoc,
          stx: Box::new(Pat::Obj(pat)),
        };
        self.compile_destructuring(pat, Arg::Var(value_tmp_var))?;
        Ok(Arg::Var(value_tmp_var))
      }
      other => {
        let target = Node {
          loc,
          assoc,
          stx: Box::new(other),
        };

        // We'll use this as a placeholder that will be replaced at the end.
        let dummy_val = Arg::Const(Const::Num(JsNumber(0xdeadbeefu32 as f64)));
        // The LHS of an assignment cannot contain a conditional chaining anywhere in the chain, as prohibited by the spec.
        // We assume this is enforced at a previous stage (e.g. parsing).
        // The LHS is earlier in execution order, which is why we do this first, before processing the value, which is why we need a dummy (we don't have the value yet). The LHS can be complex (e.g. `(a + b).c[d + e] = f`), so it does matter.
        let mut assign_inst = match *target.stx {
          Expr::IdPat(n) => {
            let IdPat { name } = *n.stx;
            match self.var_type(n.assoc, name) {
              VarType::Local(l) => Inst::var_assign(self.symbol_to_temp(l), dummy_val),
              VarType::Foreign(f) => Inst::foreign_store(f, dummy_val),
              VarType::Unknown(n) => Inst::unknown_store(n, dummy_val),
              VarType::Builtin(builtin) => {
                return Err(unsupported_syntax(
                  span,
                  format!("assignment to builtin {builtin}"),
                ))
              }
            }
          }
          Expr::Member(n) => {
            let MemberExpr {
              optional_chaining,
              left,
              right,
            } = *n.stx;
            if optional_chaining {
              return Err(unsupported_syntax(
                span,
                "optional chaining in assignment target",
              ));
            }
            let left_arg = self.compile_expr(left)?;
            let member_arg = Arg::Const(Const::Str(right.to_string()));
            Inst::prop_assign(left_arg, member_arg, dummy_val)
          }
          Expr::ComputedMember(n) => {
            let ComputedMemberExpr {
              optional_chaining,
              object,
              member,
            } = *n.stx;
            if optional_chaining {
              return Err(unsupported_syntax(
                span,
                "optional chaining in assignment target",
              ));
            }
            let left_arg = self.compile_expr(object)?;
            let member_arg = self.compile_expr(member)?;
            Inst::prop_assign(left_arg, member_arg, dummy_val)
          }
          _ => return Err(unsupported_syntax(span, "unsupported assignment target")),
        };
        let value_tmp_var = self.c_temp.bump();
        let mut value_arg = self.compile_expr(value)?;
        if operator == OperatorName::Assignment {
          // Direct assignment. Since we need to return a var holding the result of this assignment expression, assign the value to our tmp var. (This is a precaution, in case the value isn't already a var.)
          self
            .out
            .push(Inst::var_assign(value_tmp_var, value_arg.clone()));
        } else {
          // Not direct assignment. We need to perform the operation first. No need for a new tmp var, we can just assign to our expr result tmp var.
          let op = match operator {
            OperatorName::AssignmentAddition => BinOp::Add,
            OperatorName::AssignmentSubtraction => BinOp::Sub,
            OperatorName::AssignmentMultiplication => BinOp::Mul,
            OperatorName::AssignmentDivision => BinOp::Div,
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
            InstTyp::PropAssign => {
              let (obj, prop, _) = assign_inst.as_prop_assign();
              let left_tmp_var = self.c_temp.bump();
              self.out.push(Inst::bin(
                left_tmp_var,
                obj.clone(),
                BinOp::GetProp,
                prop.clone(),
              ));
              Arg::Var(left_tmp_var)
            }
            _ => return Err(unsupported_syntax(span, "unsupported assignment target")),
          };
          let rhs_inst = Inst::bin(value_tmp_var, left_arg, op, value_arg);
          self.out.push(rhs_inst);
          value_arg = Arg::Var(value_tmp_var);
        };
        // The last Inst arg is the dummy arg position for all cases (check above usages).
        // We can't just find the arg that equals our dummy as it's possible actual source produces it.
        *assign_inst.args.last_mut().unwrap() = value_arg;
        self.out.push(assign_inst);
        // The result of an assignment is always the value.
        // - For member access like `a.b = c`, the getter is not invoked.
        // - For non-direct assignment operators like `a += b`, the result is `a + b` since it's a shorthand for `a = a + b`.
        Ok(Arg::Var(value_tmp_var))
      }
    }
  }

  pub fn compile_logical_expr(
    &mut self,
    span: Loc,
    operator: OperatorName,
    left: Node<Expr>,
    right: Node<Expr>,
  ) -> OptimizeResult<Arg> {
    let converge_label_id = self.c_label.bump();
    let res_tmp_var = self.c_temp.bump();
    let left = self.compile_expr(left)?;
    self.out.push(Inst::var_assign(res_tmp_var, left.clone()));
    self.out.push(match operator {
      // Given `a && b`, skip `b` only if NOT `a`.
      OperatorName::LogicalAnd => Inst::cond_goto(left, DUMMY_LABEL, converge_label_id),
      // Given `a || b`, skip `b` only IF `a`.
      OperatorName::LogicalOr => Inst::cond_goto(left, converge_label_id, DUMMY_LABEL),
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

  pub fn compile_binary_expr(
    &mut self,
    span: Loc,
    BinaryExpr {
      left,
      operator,
      right,
    }: BinaryExpr,
  ) -> OptimizeResult<Arg> {
    // TODO Shorthand logic for `&&=` and `||=`.
    if operator.is_assignment()
      && !matches!(
        operator,
        OperatorName::AssignmentLogicalAnd | OperatorName::AssignmentLogicalOr
      )
    {
      self.compile_assignment(span, operator, left, right)
    } else if matches!(operator, OperatorName::LogicalAnd | OperatorName::LogicalOr) {
      self.compile_logical_expr(span, operator, left, right)
    } else {
      let op = match operator {
        OperatorName::Addition => BinOp::Add,
        OperatorName::Division => BinOp::Div,
        OperatorName::LessThan => BinOp::Lt,
        OperatorName::Multiplication => BinOp::Mul,
        OperatorName::StrictEquality => BinOp::StrictEq,
        OperatorName::Subtraction => BinOp::Sub,
        OperatorName::GreaterThan => BinOp::Gt,
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
  }

  pub fn compile_cond_expr(
    &mut self,
    CondExpr {
      test,
      consequent,
      alternate,
    }: CondExpr,
  ) -> OptimizeResult<Arg> {
    let res_tmp_var = self.c_temp.bump();
    let test_arg = self.compile_expr(test)?;
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

  pub fn compile_unary_postfix_expr(
    &mut self,
    span: Loc,
    UnaryPostfixExpr { operator, argument }: UnaryPostfixExpr,
  ) -> OptimizeResult<Arg> {
    let arg = self.compile_expr(argument)?;
    let tmp_var = self.c_temp.bump();
    self.out.push(Inst::var_assign(tmp_var, arg.clone()));
    self.out.push(Inst::bin(
      arg.clone().to_var(),
      arg,
      match operator {
        OperatorName::PostfixDecrement => BinOp::Sub,
        OperatorName::PostfixIncrement => BinOp::Add,
        other => {
          return Err(unsupported_syntax(
            span,
            format!("unsupported postfix operator {other:?}"),
          ))
        }
      },
      Arg::Const(Const::Num(JsNumber(1.0))),
    ));
    Ok(Arg::Var(tmp_var))
  }

  pub fn compile_unary_expr(
    &mut self,
    span: Loc,
    UnaryExpr { operator, argument }: UnaryExpr,
  ) -> OptimizeResult<Arg> {
    match operator {
      // Prefix increment/decrement.
      OperatorName::PrefixDecrement | OperatorName::PrefixIncrement => {
        let arg = self.compile_expr(argument)?;
        self.out.push(Inst::bin(
          arg.to_var(),
          arg.clone(),
          match operator {
            OperatorName::PrefixDecrement => BinOp::Sub,
            OperatorName::PrefixIncrement => BinOp::Add,
            other => {
              return Err(unsupported_syntax(
                span,
                format!("unsupported prefix operator {other:?}"),
              ))
            }
          },
          Arg::Const(Const::Num(JsNumber(1.0))),
        ));
        Ok(arg)
      }
      // Other expressions.
      _ => {
        let op = match operator {
          OperatorName::UnaryNegation => UnOp::Neg,
          _ => {
            return Err(unsupported_syntax(
              span,
              format!("unsupported unary operator {operator:?}"),
            ))
          }
        };
        let arg = self.compile_expr(argument)?;
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, op, arg));
        Ok(Arg::Var(tmp))
      }
    }
  }

  pub fn compile_member_expr(
    &mut self,
    MemberExpr {
      optional_chaining,
      left,
      right,
    }: MemberExpr,
    chain: impl Into<Option<Chain>>,
  ) -> OptimizeResult<CompiledMemberExpr> {
    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    let left_arg = self.compile_expr_with_chain(left, chain)?;
    // Handle `maybe_obj?.a`: skip access if nullish.
    self.conditional_chain_jump(optional_chaining, &left_arg, chain);
    let res_tmp_var = self.c_temp.bump();
    let right_arg = Arg::Const(Const::Str(right.to_string()));
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

  pub fn compile_computed_member_expr(
    &mut self,
    ComputedMemberExpr {
      optional_chaining,
      object,
      member,
    }: ComputedMemberExpr,
    chain: impl Into<Option<Chain>>,
  ) -> OptimizeResult<CompiledMemberExpr> {
    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    let left_arg = self.compile_expr_with_chain(object, chain)?;
    // Handle `maybe_obj?.["a"]`: skip access if nullish.
    self.conditional_chain_jump(optional_chaining, &left_arg, chain);
    let res_tmp_var = self.c_temp.bump();
    // WARNING: The computed member expr does *not* use the same chain!
    let right_arg = self.compile_expr(member)?;
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
    CallExpr {
      optional_chaining,
      callee,
      arguments,
    }: CallExpr,
    chain: impl Into<Option<Chain>>,
  ) -> OptimizeResult<Arg> {
    if let Expr::Id(id_expr) = callee.stx.as_ref() {
      if id_expr.stx.name == "eval" && !assoc_has_resolved_symbol(&id_expr.assoc) {
        return Err(unsupported_syntax(span, "direct eval is not supported"));
      }
    }

    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    // We need to handle methods specially due to `this`.
    let (this_arg, callee_arg) = match *callee.stx {
      Expr::Member(m) => {
        let c = self.compile_member_expr(*m.stx, chain)?;
        (c.left, c.res)
      }
      Expr::ComputedMember(m) => {
        let c = self.compile_computed_member_expr(*m.stx, chain)?;
        (c.left, c.res)
      }
      _ => {
        let c = self.compile_expr_with_chain(callee, chain)?;
        // If there's no `this`, Const::Undefined is correct, no need for None.
        // Calling a function without an explicit this does use undefined in strict mode (try `function f() { console.log(this); }; f()`).
        // If a function has a bound this (e.g. arrow function, `fn.bind`), that's "decl-site"; it doesn't change our "call-site" (e.g. `fn.call(this)`, `obj.method()`) `this` (but does ignore it at runtime).
        // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/this
        let this = Arg::Const(Const::Undefined);
        (this, c)
      }
    };
    // This value will hold the result of the call, or undefined if we set up the chain (i.e. we're the tail result node of the chain).
    let res_tmp_var = self.c_temp.bump();
    // Handle `maybe_fn?.()`: skip call if nullish.
    self.conditional_chain_jump(optional_chaining, &callee_arg, chain);

    // Compile args.
    let mut args = Vec::new();
    let mut spreads = Vec::new();
    for a in arguments.into_iter() {
      let CallArg { spread, value } = *a.stx;
      let arg = self.compile_expr(value)?;
      let arg_idx = args.len();
      args.push(arg);
      if spread {
        // spread indices are relative to Inst.args, which are prefixed with [callee, this]
        spreads.push(arg_idx + 2);
      }
    }
    // Make the call, collecting the result to `res_tmp_var`.
    self
      .out
      .push(Inst::call(res_tmp_var, callee_arg, this_arg, args, spreads));
    self.complete_chain_setup(did_chain_setup, res_tmp_var, chain);
    Ok(Arg::Var(res_tmp_var))
  }

  #[rustfmt::skip]
  pub fn compile_expr_with_chain(
    &mut self,
    n: Node<Expr>,
    chain: impl Into<Option<Chain>>,
  ) -> OptimizeResult<Arg> {
    let span = n.loc;
    match *n.stx {
      Expr::ArrowFunc(n) => self.compile_func(*n.stx.func.stx),
      Expr::Binary(n) => self.compile_binary_expr(span, *n.stx),
      Expr::Call(n) => self.compile_call_expr(span, *n.stx, chain),
      Expr::ComputedMember(n) => Ok(self.compile_computed_member_expr(*n.stx, chain)?.res),
      Expr::Cond(n) => self.compile_cond_expr(*n.stx),
      Expr::Id(s) => self.compile_id_expr(s.assoc, *s.stx),
      Expr::LitBool(n) => Ok(Arg::Const(Const::Bool(n.stx.value))),
      Expr::LitNum(n) => Ok(Arg::Const(Const::Num(n.stx.value))),
      Expr::LitStr(n) => Ok(Arg::Const(Const::Str(n.stx.value))),
      Expr::Member(n) => Ok(self.compile_member_expr(*n.stx, chain)?.res),
      Expr::Unary(n) => self.compile_unary_expr(span, *n.stx),
      Expr::UnaryPostfix(n) => self.compile_unary_postfix_expr(span, *n.stx),
      other => Err(unsupported_syntax(
        span,
        format!("unsupported expression {other:?}"),
      )),
    }
  }

  pub fn compile_expr(&mut self, n: Node<Expr>) -> OptimizeResult<Arg> {
    self.compile_expr_with_chain(n, None)
  }
}
