use std::sync::atomic::Ordering;

use parse_js::{ast::{expr::{pat::IdPat, ArrowFuncExpr, BinaryExpr, CallArg, CallExpr, ComputedMemberExpr, CondExpr, Expr, IdExpr, MemberExpr, UnaryExpr, UnaryPostfixExpr}, func::{Func, FuncBody}, node::Node}, num::JsNumber, operator::OperatorName};

use crate::{compile_js_statements, il::inst::{Arg, BinOp, Const, Inst, InstTyp, UnOp}};

use super::{Chain, SourceToInst, VarType, DUMMY_LABEL};

struct CompiledMemberExpr {
  left: Arg,
  res: Arg,
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
      None => (true, Chain { is_nullish_label: self.c_label.bump() }),
    }
  }

  /// Jumps to the on-nullish chain label if the `left_arg` value to the left of the operator with `optional_chaining` is null or undefined.
  /// Does nothing if the operator is not `optional_chaining`.
  /// See `Chain` for more details.
  fn conditional_chain_jump(&mut self, optional_chaining: bool, left_arg: Arg, chain: Chain) {
    if optional_chaining {
      let is_undefined_tmp_var = self.c_temp.bump();
      self.out.push(Inst::bin(is_undefined_tmp_var, left_arg, BinOp::LooseEq, Arg::Const(Const::Null)));
      self.out.push(Inst::cond_goto(Arg::Var(is_undefined_tmp_var), chain.is_nullish_label, DUMMY_LABEL));
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
      self.out.push(Inst::var_assign(res_tmp_var, Arg::Const(Const::Undefined)));
      self.out.push(Inst::goto(after_chain_label));
      self.out.push(Inst::label(after_chain_label));
    }
  }

  pub fn compile_func(&mut self, n: Node<Func>) -> Arg {
    let Func { arrow, async_, generator, parameters, body } = n.stx;
    let pg = self.program.clone();
    let id = pg.next_fn_id.fetch_add(1, Ordering::Relaxed);
    rayon::spawn(|| {
      let wg = pg.wg.clone();
      // TODO params, arrow, async, etc.
      match body {
        FuncBody::Block(vec) => {
          let func = compile_js_statements(&pg, body);
          pg.functions.insert(id, func);
        }
        FuncBody::Expression(node) => todo!(),
      };
      drop(wg);
    });
    Arg::Fn(id)
  }

  pub fn compile_id_expr(&mut self, n: Node<IdExpr>) -> Arg {
    match self.var_type(&n, n.stx.name) {
      VarType::Local(local) => Arg::Var(self.symbol_to_temp(local)),
      VarType::Builtin(builtin) => Arg::Builtin(builtin),
      VarType::Foreign(foreign) => self.temp_var_arg(|tgt| Inst::foreign_load(tgt, foreign)),
      VarType::Unknown(name) => self.temp_var_arg(|tgt| Inst::unknown_load(tgt, name)),
    }
  }

  pub fn compile_assignment(&mut self, operator: OperatorName, left: Node<Expr>, right: Node<Expr>) -> Arg {
    // We'll use this as a placeholder that will be replaced at the end.
    let dummy_val = Arg::Const(Const::Num(JsNumber(0xdeadbeefu32 as f64)));
    // The LHS of an assignment cannot contain a conditional chaining anywhere in the chain, as prohibited by the spec.
    // We assume this is enforced at a previous stage (e.g. parsing).
    let mut ass_inst = match left.stx {
      Expr::IdPat(IdPat { name }) => {
        match self.var_type(left.assoc, name) {
          VarType::Local(l) => Inst::var_assign(
            self.symbol_to_temp(l),
            dummy_val,
          ),
          VarType::Foreign(f) => Inst::foreign_store(
            f,
            dummy_val,
          ),
          VarType::Unknown(n) => Inst::unknown_store(
            n,
            dummy_val,
          ),
          VarType::Builtin(builtin) => panic!("assignment to builtin {builtin}"),
        }
      }
      Expr::Member(MemberExpr { optional_chaining, left, right }) => {
        assert!(!optional_chaining);
        let left_arg = self.compile_arg(&left);
        Inst::prop_assign(
          left_arg,
          Arg::Const(Const::Str(right.to_string())),
          dummy_val,
        )
      }
      Expr::ComputedMember(ComputedMemberExpr { optional_chaining, object, member }) => {
        assert!(!optional_chaining);
        let left_arg = self.compile_expr(&object, None);
        let member_arg = self.compile_expr(&member, None);
        Inst::prop_assign(
          left_arg,
          member_arg,
          dummy_val,
        )
      }
      _ => unreachable!(),
    };
    let mut value = self.compile_expr(right);
    if *operator != OperatorName::Assignment {
      let op = match operator {
        OperatorName::AssignmentAddition => BinOp::Add,
        OperatorName::AssignmentSubtraction => BinOp::Sub,
        OperatorName::AssignmentMultiplication => BinOp::Mul,
        OperatorName::AssignmentDivision => BinOp::Div,
        _ => unimplemented!(),
      };
      let left_arg = match ass_inst.t {
        InstTyp::VarAssign => Arg::Var(ass_inst.tgts[0]),
        InstTyp::ForeignStore => {
          let left_tmp_var = self.c_temp.bump();
          self.out.push(Inst::foreign_load(left_tmp_var, ass_inst.foreign));
          Arg::Var(left_tmp_var)
        }
        InstTyp::UnknownStore => {
          let left_tmp_var = self.c_temp.bump();
          self.out.push(Inst::unknown_load(left_tmp_var, ass_inst.unknown.clone()));
          Arg::Var(left_tmp_var)
        }
        InstTyp::PropAssign => {
          let (obj, prop, _) = ass_inst.as_prop_assign();
          let left_tmp_var = self.c_temp.bump();
          self.out.push(Inst::bin(
            left_tmp_var,
            obj.clone(),
            BinOp::GetProp,
            prop.clone(),
          ));
          Arg::Var(left_tmp_var)
        }
        _ => unreachable!(),
      };
      let rhs_tmp_var = self.c_temp.bump();
      let rhs_inst = Inst::bin(
        rhs_tmp_var,
        left_arg,
        op,
        value,
      );
      self.out.push(rhs_inst);
      value = Arg::Var(rhs_tmp_var);
    };
    for a in ass_inst.args.iter_mut() {
      if a == dummy_val {
        a = value;
        break;
      };
    };
    self.out.push(ass_inst);
    // TODO
    Arg::Var(self.out.last().unwrap().tgts[0])
  }

  pub fn compile_logical_expr(&mut self, operator: OperatorName, left: Node<Expr>, right: Node<Expr>) -> Arg {
    let converge_label_id = self.c_label.bump();
    let res_tmp_var = self.c_temp.bump();
    let left = self.compile_expr(left);
    self.out.push(Inst::var_assign(res_tmp_var, left.clone()));
    self.out.push(match operator {
      // Given `a && b`, skip `b` only if NOT `a`.
      OperatorName::LogicalAnd => Inst::cond_goto( left, DUMMY_LABEL,  converge_label_id),
      // Given `a || b`, skip `b` only IF `a`.
      OperatorName::LogicalOr => Inst::cond_goto( left,  converge_label_id, DUMMY_LABEL),
      _ => unreachable!(),
    });
    let right = self.compile_expr(right);
    self.out.push(Inst::var_assign(res_tmp_var, right));
    self.out.push(Inst::label( converge_label_id));
    Arg::Var(res_tmp_var)
  }

  pub fn compile_binary_expr(&mut self, BinaryExpr { left, operator, right }: BinaryExpr) -> Arg {
    // TODO Shorthand logic for `&&=` and `||=`.
    if operator.is_assignment() && !matches!(operator, OperatorName::AssignmentLogicalAnd | OperatorName::AssignmentLogicalOr) {
      self.compile_assignment(operator, left, right)
    } else if matches!(operator, OperatorName::LogicalAnd | OperatorName::LogicalOr) {
      self.compile_logical_expr(operator, left, right)
    } else {
      let op = match operator {
        OperatorName::Addition => BinOp::Add,
        OperatorName::Division => BinOp::Div,
        OperatorName::LessThan => BinOp::Lt,
        OperatorName::Multiplication => BinOp::Mul,
        OperatorName::StrictEquality => BinOp::StrictEq,
        OperatorName::Subtraction => BinOp::Sub,
        OperatorName::GreaterThan => BinOp::Gt,
        _ => unimplemented!(),
      };
      let left = self.compile_expr(left);
      let right = self.compile_expr(right);
      let res_tmp_var = self.c_temp.bump();
      self.out.push(Inst::bin(
        res_tmp_var,
        left,
        op,
        right,
      ));
      Arg::Var(res_tmp_var)
    }
  }

  pub fn compile_cond_expr(&mut self, CondExpr { test, consequent, alternate }: CondExpr) -> Arg {
    let res_tmp_var = self.c_temp.bump();
    let test_arg = self.compile_expr(test);
    let cons_label_id = self.c_label.bump();
    let after_label_id = self.c_label.bump();
    self.out.push(Inst::cond_goto(test_arg, cons_label_id, DUMMY_LABEL));
    let alt_res = self.compile_expr(alternate);
    self.out.push(Inst::var_assign(res_tmp_var, alt_res));
    self.out.push(Inst::goto(after_label_id));
    self.out.push(Inst::label(cons_label_id));
    let cons_res = self.compile_expr(consequent);
    self.out.push(Inst::var_assign(res_tmp_var, cons_res));
    self.out.push(Inst::label(after_label_id));
    Arg::Var(res_tmp_var)
  }

  pub fn compile_unary_postfix_expr(&mut self, UnaryPostfixExpr { operator, argument }: UnaryPostfixExpr) -> Arg {
    let arg = self.compile_expr(argument, None);
    let tmp_var = self.c_temp.bump();
    self.out.push(Inst::var_assign(tmp_var, arg.clone()));
    self.out.push(Inst::bin(
      arg.clone().to_var(),
      arg,
      match operator {
        OperatorName::PostfixDecrement => BinOp::Sub,
        OperatorName::PostfixIncrement => BinOp::Add,
        _ => unreachable!(),
      },
      Arg::Const(Const::Num(JsNumber(1.0))),
    ));
    Arg::Var(tmp_var)
  }

  pub fn compile_unary_expr(&mut self, UnaryExpr { operator, argument }: UnaryExpr) -> Arg {
    match operator {
      // Prefix increment/decrement.
      OperatorName::PrefixDecrement | OperatorName::PrefixIncrement => {
        let arg = self.compile_expr(argument, None);
        self.out.push(Inst::bin(
          arg.to_var(),
          arg,
          match operator {
            OperatorName::PrefixDecrement => BinOp::Sub,
            OperatorName::PrefixIncrement => BinOp::Add,
            _ => unreachable!(),
          },
          Arg::Const(Const::Num(JsNumber(1.0))),
        ));
        arg
      }
      // Other expressions.
      _ => {
        let op = match operator {
          OperatorName::UnaryNegation => UnOp::Neg,
          _ => unimplemented!(),
        };
        let arg = self.compile_expr(argument, None);
        let tmp = self.c_temp.bump();
        self.out.push(Inst::un(tmp, op, arg));
        Arg::Var(tmp)
      }
    }
  }

  pub fn compile_member_expr(&mut self, MemberExpr { optional_chaining, left, right }: MemberExpr, chain: impl Into<Option<Chain>>) -> CompiledMemberExpr {
    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    let left_arg = self.compile_expr(left, chain);
    // Handle `maybe_obj?.a`: skip access if nullish.
    self.conditional_chain_jump(optional_chaining, left_arg, chain);
    let res_tmp_var = self.c_temp.bump();
    let right_arg = Arg::Const(Const::Str(right.to_string()));
    self.out.push(Inst::bin(res_tmp_var, left_arg.clone(), BinOp::GetProp, right_arg));
    self.complete_chain_setup(did_chain_setup, res_tmp_var, chain);
    CompiledMemberExpr {
      res: Arg::Var(res_tmp_var),
      left: left_arg.clone(),
    }
  }

  pub fn compile_computed_member_expr(&mut self, ComputedMemberExpr { optional_chaining, object, member }: ComputedMemberExpr, chain: impl Into<Option<Chain>>) -> CompiledMemberExpr {
    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    let left_arg = self.compile_expr(object, chain);
    // Handle `maybe_obj?.["a"]`: skip access if nullish.
    self.conditional_chain_jump(optional_chaining, left_arg, chain);
    let res_tmp_var = self.c_temp.bump();
    // WARNING: The computed member expr does *not* use the same chain!
    let right_arg = self.compile_expr(member, None);
    self.out.push(Inst::bin(res_tmp_var, left_arg.clone(), BinOp::GetProp, right_arg));
    self.complete_chain_setup(did_chain_setup, res_tmp_var, chain);
    CompiledMemberExpr {
      res: Arg::Var(res_tmp_var),
      left: left_arg.clone(),
    }
  }

  pub fn compile_call_expr(&mut self, CallExpr { optional_chaining, callee, arguments }: CallExpr, chain: impl Into<Option<Chain>>) -> Arg {
    let (did_chain_setup, chain) = self.maybe_setup_chain(chain);
    // We need to handle methods specially due to `this`.
    let (this_arg, callee_arg) = match callee.stx {
      Expr::Member(m) => {
        let c = self.compile_member_expr(m, chain);
        (c.left, c.res)
      }
      Expr::ComputedMember(m) => {
        let c = self.compile_computed_member_expr(m, chain);
        (c.left, c.res)
      }
      _ => {
        let c = self.compile_expr(callee, chain);
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
    self.conditional_chain_jump(optional_chaining, callee_arg, chain);

    // Compile args.
    let mut args = Vec::new();
    let mut spreads = Vec::new();
    for a in arguments.into_iter() {
      let CallArg { spread: s, value } = a.stx;
      args.push(self.compile_arg(&value));
      if *s {
        spreads.push(args.len());
      }
    };
    // Make the call, collecting the result to `res_tmp_var`.
    self.out.push(Inst::call(
      res_tmp_var,
      callee_arg,
      this_arg,
      args,
      spreads,
    ));
    self.complete_chain_setup(did_chain_setup, res_tmp_var, chain);
    Arg::Var(res_tmp_var)
  }

  #[rustfmt::skip]
  pub fn compile_expr_with_chain(&mut self, n: Node<Expr>, chain: impl Into<Option<Chain>>) -> Arg {
    match n.stx.as_ref() {
      Expr::ArrowFunc(ArrowFuncExpr { func }) => self.compile_func(func),
      Expr::Call(n) => self.compile_call_expr(n, chain),
      Expr::ComputedMember(n) => self.compile_computed_member_expr(n, chain),
      Expr::Cond(n) => self.compile_cond_expr(n),
      Expr::Id(_) => self.compile_id_expr(n.try_into_stx().unwrap()),
      Expr::LitBool(n) => Arg::Const(Const::Bool(n.value)),
      Expr::LitNum(n) => Arg::Const(Const::Num(n.value)),
      Expr::LitStr(n) => Arg::Const(Const::Str(n.value)),
      Expr::Member(n) => self.compile_member_expr(n, chain),
    }
  }

  pub fn compile_expr(&mut self, n: Node<Expr>) -> Arg {
    self.compile_expr_with_chain(n, None)
  }
}
