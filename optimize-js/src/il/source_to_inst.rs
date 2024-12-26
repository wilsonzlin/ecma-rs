use crate::compile_js_statements;
use crate::eval::builtin::BUILTINS;
use crate::util::counter::Counter;
use crate::ProgramCompiler;

use super::inst::Arg;
use super::inst::BinOp;
use super::inst::Const;
use super::inst::Inst;
use super::inst::InstTyp;
use super::inst::UnOp;
use ahash::HashMap;
use ahash::HashMapExt;
use parse_js::ast::ClassOrObjectMemberKey;
use parse_js::ast::ForInit;
use parse_js::ast::node::Node;
use parse_js::ast::Syntax;
use parse_js::ast::VariableDeclarator;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use symbol_js::symbol::Scope;
use symbol_js::symbol::Symbol;
use std::collections::VecDeque;
use std::sync::atomic::Ordering;

// CondGoto fallthrough placeholder label.
pub const DUMMY_LABEL: u32 = u32::MAX;

struct SourceToInst<'program, 'c_temp, 'c_label> {
  program: &'program ProgramCompiler,
  out: Vec<Inst>,
  c_temp: &'c_temp mut Counter,
  c_label: &'c_label mut Counter,
  symbol_to_temp: HashMap<Symbol, u32>,
  break_stack: Vec<u32>, // Upon `break`, generate Inst::Goto to the label at the top of this stack.
}

enum VarType {
  Local(Symbol),
  Foreign(Symbol),
  Unknown(String),
  Builtin(String),
}

impl<'program, 'c_temp, 'c_label> SourceToInst<'program, 'c_temp, 'c_label> {
  fn var_type(&self, node: &Node, name: String) -> VarType {
    let scope = node.assoc.get::<Scope>().unwrap();
    // WARNING: Don't simply find_symbol_up_to_with_scope to nearest closure, as just because it's locally declared doesn't mean it's not a foreign.
    match scope.find_symbol(name.clone()) {
      Some(local_or_foreign) => if self.program.foreign_vars.contains(&local_or_foreign) {
        VarType::Foreign(local_or_foreign)
      } else {
        VarType::Local(local_or_foreign)
      },
      None => match BUILTINS.get(name.as_str()) {
        Some(_) => VarType::Builtin(name),
        None => VarType::Unknown(name),
      },
    }
  }

  fn symbol_to_temp(&mut self, sym: Symbol) -> u32 {
    *self
      .symbol_to_temp
      .entry(sym)
      .or_insert_with(|| self.c_temp.bump())
  }

  fn compile_arg(&mut self, n: &Node) -> Arg {
    match n.stx.as_ref() {
      Syntax::LiteralBooleanExpr { value } => Arg::Const(Const::Bool(*value)),
      Syntax::LiteralNumberExpr { value } => Arg::Const(Const::Num(*value)),
      Syntax::LiteralStringExpr { value } => Arg::Const(Const::Str(value.to_string())),
      // Recurse into expression.
      Syntax::ArrowFunctionExpr { .. }
      | Syntax::BinaryExpr { .. }
      | Syntax::CallExpr { .. }
      | Syntax::ConditionalExpr { .. }
      | Syntax::IdentifierExpr { .. }
      | Syntax::MemberExpr { .. }
      | Syntax::UnaryExpr { .. }
      | Syntax::UnaryPostfixExpr { .. } => {
        self.compile_expr(n);
        Arg::Var(self.out.last().unwrap().tgts[0])
      }
      n => panic!("unknown arg: {n:?}"),
    }
  }

  fn compile_expr(&mut self, n: &Node) {
    match n.stx.as_ref() {
      Syntax::ArrowFunctionExpr { parenthesised, function } => {
        self.compile_expr(function);
      }
      Syntax::Function { arrow, async_, generator, parameters, body } => {
        let pg = self.program.clone();
        let id = pg.next_fn_id.fetch_add(1, Ordering::Relaxed);
        // Unfortunately we can't use rayon::spawn because the node is borrowed. Everything else otherwise has 'static, including ProgramCompiler which is wrapped in an Arc.
        // TODO Maybe we should consume AST?
        rayon::scope(|s| {
          s.spawn(|_| {
            let wg = pg.wg.clone();
            // TODO params, arrow, async, etc.
            let Syntax::FunctionBody { body } = body.stx.as_ref() else {
              panic!();
            };
            let func = compile_js_statements(&pg, body);
            pg.functions.insert(id, func);
            drop(wg);
          });
        });
        // TODO This seems hacky, but our implementation requires that the last Inst in the `out` stack represents the value/target to use.
        let res_tmp_var = self.c_temp.bump();
        self.out.push(Inst::var_assign(res_tmp_var, Arg::Fn(id)));
      }
      // Due to conditional chaining requiring us to know the location after the entire chain (and not just a single node/subexpression), upon entry into any node that is possibly part of a chain, we run an inner algorithm that flattens the chain nodes and then compiles left to right.
      // TODO `(a?.b).c` is not the same as `a?.b.c`.
      Syntax::CallExpr { .. } | Syntax::MemberExpr { .. } | Syntax::ComputedMemberExpr { .. } => {
        let mut chain = Vec::new();
        let mut q = VecDeque::new();
        q.push_back(n);
        while let Some(n) = q.pop_front() {
          chain.push(n);
          match n.stx.as_ref() {
            Syntax::CallExpr { callee, .. } => {
              q.push_back(&*callee);
            }
            Syntax::MemberExpr { left, .. } => {
              q.push_back(&*left);
            }
            Syntax::ComputedMemberExpr { object, .. } => {
              q.push_back(&*object);
            }
            _ => {}
          };
        }
        chain.reverse();

        let after_chain_label_id = self.c_label.bump();
        // Optional chains result in undefined, whether null or undefined, so we CANNOT simply use the last non-nullish value in the chain.
        let set_as_undefined_label_id = self.c_label.bump();
        // This is the var that will store the result of our chain.
        // We must repeatedly assign to this target instead of creating new temporaries. Otherwise, consider `b?.c?.d?.e`. What's the target that the subsequent code can use for the result of this chain?
        let res_tmp_var = self.c_temp.bump();
        let mut did_optional_chaining = false;
        let mut last_last_arg = None;
        let mut last_arg = None;
        let mut prev_was_member = false;
        for n in chain {
          match n.stx.as_ref() {
            Syntax::MemberExpr {
              optional_chaining, ..
            }
            | Syntax::ComputedMemberExpr {
              optional_chaining, ..
            }
            | Syntax::CallExpr {
              optional_chaining, ..
            } if *optional_chaining => {
              did_optional_chaining = true;
              let is_undefined_tmp_var = self.c_temp.bump();
              self.out.push(Inst::bin(is_undefined_tmp_var, last_arg.clone().unwrap(), BinOp::LooseEq, Arg::Const(Const::Null)));
              self.out.push(Inst::cond_goto(Arg::Var(is_undefined_tmp_var), set_as_undefined_label_id, DUMMY_LABEL));
            }
            _ => {}
          };
          let next_arg = match n.stx.as_ref() {
            Syntax::MemberExpr { .. } | Syntax::ComputedMemberExpr { .. } => {
              let next_arg_tmp_var = self.c_temp.bump();
              let right_arg = match n.stx.as_ref() {
                Syntax::MemberExpr { right, .. } => Arg::Const(Const::Str(right.to_string())),
                Syntax::ComputedMemberExpr { member, .. } => self.compile_arg(&member),
                _ => unreachable!(),
              };
              self.out.push(Inst::bin(next_arg_tmp_var, last_arg.clone().unwrap(), BinOp::GetProp, right_arg));
              Arg::Var(next_arg_tmp_var)
            }
            Syntax::CallExpr { arguments, .. } => {
              let next_arg_tmp_var = self.c_temp.bump();
              let mut args = Vec::new();
              let mut spreads = Vec::new();
              for a in arguments.into_iter() {
                let Syntax::CallArg { spread: s, value } = a.stx.as_ref() else {
                  unreachable!();
                };
                args.push(self.compile_arg(&value));
                if *s {
                  spreads.push(args.len());
                }
              };
              self.out.push(Inst::call(next_arg_tmp_var, last_arg.clone().unwrap(),
              last_last_arg
                  .clone()
                  .filter(|_| prev_was_member)
                  .unwrap_or_else(|| Arg::Const(Const::Undefined)),
                args,
                spreads,
              ));
              Arg::Var(next_arg_tmp_var)
            }
            _ => self.compile_arg(n),
          };
          self.out.push(Inst::var_assign(res_tmp_var, next_arg.clone()));
          prev_was_member = match n.stx.as_ref() {
            Syntax::MemberExpr { .. } | Syntax::ComputedMemberExpr { .. } => true,
            _ => false,
          };
          last_last_arg = last_arg;
          last_arg = Some(next_arg);
        }
        if did_optional_chaining {
          // This is for when our chain is fully evaluated i.e. there was no short-circuiting due to optional chaining.
          self.out.push(Inst::goto(after_chain_label_id));
          self.out.push(Inst::label(set_as_undefined_label_id));
          self.out.push(Inst::var_assign(res_tmp_var, Arg::Const(Const::Undefined)));
          self.out.push(Inst::label(after_chain_label_id));
          // TODO This seems hacky, but our implementation requires that the last Inst in the `out` stack represents the value/target to use.
          self.out.push(Inst::var_assign(res_tmp_var, Arg::Var(res_tmp_var)));
        };
      }
      // This branch is rare, but can happen (e.g. redundant no-op statement like `a;`).
      Syntax::IdentifierExpr { name } => {
        let inst = match self.var_type(n, name.clone()) {
          // TODO This seems hacky, but our implementation requires that the last Inst in the `out` stack represents the value/target to use.
          VarType::Local(local) => Inst::var_assign(self.symbol_to_temp(local), Arg::Var(self.symbol_to_temp(local))),
          // TODO This seems hacky, but our implementation requires that the last Inst in the `out` stack represents the value/target to use.
          VarType::Builtin(builtin) => Inst::var_assign(self.c_temp.bump(), Arg::Builtin(builtin)),
          VarType::Foreign(foreign) => Inst::foreign_load(self.c_temp.bump(), foreign),
          VarType::Unknown(name) => Inst::unknown_load(self.c_temp.bump(), name),
        };
        self.out.push(inst);
      }
      Syntax::ConditionalExpr {
        test,
        consequent,
        alternate,
        ..
      } => {
        let res_tmp_var = self.c_temp.bump();
        let test_arg = self.compile_arg(&test);
        let cons_label_id = self.c_label.bump();
        let after_label_id = self.c_label.bump();
        self.out.push(Inst::cond_goto(test_arg, cons_label_id, DUMMY_LABEL));
        let alt_res = self.compile_arg(&alternate);
        self.out.push(Inst::var_assign(res_tmp_var, alt_res));
        self.out.push(Inst::goto(after_label_id));
        self.out.push(Inst::label(cons_label_id));
        let cons_res = self.compile_arg(&consequent);
        self.out.push(Inst::var_assign(res_tmp_var, cons_res));
        self.out.push(Inst::label(after_label_id));
        // TODO This seems hacky, but our implementation requires that the last Inst in the `out` stack represents the value/target to use.
        self.out.push(Inst::var_assign(res_tmp_var, Arg::Var(res_tmp_var)));
      }
      Syntax::UnaryPostfixExpr {
        operator, argument, ..
      } => {
        let arg = self.compile_arg(&argument);
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
        // TODO This seems hacky, but our implementation requires that the last Inst in the `out` stack represents the value/target to use.
        self.out.push(Inst::var_assign(tmp_var, Arg::Var(tmp_var)));
      }
      Syntax::UnaryExpr {
        operator, argument, ..
      } => {
        match operator {
          // Prefix increment/decrement.
          OperatorName::PrefixDecrement | OperatorName::PrefixIncrement => {
            let arg = self.compile_arg(&argument);
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
          }
          // Other expressions.
          _ => {
            let op = match operator {
              OperatorName::UnaryNegation => UnOp::Neg,
              _ => unimplemented!(),
            };
            let arg = self.compile_arg(&argument);
            self.out.push(Inst::un(self.c_temp.bump(),
              op,
              arg,
            ));
          }
        }
      }
      Syntax::BinaryExpr {
        operator,
        left,
        right,
        ..
      } => {
        // TODO Shorthand logic for `&&=` and `||=`.
        if operator.is_assignment()
          && !matches!(
            operator,
            OperatorName::AssignmentLogicalAnd | OperatorName::AssignmentLogicalOr
          )
        {
          // WARNING: We assume that the LHS of an assignment will never contain a conditional chaining anywhere in the chain, and that this is enforced at a previous stage (e.g. parsing).
          let dummy_val = Arg::Const(Const::Num(JsNumber(0xdeadbeefu32 as f64)));
          let mut ass_inst = match left.stx.as_ref() {
            Syntax::IdentifierPattern { name } => {
              let vartype = self.var_type(n, name.clone());
              match vartype {
                VarType::Local(l) => Inst::var_assign(
                  self.symbol_to_temp(l),
                  dummy_val, // This will be replaced later.
                ),
                VarType::Foreign(f) => Inst::foreign_store(
                  f,
                  dummy_val, // This will be replaced later.
                ),
                VarType::Unknown(n) => Inst::unknown_store(
                  n,
                  dummy_val, // This will be replaced later.
                ),
                VarType::Builtin(builtin) => panic!("assignment to builtin {builtin}"),
              }
            }
            Syntax::MemberExpr { left, right, .. } => {
              let left_arg = self.compile_arg(&left);
              Inst::prop_assign(
                left_arg,
                Arg::Const(Const::Str(right.to_string())),
                dummy_val, // This will be replaced later.
              )
            }
            Syntax::ComputedMemberExpr { object, member, .. } => {
              let left_arg = self.compile_arg(&object);
              let member_arg = self.compile_arg(&member);
              Inst::prop_assign(
                left_arg,
                member_arg,
                dummy_val, // This will be replaced later.
              )
            }
            _ => unreachable!(),
          };
          let mut value = self.compile_arg(&right);
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
          ass_inst.args[0] = value;
          self.out.push(ass_inst);
        } else if matches!(operator, OperatorName::LogicalAnd | OperatorName::LogicalOr) {
          let converge_label_id = self.c_label.bump();
          let res_tmp_var = self.c_temp.bump();
          let left = self.compile_arg(&left);
          self.out.push(Inst::var_assign(res_tmp_var, left.clone()));
          self.out.push(match operator {
            // Given `a && b`, skip `b` only if NOT `a`.
            OperatorName::LogicalAnd => Inst::cond_goto( left, DUMMY_LABEL,  converge_label_id),
            // Given `a || b`, skip `b` only IF `a`.
            OperatorName::LogicalOr => Inst::cond_goto( left,  converge_label_id, DUMMY_LABEL),
            _ => unreachable!(),
          });
          let right = self.compile_arg(&right);
          self.out.push(Inst::var_assign(res_tmp_var, right));
          self.out.push(Inst::label( converge_label_id));
          // TODO This seems hacky, but our implementation requires that the last Inst in the `out` stack represents the value/target to use.
          self.out.push(Inst::var_assign(res_tmp_var, Arg::Var(res_tmp_var)));
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
          let left = self.compile_arg(&left);
          let right = self.compile_arg(&right);
          self.out.push(Inst::bin(
            self.c_temp.bump(),
            left,
            op,
            right,
          ));
        }
      }
      n => panic!("not yet implemented: {n:?}"),
    };
  }

  // Handle `[a = 1] = x;` or `{b: c = 2} = y;`.
  fn compile_destructuring_via_prop(
    &mut self,
    obj: Arg,
    prop: Arg,
    target: &Node, // Pattern.
    default_value: Option<&Node>,
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
      let dv_arg = self.compile_arg(&dv);
      self.out.push(Inst::var_assign(
        tmp_var,
        dv_arg,
      ));
      self.out.push(Inst::label( after_label_id));
    };
    self.compile_destructuring(target, Arg::Var(tmp_var));
  }

  fn compile_destructuring(&mut self, pat: &Node, rval: Arg) {
    match pat.stx.as_ref() {
      Syntax::ArrayPattern { elements, rest } => {
        for (i, e) in elements.iter().enumerate() {
          let Some(e) = e else {
            continue;
          };
          self.compile_destructuring_via_prop(
            rval.clone(),
            Arg::Const(Const::Num(JsNumber(i as f64))),
            &e.target,
            e.default_value.as_ref(),
          );
        }
        // TODO `rest`.
      }
      Syntax::ObjectPattern { properties, rest } => {
        for p in properties {
          let Syntax::ObjectPatternProperty {
            key,
            target,
            default_value,
            ..
          } = p.stx.as_ref()
          else {
            unreachable!();
          };
          let prop = match key {
            ClassOrObjectMemberKey::Direct(d) => Arg::Const(Const::Str(d.to_string())),
            ClassOrObjectMemberKey::Computed(c) => self.compile_arg(c),
          };
          self.compile_destructuring_via_prop(rval.clone(), prop, target, default_value.as_ref());
        }
        // TODO `rest`.
      }
      Syntax::IdentifierPattern { name } => {
        // NOTE: It's possible to destructure-assign to ancestor scope vars (including globals), so just because this is a pattern doesn't mean it's for a local var.
        let inst = match self.var_type(pat, name.clone()) {
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

  fn compile_stmt(&mut self, n: &Node) {
    match n.stx.as_ref() {
      Syntax::BlockStmt { body } | Syntax::ForBody { body } => {
        for stmt in body {
          self.compile_stmt(stmt);
        }
      }
      Syntax::BreakStmt { label } => {
        // TODO Label.
        self.out.push(Inst::goto(*self.break_stack.last().unwrap()));
      }
      Syntax::ExpressionStmt { expression } => {
        self.compile_expr(expression);
      }
      Syntax::ForStmt {
        init,
        condition,
        post,
        body,
      } => {
        match init {
          ForInit::None => {}
          ForInit::Expression(e) => self.compile_expr(e),
          ForInit::Declaration(d) => self.compile_stmt(d),
        };
        let loop_entry_label = self.c_label.bump();
        let after_loop_label = self.c_label.bump();
        self.out.push(Inst::label( loop_entry_label));
        if let Some(condition) = condition {
          let cond_arg = self.compile_arg(&condition);
          self.out.push(Inst::cond_goto( cond_arg, DUMMY_LABEL,  after_loop_label));
        };
        self.break_stack.push(after_loop_label);
        self.compile_stmt(&body);
        self.break_stack.pop().unwrap();
        if let Some(post) = post {
          self.compile_expr(post);
        };
        self.out.push(Inst::goto( loop_entry_label,));
        self.out.push(Inst::label( after_loop_label));
      }
      Syntax::IfStmt {
        test,
        consequent,
        alternate,
      } => {
        let test_arg = self.compile_arg(&test);
        match alternate {
          Some(alternate) => {
            let cons_label_id = self.c_label.bump();
            let after_label_id = self.c_label.bump();
            self.out.push(Inst::cond_goto( test_arg,  cons_label_id, DUMMY_LABEL));
            self.compile_stmt(&alternate);
            self.out.push(Inst::goto( after_label_id,));
            self.out.push(Inst::label( cons_label_id));
            self.compile_stmt(&consequent);
            self.out.push(Inst::label( after_label_id));
          }
          None => {
            let after_label_id = self.c_label.bump();
            self.out.push(Inst::cond_goto( test_arg, DUMMY_LABEL,  after_label_id));
            self.compile_stmt(&consequent);
            self.out.push(Inst::label( after_label_id));
          }
        }
      }
      // TODO export.
      Syntax::VarDecl { declarators, .. } => {
        for VariableDeclarator {
          initializer,
          pattern,
        } in declarators
        {
          // TODO `initializer` must exist if `pattern` isn't IdentifierPattern (e.g. `var [a]; var {b};`).
          let Some(init) = initializer else {
            continue;
          };
          let tmp = self.c_temp.bump();
          let rval = self.compile_arg(&init);
          self.out.push(Inst::var_assign(tmp, rval));
          self.compile_destructuring(&pattern, Arg::Var(tmp));
        }
      }
      Syntax::WhileStmt { condition, body } => {
        let before_test_label = self.c_label.bump();
        let after_loop_label = self.c_label.bump();
        self.out.push(Inst::label( before_test_label));
        let test_arg = self.compile_arg(&condition);
        self.out.push(Inst::cond_goto( test_arg, DUMMY_LABEL,  after_loop_label));
        self.break_stack.push(after_loop_label);
        self.compile_stmt(body);
        self.break_stack.pop();
        self.out.push(Inst::goto( before_test_label));
        self.out.push(Inst::label( after_loop_label));
      }
      _ => unreachable!(),
    };
  }
}

impl ProgramCompiler {
  pub fn translate_source_to_inst(
    &self,
    stmts: &[Node],
    c_label: &mut Counter,
    c_temp: &mut Counter,
  ) -> Vec<Inst> {
    let mut compiler = SourceToInst {
      program: self,
      c_label,
      c_temp,
      out: Vec::new(),
      symbol_to_temp: HashMap::new(),
      break_stack: Vec::new(),
    };
    for stmt in stmts {
      compiler.compile_stmt(stmt);
    }
    compiler.out
  }

}
