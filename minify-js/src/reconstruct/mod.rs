pub mod usage;

use optimize_js::analysis::find_conds::find_conds;
use optimize_js::analysis::find_loops::find_loops;
use optimize_js::analysis::interference::calculate_interference_graph;
use optimize_js::analysis::liveness::calculate_live_ins;
use optimize_js::analysis::registers::allocate_registers;
use optimize_js::analysis::registers::{self};
use optimize_js::analysis::single_use_insts::analyse_single_use_defs;
use optimize_js::dom::Dom;
use optimize_js::dom::PostDom;
use optimize_js::il::inst::Arg;
use optimize_js::il::inst::Const;
use optimize_js::Program;
use optimize_js::ProgramFunction;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;

fn reconstruct_fn(f: ProgramFunction) -> Node {
  let cfg = f.body;
  let (inlines, inlined_tgts) = analyse_single_use_defs(&cfg);
  let liveness = calculate_live_ins(&cfg, &inlines, &inlined_tgts);
  let intgraph = calculate_interference_graph(&liveness);
  let var_alloc = allocate_registers(&intgraph);

  let dom = Dom::calculate(&cfg);
  let postdom = PostDom::calculate(&cfg);
  let loops = find_loops(&cfg, &dom);
  let conds = find_conds(&cfg, &dom, &postdom);
  todo!()
}

pub(crate) fn reconstruct_ast_from_program(pg: Program) -> Node {
  fn arg_to_expr(arg: &Arg) -> Node {
    let stx = match arg {
      Arg::Builtin(v) => todo!(),
      Arg::Const(v) => match v {
        Const::BigInt(v) => todo!(),
        Const::Bool(v) => todo!(),
        Const::Null => Syntax::LiteralNull {},
        Const::Num(v) => Syntax::LiteralNumberExpr { value: *v },
        Const::Str(v) => todo!(),
        Const::Undefined => todo!(),
      },
      Arg::Fn(id) => todo!(),
      // TODO
      Arg::Var(v) => Syntax::IdentifierExpr {
        name: format!("tmp{v}"),
      },
    };
    Node::new(Loc(0, 0), stx)
  }
  let bblock = pg.top_level.body.bblocks.get(0);
  let mut stmts = Vec::new();
  for inst in bblock {
    let stx = match inst {
      Inst::Bin {
        tgt,
        left,
        op,
        right,
      } => {
        let operator = match op {
          BinOp::Add => OperatorName::Addition,
          BinOp::Div => OperatorName::Division,
          BinOp::Exp => OperatorName::Exponentiation,
          BinOp::Geq => OperatorName::GreaterThanOrEqual,
          BinOp::GetProp => todo!(),
          BinOp::Gt => OperatorName::GreaterThan,
          BinOp::Leq => OperatorName::LessThanOrEqual,
          BinOp::LooseEq => OperatorName::Equality,
          BinOp::Lt => OperatorName::LessThan,
          BinOp::Mod => OperatorName::Remainder,
          BinOp::Mul => OperatorName::Multiplication,
          BinOp::NotLooseEq => OperatorName::Inequality,
          BinOp::NotStrictEq => OperatorName::StrictInequality,
          BinOp::StrictEq => OperatorName::StrictEquality,
          BinOp::Sub => OperatorName::Subtraction,
        };
        Syntax::BinaryExpr {
          parenthesised: false, // TODO
          operator: OperatorName::Assignment,
          left: Node::new(Loc(0, 0), Syntax::IdentifierPattern {
            name: format!("tmp{tgt}"), // TODO
          }),
          right: Node::new(Loc(0, 0), Syntax::BinaryExpr {
            left: arg_to_expr(left),
            operator,
            parenthesised: false, // TODO
            right: arg_to_expr(right),
          }),
        }
      }
      Inst::Un { tgt, arg, op } => {
        let operator = match op {
          UnOp::Neg => OperatorName::UnaryNegation,
          UnOp::Not => OperatorName::LogicalNot,
          UnOp::Plus => OperatorName::UnaryPlus,
          UnOp::Typeof => OperatorName::Typeof,
          UnOp::Void => OperatorName::Void,
        };
        Syntax::UnaryExpr {
          parenthesised: false, // TODO
          operator,
          argument: arg_to_expr(arg),
        }
      }
      Inst::VarAssign { tgt, value } => {
        Syntax::BinaryExpr {
          parenthesised: false, // TODO
          operator: OperatorName::Assignment,
          left: Node::new(Loc(0, 0), Syntax::IdentifierPattern {
            name: format!("tmp{tgt}"), // TODO
          }),
          right: arg_to_expr(value),
        }
      }
      Inst::UnknownLoad { from, to } => {
        Syntax::BinaryExpr {
          parenthesised: false, // TODO
          operator: OperatorName::Assignment,
          left: Node::new(Loc(0, 0), Syntax::IdentifierPattern {
            name: format!("tmp{to}"),
          }), // TODO
          right: Node::new(Loc(0, 0), Syntax::IdentifierPattern { name: from.clone() }),
        }
      }
      Inst::UnknownStore { from, to } => {
        Syntax::BinaryExpr {
          parenthesised: false, // TODO
          operator: OperatorName::Assignment,
          left: Node::new(Loc(0, 0), Syntax::IdentifierPattern { name: to.clone() }),
          right: arg_to_expr(from),
        }
      }
      t => panic!("unimplemented: {:?}", t),
    };
    let n_expr = Node::new(Loc(0, 0), stx);
    let n_stmt = Node::new(Loc(0, 0), Syntax::ExpressionStmt { expression: n_expr });
    stmts.push(n_stmt);
  }
  Node::new(Loc(0, 0), Syntax::TopLevel { body: stmts })
}
