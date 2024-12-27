pub mod expr;
pub mod stmt;

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
use derive_visitor::Drive;
use derive_visitor::DriveMut;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::node::Node;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use symbol_js::symbol::Scope;
use symbol_js::symbol::Symbol;
use std::collections::VecDeque;
use std::sync::atomic::Ordering;

// CondGoto fallthrough placeholder label.
pub const DUMMY_LABEL: u32 = u32::MAX;

// Optional chains like `a.b?.c["d"]?.e.f?.().g` are tricky: we normally visit nodes in postorder (execution order), but conditional chaining means that any nullish property requires jumping out of the entire chain and setting the expr eval result to `undefined`. In the example, visiting the `CondMember { left: a.b, right: c }` node would need a jump past the root/tail `Call` node if `a.b == null`, something not visible to it.
// To solve this, whenever we visit a node that *could* be part of a chain, we check to see if `chain` is Some. If not, that node is the root/tail of the chain, and needs to set up the "escape hatch" on-nullish label, which is passed down so that child nodes can "see" and jump to it. The root/tail node is then the one responsible for setting up the label and its behaviour.
#[derive(Clone, Copy)]
struct Chain {
  // Optional chains result in undefined, not null or undefined, so we CANNOT simply use the last nullish value in the chain.
  is_nullish_label: u32,
}

struct SourceToInst<'p> {
  program: &'p ProgramCompiler,
  out: Vec<Inst>,
  c_temp: Counter,
  c_label: Counter,
  symbol_to_temp: HashMap<Symbol, u32>,
  // Upon `break`, generate Inst::Goto to the label at the top of this stack.
  break_stack: Vec<u32>,
}

enum VarType {
  Local(Symbol),
  Foreign(Symbol),
  Unknown(String),
  Builtin(String),
}

impl<'p> SourceToInst<'p> {
  fn var_type(&self, node_assoc: NodeAssocData, name: String) -> VarType {
    let scope = node_assoc.get::<Scope>().unwrap();
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
}

impl ProgramCompiler {
  pub fn translate_source_to_inst(&self, stmts: Vec<Node<Stmt>>) -> (Vec<Inst>, Counter, Counter) {
    let mut compiler = SourceToInst {
      program: self,
      // Label 0 is for entry.
      c_label: Counter::new(1),
      c_temp: Counter::new(0),
      out: Vec::new(),
      symbol_to_temp: HashMap::new(),
      break_stack: Vec::new(),
    };
    for stmt in stmts {
      compiler.compile_stmt(stmt);
    }
    (compiler.out, compiler.c_label, compiler.c_temp)
  }
}
