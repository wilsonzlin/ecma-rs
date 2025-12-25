pub mod expr;
pub mod stmt;

#[cfg(test)]
mod tests;

use super::inst::Inst;
use crate::eval::builtin::BUILTINS;
use crate::symbol::semantics::{assoc_resolved_symbol, SymbolId};
use crate::util::counter::Counter;
use crate::OptimizeResult;
use crate::ProgramCompiler;
use ahash::HashMap;
use ahash::HashMapExt;
use parse_js::ast::node::Node;
use parse_js::ast::node::NodeAssocData;
use parse_js::ast::stmt::Stmt;

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
  symbol_to_temp: HashMap<SymbolId, u32>,
  // Upon `break`, generate Inst::Goto to the label at the top of this stack.
  break_stack: Vec<u32>,
}

enum VarType {
  Local(SymbolId),
  Foreign(SymbolId),
  Unknown(String),
  Builtin(String),
}

impl<'p> SourceToInst<'p> {
  fn var_type(&self, node_assoc: NodeAssocData, name: String) -> VarType {
    match assoc_resolved_symbol(&node_assoc) {
      Some(sym) => {
        if self.program.foreign_vars.contains(&sym) {
          VarType::Foreign(sym)
        } else {
          VarType::Local(sym)
        }
      }
      None => match BUILTINS.get(name.as_str()) {
        Some(_) => VarType::Builtin(name),
        None => VarType::Unknown(name),
      },
    }
  }

  fn symbol_to_temp(&mut self, sym: SymbolId) -> u32 {
    *self
      .symbol_to_temp
      .entry(sym)
      .or_insert_with(|| self.c_temp.bump())
  }
}

impl ProgramCompiler {
  pub fn translate_source_to_inst(
    &self,
    stmts: Vec<Node<Stmt>>,
  ) -> OptimizeResult<(Vec<Inst>, Counter, Counter)> {
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
      compiler.compile_stmt(stmt)?;
    }
    Ok((compiler.out, compiler.c_label, compiler.c_temp))
  }
}
