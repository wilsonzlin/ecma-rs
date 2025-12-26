#[path = "expr.rs"]
pub mod expr;
#[path = "stmt.rs"]
pub mod stmt;

pub use super::DUMMY_LABEL;
use crate::eval::builtin::BUILTINS;
use crate::il::inst::Inst;
use crate::symbol::semantics::{assoc_resolved_symbol, SymbolId};
use crate::util::counter::Counter;
use crate::{build_program_function, OptimizeResult, ProgramCompiler};
use ahash::{HashMap, HashMapExt};
use parse_js::ast::node::{Node, NodeAssocData};
use parse_js::ast::stmt::Stmt;

#[derive(Clone, Copy)]
pub struct Chain {
  pub is_nullish_label: u32,
}

pub struct SourceToInst<'p> {
  pub program: &'p ProgramCompiler,
  pub out: Vec<Inst>,
  pub c_temp: Counter,
  pub c_label: Counter,
  pub symbol_to_temp: HashMap<SymbolId, u32>,
  pub break_stack: Vec<u32>,
}

pub enum VarType {
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

pub fn translate_source_to_inst(
  program: &ProgramCompiler,
  stmts: Vec<Node<Stmt>>,
) -> OptimizeResult<(Vec<Inst>, Counter, Counter)> {
  let mut compiler = SourceToInst {
    program,
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

pub fn compile_js_statements(
  program: &ProgramCompiler,
  stmts: Vec<Node<Stmt>>,
) -> OptimizeResult<crate::ProgramFunction> {
  let (insts, c_label, c_temp) = translate_source_to_inst(program, stmts)?;
  Ok(build_program_function(program, insts, c_label, c_temp))
}
