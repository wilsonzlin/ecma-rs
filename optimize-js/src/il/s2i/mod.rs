pub mod expr;
pub mod stmt;

#[cfg(test)]
mod tests;

use super::inst::Inst;
use crate::eval::builtin::BUILTINS;
use crate::symbol::semantics::SymbolId;
use crate::util::counter::Counter;
use crate::ProgramCompiler;
use ahash::HashMap;
use ahash::HashMapExt;
use hir_js::{Body, BodyId, ExprId, NameId, PatId};

// CondGoto fallthrough placeholder label.
pub const DUMMY_LABEL: u32 = u32::MAX;

// Optional chains like `a.b?.c["d"]?.e.f?.().g` are tricky: we normally visit nodes in postorder (execution order), but conditional chaining means that any nullish property requires jumping out of the entire chain and setting the expr eval result to `undefined`. In the example, visiting the `CondMember { left: a.b, right: c }` node would need a jump past the root/tail `Call` node if `a.b == null`, something not visible to it.
// To solve this, whenever we visit a node that *could* be part of a chain, we check to see if `chain` is Some. If not, that node is the root/tail of the chain, and needs to set up the "escape hatch" on-nullish label, which is passed down so that child nodes can "see" and jump to it. The root/tail node is then the one responsible for setting up the label and its behaviour.
#[derive(Clone, Copy)]
pub struct Chain {
  // Optional chains result in undefined, not null or undefined, so we CANNOT simply use the last nullish value in the chain.
  pub is_nullish_label: u32,
}

pub enum VarType {
  Local(SymbolId),
  Foreign(SymbolId),
  Unknown(String),
  Builtin(String),
}

pub struct HirSourceToInst<'p> {
  pub program: &'p ProgramCompiler,
  pub body_id: BodyId,
  pub body: &'p Body,
  pub out: Vec<Inst>,
  pub c_temp: Counter,
  pub c_label: Counter,
  pub symbol_to_temp: HashMap<SymbolId, u32>,
  pub break_stack: Vec<u32>,
}

impl<'p> HirSourceToInst<'p> {
  pub fn new(program: &'p ProgramCompiler, body_id: BodyId) -> Self {
    let body = program.body(body_id);
    Self {
      program,
      body_id,
      body,
      // Label 0 is for entry.
      c_label: Counter::new(1),
      c_temp: Counter::new(0),
      out: Vec::new(),
      symbol_to_temp: HashMap::new(),
      break_stack: Vec::new(),
    }
  }

  pub fn symbol_to_temp(&mut self, sym: SymbolId) -> u32 {
    *self
      .symbol_to_temp
      .entry(sym)
      .or_insert_with(|| self.c_temp.bump())
  }

  pub fn name_for(&self, name: NameId) -> String {
    self.program.name_for(name)
  }

  pub fn symbol_for_expr(&self, expr: ExprId) -> Option<SymbolId> {
    self.program.symbol_for_expr(self.body_id, expr)
  }

  pub fn symbol_for_pat(&self, pat: PatId) -> Option<SymbolId> {
    let sym = self.program.symbol_for_pat(self.body_id, pat);
    #[cfg(test)]
    if sym.is_none() {
      eprintln!(
        "missing symbol for pat {:?} in body {:?} span {:?}",
        pat, self.body_id, self.body.pats[pat.0 as usize].span
      );
    }
    sym
  }

  pub fn classify_symbol(&self, symbol: Option<SymbolId>, name: String) -> VarType {
    match symbol {
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

  pub fn bool_literal_expr(&self, expr: ExprId) -> Option<bool> {
    self.program.types.bool_literal_expr(self.body_id, expr)
  }

  pub fn expr_excludes_nullish(&self, expr: ExprId) -> bool {
    self.program.types.expr_excludes_nullish(self.body_id, expr)
  }

  pub fn typeof_string_expr(&self, expr: ExprId) -> Option<&'static str> {
    self.program.types.expr_typeof_string(self.body_id, expr)
  }
}
