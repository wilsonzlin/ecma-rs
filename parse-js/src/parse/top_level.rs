use super::expr::pat::ParsePatternRules;
use super::ParseCtx;
use super::Parser;
use crate::ast::node::Node;
use crate::ast::stx::TopLevel;
use crate::error::SyntaxResult;
use crate::token::TT;

impl<'a> Parser<'a> {
  pub fn parse_top_level(&mut self) -> SyntaxResult<Node<TopLevel>> {
    let ctx = ParseCtx {
      rules: ParsePatternRules {
        await_allowed: true,
        yield_allowed: true,
      },
      strict_mode: false,
      is_module: false,
      in_function: false,
      in_iteration: false,
      in_switch: false,
      in_single_statement: false,
    };
    let body = self.stmts(ctx, TT::EOF)?;
    self.require(TT::EOF)?;
    let top_level_node = Node::new(self.source_range(), TopLevel { body });
    Ok(top_level_node)
  }
  
  pub fn parse_module(&mut self) -> SyntaxResult<Node<TopLevel>> {
    let ctx = ParseCtx {
      rules: ParsePatternRules {
        await_allowed: false,  // await is reserved at module top level
        yield_allowed: true,
      },
      strict_mode: true,  // Modules are always in strict mode
      is_module: true,
      in_function: false,
      in_iteration: false,
      in_switch: false,
      in_single_statement: false,
    };
    let body = self.stmts(ctx, TT::EOF)?;
    self.require(TT::EOF)?;
    let top_level_node = Node::new(self.source_range(), TopLevel { body });
    Ok(top_level_node)
  }
}
