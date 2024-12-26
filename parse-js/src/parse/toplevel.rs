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
    };
    let body = self.stmts(ctx, TT::EOF)?;
    self.require(TT::EOF)?;
    let top_level_node = Node::new(self.source_range(), TopLevel { body });
    Ok(top_level_node)
  }
}
