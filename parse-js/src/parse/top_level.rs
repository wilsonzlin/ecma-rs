use super::expr::pat::ParsePatternRules;
use super::ParseCtx;
use super::Parser;
use crate::ast::node::Node;
use crate::ast::stx::TopLevel;
use crate::error::SyntaxResult;
use crate::token::TT;

impl<'a> Parser<'a> {
  pub fn parse_top_level(&mut self) -> SyntaxResult<Node<TopLevel>> {
    let is_module = self.is_module();
    let ctx = ParseCtx {
      rules: ParsePatternRules {
        await_allowed: !is_module,
        yield_allowed: !is_module,
        await_expr_allowed: is_module,
        yield_expr_allowed: false,
      },
      top_level: true,
      in_namespace: false,
      asi: super::AsiContext::Statements,
    };
    let body = self.stmts(ctx, TT::EOF)?;
    self.require(TT::EOF)?;
    let top_level_node = Node::new(self.source_range(), TopLevel { body });
    Ok(top_level_node)
  }
}
