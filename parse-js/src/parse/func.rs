use super::ParseCtx;
use super::Parser;
use crate::ast::node::Node;
use crate::ast::stmt::decl::ParamDecl;
use crate::ast::stmt::Stmt;
use crate::error::SyntaxResult;
use crate::token::TT;

impl<'a> Parser<'a> {
  // `scope` should be a newly created closure scope for this function.
  pub fn func_params(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<ParamDecl>>> {
    self.require(TT::ParenthesisOpen)?;
    let parameters = self.list_with_loc(
      TT::Comma,
      TT::ParenthesisClose,
      |p| {
        let rest = p.consume_if(TT::DotDotDot).is_match();
        let pattern = p.pat_decl(ctx)?;
        let default_value = p.consume_if(TT::Equals)
          .and_then(|| {
            p.expr(ctx, [TT::Comma, TT::ParenthesisClose])
          })?;
        Ok(ParamDecl {
          rest,
          pattern,
          default_value,
        })
      },
    )?;
    Ok(parameters)
  }

  pub fn parse_func_block_body(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<Stmt>>> {
    self.require(TT::BraceOpen)?;
    let body = self.stmts(ctx, TT::BraceClose)?;
    self.require(TT::BraceClose)?;
    Ok(body)
  }
}
