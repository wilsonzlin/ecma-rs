use super::ParseCtx;
use super::Parser;
use crate::ast::node::Node;
use crate::ast::stmt::decl::{Accessibility, ParamDecl};
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
        // TypeScript: accessibility modifiers
        let accessibility = if p.consume_if(TT::KeywordPublic).is_match() {
          Some(Accessibility::Public)
        } else if p.consume_if(TT::KeywordPrivate).is_match() {
          Some(Accessibility::Private)
        } else if p.consume_if(TT::KeywordProtected).is_match() {
          Some(Accessibility::Protected)
        } else {
          None
        };

        // TypeScript: readonly modifier
        let readonly = p.consume_if(TT::KeywordReadonly).is_match();

        let rest = p.consume_if(TT::DotDotDot).is_match();
        let pattern = p.pat_decl(ctx)?;

        // TypeScript: optional parameter
        let optional = p.consume_if(TT::Question).is_match();

        // TypeScript: type annotation
        let type_annotation = if p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr(ctx)?)
        } else {
          None
        };

        let default_value = p.consume_if(TT::Equals)
          .and_then(|| {
            p.expr(ctx, [TT::Comma, TT::ParenthesisClose])
          })?;

        Ok(ParamDecl {
          rest,
          optional,
          accessibility,
          readonly,
          pattern,
          type_annotation,
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
