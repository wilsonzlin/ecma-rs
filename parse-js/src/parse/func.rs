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
        // TypeScript: check for `this` parameter (can only be first parameter)
        // Syntax: `this: Type`
        if p.peek().typ == TT::KeywordThis {
          let [_, next] = p.peek_n::<2>();
          if next.typ == TT::Colon {
            // This is a `this` parameter
            p.consume(); // consume 'this'
            p.require(TT::Colon)?;
            let type_annotation = Some(p.type_expr(ctx)?);
            // Create a pseudo-pattern for the `this` parameter
            use crate::ast::expr::pat::{IdPat, Pat};
            use crate::ast::stmt::decl::PatDecl;
            use crate::loc::Loc;
            let this_pattern = Node::new(
              Loc(0, 0),
              PatDecl {
                pat: Node::new(
                  Loc(0, 0),
                  Pat::Id(Node::new(
                    Loc(0, 0),
                    IdPat {
                      name: String::from("this"),
                    },
                  )),
                ),
              },
            );
            return Ok(ParamDecl {
              decorators: Vec::new(),
              rest: false,
              optional: false,
              accessibility: None,
              readonly: false,
              pattern: this_pattern,
              type_annotation,
              default_value: None,
            });
          }
        }

        // TypeScript: parse decorators for parameters (before modifiers)
        let mut decorators = p.decorators(ctx)?;

        // TypeScript: accessibility modifiers and readonly can appear in either order
        // e.g. `readonly public x` or `public readonly x` are both valid
        // Error recovery: allow duplicate modifiers
        let mut accessibility = None;
        let mut readonly = false;

        // Parse modifiers in a loop to allow duplicates
        loop {
          let mut found_modifier = false;

          // Try readonly
          if p.consume_if(TT::KeywordReadonly).is_match() {
            readonly = true;
            found_modifier = true;
          }

          // Try accessibility
          if p.consume_if(TT::KeywordPublic).is_match() {
            accessibility = Some(Accessibility::Public);
            found_modifier = true;
          } else if p.consume_if(TT::KeywordPrivate).is_match() {
            accessibility = Some(Accessibility::Private);
            found_modifier = true;
          } else if p.consume_if(TT::KeywordProtected).is_match() {
            accessibility = Some(Accessibility::Protected);
            found_modifier = true;
          }

          if !found_modifier {
            break;
          }
        }

        // TypeScript: Also allow decorators after modifiers for error recovery
        // e.g. `public @dec p` in addition to `@dec public p`
        if p.peek().typ == TT::At {
          let post_modifiers_decorators = p.decorators(ctx)?;
          decorators.extend(post_modifiers_decorators);
        }

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
          decorators,
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
