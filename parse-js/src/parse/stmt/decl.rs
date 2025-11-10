use super::ParseCtx;
use super::Parser;
use crate::ast::stmt::decl::ClassDecl;
use crate::ast::stmt::decl::FuncDecl;
use crate::ast::stmt::decl::PatDecl;
use crate::ast::stmt::decl::VarDecl;
use crate::ast::stmt::decl::VarDeclMode;
use crate::ast::stmt::decl::VarDeclarator;
use crate::ast::func::Func;
use crate::ast::node::Node;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::parse::expr::pat::ParsePatternRules;
use crate::parse::expr::Asi;
use crate::token::TT;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum VarDeclParseMode {
  // Standard parsing mode for var/let/const statement.
  Asi,
  // Parse as many valid declarators as possible, then break before the first invalid token (i.e. not a comma). Used by for-loop parser.
  Leftmost,
}

impl<'a> Parser<'a> {
  pub fn pat_decl(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<PatDecl>> {
    self.with_loc(|p| {
      let pat = p.pat(ctx)?;
      Ok(PatDecl { pat })
    })
  }

  pub fn id_pat_decl(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<PatDecl>> {
    self.with_loc(|p| {
      let pat = p.id_pat(ctx)?.into_wrapped();
      Ok(PatDecl { pat })
    })
  }

  pub fn var_decl_mode(&mut self) -> SyntaxResult<VarDeclMode> {
    let t = self.consume();
    Ok(match t.typ {
      TT::KeywordLet => VarDeclMode::Let,
      TT::KeywordConst => VarDeclMode::Const,
      TT::KeywordVar => VarDeclMode::Var,
      _ => return Err(t.error(SyntaxErrorType::ExpectedSyntax("variable declaration"))),
    })
  }

  /// Parses a variable declaration, which contains one or more declarators, each with an optional initializer. Examples of variable declarations:
  /// - `const a = 1`
  /// - `let a, b = 2, c`
  /// - `let a = 1, b = 2`
  /// - `var a`
  /// - `var a, b`
  pub fn var_decl(
    &mut self,
    ctx: ParseCtx,
    parse_mode: VarDeclParseMode,
  ) -> SyntaxResult<Node<VarDecl>> {
    self.with_loc(|p| {
      let export = p.consume_if(TT::KeywordExport).is_match();
      let mode = p.var_decl_mode()?;
      let mut declarators = Vec::new();
      loop {
        let pattern = p.pat_decl(ctx)?;

        // TypeScript: type annotation
        let type_annotation = if p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr(ctx)?)
        } else {
          None
        };

        let mut asi = match parse_mode {
          VarDeclParseMode::Asi => Asi::can(),
          VarDeclParseMode::Leftmost => Asi::no(),
        };
        let initializer = p.consume_if(TT::Equals)
          .and_then(|| p.expr_with_asi(
            ctx,
            [TT::Semicolon, TT::Comma],
            &mut asi,
          ))?;
        declarators.push(VarDeclarator {
          pattern,
          type_annotation,
          initializer,
        });
        match parse_mode {
          VarDeclParseMode::Asi => {
            if p.consume_if(TT::Semicolon).is_match() || asi.did_end_with_asi {
              break;
            }
            let t = p.peek();
            if t.typ == TT::EOF || t.typ == TT::BraceClose || (t.preceded_by_line_terminator && t.typ != TT::Comma) {
              break;
            };
            p.require(TT::Comma)?;
          }
          VarDeclParseMode::Leftmost => {
            if !p.consume_if(TT::Comma).is_match() {
              break;
            }
          }
        }
      }
      Ok(VarDecl {
        export,
        mode,
        declarators,
      })
    })
  }

  pub fn func_decl(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<Node<FuncDecl>> {
    self.with_loc(|p| {
      let export = p.consume_if(TT::KeywordExport).is_match();
      let export_default = export && p.consume_if(TT::KeywordDefault).is_match();
      let is_async = p.consume_if(TT::KeywordAsync).is_match();
      let start = p.require(TT::KeywordFunction)?.loc;
      let generator = p.consume_if(TT::Asterisk).is_match();
      // Function name is always parsed with yield/await allowed as identifiers,
      // even for generator/async functions (the function can be named "yield" or "await")
      let name_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: true,
        yield_allowed: true,
      });
      let name = p.maybe_class_or_func_name(name_ctx);
      // The name can only be omitted in default exports.
      if name.is_none() && !export_default {
        return Err(start.error(SyntaxErrorType::ExpectedSyntax("function name"), None));
      };
      let function = p.with_loc(|p| {
        // TypeScript: generic type parameters
        let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
          Some(p.type_parameters(ctx)?)
        } else {
          None
        };
        // Parameters and body use the function's own context, not the parent's
        let fn_ctx = ctx.with_rules(ParsePatternRules {
          await_allowed: !is_async && ctx.rules.await_allowed,
          yield_allowed: !generator && ctx.rules.yield_allowed,
        });
        let parameters = p.func_params(fn_ctx)?;
        // TypeScript: return type annotation (may be type predicate)
        let return_type = if p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr_or_predicate(ctx)?)
        } else {
          None
        };
        let body = p.parse_func_block_body(fn_ctx)?.into();
        Ok(Func {
          arrow: false,
          async_: is_async,
          generator,
          type_parameters,
          parameters,
          return_type,
          body,
        })
      })?;
      Ok(FuncDecl {
        export,
        export_default,
        name,
        function,
      })
    })
  }

  pub fn class_decl(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<Node<ClassDecl>> {
    self.with_loc(|p| {
      // TypeScript: parse decorators before export/class
      let decorators = p.decorators(ctx)?;

      let export = p.consume_if(TT::KeywordExport).is_match();
      let export_default = export && p.consume_if(TT::KeywordDefault).is_match();
      // TypeScript: abstract keyword
      let abstract_ = p.consume_if(TT::KeywordAbstract).is_match();
      let start = p.require(TT::KeywordClass)?.loc;
      // Names can be omitted only in default exports.
      let name = p.maybe_class_or_func_name(ctx);
      if name.is_none() && !export_default {
        return Err(start.error(SyntaxErrorType::ExpectedSyntax("class name"), None));
      };

      // TypeScript: generic type parameters
      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      // Unlike functions, classes are scoped to their block.
      let extends = if p.consume_if(TT::KeywordExtends).is_match() {
        Some(p.expr(ctx, [TT::BraceOpen, TT::KeywordImplements])?)
      } else {
        None
      };

      // TypeScript: implements clause
      let mut implements = Vec::new();
      if p.consume_if(TT::KeywordImplements).is_match() {
        loop {
          implements.push(p.type_expr(ctx)?);
          if !p.consume_if(TT::Comma).is_match() {
            break;
          }
        }
      }

      let members = p.class_body(ctx)?;
      Ok(ClassDecl {
        decorators,
        export,
        export_default,
        abstract_,
        name,
        type_parameters,
        extends,
        implements,
        members,
      })
    })
  }
}
