pub mod decl;

use decl::VarDeclParseMode;

use super::expr::pat::is_valid_pattern_identifier;
use super::expr::Asi;
use super::ParseCtx;
use super::Parser;
use crate::ast::node::Node;
use crate::ast::stmt::BlockStmt;
use crate::ast::stmt::BreakStmt;
use crate::ast::stmt::CatchBlock;
use crate::ast::stmt::ContinueStmt;
use crate::ast::stmt::DebuggerStmt;
use crate::ast::stmt::DoWhileStmt;
use crate::ast::stmt::EmptyStmt;
use crate::ast::stmt::ExprStmt;
use crate::ast::stmt::ForBody;
use crate::ast::stmt::ForInOfLhs;
use crate::ast::stmt::ForInStmt;
use crate::ast::stmt::ForOfStmt;
use crate::ast::stmt::ForTripleStmt;
use crate::ast::stmt::ForTripleStmtInit;
use crate::ast::stmt::IfStmt;
use crate::ast::stmt::LabelStmt;
use crate::ast::stmt::ReturnStmt;
use crate::ast::stmt::Stmt;
use crate::ast::stmt::SwitchBranch;
use crate::ast::stmt::SwitchStmt;
use crate::ast::stmt::ThrowStmt;
use crate::ast::stmt::TryStmt;
use crate::ast::stmt::WhileStmt;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::token::TT;

impl<'a> Parser<'a> {
  pub fn stmts(&mut self, ctx: ParseCtx, end: TT) -> SyntaxResult<Vec<Node<Stmt>>> {
    self.repeat_until_tt(end, |p| p.stmt(ctx))
  }

  pub fn stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    let (t0, t1) = self.peek_2();
    #[rustfmt::skip]
    let stmt: Node<Stmt> = match t0.typ {
      TT::BraceOpen => self.block_stmt(ctx)?.into_stx(),
      TT::KeywordBreak => self.break_stmt(ctx)?.into_stx(),
      TT::KeywordClass => self.class_decl(ctx)?.into_stx(),
      TT::KeywordConst | TT::KeywordLet | TT::KeywordVar => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_stx(),
      TT::KeywordContinue => self.continue_stmt(ctx)?.into_stx(),
      TT::KeywordDebugger => self.debugger_stmt()?.into_stx(),
      TT::KeywordDo => self.do_while_stmt(ctx)?.into_stx(),
      TT::KeywordExport => self.export_stmt(ctx)?.into_stx(),
      TT::KeywordFor => self.for_stmt(ctx)?.into_stx(),
      TT::KeywordAsync | TT::KeywordFunction => self.func_decl(ctx)?.into_stx(),
      TT::KeywordIf => self.if_stmt(ctx)?.into_stx(),
      TT::KeywordImport if t1.typ != TT::ParenthesisOpen => self.import_stmt(ctx)?.into_stx(),
      TT::KeywordReturn => self.return_stmt(ctx)?.into_stx(),
      TT::KeywordSwitch => self.switch_stmt(ctx)?.into_stx(),
      TT::KeywordThrow => self.throw_stmt(ctx)?.into_stx(),
      TT::KeywordTry => self.try_stmt(ctx)?.into_stx(),
      TT::KeywordWhile => self.while_stmt(ctx)?.into_stx(),
      TT::Semicolon => self.empty_stmt()?.into_stx(),
      t if is_valid_pattern_identifier(t, ctx.rules) && t1.typ == TT::Colon => self.label_stmt(ctx)?.into_stx(),
      _ => self.expr_stmt(ctx)?.into_stx(),
    };
    Ok(stmt)
  }

  pub fn label_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LabelStmt>> {
    self.with_loc(|p| {
      let label_name = p.consume_as_string();
      p.require(TT::Colon)?;
      let statement = p.stmt(ctx)?;
      Ok(LabelStmt {
        name: label_name,
        statement,
      })
    })
  }

  pub fn empty_stmt(&mut self) -> SyntaxResult<Node<EmptyStmt>> {
    self.with_loc(|p| {
      p.require(TT::Semicolon).map(|_| EmptyStmt {})
    })
  }

  pub fn block_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<BlockStmt>> {
    self.with_loc(|p| {
      p.require(TT::BraceOpen)?;
      let body = p.stmts(ctx, TT::BraceClose)?;
      p.require(TT::BraceClose)?;
      Ok(BlockStmt { body })
    })
  }

  fn break_or_continue_label(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<Option<String>> {
    let t = self.peek();
    let label =
      if is_valid_pattern_identifier(t.typ, ctx.rules) && !t.preceded_by_line_terminator {
        // Label.
        Some(self.consume_as_string())
      } else if t.typ == TT::Semicolon {
        self.consume();
        None
      } else if t.preceded_by_line_terminator || t.typ == TT::BraceClose {
        // ASI.
        None
      } else {
        return Err(t.error(SyntaxErrorType::ExpectedSyntax("label")));
      };
    Ok(label)
  }

  pub fn break_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<BreakStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordBreak)?;
      let label = p.break_or_continue_label(ctx)?;
      Ok(BreakStmt { label })
    })
  }

  pub fn continue_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ContinueStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordContinue)?;
      let label = p.break_or_continue_label(ctx)?;
      Ok(ContinueStmt { label })
    })
  }

  pub fn debugger_stmt(&mut self) -> SyntaxResult<Node<DebuggerStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordDebugger).map(|_| DebuggerStmt {})
    })
  }

  // WARNING: Do not reuse this functions for other statements, as this will output a statement node, not an expression, which can lead to double semicolons that cause invalid code when outputting.
  pub fn expr_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ExprStmt>> {
    self.with_loc(|p| {
      let mut asi = Asi::can();
      let expr = p.expr_with_asi(ctx, [TT::Semicolon], &mut asi)?;
      if !asi.did_end_with_asi {
        p.require(TT::Semicolon)?;
      };
      Ok(ExprStmt {
        expr,
      })
    })
  }

  fn for_body(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ForBody>> {
     self.with_loc(|p| {
      if p.peek().typ == TT::BraceOpen {
        // Block.
        p.require(TT::BraceOpen)?;
        let body = p.stmts(ctx, TT::BraceClose)?;
        p.require(TT::BraceClose)?;
        Ok(ForBody { body })
      } else {
        // Single statement.
        Ok(ForBody { body: vec![p.stmt(ctx)?] })
      }
    })
  }

  pub fn for_triple_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ForTripleStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordFor)?;
      p.require(TT::ParenthesisOpen)?;
      let init = match p.peek().typ {
        TT::KeywordVar | TT::KeywordLet | TT::KeywordConst => ForTripleStmtInit::Decl(p.var_decl(ctx, VarDeclParseMode::Leftmost)?),
        TT::Semicolon => ForTripleStmtInit::None,
        _ => ForTripleStmtInit::Expr(p.expr(ctx, [TT::Semicolon])?),
      };
      p.require(TT::Semicolon)?;
      let cond = (p.peek().typ != TT::Semicolon).then(|| p.expr(ctx, [TT::Semicolon])).transpose()?;
      p.require(TT::Semicolon)?;
      let post = (p.peek().typ != TT::ParenthesisClose).then(|| p.expr(ctx, [TT::ParenthesisClose])).transpose()?;
      p.require(TT::ParenthesisClose)?;
      let body = p.for_body(ctx)?;
      Ok(ForTripleStmt { init, cond, post, body })
    })
  }

  pub fn for_in_of_lhs(&mut self, ctx: ParseCtx) -> SyntaxResult<ForInOfLhs> {
    Ok(match self.peek().typ {
      TT::KeywordVar | TT::KeywordLet | TT::KeywordConst => ForInOfLhs::Decl({
        let mode = self.var_decl_mode()?;
        let pat = self.pat_decl(ctx)?;
        (mode, pat)
      }),
      _ => ForInOfLhs::Assign(self.pat(ctx)?),
    })
  }

  pub fn for_in_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ForInStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordFor)?;
      p.require(TT::ParenthesisOpen)?;
      let lhs = p.for_in_of_lhs(ctx)?;
      p.require(TT::KeywordOf)?;
      let rhs = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      let body = p.for_body(ctx)?;
      Ok(ForInStmt { lhs, rhs, body })
    })
  }

  pub fn for_of_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ForOfStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordFor)?;
      let await_ = p.consume_if(TT::KeywordAwait).is_match();
      p.require(TT::ParenthesisOpen)?;
      let lhs = p.for_in_of_lhs(ctx)?;
      p.require(TT::KeywordOf)?;
      let rhs = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      let body = p.for_body(ctx)?;
      Ok(ForOfStmt { await_, lhs, rhs, body })
    })
  }

  /// One of:
  /// - for ( [<expr> | <var decls> ]? ; <expr>? ; <expr>? )
  /// - for ( [<pat> | <var decl>] in <expr> )
  /// - for await? ( [<pat> | <var decl>] of <expr> )
  pub fn for_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    // Determine the type of for stmt, so we can call the correct parser.
    // Given the ambiguity and dynamic length of patterns and exprs, we'll need to drive the parser for a while, and can't merely peek a few fixed tokens ahead.
    // In pathological cases, the header may be very long, so rewinding may seem wasteful. In reality, it's rarely the case, and a single function that tries to parse all variants in one drive/function tends to lead to spaghetti error-prone code.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Type {
      In,
      Of,
      Triple,
    }
    impl Type {
      fn determine(p: &mut Parser, ctx: ParseCtx) -> SyntaxResult<Self> {
        p.require(TT::KeywordFor)?;
        if p.consume_if(TT::KeywordAwait).is_match() {
          // Only for-of supports await.
          return Ok(Self::Of);
        };
        p.require(TT::ParenthesisOpen)?;
        Ok(match p.peek().typ {
          TT::KeywordVar | TT::KeywordLet | TT::KeywordConst => {
            p.var_decl(ctx, VarDeclParseMode::Leftmost)?;
            match p.peek().typ {
              TT::KeywordIn => Self::In,
              TT::KeywordOf => Self::Of,
              // This should be an error (we expect a semicolon), but we'll let the for(;;) parser handle it for better error messages and simplicity here.
              _ => Self::Triple,
            }
          }
          TT::Semicolon => {
            // Only for(;;) loops have semicolons in the header.
            Self::Triple
          }
          _ => {
            // for-in and for-of loops must have an assignment target or variable declarator at the beginning of its header. We've already handled var decl before, so if it's for-in or for-of there must be a pattern now, followed by the keyword.
            match p.pat(ctx) {
              Ok(_) => match p.peek().typ {
                TT::KeywordIn => Self::In,
                TT::KeywordOf => Self::Of,
                _ => Self::Triple,
              }
              Err(_) => Self::Triple,
            }
          }
        })
      }
    }

    let cp = self.checkpoint();
    let typ = Type::determine(self, ctx)?;
    self.restore_checkpoint(cp);
    Ok(match typ {
      Type::Triple => self.for_triple_stmt(ctx)?.into_stx(),
      Type::In => self.for_in_stmt(ctx)?.into_stx(),
      Type::Of => self.for_of_stmt(ctx)?.into_stx(),
    })
  }

  pub fn if_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<IfStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordIf)?;
      p.require(TT::ParenthesisOpen)?;
      let test = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      let consequent = p.stmt(ctx)?;
      let alternate = p.consume_if(TT::KeywordElse)
        .and_then(|| p.stmt(ctx))?;
      Ok(IfStmt {
        test,
        consequent,
        alternate,
      })
    })
  }

  pub fn return_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ReturnStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordReturn)?;
      let value =
        if p.peek().preceded_by_line_terminator || p.peek().typ == TT::BraceClose {
          // Automatic Semicolon Insertion.
          None
        } else if p.consume_if(TT::Semicolon).is_match() {
          None
        } else {
          let mut asi = Asi::can();
          let value = p.expr_with_asi(ctx, [TT::Semicolon], &mut asi)?;
          if !asi.did_end_with_asi {
            p.require(TT::Semicolon)?;
          };
          Some(value)
        };
      Ok(ReturnStmt { value })
    })
  }

  pub fn throw_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ThrowStmt>> {
    self.with_loc(|p| {
      let start = p.require(TT::KeywordThrow)?;
      if p.peek().preceded_by_line_terminator {
        // Illegal under Automatic Semicolon Insertion rules.
        return Err(start.error(SyntaxErrorType::LineTerminatorAfterThrow));
      }
      let mut asi = Asi::can();
      let value = p.expr_with_asi(ctx, [TT::Semicolon], &mut asi)?;
      if !asi.did_end_with_asi {
        p.require(TT::Semicolon)?;
      };
      Ok(ThrowStmt {
        value,
      })
    })
  }

  pub fn try_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TryStmt>> {
    self.with_loc(|p| {
      let start = p.require(TT::KeywordTry)?;
      let wrapped = p.block_stmt(ctx)?;
      let catch = p.consume_if(TT::KeywordCatch)
        .and_then(|| {
          let parameter = p.consume_if(TT::ParenthesisOpen)
            .and_then(|| {
              let pattern = p.pat_decl(ctx)?;
              p.require(TT::ParenthesisClose)?;
              Ok(pattern)
            })?;
          p.with_loc(|p| {
            p.require(TT::BraceOpen)?;
            let body = p.stmts(ctx, TT::BraceClose)?;
            p.require(TT::BraceClose)?;
            Ok(CatchBlock {
              parameter,
              body,
            })
          })
        })?;
      let finally = p.consume_if(TT::KeywordFinally)
        .and_then(|| p.block_stmt(ctx))?;
      if catch.is_none() && finally.is_none() {
        return Err(start.error(SyntaxErrorType::TryStatementHasNoCatchOrFinally));
      }
      Ok(TryStmt {
        wrapped,
        catch,
        finally,
      })
    })
  }

  pub fn while_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<WhileStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordWhile)?;
      p.require(TT::ParenthesisOpen)?;
      let condition = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      let body = p.stmt(ctx)?;
      Ok(WhileStmt {
        condition,
        body,
      })
    })
  }

  pub fn do_while_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<DoWhileStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordDo)?;
      let body = p.stmt(ctx)?;
      p.require(TT::KeywordWhile)?;
      p.require(TT::ParenthesisOpen)?;
      let condition = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      Ok(DoWhileStmt {
        condition,
        body,
      })
    })
  }

  pub fn switch_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<SwitchStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordSwitch)?;
      p.require(TT::ParenthesisOpen)?;
      let test = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      p.require(TT::BraceOpen)?;
      let branches = p.repeat_until_tt_with_loc(TT::BraceClose, |p| {
        let case = if p.consume_if(TT::KeywordCase).is_match() {
          Some(p.expr(ctx, [TT::Colon])?)
        } else {
          p.require(TT::KeywordDefault)?;
          None
        };
        p.require(TT::Colon)?;
        let body = p.repeat_while(
          |p| !matches!(p.peek().typ, TT::KeywordCase | TT::KeywordDefault | TT::BraceClose),
          |p| p.stmt(ctx),
        )?;
        Ok(SwitchBranch { case, body })
      })?;
      p.require(TT::BraceClose)?;
      Ok(SwitchStmt {
        test,
        branches,
      })
    })
  }
}
