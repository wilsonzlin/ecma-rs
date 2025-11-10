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
use crate::ast::stmt::WithStmt;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::token::TT;

impl<'a> Parser<'a> {
  pub fn stmts(&mut self, ctx: ParseCtx, end: TT) -> SyntaxResult<Vec<Node<Stmt>>> {
    self.repeat_until_tt(end, |p| p.stmt(ctx))
  }

  pub fn stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    let [t0, t1, t2] = self.peek_n();
    #[rustfmt::skip]
    let stmt: Node<Stmt> = match t0.typ {
      TT::BraceOpen => self.block_stmt(ctx)?.into_wrapped(),
      TT::KeywordBreak => self.break_stmt(ctx)?.into_wrapped(),
      TT::KeywordClass => self.class_decl(ctx)?.into_wrapped(),
      // TypeScript: const enum
      TT::KeywordConst if t1.typ == TT::KeywordEnum => {
        self.consume(); // consume 'const'
        self.enum_decl(ctx, false, false, true)?.into_wrapped()
      },
      TT::KeywordConst | TT::KeywordVar => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_wrapped(),
      // `let` is a contextual keyword - only treat it as a declaration if followed by a pattern start
      // TypeScript: `let identifier :` is a variable declaration with type annotation, not a labeled statement
      TT::KeywordLet if t1.typ == TT::BraceOpen || t1.typ == TT::BracketOpen || is_valid_pattern_identifier(t1.typ, ctx.rules) => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_wrapped(),
      // `using` is a contextual keyword for resource management
      TT::KeywordUsing if t1.typ == TT::BraceOpen || t1.typ == TT::BracketOpen || is_valid_pattern_identifier(t1.typ, ctx.rules) => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_wrapped(),
      // `await using` for async resource management
      TT::KeywordAwait if t1.typ == TT::KeywordUsing => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_wrapped(),
      TT::KeywordContinue => self.continue_stmt(ctx)?.into_wrapped(),
      TT::KeywordDebugger => self.debugger_stmt()?.into_wrapped(),
      TT::KeywordDo => self.do_while_stmt(ctx)?.into_wrapped(),
      TT::KeywordExport => self.export_stmt(ctx)?,
      TT::KeywordFor => self.for_stmt(ctx)?,
      // Only treat async as function decl if followed by function keyword
      TT::KeywordAsync if t1.typ == TT::KeywordFunction => self.func_decl(ctx)?.into_wrapped(),
      TT::KeywordFunction => self.func_decl(ctx)?.into_wrapped(),
      TT::KeywordIf => self.if_stmt(ctx)?.into_wrapped(),
      TT::KeywordImport if t1.typ != TT::ParenthesisOpen => self.import_stmt(ctx)?.into_wrapped(),
      TT::KeywordReturn => self.return_stmt(ctx)?.into_wrapped(),
      TT::KeywordSwitch => self.switch_stmt(ctx)?.into_wrapped(),
      TT::KeywordThrow => self.throw_stmt(ctx)?.into_wrapped(),
      TT::KeywordTry => self.try_stmt(ctx)?.into_wrapped(),
      TT::KeywordWhile => self.while_stmt(ctx)?.into_wrapped(),
      TT::KeywordWith => self.with_stmt(ctx)?.into_wrapped(),
      TT::Semicolon => self.empty_stmt()?.into_wrapped(),

      // TypeScript declarations
      TT::KeywordInterface => self.interface_decl(ctx, false, false)?.into_wrapped(),
      TT::KeywordType => self.type_alias_decl(ctx, false, false)?.into_wrapped(),
      TT::KeywordEnum => self.enum_decl(ctx, false, false, false)?.into_wrapped(),
      TT::KeywordNamespace | TT::KeywordModule => self.namespace_or_module_decl(ctx, false, false)?,
      TT::KeywordDeclare => self.declare_stmt(ctx)?,
      TT::KeywordAbstract if t1.typ == TT::KeywordClass => self.abstract_class_decl(ctx)?.into_wrapped(),
      // Decorators can appear before class declarations
      TT::At => self.class_decl_impl(ctx, false)?.into_wrapped(),

      t if is_valid_pattern_identifier(t, ctx.rules) && t1.typ == TT::Colon => self.label_stmt(ctx)?.into_wrapped(),
      _ => self.expr_stmt(ctx)?.into_wrapped(),
    };
    Ok(stmt)
  }

  /// Handle declare keyword
  fn declare_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    self.consume(); // consume 'declare'
    let t = self.peek().typ;
    match t {
      TT::KeywordInterface => Ok(self.interface_decl(ctx, false, true)?.wrap(Stmt::InterfaceDecl)),
      TT::KeywordType => Ok(self.type_alias_decl(ctx, false, true)?.wrap(Stmt::TypeAliasDecl)),
      TT::KeywordEnum => Ok(self.enum_decl(ctx, false, true, false)?.wrap(Stmt::EnumDecl)),
      TT::KeywordNamespace | TT::KeywordModule => self.namespace_or_module_decl(ctx, false, true),
      TT::KeywordClass => Ok(self.class_decl_with_modifiers(ctx, false, true, false)?.wrap(Stmt::ClassDecl)),
      TT::KeywordFunction => Ok(self.func_decl_with_modifiers(ctx, false, true)?.wrap(Stmt::FunctionDecl)),
      // Support declare async function
      TT::KeywordAsync if self.peek_n::<2>()[1].typ == TT::KeywordFunction => {
        self.consume(); // consume 'async'
        Ok(self.func_decl_with_modifiers(ctx, false, true)?.wrap(Stmt::FunctionDecl))
      }
      TT::KeywordConst if self.peek_n::<2>()[1].typ == TT::KeywordEnum => {
        self.consume(); // consume 'const'
        Ok(self.enum_decl(ctx, false, true, true)?.wrap(Stmt::EnumDecl))
      }
      // Support declare abstract class
      TT::KeywordAbstract if self.peek_n::<2>()[1].typ == TT::KeywordClass => {
        self.consume(); // consume 'abstract'
        Ok(self.class_decl_with_modifiers(ctx, false, true, true)?.wrap(Stmt::ClassDecl))
      }
      // Support declare var, declare let, declare const, declare using
      TT::KeywordVar | TT::KeywordLet | TT::KeywordConst | TT::KeywordUsing => Ok(self.var_decl(ctx, VarDeclParseMode::Asi)?.wrap(Stmt::VarDecl)),
      _ => Err(self.peek().error(SyntaxErrorType::ExpectedSyntax("declaration after declare"))),
    }
  }

  /// Handle namespace or module declaration
  fn namespace_or_module_decl(&mut self, ctx: ParseCtx, export: bool, declare: bool) -> SyntaxResult<Node<Stmt>> {
    // Check if it's a string module (declare module "foo")
    if self.peek().typ == TT::KeywordModule && self.peek_n::<2>()[1].typ == TT::LiteralString {
      Ok(self.module_decl(ctx, export, declare)?.wrap(Stmt::ModuleDecl))
    } else {
      Ok(self.namespace_decl(ctx, export, declare)?.wrap(Stmt::NamespaceDecl))
    }
  }

  /// Handle abstract class
  fn abstract_class_decl(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<crate::ast::stmt::decl::ClassDecl>> {
    // Don't consume 'abstract' here - let class_decl_impl do it
    self.class_decl_with_modifiers(ctx, false, false, true)
  }

  /// Parse class declaration with TypeScript modifiers
  fn class_decl_with_modifiers(&mut self, ctx: ParseCtx, _export: bool, declare: bool, _abstract_: bool) -> SyntaxResult<Node<crate::ast::stmt::decl::ClassDecl>> {
    // export and abstract are parsed inside class_decl_impl, so we only need to pass declare
    self.class_decl_impl(ctx, declare)
  }

  /// Parse function declaration with TypeScript modifiers
  fn func_decl_with_modifiers(&mut self, ctx: ParseCtx, export: bool, declare: bool) -> SyntaxResult<Node<crate::ast::stmt::decl::FuncDecl>> {
    // Implementation will be added when we update func_decl
    self.func_decl(ctx)
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
      let init = {
        let [t0, t1] = p.peek_n();
        match t0.typ {
          TT::KeywordVar | TT::KeywordConst => ForTripleStmtInit::Decl(p.var_decl(ctx, VarDeclParseMode::Leftmost)?),
          // `let` is contextual - only a declaration if followed by a pattern
          TT::KeywordLet if t1.typ == TT::BraceOpen || t1.typ == TT::BracketOpen || is_valid_pattern_identifier(t1.typ, ctx.rules) => ForTripleStmtInit::Decl(p.var_decl(ctx, VarDeclParseMode::Leftmost)?),
          TT::Semicolon => ForTripleStmtInit::None,
          _ => ForTripleStmtInit::Expr(p.expr(ctx, [TT::Semicolon])?),
        }
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
    let [t0, t1] = self.peek_n();
    Ok(match t0.typ {
      TT::KeywordVar | TT::KeywordConst => ForInOfLhs::Decl({
        let mode = self.var_decl_mode()?;
        let pat = self.pat_decl(ctx)?;
        (mode, pat)
      }),
      // `let` is contextual - only a declaration if followed by a pattern
      TT::KeywordLet if t1.typ == TT::BraceOpen || t1.typ == TT::BracketOpen || is_valid_pattern_identifier(t1.typ, ctx.rules) => ForInOfLhs::Decl({
        let mode = self.var_decl_mode()?;
        let pat = self.pat_decl(ctx)?;
        (mode, pat)
      }),
      _ => {
        // Parse as expression (which handles member expressions, patterns, etc.)
        // then convert to pattern/assignment target
        use super::expr::util::lit_to_pat;
        let expr = self.expr(ctx, [TT::KeywordIn, TT::KeywordOf])?;
        let pat = lit_to_pat(expr)?;
        ForInOfLhs::Assign(pat)
      }
    })
  }

  pub fn for_in_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ForInStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordFor)?;
      p.require(TT::ParenthesisOpen)?;
      let lhs = p.for_in_of_lhs(ctx)?;
      p.require(TT::KeywordIn)?;
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
          TT::KeywordVar | TT::KeywordConst => {
            p.var_decl(ctx, VarDeclParseMode::Leftmost)?;
            match p.peek().typ {
              TT::KeywordIn => Self::In,
              TT::KeywordOf => Self::Of,
              // This should be an error (we expect a semicolon), but we'll let the for(;;) parser handle it for better error messages and simplicity here.
              _ => Self::Triple,
            }
          }
          // `await using` for async resource management in for-of
          TT::KeywordAwait if p.peek_n::<2>()[1].typ == TT::KeywordUsing => {
            p.var_decl(ctx, VarDeclParseMode::Leftmost)?;
            match p.peek().typ {
              TT::KeywordOf => Self::Of,
              _ => Self::Triple,
            }
          }
          // `using` is a contextual keyword for resource management
          TT::KeywordUsing => {
            let [_, next_token] = p.peek_n::<2>();
            let next = next_token.typ;
            if next == TT::BraceOpen || next == TT::BracketOpen || is_valid_pattern_identifier(next, ctx.rules) {
              p.var_decl(ctx, VarDeclParseMode::Leftmost)?;
              match p.peek().typ {
                TT::KeywordOf => Self::Of,
                _ => Self::Triple,
              }
            } else {
              // Not a declaration, parse as expression
              match p.expr(ctx, [TT::KeywordIn, TT::KeywordOf]) {
                Ok(_) => match p.peek().typ {
                  TT::KeywordIn => Self::In,
                  TT::KeywordOf => Self::Of,
                  _ => Self::Triple,
                }
                Err(_) => Self::Triple,
              }
            }
          }
          // `let` is a contextual keyword - it's only a declaration keyword when followed by a pattern.
          // `let.x`, `let()`, `let[x]` where x is not a valid identifier are all expressions.
          TT::KeywordLet => {
            let [_, next_token] = p.peek_n::<2>();
            let next = next_token.typ;
            if next == TT::BraceOpen || next == TT::BracketOpen || is_valid_pattern_identifier(next, ctx.rules) {
              // Looks like a variable declaration
              p.var_decl(ctx, VarDeclParseMode::Leftmost)?;
              match p.peek().typ {
                TT::KeywordIn => Self::In,
                TT::KeywordOf => Self::Of,
                _ => Self::Triple,
              }
            } else {
              // Not a declaration, parse as expression to handle member expressions etc.
              match p.expr(ctx, [TT::KeywordIn, TT::KeywordOf]) {
                Ok(_) => match p.peek().typ {
                  TT::KeywordIn => Self::In,
                  TT::KeywordOf => Self::Of,
                  _ => Self::Triple,
                }
                Err(_) => Self::Triple,
              }
            }
          }
          TT::Semicolon => {
            // Only for(;;) loops have semicolons in the header.
            Self::Triple
          }
          _ => {
            // for-in and for-of loops must have an assignment target or variable declarator at the beginning of its header. We've already handled var decl before, so if it's for-in or for-of there must be an expression/pattern now, followed by the keyword.
            match p.expr(ctx, [TT::KeywordIn, TT::KeywordOf]) {
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
      Type::Triple => self.for_triple_stmt(ctx)?.into_wrapped(),
      Type::In => self.for_in_stmt(ctx)?.into_wrapped(),
      Type::Of => self.for_of_stmt(ctx)?.into_wrapped(),
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

  pub fn with_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<WithStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordWith)?;
      p.require(TT::ParenthesisOpen)?;
      let object = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      let body = p.stmt(ctx)?;
      Ok(WithStmt {
        object,
        body,
      })
    })
  }

  pub fn do_while_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<DoWhileStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordDo)?;
      let body = p.stmt(ctx)?;
      // Consume optional semicolon after body statement (ASI)
      p.consume_if(TT::Semicolon);
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

