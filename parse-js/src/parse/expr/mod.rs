pub mod pat;
pub mod lit;
pub mod jsx;
pub mod util;

use pat::is_valid_pattern_identifier;
use pat::ParsePatternRules;
use util::lhs_expr_to_assign_target;

use super::ParseCtx;
use super::Parser;
use crate::ast::expr::pat::IdPat;
use crate::ast::expr::pat::Pat;
use crate::ast::stmt::decl::ParamDecl;
use crate::ast::stmt::decl::PatDecl;
use crate::ast::expr::ArrowFuncExpr;
use crate::ast::expr::BinaryExpr;
use crate::ast::expr::CallArg;
use crate::ast::expr::CallExpr;
use crate::ast::expr::ClassExpr;
use crate::ast::expr::ComputedMemberExpr;
use crate::ast::expr::CondExpr;
use crate::ast::expr::Expr;
use crate::ast::expr::FuncExpr;
use crate::ast::expr::IdExpr;
use crate::ast::expr::MemberExpr;
use crate::ast::expr::SuperExpr;
use crate::ast::expr::TaggedTemplateExpr;
use crate::ast::expr::ThisExpr;
use crate::ast::expr::UnaryExpr;
use crate::ast::expr::UnaryPostfixExpr;
use crate::ast::func::Func;
use crate::ast::node::Node;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::LexMode;
use crate::lex::KEYWORDS_MAPPING;
use crate::operator::Associativity;
use crate::operator::OperatorName;
use crate::operator::OPERATORS;
use crate::parse::operator::MULTARY_OPERATOR_MAPPING;
use crate::parse::operator::UNARY_OPERATOR_MAPPING;
use crate::token::TT;

pub struct Asi {
  pub can_end_with_asi: bool,
  pub did_end_with_asi: bool,
}

impl Asi {
  pub fn can() -> Asi {
    Asi {
      can_end_with_asi: true,
      did_end_with_asi: false,
    }
  }

  pub fn no() -> Asi {
    Asi {
      can_end_with_asi: false,
      did_end_with_asi: false,
    }
  }
}

impl<'a> Parser<'a> {
  pub fn call_args(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<CallArg>>> {
    let mut args = Vec::new();
    while self.peek().typ != TT::ParenthesisClose {
      let arg = self.with_loc(|p| {
        let spread = p.consume_if(TT::DotDotDot).is_match();
        let value = p.expr(ctx, [TT::Comma, TT::ParenthesisClose])?;
        Ok(CallArg { spread, value })
      })?;
      args.push(arg);
      if !self.consume_if(TT::Comma).is_match() {
        break;
      };
    }
    Ok(args)
  }

  pub fn expr<const N: usize>(&mut self, ctx: ParseCtx, terminators: [TT; N]) -> SyntaxResult<Node<Expr>> {
    self.expr_with_min_prec(ctx, 1, terminators, &mut Asi::no())
  }

  pub fn expr_with_asi<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
    asi: &mut Asi,
  ) -> SyntaxResult<Node<Expr>> {
    self.expr_with_min_prec(ctx, 1, terminators, asi)
  }

  /// Parses a parenthesised expression like `(a + b)`.
  pub fn grouping(&mut self, ctx: ParseCtx, asi: &mut Asi) -> SyntaxResult<Node<Expr>> {
    self.require(TT::ParenthesisOpen)?;
    let expr = self.expr_with_min_prec(
      ctx,
      1,
      [TT::ParenthesisClose],
      asi,
    )?;
    self.require(TT::ParenthesisClose)?;
    Ok(expr)
  }

  pub fn arrow_func_expr<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
  ) -> SyntaxResult<Node<ArrowFuncExpr>> {
    let func = self.with_loc(|p| {
      let is_async = p.consume_if(TT::KeywordAsync).is_match();

      let (parameters, arrow) = if !is_async
        && is_valid_pattern_identifier(p.peek().typ, ParsePatternRules {
          await_allowed: false,
          yield_allowed: ctx.rules.yield_allowed,
        }) {
        // Single-unparenthesised-parameter arrow function.
        // Parse arrow first for fast fail (and in case we are merely trying to parse as arrow function), before we mutate state by creating nodes and adding symbols.
        let param_name = p.consume().loc;
        let arrow = p.require(TT::EqualsChevronRight)?;
        let pattern = Node::new(param_name, PatDecl {
          pat: Node::new(param_name, IdPat {
            name: p.string(param_name),
          }).into_wrapped(),
        });
        let param = Node::new(param_name, ParamDecl {
          rest: false,
          pattern,
          default_value: None,
        });
        (vec![param], arrow)
      } else {
        let params = p.func_params(ctx)?;
        let arrow = p.require(TT::EqualsChevronRight)?;
        (params, arrow)
      };

      if arrow.preceded_by_line_terminator {
        // Illegal under Automatic Semicolon Insertion rules.
        return Err(arrow.error(SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters));
      }
      let fn_body_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: !is_async && ctx.rules.await_allowed,
        ..ctx.rules
      });
      let body = match p.peek().typ {
        TT::BraceOpen => p.parse_func_block_body(fn_body_ctx)?.into(),
        _ => p.expr_with_asi(
          fn_body_ctx,
          terminators,
          &mut Asi::can(),
        )?.into(),
      };
      Ok(Func {
        arrow: true,
        async_: is_async,
        generator: false,
        parameters,
        body,
      })
    })?;
    Ok(Node::new(func.loc, ArrowFuncExpr { func }))
  }

  pub fn arrow_function_or_grouping_expr<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
    asi: &mut Asi,
  ) -> SyntaxResult<Node<Expr>> {
    // Try and parse as arrow function signature first.
    // If we fail, backtrack and parse as grouping instead.
    // After we see `=>`, we assume it's definitely an arrow function and do not backtrack.

    // NOTE: We originally implemented conversion from parameters to expression to prevent the need
    // for backtracking. However, this ended up being too complex for little performance gain,
    // as most usages of grouping involve a non-comma binary operator (such as `+`) and so parsing
    // as arrow function fails quickly. Complex patterns like `{a, b: { c: [d, e] } = f }` are
    // unlikely to be used as operands in a grouping.

    self.rewindable::<Node<Expr>, _>(|p| {
      match p.arrow_func_expr(ctx, terminators) {
        Ok(expr) => Ok(Some(expr.into_wrapped())),
        Err(err) if err.typ == SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters => Err(err),
        Err(_) => Ok(None),
      }
    })
      .transpose()
      .unwrap_or_else(|| self.grouping(ctx, asi))
  }

  pub fn func_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<FuncExpr>> {
    self.with_loc(|p| {
      let is_async = p.consume_if(TT::KeywordAsync).is_match();
      p.require(TT::KeywordFunction)?;
      let generator = p.consume_if(TT::Asterisk).is_match();
      let name = p.maybe_class_or_func_name(ctx);
      let func = p.with_loc(|p| {
        let parameters = p.func_params(ctx)?;
        let fn_body_ctx = ctx.with_rules(ParsePatternRules {
          await_allowed: !is_async && ctx.rules.await_allowed,
          yield_allowed: !generator && ctx.rules.yield_allowed,
        });
        let body = p.parse_func_block_body(fn_body_ctx)?.into();
        Ok(Func {
          arrow: false,
          async_: is_async,
          generator,
          parameters,
          body,
        })
      })?;
      Ok(FuncExpr {
        name,
        func,
      })
    })
  }

  pub fn class_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ClassExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordClass)?.loc;
      let name = p.maybe_class_or_func_name(ctx);
      let extends = p.consume_if(TT::KeywordExtends).and_then(|| p.expr(ctx, [TT::BraceOpen]))?;
      let members = p.class_body(ctx)?;
      Ok(ClassExpr {
        name,
        extends,
        members,
      })
    })
  }

  pub fn id_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<IdExpr>> {
    self.with_loc(|p| {
      let name = p.id_name(ctx)?;
      Ok(IdExpr { name })
    })
  }

  /// Parses a raw valid identifier name as a string. To parse an IdExpr, use `id_expr`.
  pub fn id_name(&mut self, ctx: ParseCtx) -> SyntaxResult<String> {
    let t = self.consume();
    if !is_valid_pattern_identifier(t.typ, ctx.rules) {
      return Err(t.error(SyntaxErrorType::ExpectedSyntax("identifier")));
    };
    Ok(self.string(t.loc))
  }

  fn expr_operand<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
    asi: &mut Asi,
  ) -> SyntaxResult<Node<Expr>> {
    let [t0, t1] = self.peek_n_with_mode([LexMode::SlashIsRegex, LexMode::Standard]);
    // Handle unary operators before operand.
    if let Some(operator) = UNARY_OPERATOR_MAPPING.get(&t0.typ).filter(|operator| {
      // TODO Is this correct? Should it be possible to use as operator or keyword depending on whether there is an operand following?
      (operator.name != OperatorName::Await && operator.name != OperatorName::Yield)
        || (operator.name == OperatorName::Await && !ctx.rules.await_allowed)
        || (operator.name == OperatorName::Yield && !ctx.rules.yield_allowed)
    }) {
      return Ok(self.with_loc(|p| {
        p.consume_with_mode(LexMode::SlashIsRegex);
        let operator = if operator.name == OperatorName::Yield
          && p.consume_if(TT::Asterisk).is_match()
        {
          &OPERATORS[&OperatorName::YieldDelegated]
        } else {
          *operator
        };
        let next_min_prec =
          operator.precedence + (operator.associativity == Associativity::Left) as u8;
        let operand = p.expr_with_min_prec(
          ctx,
          next_min_prec,
          terminators,
          asi,
        )?;
        return Ok(UnaryExpr {
          operator: operator.name,
          argument: operand,
        })
      })?.into_wrapped());
    };

    // Check this before KeywordAsync.
    if is_valid_pattern_identifier(t0.typ, ctx.rules) {
      return Ok(if t1.typ == TT::EqualsChevronRight {
        // Single-unparenthesised-parameter arrow function.
        // NOTE: `await` is not allowed as an arrow function parameter, but we'll check this in parse_expr_arrow_function.
        self.arrow_func_expr(ctx, terminators)?.into_wrapped()
      } else {
        self.id_expr(ctx)?.into_wrapped()
      });
    };

    #[rustfmt::skip]
    let expr: Node<Expr> = match t0.typ {
      TT::KeywordAsync => match t1.typ {
        TT::ParenthesisOpen => self.arrow_func_expr(ctx, terminators)?.into_wrapped(),
        TT::KeywordFunction => self.func_expr(ctx)?.into_wrapped(),
        // `async` is being used as an identifier.
        _ => self.id_expr(ctx)?.into_wrapped(),
      }
      TT::BracketOpen => self.lit_arr(ctx)?.into_wrapped(),
      TT::BraceOpen => self.lit_obj(ctx)?.into_wrapped(),
      TT::ChevronLeft => self.jsx_elem(ctx)?.into_wrapped(),
      TT::KeywordClass => self.class_expr(ctx)?.into_wrapped(),
      TT::KeywordFunction => self.func_expr(ctx)?.into_wrapped(),
      TT::KeywordImport => match t1.typ {
        TT::Dot => self.import_meta()?.into_wrapped(),
        TT::ParenthesisOpen => self.import_call(ctx)?.into_wrapped(),
        _ => return Err(t0.error(SyntaxErrorType::ExpectedSyntax("import expression"))),
      },
      TT::KeywordSuper => self.super_expr()?.into_wrapped(),
      TT::KeywordThis => self.this_expr()?.into_wrapped(),
      TT::LiteralBigInt => self.lit_bigint()?.into_wrapped(),
      TT::LiteralTrue | TT::LiteralFalse => self.lit_bool()?.into_wrapped(),
      TT::LiteralNull => self.lit_null()?.into_wrapped(),
      TT::LiteralNumber => self.lit_num()?.into_wrapped(),
      TT::LiteralRegex => self.lit_regex()?.into_wrapped(),
      TT::LiteralString => self.lit_str()?.into_wrapped(),
      TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd => self.lit_template(ctx)?.into_wrapped(),
      TT::ParenthesisOpen => self.arrow_function_or_grouping_expr(ctx, terminators, asi)?,
      _ => return Err(t0.error(SyntaxErrorType::ExpectedSyntax("expression operand"))),
    };
    Ok(expr)
  }

  pub fn expr_with_min_prec<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    min_prec: u8,
    terminators: [TT; N],
    asi: &mut Asi,
  ) -> SyntaxResult<Node<Expr>> {
    let mut left = self.expr_operand(ctx, terminators, asi)?;

    loop {
      let cp = self.checkpoint();
      let t = self.consume();

      if terminators.contains(&t.typ) {
        self.restore_checkpoint(cp);
        break;
      };

      match t.typ {
        // Automatic Semicolon Insertion rules: no newline between operand and postfix operator.
        TT::PlusPlus | TT::HyphenHyphen if !t.preceded_by_line_terminator => {
          let operator_name = match t.typ {
            TT::PlusPlus => OperatorName::PostfixIncrement,
            TT::HyphenHyphen => OperatorName::PostfixDecrement,
            _ => unreachable!(),
          };
          let operator = &OPERATORS[&operator_name];
          if operator.precedence < min_prec {
            self.restore_checkpoint(cp);
            break;
          };
          left = Node::new(left.loc + t.loc, UnaryPostfixExpr {
            operator: operator_name,
            argument: left,
          }).into_wrapped();
          continue;
        }
        // Automatic Semicolon Insertion rules: no newline between operand and template literal.
        TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd
          if !t.preceded_by_line_terminator =>
        {
          let loc = t.loc;
          self.restore_checkpoint(cp);
          let parts = self.lit_template_parts(ctx)?;
          left = Node::new(left.loc + loc, TaggedTemplateExpr {
            function: left,
            parts,
          }).into_wrapped();
          continue;
        }
        _ => {}
      };

      match MULTARY_OPERATOR_MAPPING.get(&t.typ) {
        None => {
          if asi.can_end_with_asi
            && (t.preceded_by_line_terminator
              || t.typ == TT::BraceClose
              || t.typ == TT::EOF)
          {
            // Automatic Semicolon Insertion.
            // TODO Exceptions (e.g. for loop header).
            self.restore_checkpoint(cp);
            asi.did_end_with_asi = true;
            break;
          };
          return Err(t.error(SyntaxErrorType::ExpectedSyntax("expression operator")));
        }
        Some(operator) => {
          if operator.precedence < min_prec {
            self.restore_checkpoint(cp);
            break;
          };

          let next_min_prec =
            operator.precedence + (operator.associativity == Associativity::Left) as u8;

          left = match operator.name {
            OperatorName::Call | OperatorName::OptionalChainingCall => {
              let arguments = self.call_args(ctx)?;
              let end = self.require(TT::ParenthesisClose)?;
              Node::new(left.loc + end.loc, CallExpr {
                optional_chaining: match operator.name {
                  OperatorName::OptionalChainingCall => true,
                  _ => false,
                },
                arguments,
                callee: left,
              }).into_wrapped()
            }
            OperatorName::ComputedMemberAccess
            | OperatorName::OptionalChainingComputedMemberAccess => {
              let member = self.expr(ctx, [TT::BracketClose])?;
              let end = self.require(TT::BracketClose)?;
              Node::new(left.loc + end.loc, ComputedMemberExpr {
                optional_chaining: operator.name == OperatorName::OptionalChainingComputedMemberAccess,
                object: left,
                member,
              }).into_wrapped()
            }
            OperatorName::Conditional => {
              let consequent = self.expr(ctx, [TT::Colon])?;
              self.require(TT::Colon)?;
              let alternate = self.expr_with_min_prec(
                ctx,
                OPERATORS[&OperatorName::ConditionalAlternate].precedence,
                terminators,
                asi,
              )?;
              Node::new(left.loc + alternate.loc, CondExpr {
                test: left,
                consequent,
                alternate,
              }).into_wrapped()
            }
            OperatorName::MemberAccess | OperatorName::OptionalChainingMemberAccess => {
              let right_tok = self.consume();
              match right_tok.typ {
                TT::Identifier => {}
                TT::PrivateMember => {}
                t if KEYWORDS_MAPPING.contains_key(&t) => {}
                _ => {
                  return Err(
                    right_tok.error(SyntaxErrorType::ExpectedSyntax("member access property")),
                  )
                }
              };
              let right = right_tok.loc;
              Node::new(left.loc + right, MemberExpr {
                optional_chaining: operator.name == OperatorName::OptionalChainingMemberAccess,
                left,
                right: self.string(right),
              }).into_wrapped()
            }
            _ => {
              if operator.name.is_assignment() {
                left = lhs_expr_to_assign_target(left, operator.name)?;
              };
              let right = self.expr_with_min_prec(
                ctx,
                next_min_prec,
                terminators,
                asi,
              )?;
              Node::new(left.loc + right.loc, BinaryExpr {
                operator: operator.name,
                left,
                right,
              }).into_wrapped()
            }
          };
        }
      };
    }

    Ok(left)
  }

  pub fn super_expr(&mut self) -> SyntaxResult<Node<SuperExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordSuper)?;
      Ok(SuperExpr {}.into())
    })
  }

  pub fn this_expr(&mut self) -> SyntaxResult<Node<ThisExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordThis)?;
      Ok(ThisExpr {}.into())
    })
  }
}
