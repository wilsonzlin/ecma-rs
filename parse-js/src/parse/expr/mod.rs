pub mod jsx;
pub mod lit;
pub mod pat;
pub mod util;

use super::ParseCtx;
use super::Parser;
use crate::ast::expr::pat::IdPat;
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
use crate::ast::expr::NewTarget;
use crate::ast::expr::SuperExpr;
use crate::ast::expr::TaggedTemplateExpr;
use crate::ast::expr::ThisExpr;
use crate::ast::expr::UnaryExpr;
use crate::ast::expr::UnaryPostfixExpr;
use crate::ast::func::Func;
use crate::ast::node::Node;
use crate::ast::stmt::decl::ParamDecl;
use crate::ast::stmt::decl::PatDecl;
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
use pat::is_valid_pattern_identifier;
use pat::ParsePatternRules;
use util::lhs_expr_to_assign_target;

struct ParenthesizedExpr;

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
  /// Creates a synthetic `undefined` identifier expression for error recovery.
  /// Used when parsing fails or encounters empty expressions like `()`.
  fn create_synthetic_undefined(&self, loc: crate::loc::Loc) -> Node<Expr> {
    Node::new(
      loc,
      IdExpr {
        name: "undefined".to_string(),
      },
    )
    .into_wrapped()
  }

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

  pub fn expr<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
  ) -> SyntaxResult<Node<Expr>> {
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

  /// Parse expression with TypeScript type arguments support
  /// Type arguments are permitted without a call suffix (e.g. `Base<T>`) in
  /// contexts like class heritage clauses.
  pub fn expr_with_ts_type_args<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
  ) -> SyntaxResult<Node<Expr>> {
    let prev = self.allow_bare_ts_type_args;
    self.allow_bare_ts_type_args = true;
    let out = self.expr(ctx, terminators);
    self.allow_bare_ts_type_args = prev;
    out
  }

  fn ts_type_arguments_after_chevron_left(&mut self, ctx: ParseCtx) -> SyntaxResult<()> {
    loop {
      if matches!(
        self.peek().typ,
        TT::ChevronRight
          | TT::ChevronRightEquals
          | TT::ChevronRightChevronRight
          | TT::ChevronRightChevronRightEquals
          | TT::ChevronRightChevronRightChevronRight
          | TT::ChevronRightChevronRightChevronRightEquals
      ) {
        self.require_chevron_right()?;
        break;
      }

      let _ = self.type_expr(ctx)?;
      if self.consume_if(TT::Comma).is_match() {
        continue;
      }
      self.require_chevron_right()?;
      break;
    }
    Ok(())
  }

  /// Parses a parenthesised expression like `(a + b)`.
  pub fn grouping(&mut self, ctx: ParseCtx, asi: &mut Asi) -> SyntaxResult<Node<Expr>> {
    self.require(TT::ParenthesisOpen)?;
    // TypeScript: Allow empty parenthesized expressions for error recovery: ()
    // Also handles comma operator with missing operands: (, x) or (x, )
    let mut expr = if self.peek().typ == TT::ParenthesisClose {
      // Empty expression: () - create synthetic undefined
      let loc = self.peek().loc;
      self.create_synthetic_undefined(loc)
    } else {
      self
        .expr_with_min_prec(ctx, 1, [TT::ParenthesisClose], asi)
        .unwrap_or_else(|_| {
          // If expression parsing fails, create synthetic undefined for error recovery
          let loc = self.peek().loc;
          self.create_synthetic_undefined(loc)
        })
    };
    self.require(TT::ParenthesisClose)?;
    expr.assoc.set(ParenthesizedExpr);
    Ok(expr)
  }

  pub fn arrow_func_expr<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
  ) -> SyntaxResult<Node<ArrowFuncExpr>> {
    let func = self.with_loc(|p| {
      // Check if current token is 'async' followed by '=>'
      // In that case, 'async' is the parameter name, not the async keyword
      let is_async_param_name =
        p.peek().typ == TT::KeywordAsync && p.peek_n::<2>()[1].typ == TT::EqualsChevronRight;

      let is_async = if !is_async_param_name {
        p.consume_if(TT::KeywordAsync).is_match()
      } else {
        false
      };

      // Check if this is a single-unparenthesised-parameter arrow function
      // Works for both sync (x => ...) and async (async x => ...)
      let next_token = p.peek().typ;
      let is_unparenthesised_single_param = is_valid_pattern_identifier(
        next_token,
        ParsePatternRules {
          await_allowed: false,
          yield_allowed: ctx.rules.yield_allowed,
        },
      ) && {
        // Need to peek further to see if there's => coming up
        let peek2 = p.peek_n::<2>()[1].typ;
        // Could be either:
        // - identifier =>
        // - identifier : type =>
        peek2 == TT::EqualsChevronRight || peek2 == TT::Colon
      };

      let (type_parameters, parameters, return_type, arrow) = if is_unparenthesised_single_param {
        // Single-unparenthesised-parameter arrow function.
        // Parse arrow first for fast fail (and in case we are merely trying to parse as arrow function), before we mutate state by creating nodes and adding symbols.
        let param_name = p.consume().loc;
        // TypeScript: return type annotation (after param, before =>) - may be type predicate.
        let return_type = if p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr_or_predicate(ctx)?)
        } else {
          None
        };
        let arrow = p.require(TT::EqualsChevronRight)?;
        let pattern = Node::new(
          param_name,
          PatDecl {
            pat: Node::new(
              param_name,
              IdPat {
                name: p.string(param_name),
              },
            )
            .into_wrapped(),
          },
        );
        let param = Node::new(
          param_name,
          ParamDecl {
            decorators: vec![],
            rest: false,
            optional: false,
            accessibility: None,
            readonly: false,
            pattern,
            type_annotation: None,
            default_value: None,
          },
        );
        (None, vec![param], return_type, arrow)
      } else {
        // TypeScript: generic type parameters
        let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
          Some(p.type_parameters(ctx)?)
        } else {
          None
        };
        let params = p.func_params(ctx)?;
        // TypeScript: return type annotation (after params, before =>) - may be type predicate.
        let return_type = if p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr_or_predicate(ctx)?)
        } else {
          None
        };
        let arrow = p.require(TT::EqualsChevronRight)?;
        (type_parameters, params, return_type, arrow)
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
        _ => p
          .expr_with_asi(fn_body_ctx, terminators, &mut Asi::can())?
          .into(),
      };
      if terminators.contains(&TT::Colon) && p.peek().typ != TT::Colon {
        return Err(
          p.peek()
            .error(SyntaxErrorType::RequiredTokenNotFound(TT::Colon)),
        );
      }
      Ok(Func {
        arrow: true,
        async_: is_async,
        generator: false,
        type_parameters,
        parameters,
        return_type,
        body: Some(body),
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

    self
      .rewindable::<Node<Expr>, _>(|p| match p.arrow_func_expr(ctx, terminators) {
        Ok(expr) => Ok(Some(expr.into_wrapped())),
        Err(err) if err.typ == SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters => {
          Err(err)
        }
        Err(_) => Ok(None),
      })
      .transpose()
      .unwrap_or_else(|| self.grouping(ctx, asi))
  }

  pub fn func_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<FuncExpr>> {
    self.with_loc(|p| {
      let is_async = p.consume_if(TT::KeywordAsync).is_match();
      p.require(TT::KeywordFunction)?;
      let generator = p.consume_if(TT::Asterisk).is_match();
      // Function name is always parsed with yield/await allowed as identifiers,
      // even for generator/async functions (the function can be named "yield" or "await")
      let name_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: true,
        yield_allowed: true,
      });
      let name = p.maybe_class_or_func_name(name_ctx);
      let func = p.with_loc(|p| {
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
        // TypeScript: return type annotation - may be type predicate
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
          body: Some(body),
        })
      })?;
      Ok(FuncExpr { name, func })
    })
  }

  pub fn class_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ClassExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordClass)?.loc;
      let name = p.maybe_class_or_func_name(ctx);

      // TypeScript: generic type parameters
      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      let extends = p
        .consume_if(TT::KeywordExtends)
        .and_then(|| p.expr_with_ts_type_args(ctx, [TT::BraceOpen, TT::KeywordImplements]))?;

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
      Ok(ClassExpr {
        decorators: Vec::new(),
        name,
        type_parameters,
        extends,
        implements,
        members,
      })
    })
  }

  pub fn class_expr_with_decorators(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ClassExpr>> {
    self.with_loc(|p| {
      let decorators = p.decorators(ctx)?;
      p.require(TT::KeywordClass)?.loc;
      let name = p.maybe_class_or_func_name(ctx);

      // TypeScript: generic type parameters
      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      let extends = p
        .consume_if(TT::KeywordExtends)
        .and_then(|| p.expr_with_ts_type_args(ctx, [TT::BraceOpen, TT::KeywordImplements]))?;

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
      Ok(ClassExpr {
        decorators,
        name,
        type_parameters,
        extends,
        implements,
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

  /// Try to parse angle-bracket type assertion: <Type>expr
  /// Returns parsed assertion or error if it doesn't look like a type assertion
  fn try_parse_angle_bracket_type_assertion<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
    asi: &mut Asi,
  ) -> SyntaxResult<Node<Expr>> {
    // Quick lookahead: check if this looks like a type assertion
    // Type assertions start with type expression keywords or identifiers that are type names
    let [_, t1] = self.peek_n::<2>();

    // Heuristic: in dialects that permit JSX, `<lowercase>` is more likely to be JSX
    // than an angle-bracket type assertion.
    let is_likely_jsx_tag = self.allows_jsx()
      && t1.typ == TT::Identifier
      && self
        .str(t1.loc)
        .chars()
        .next()
        .map_or(false, |c| c.is_ascii_lowercase());

    let looks_like_type_assertion = !is_likely_jsx_tag
      && matches!(
        t1.typ,
        TT::KeywordAny
          | TT::KeywordUnknown
          | TT::KeywordNever
          | TT::KeywordVoid
          | TT::KeywordStringType
          | TT::KeywordNumberType
          | TT::KeywordBooleanType
          | TT::KeywordBigIntType
          | TT::KeywordSymbolType
          | TT::KeywordObjectType
          | TT::KeywordUndefinedType
          | TT::Identifier
          | TT::BraceOpen
          | TT::BracketOpen
          | TT::KeywordTypeof
          | TT::KeywordKeyof
          | TT::ParenthesisOpen
          | TT::LiteralString
          | TT::LiteralNumber
          | TT::LiteralTrue
          | TT::LiteralFalse
          | TT::LiteralNull
          | TT::KeywordConst
      );

    if !looks_like_type_assertion {
      return Err(
        self
          .peek()
          .error(SyntaxErrorType::ExpectedSyntax("type assertion")),
      );
    }

    self
      .with_loc(|p| {
        p.require(TT::ChevronLeft)?;

        // Check for <const> type assertion
        let is_const_assertion = p.peek().typ == TT::KeywordConst;
        if is_const_assertion {
          p.consume(); // consume 'const'
          p.require(TT::ChevronRight)?;

          let min_prec = OPERATORS[&OperatorName::UnaryPlus].precedence;
          let expression = p.expr_with_min_prec(ctx, min_prec, terminators, asi)?;

          use crate::ast::expr::TypeAssertionExpr;
          return Ok(
            TypeAssertionExpr {
              expression: Box::new(expression),
              type_annotation: None,
              const_assertion: true,
            }
            .into(),
          );
        }

        let type_annotation = p.type_expr(ctx)?;
        p.require(TT::ChevronRight)?;

        // TypeScript: If we're followed by `<`, this could be JSX, not a nested type assertion
        // E.g., <Panel><Div /></Panel> should be JSX, not <Panel>(<Div>(...))</Panel> as nested type assertions
        // Check if it looks like a JSX element: `<identifier` followed by whitespace, `/`, or `>`
        if p.peek().typ == TT::ChevronLeft {
          let [_, t1, _t2] = p.peek_n::<3>();
          if t1.typ == TT::Identifier {
            // This looks like JSX: <identifier ...
            // Reject the type assertion and let JSX parser handle it
            return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
              "not a type assertion (followed by JSX element)",
            )));
          }
        }

        let min_prec = OPERATORS[&OperatorName::UnaryPlus].precedence;
        let expression = p.expr_with_min_prec(ctx, min_prec, terminators, asi)?;

        // If we're followed by a JSX closing tag, this is actually JSX, not a type assertion
        // E.g., <Comp>text</Comp> should be JSX, not <Comp>(text) as type assertion
        if p.peek().typ == TT::ChevronLeftSlash {
          return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
            "not a type assertion (followed by JSX closing tag)",
          )));
        }

        use crate::ast::expr::TypeAssertionExpr;
        Ok(TypeAssertionExpr {
          expression: Box::new(expression),
          type_annotation: Some(type_annotation),
          const_assertion: false,
        })
      })
      .map(|node| node.into_wrapped())
  }

  fn expr_operand<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    terminators: [TT; N],
    asi: &mut Asi,
  ) -> SyntaxResult<Node<Expr>> {
    let [t0, t1, t2] =
      self.peek_n_with_mode([LexMode::SlashIsRegex, LexMode::Standard, LexMode::Standard]);
    // Handle unary operators before operand.
    // Special case: `new.target` should not be treated as `new` operator
    if let Some(operator) = UNARY_OPERATOR_MAPPING
      .get(&t0.typ)
      .filter(|operator| {
        // Treat await/yield as operators only when they're keywords (not allowed as identifiers)
        (operator.name != OperatorName::Await && operator.name != OperatorName::Yield)
          || (operator.name == OperatorName::Await && !ctx.rules.await_allowed)
          || (operator.name == OperatorName::Yield && !ctx.rules.yield_allowed)
      })
      .filter(|operator| {
        // Don't treat `new` as operator if followed by `.` (for new.target)
        !(operator.name == OperatorName::New && t1.typ == TT::Dot)
      })
      .filter(|operator| {
        // Don't treat `await` or `yield` as operators if followed by `=>` (arrow function parameter)
        !((operator.name == OperatorName::Await || operator.name == OperatorName::Yield)
          && t1.typ == TT::EqualsChevronRight)
      })
    {
      return Ok(
        self
          .with_loc(|p| {
            let op_loc = p.consume_with_mode(LexMode::SlashIsRegex).loc;
            let operator =
              if operator.name == OperatorName::Yield && p.consume_if(TT::Asterisk).is_match() {
                &OPERATORS[&OperatorName::YieldDelegated]
              } else {
                *operator
              };
            let next_min_prec =
              operator.precedence + (operator.associativity == Associativity::Left) as u8;

            // For yield and await, the operand is optional. Check if there should be an operand.
            let next_token = p.peek();
            let has_operand = if operator.name == OperatorName::Yield
              || operator.name == OperatorName::Await
              || operator.name == OperatorName::YieldDelegated
            {
              // No operand if:
              // 1. Next token is preceded by line terminator
              // 2. Next token is a terminator we're looking for
              // 3. Next token is a closing bracket/paren/brace
              // 4. Next token is semicolon or comma
              // 5. Next token is EOF
              !next_token.preceded_by_line_terminator
                && next_token.typ != TT::EOF
                && next_token.typ != TT::Semicolon
                && next_token.typ != TT::Comma
                && next_token.typ != TT::ParenthesisClose
                && next_token.typ != TT::BracketClose
                && next_token.typ != TT::BraceClose
                && !terminators.contains(&next_token.typ)
            } else {
              // TypeScript: For other unary operators, allow missing operand for error recovery
              // Accept semicolon, closing braces/brackets/parens as missing operand
              next_token.typ != TT::Semicolon
                && next_token.typ != TT::ParenthesisClose
                && next_token.typ != TT::BracketClose
                && next_token.typ != TT::BraceClose
                && next_token.typ != TT::EOF
                && !terminators.contains(&next_token.typ)
            };

            let operand = if has_operand {
              p.expr_with_min_prec(ctx, next_min_prec, terminators, asi)?
            } else {
              // For unary operators without operand, use `undefined` identifier for error recovery
              p.create_synthetic_undefined(op_loc)
            };

            return Ok(UnaryExpr {
              operator: operator.name,
              argument: operand,
            });
          })?
          .into_wrapped(),
      );
    };

    // Check for async keyword first, before checking if it's a valid identifier.
    // Exception: `async => ...` should be treated as a parameter name, not async keyword
    if t0.typ == TT::KeywordAsync && t1.typ != TT::EqualsChevronRight {
      return Ok(match t1.typ {
        TT::ParenthesisOpen => self.arrow_func_expr(ctx, terminators)?.into_wrapped(),
        TT::KeywordFunction => self.func_expr(ctx)?.into_wrapped(),
        // Check if this could be a single-parameter arrow function: `async x => {}`
        // t1 is the identifier, t2 should be =>
        _ if is_valid_pattern_identifier(t1.typ, ctx.rules) && t2.typ == TT::EqualsChevronRight => {
          self.arrow_func_expr(ctx, terminators)?.into_wrapped()
        }
        // `async` is being used as an identifier.
        _ => self.id_expr(ctx)?.into_wrapped(),
      });
    };

    // Check for other valid pattern identifiers.
    if is_valid_pattern_identifier(t0.typ, ctx.rules) {
      // Error recovery: `yield *` should be treated as yield expression even at top level
      // This handles cases like bare `yield *;` for error recovery
      if t0.typ == TT::KeywordYield && t1.typ == TT::Asterisk {
        return Ok(
          self
            .with_loc(|p| {
              let op_loc = p.consume_with_mode(LexMode::SlashIsRegex).loc; // consume 'yield'
              p.consume(); // consume '*'
              let operator = &OPERATORS[&OperatorName::YieldDelegated];

              // Check if there's an operand
              let next_token = p.peek();
              let has_operand = !next_token.preceded_by_line_terminator
                && next_token.typ != TT::EOF
                && next_token.typ != TT::Semicolon
                && next_token.typ != TT::Comma
                && next_token.typ != TT::ParenthesisClose
                && next_token.typ != TT::BracketClose
                && next_token.typ != TT::BraceClose
                && !terminators.contains(&next_token.typ);

              let operand = if has_operand {
                p.expr_with_min_prec(ctx, operator.precedence + 1, terminators, asi)?
              } else {
                p.create_synthetic_undefined(op_loc)
              };

              Ok(UnaryExpr {
                operator: operator.name,
                argument: operand,
              })
            })?
            .into_wrapped(),
        );
      }

      return Ok(if t1.typ == TT::EqualsChevronRight {
        // Single-unparenthesised-parameter arrow function.
        self.arrow_func_expr(ctx, terminators)?.into_wrapped()
      } else {
        self.id_expr(ctx)?.into_wrapped()
      });
    };

    // Decorated class expression: `@dec class C {}`.
    if t0.typ == TT::At {
      let checkpoint = self.checkpoint();
      match self.class_expr_with_decorators(ctx) {
        Ok(class) => return Ok(class.into_wrapped()),
        Err(_) => self.restore_checkpoint(checkpoint),
      }
    }

    #[rustfmt::skip]
    let expr: Node<Expr> = match t0.typ {
      TT::BracketOpen => self.lit_arr(ctx)?.into_wrapped(),
      TT::BraceOpen => self.lit_obj(ctx)?.into_wrapped(),
      TT::ChevronLeft => {
        let allow_jsx = self.allows_jsx();
        let allow_type_assertions = self.allows_angle_bracket_type_assertions();
        let chevron_checkpoint = self.checkpoint();

        if self.is_typescript() && self.is_start_of_type_arguments() {
          if let Ok(arrow) = self.arrow_func_expr(ctx, terminators) {
            return Ok(arrow.into_wrapped());
          }
          self.restore_checkpoint(chevron_checkpoint);
        }

        if allow_type_assertions {
          if let Ok(assertion) =
            self.try_parse_angle_bracket_type_assertion(ctx, terminators, asi)
          {
            return Ok(assertion);
          }
          self.restore_checkpoint(chevron_checkpoint);
        }

        if allow_jsx {
          self.restore_checkpoint(chevron_checkpoint);
          self.jsx_elem(ctx)?.into_wrapped()
        } else {
          self.restore_checkpoint(chevron_checkpoint);
          return Err(t0.error(SyntaxErrorType::ExpectedSyntax("expression operand")));
        }
      },
      TT::KeywordClass => self.class_expr(ctx)?.into_wrapped(),
      TT::KeywordFunction => self.func_expr(ctx)?.into_wrapped(),
      TT::KeywordImport => match t1.typ {
        TT::Dot => self.import_meta()?.into_wrapped(),
        TT::ParenthesisOpen => self.import_call(ctx)?.into_wrapped(),
        _ => return Err(t0.error(SyntaxErrorType::ExpectedSyntax("import expression"))),
      },
      TT::KeywordNew if t1.typ == TT::Dot => self.new_target()?.into_wrapped(),
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
      // ES2022: Private identifier in expression position (e.g., `#field in obj`)
      TT::PrivateMember => self.with_loc(|p| {
        let name = p.consume_as_string();
        Ok(IdExpr { name })
      })?.into_wrapped(),
      TT::Invalid => {
        let raw = self.bytes(t0.loc);
        let starts_like_number = raw
          .chars()
          .next()
          .is_some_and(|c| c.is_ascii_digit() || c == '.');
        if starts_like_number && raw.ends_with('n') {
          return Err(t0.error(SyntaxErrorType::MalformedLiteralBigInt));
        }
        if starts_like_number {
          return Err(t0.error(SyntaxErrorType::MalformedLiteralNumber));
        }
        match raw.chars().next() {
          Some('"') | Some('\'') => self.lit_str()?.into_wrapped(),
          Some('`') => self.lit_template(ctx)?.into_wrapped(),
          Some('/') => self.lit_regex()?.into_wrapped(),
          _ => return Err(t0.error(SyntaxErrorType::ExpectedSyntax("expression operand"))),
        }
      }
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
    let asi_allowed = asi.can_end_with_asi && ctx.asi.allows_asi();

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
          left = Node::new(
            left.loc + t.loc,
            UnaryPostfixExpr {
              operator: operator_name,
              argument: left,
            },
          )
          .into_wrapped();
          continue;
        }
        // TypeScript: Non-null assertion: expr!
        // We need to distinguish between non-null assertion (expr!) and inequality operators (!= and !==)
        TT::Exclamation if !t.preceded_by_line_terminator => {
          let next = self.peek();
          if next.typ != TT::Equals && next.typ != TT::EqualsEquals {
            // This is a non-null assertion: expr!
            use crate::ast::expr::NonNullAssertionExpr;
            left = Node::new(
              left.loc + t.loc,
              NonNullAssertionExpr {
                expression: Box::new(left),
              },
            )
            .into_wrapped();
            continue;
          }
          // Otherwise it's != or !==, so restore checkpoint and continue loop to re-process
          // We restore so the binary operator handling code below can process != or !==
          self.restore_checkpoint(cp);
          continue; // Restart loop to re-process the ! token as part of != or !==
        }
        // Automatic Semicolon Insertion rules: no newline between operand and template literal.
        TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd
          if !t.preceded_by_line_terminator =>
        {
          let loc = t.loc;
          self.restore_checkpoint(cp);
          // ES2018: Tagged templates allow invalid escape sequences
          let parts = self.lit_template_parts(ctx, true)?;
          left = Node::new(
            left.loc + loc,
            TaggedTemplateExpr {
              function: left,
              parts,
            },
          )
          .into_wrapped();
          continue;
        }
        // TypeScript: Type assertion: expr as Type or expr as const
        TT::KeywordAs => {
          if asi_allowed && t.preceded_by_line_terminator {
            self.restore_checkpoint(cp);
            asi.did_end_with_asi = true;
            break;
          }
          // Check if this is "as const"
          if self.peek().typ == TT::KeywordConst {
            let const_loc = self.consume().loc;
            use crate::ast::expr::TypeAssertionExpr;
            left = Node::new(
              left.loc + const_loc,
              TypeAssertionExpr {
                expression: Box::new(left),
                type_annotation: None,
                const_assertion: true,
              },
            )
            .into_wrapped();
          } else {
            let type_annotation = self.type_expr(ctx)?;
            use crate::ast::expr::TypeAssertionExpr;
            left = Node::new(
              left.loc + type_annotation.loc,
              TypeAssertionExpr {
                expression: Box::new(left),
                type_annotation: Some(type_annotation),
                const_assertion: false,
              },
            )
            .into_wrapped();
          }
          continue;
        }
        // TypeScript: Satisfies expression: expr satisfies Type
        TT::KeywordSatisfies => {
          if asi_allowed && t.preceded_by_line_terminator {
            self.restore_checkpoint(cp);
            asi.did_end_with_asi = true;
            break;
          }
          let type_annotation = self.type_expr(ctx)?;
          use crate::ast::expr::SatisfiesExpr;
          left = Node::new(
            left.loc + type_annotation.loc,
            SatisfiesExpr {
              expression: Box::new(left),
              type_annotation,
            },
          )
          .into_wrapped();
          continue;
        }
        // TypeScript: Skip type arguments after identifiers/member expressions/call expressions
        // e.g., Base<T> in extends clause or getBase()<T> in class extends
        // Only treat < as type arguments if left is an identifier, member expression, or call expression.
        TT::ChevronLeft => {
          if self.is_typescript()
            && matches!(
              *left.stx,
              Expr::Id(_) | Expr::Member(_) | Expr::ComputedMember(_) | Expr::Call(_)
            )
          {
            let after_lt = self.checkpoint();
            if self.ts_type_arguments_after_chevron_left(ctx).is_ok() {
              let next = self.peek();
              let tagged_template = !next.preceded_by_line_terminator
                && matches!(
                  next.typ,
                  TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd
                );

              if next.typ == TT::ParenthesisOpen {
                self.consume(); // (
                let arguments = self.call_args(ctx).unwrap_or_default();
                if let Ok(end) = self.require(TT::ParenthesisClose) {
                  left = Node::new(
                    left.loc + end.loc,
                    CallExpr {
                      optional_chaining: false,
                      arguments,
                      callee: left,
                    },
                  )
                  .into_wrapped();
                }
                continue;
              }

              if tagged_template || self.allow_bare_ts_type_args {
                continue;
              }
            }

            // Not actually type arguments in this context; discard any speculative
            // lexing/splitting and treat `<` as a binary operator.
            self.reset_to(after_lt.next_tok_i);
          }
          // Not type arguments, continue to binary operator handling
        }
        _ => {}
      };

      match MULTARY_OPERATOR_MAPPING.get(&t.typ) {
        None => {
          if asi_allowed
            && (t.preceded_by_line_terminator || t.typ == TT::BraceClose || t.typ == TT::EOF)
          {
            // Automatic Semicolon Insertion.
            // TODO Exceptions (e.g. for loop header).
            self.restore_checkpoint(cp);
            asi.did_end_with_asi = true;
            break;
          };
          // TypeScript: Allow semicolons to terminate expressions
          // This makes the parser more permissive for error recovery
          if t.typ == TT::Semicolon {
            self.restore_checkpoint(cp);
            break;
          };
          // TypeScript: Trigger ASI when identifier/keyword follows expression
          // Enables permissive parsing like "yield foo" -> "yield" + "foo" (two statements)
          if asi_allowed && (t.typ == TT::Identifier || KEYWORDS_MAPPING.contains_key(&t.typ)) {
            self.restore_checkpoint(cp);
            asi.did_end_with_asi = true;
            break;
          };
          // TypeScript: For error recovery, trigger ASI when we see tokens that typically start new constructs
          // This handles cases like `await 1` (in contexts where await is an identifier),
          // arrow functions with malformed types `(a): =>`, object literals after expressions, etc.
          if asi_allowed
            && matches!(
              t.typ,
              TT::Colon |           // Arrow function malformed type annotation: (a):
            TT::BraceOpen |       // New object/block after expression
            TT::LiteralNumber |   // Number after identifier: `await 1` where await is identifier
            TT::LiteralString |   // String after expression
            TT::LiteralTrue |     // Boolean after expression
            TT::LiteralFalse |    // Boolean after expression
            TT::LiteralNull |     // Null after expression
            TT::ChevronLeftSlash // JSX closing tag: </div> after JSX element with text children
            )
          {
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
              Node::new(
                left.loc + end.loc,
                CallExpr {
                  optional_chaining: match operator.name {
                    OperatorName::OptionalChainingCall => true,
                    _ => false,
                  },
                  arguments,
                  callee: left,
                },
              )
              .into_wrapped()
            }
            OperatorName::ComputedMemberAccess
            | OperatorName::OptionalChainingComputedMemberAccess => {
              // TypeScript: Allow empty bracket expressions for error recovery: obj[]
              let member = if self.peek().typ == TT::BracketClose {
                let loc = self.peek().loc;
                self.create_synthetic_undefined(loc)
              } else {
                self.expr(ctx, [TT::BracketClose]).unwrap_or_else(|_| {
                  let loc = self.peek().loc;
                  self.create_synthetic_undefined(loc)
                })
              };
              let end = self.require(TT::BracketClose)?;
              Node::new(
                left.loc + end.loc,
                ComputedMemberExpr {
                  optional_chaining: operator.name
                    == OperatorName::OptionalChainingComputedMemberAccess,
                  object: left,
                  member,
                },
              )
              .into_wrapped()
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
              Node::new(
                left.loc + alternate.loc,
                CondExpr {
                  test: left,
                  consequent,
                  alternate,
                },
              )
              .into_wrapped()
            }
            OperatorName::MemberAccess | OperatorName::OptionalChainingMemberAccess => {
              let checkpoint = self.checkpoint();
              let right_tok = self.consume();
              let mut prop = String::new();
              let mut right = right_tok.loc;
              match right_tok.typ {
                TT::Identifier | TT::PrivateMember => {
                  prop = self.string(right);
                }
                t if KEYWORDS_MAPPING.contains_key(&t) => {
                  prop = self.string(right);
                }
                _ => {
                  // Error recovery: if the next token is a likely terminator for the containing
                  // expression/block, don't consume it; instead, fabricate an empty property name
                  // and let the outer parser handle the terminator.
                  if matches!(
                    right_tok.typ,
                    TT::BraceClose
                      | TT::ParenthesisClose
                      | TT::BracketClose
                      | TT::Semicolon
                      | TT::EOF
                  ) {
                    self.restore_checkpoint(checkpoint);
                    right = left.loc;
                    prop.clear();
                  }
                }
              }
              Node::new(
                left.loc + right,
                MemberExpr {
                  optional_chaining: operator.name == OperatorName::OptionalChainingMemberAccess,
                  left,
                  right: prop,
                },
              )
              .into_wrapped()
            }
            _ => {
              if operator.name == OperatorName::Exponentiation {
                let is_parenthesized = left.assoc.get::<ParenthesizedExpr>().is_some();
                let is_disallowed = match left.stx.as_ref() {
                  Expr::Unary(unary) => matches!(
                    unary.stx.operator,
                    OperatorName::Await
                      | OperatorName::BitwiseNot
                      | OperatorName::Delete
                      | OperatorName::LogicalNot
                      | OperatorName::Typeof
                      | OperatorName::UnaryNegation
                      | OperatorName::UnaryPlus
                      | OperatorName::Void
                  ),
                  Expr::TypeAssertion(_) => true,
                  _ => false,
                };
                if !is_parenthesized && is_disallowed {
                  return Err(t.error(SyntaxErrorType::ExpectedSyntax("parenthesized expression")));
                }
              }
              if operator.name.is_assignment() {
                left = lhs_expr_to_assign_target(left, operator.name)?;
              };
              let right = self.expr_with_min_prec(ctx, next_min_prec, terminators, asi)?;
              Node::new(
                left.loc + right.loc,
                BinaryExpr {
                  operator: operator.name,
                  left,
                  right,
                },
              )
              .into_wrapped()
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

  pub fn new_target(&mut self) -> SyntaxResult<Node<NewTarget>> {
    self.with_loc(|p| {
      p.require(TT::KeywordNew)?;
      p.require(TT::Dot)?;
      let prop = p.require(TT::Identifier)?;
      if p.str(prop.loc) != "target" {
        return Err(prop.error(SyntaxErrorType::ExpectedSyntax("`target` property")));
      };
      Ok(NewTarget {}.into())
    })
  }
}
