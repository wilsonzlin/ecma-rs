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
use crate::ast::expr::InstantiationExpr;
use crate::ast::expr::MemberExpr;
use crate::ast::expr::NewTarget;
use crate::ast::expr::SuperExpr;
use crate::ast::expr::TaggedTemplateExpr;
use crate::ast::expr::ThisExpr;
use crate::ast::expr::UnaryExpr;
use crate::ast::expr::UnaryPostfixExpr;
use crate::ast::func::Func;
use crate::ast::node::Node;
use crate::ast::node::ParenthesizedExpr;
use crate::ast::stmt::decl::ParamDecl;
use crate::ast::stmt::decl::PatDecl;
use crate::ast::type_expr::TypeExpr;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::LexMode;
use crate::lex::KEYWORDS_MAPPING;
use crate::loc::Loc;
use crate::operator::Associativity;
use crate::operator::OperatorName;
use crate::operator::OPERATORS;
use crate::parse::operator::MULTARY_OPERATOR_MAPPING;
use crate::parse::operator::UNARY_OPERATOR_MAPPING;
use crate::token::TT;
use pat::is_valid_pattern_identifier;
use pat::ParsePatternRules;
use util::lhs_expr_to_assign_target_with_recover;

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

/// `true` when `expr` is an unparenthesized `new` without Arguments.
///
/// Per ECMA-262, `new MemberExpression Arguments` is itself a MemberExpression and may
/// be followed by OptionalChain (`new F()?.x`). Bare `new NewExpression` (no Arguments)
/// is only a NewExpression, so `new F?.x` / `new F?.()` are SyntaxErrors unless the
/// `new` is parenthesized: `(new F)?.x`.
fn is_bare_new_expression(expr: &Node<Expr>) -> bool {
  if expr.assoc.get::<ParenthesizedExpr>().is_some() {
    return false;
  }
  match expr.stx.as_ref() {
    Expr::Unary(u) if u.stx.operator == OperatorName::New => {
      !matches!(u.stx.argument.stx.as_ref(), Expr::Call(_))
    }
    Expr::Instantiation(inst) => is_bare_new_expression(&inst.stx.expression),
    _ => false,
  }
}

/// Unparenthesized `&&` / `||` binary (not `??`).
fn is_unparen_logical_and_or(expr: &Node<Expr>) -> bool {
  if expr.assoc.get::<ParenthesizedExpr>().is_some() {
    return false;
  }
  matches!(
    expr.stx.as_ref(),
    Expr::Binary(b)
      if matches!(
        b.stx.operator,
        OperatorName::LogicalAnd | OperatorName::LogicalOr
      )
  )
}

/// Unparenthesized `??` binary.
fn is_unparen_nullish_coalesce(expr: &Node<Expr>) -> bool {
  if expr.assoc.get::<ParenthesizedExpr>().is_some() {
    return false;
  }
  matches!(
    expr.stx.as_ref(),
    Expr::Binary(b) if b.stx.operator == OperatorName::NullishCoalescing
  )
}

/// Whether `expr` is an OptionalExpression (unparenthesized chain involving `?.`).
///
/// Parentheses break the production: `(a?.b)`\`tpl\` is legal; `a?.b`\`tpl\` is not.
fn is_optional_expression(expr: &Node<Expr>) -> bool {
  if expr.assoc.get::<ParenthesizedExpr>().is_some() {
    return false;
  }
  match expr.stx.as_ref() {
    Expr::Member(m) if m.stx.optional_chaining => true,
    Expr::ComputedMember(m) if m.stx.optional_chaining => true,
    Expr::Call(c) if c.stx.optional_chaining => true,
    Expr::Member(m) => is_optional_expression(&m.stx.left),
    Expr::ComputedMember(m) => is_optional_expression(&m.stx.object),
    Expr::Call(c) => is_optional_expression(&c.stx.callee),
    Expr::Instantiation(inst) => is_optional_expression(&inst.stx.expression),
    _ => false,
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

  /// ClassHeritage must be a LeftHandSideExpression (ECMA-262 §15.7).
  pub fn class_heritage(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Expr>> {
    let prev = self.allow_bare_ts_type_args;
    self.allow_bare_ts_type_args = true;
    // AssignmentExpression (no comma): precedence 2 is above Comma.
    let out = self.expr_with_min_prec(
      ctx,
      2,
      [TT::BraceOpen, TT::KeywordImplements],
      &mut Asi::no(),
    );
    self.allow_bare_ts_type_args = prev;
    let expr = out?;
    if self.is_strict_ecmascript() && !Self::is_left_hand_side_expression(&expr) {
      return Err(expr.error(SyntaxErrorType::InvalidClassHeritage));
    }
    Ok(expr)
  }

  fn is_left_hand_side_expression(expr: &Node<Expr>) -> bool {
    // ParenthesizedExpression is a PrimaryExpression, hence a LeftHandSideExpression,
    // regardless of the inner Expression (e.g. `extends (a + b)` is legal).
    if expr.assoc.get::<ParenthesizedExpr>().is_some() {
      return true;
    }
    match expr.stx.as_ref() {
      Expr::Id(_)
      | Expr::This(_)
      | Expr::Super(_)
      | Expr::NewTarget(_)
      | Expr::ImportMeta(_)
      | Expr::Import(_)
      | Expr::LitNum(_)
      | Expr::LitStr(_)
      | Expr::LitBool(_)
      | Expr::LitNull(_)
      | Expr::LitBigInt(_)
      | Expr::LitRegex(_)
      | Expr::LitArr(_)
      | Expr::LitObj(_)
      | Expr::LitTemplate(_)
      | Expr::Func(_)
      | Expr::ArrowFunc(_)
      | Expr::Class(_)
      | Expr::TaggedTemplate(_) => true,
      Expr::Member(m) => Self::is_left_hand_side_expression(&m.stx.left),
      Expr::ComputedMember(m) => Self::is_left_hand_side_expression(&m.stx.object),
      Expr::Call(c) => Self::is_left_hand_side_expression(&c.stx.callee),
      Expr::Instantiation(i) => Self::is_left_hand_side_expression(&i.stx.expression),
      // tsc `isLeftHandSideExpressionKind`: NonNullExpression is a LHS.
      Expr::NonNullAssertion(n) => Self::is_left_hand_side_expression(&n.stx.expression),
      Expr::Unary(u) if u.stx.operator == OperatorName::New => {
        // `new super` / `new super()` are not valid NewExpressions.
        match u.stx.argument.stx.as_ref() {
          Expr::Super(_) => false,
          Expr::Call(c) if matches!(c.stx.callee.stx.as_ref(), Expr::Super(_)) => false,
          Expr::Call(_) => true,
          _ => Self::is_left_hand_side_expression(&u.stx.argument),
        }
      }
      // Parentheses are assoc markers on the same node; Binary/Unary/etc. stay non-LHS.
      _ => false,
    }
  }

  fn ts_type_arguments_after_chevron_left(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<(Vec<Node<TypeExpr>>, crate::loc::Loc)> {
    let mut type_arguments = Vec::new();
    let close_loc = loop {
      if matches!(
        self.peek().typ,
        TT::ChevronRight
          | TT::ChevronRightEquals
          | TT::ChevronRightChevronRight
          | TT::ChevronRightChevronRightEquals
          | TT::ChevronRightChevronRightChevronRight
          | TT::ChevronRightChevronRightChevronRightEquals
      ) {
        break self.require_chevron_right()?.loc;
      }

      type_arguments.push(self.type_expr(ctx)?);
      if self.consume_if(TT::Comma).is_match() {
        continue;
      }
      break self.require_chevron_right()?.loc;
    };
    Ok((type_arguments, close_loc))
  }

  fn can_start_expression(typ: TT) -> bool {
    use TT::*;
    matches!(
      typ,
      // Identifiers.
      Identifier | PrivateMember
        // Literals.
        | LiteralBigInt
        | LiteralFalse
        | LiteralNull
        | LiteralNumber
        | LiteralRegex
        | LiteralString
        | LiteralTemplatePartString
        | LiteralTemplatePartStringEnd
        | LiteralTrue
        // Groupings/literals.
        | ParenthesisOpen
        | BracketOpen
        | BraceOpen
        // TS/JSX: could start JSX or type assertion.
        | ChevronLeft
        // Keywords that begin primary expressions.
        | KeywordThis
        | KeywordSuper
        | KeywordNew
        | KeywordImport
        | KeywordFunction
        | KeywordClass
        // Unary operators.
        | Plus
        | Hyphen
        | Exclamation
        | Tilde
        | PlusPlus
        | HyphenHyphen
        | KeywordAwait
        | KeywordDelete
        | KeywordTypeof
        | KeywordVoid
        | KeywordYield
        // Decorated class expression.
        | At
        // Error recovery.
        | Invalid
    )
  }

  fn can_follow_type_arguments_in_expression(next: TT) -> bool {
    matches!(
      next,
      TT::ParenthesisOpen
        | TT::QuestionDotParenthesisOpen
        | TT::BracketOpen
        | TT::QuestionDotBracketOpen
    ) || !Self::can_start_expression(next)
  }

  /// Parses a parenthesised expression like `(a + b)`.
  pub fn grouping(&mut self, ctx: ParseCtx, asi: &mut Asi) -> SyntaxResult<Node<Expr>> {
    self.require(TT::ParenthesisOpen)?;
    // TypeScript-style recovery: Allow empty parenthesized expressions `()` and
    // comma operators with missing operands like `(, x)` or `(x, )`.
    let mut expr = if self.should_recover() {
      if self.peek().typ == TT::ParenthesisClose {
        let loc = self.peek().loc;
        self.create_synthetic_undefined(loc)
      } else {
        self
          .expr_with_min_prec(ctx, 1, [TT::ParenthesisClose], asi)
          .unwrap_or_else(|_| {
            let loc = self.peek().loc;
            self.create_synthetic_undefined(loc)
          })
      }
    } else {
      self.expr_with_min_prec(ctx, 1, [TT::ParenthesisClose], asi)?
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
    // Nested arrows (e.g. default values while speculating an outer paren list
    // as parameters) must not sticky-set `arrow_parse_committed` for the outer
    // speculation. Save/restore around this call; only a failure *after this
    // arrow's own `=>`* leaves the flag set so callers refuse to backtrack.
    let saved_committed = self.arrow_parse_committed;
    self.arrow_parse_committed = false;
    let result = self.arrow_func_expr_inner(ctx, terminators);
    match &result {
      Ok(_) => {
        self.arrow_parse_committed = saved_committed;
      }
      Err(_) => {
        if !self.arrow_parse_committed {
          self.arrow_parse_committed = saved_committed;
        }
      }
    }
    result
  }

  fn arrow_func_expr_inner<const N: usize>(
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
      let is_unparenthesised_single_param = is_valid_pattern_identifier(next_token, ctx.rules) && {
        // Need to peek further to see if there's => coming up
        let peek2 = p.peek_n::<2>()[1].typ;
        // Could be either:
        // - identifier =>
        // - identifier : type =>
        peek2 == TT::EqualsChevronRight || (!p.is_strict_ecmascript() && peek2 == TT::Colon)
      };

      let (type_parameters, parameters, return_type, arrow) = if is_unparenthesised_single_param {
        // Single-unparenthesised-parameter arrow function.
        // Parse arrow first for fast fail (and in case we are merely trying to parse as arrow function), before we mutate state by creating nodes and adding symbols.
        let param_name = p.consume().loc;
        // TypeScript: return type annotation (after param, before =>) - may be type predicate.
        let return_type = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
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
        let type_parameters = if !p.is_strict_ecmascript()
          && p.peek().typ == TT::ChevronLeft
          && p.is_start_of_type_arguments()
        {
          Some(p.type_parameters(ctx)?)
        } else {
          None
        };
        // ArrowParameters inherit [?Yield, ?Await] from the enclosing context, but
        // YieldExpression / AwaitExpression in the parameter list are early errors.
        let params = p.func_params(ctx.with_rules(ctx.rules.for_formal_parameters()))?;
        // TypeScript: return type annotation (after params, before =>) - may be type predicate.
        let return_type = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr_or_predicate(ctx)?)
        } else {
          None
        };
        let arrow = p.require(TT::EqualsChevronRight)?;
        (type_parameters, params, return_type, arrow)
      };

      // Committed to an arrow function once `=>` is present: speculative
      // "arrow vs grouping" callers must not backtrack from subsequent errors.
      p.arrow_parse_committed = true;
      if arrow.preceded_by_line_terminator {
        // Illegal under Automatic Semicolon Insertion rules.
        return Err(arrow.error(SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters));
      }
      let is_module = p.is_module();
      let fn_body_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: if is_module { false } else { !is_async },
        yield_allowed: !is_module,
        await_expr_allowed: is_async,
        yield_expr_allowed: false,
      });
      let simple_params = Parser::is_simple_parameter_list(&parameters);
      // `new.target` is allowed in an arrow body only when an enclosing non-arrow
      // function (or class field/static-block) already provides a `new.target`
      // binding. Arrows inherit `new_target_allowed` from the enclosing context;
      // they must not invent one (ECMA-262 §13.3.12 / static semantics; TS17013).
      let body = match p.peek().typ {
        TT::BraceOpen => {
          let contains_use_strict =
            p.is_strict_ecmascript() && p.has_use_strict_directive_in_block_body()?;
          if p.is_strict_ecmascript() && contains_use_strict && !simple_params {
            return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
              "`use strict` directive not allowed with a non-simple parameter list",
            )));
          }

          let prev_strict_mode = p.strict_mode;
          if p.is_strict_ecmascript() && contains_use_strict && !p.is_strict_mode() {
            p.strict_mode += 1;
          }
          let res = (|| {
            p.validate_formal_parameters(None, &parameters, simple_params, true)?;
            p.parse_func_block_body(fn_body_ctx)
          })();
          p.strict_mode = prev_strict_mode;
          res?.into()
        }
        _ => {
          p.validate_formal_parameters(None, &parameters, simple_params, true)?;
          // ConciseBody is an AssignmentExpression (ECMA-262 §14.2): a top-level
          // comma belongs to the *enclosing* sequence expression, so parse one
          // precedence level above Comma (same idiom as `class_heritage`).
          // `x => a, b` is `(x => a), b`, not `x => (a, b)`.
          p.expr_with_min_prec(fn_body_ctx, 2, terminators, &mut Asi::can())?
            .into()
        }
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
    // If we fail before `=>`, backtrack and parse as grouping instead.
    // After we see `=>`, we are committed to an arrow function and must not
    // backtrack — otherwise body early errors (e.g. top-level `new.target`) are
    // swallowed and resurface as a misleading empty-grouping `PS0002`.

    // NOTE: We originally implemented conversion from parameters to expression to prevent the need
    // for backtracking. However, this ended up being too complex for little performance gain,
    // as most usages of grouping involve a non-comma binary operator (such as `+`) and so parsing
    // as arrow function fails quickly. Complex patterns like `{a, b: { c: [d, e] } = f }` are
    // unlikely to be used as operands in a grouping.

    self.arrow_parse_committed = false;
    match self.rewindable::<Node<Expr>, _>(|p| match p.arrow_func_expr(ctx, terminators) {
      Ok(expr) => Ok(Some(expr.into_wrapped())),
      Err(err) if p.arrow_parse_committed => Err(err),
      Err(err)
        if matches!(
          err.typ,
          SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters
            | SyntaxErrorType::InvalidRestParameter
        ) =>
      {
        // Rest-parameter grammar errors are unambiguous even before `=>`; do not
        // swallow them as a failed arrow speculation and reparse as grouping.
        Err(err)
      }
      Err(_) => Ok(None),
    }) {
      Ok(Some(expr)) => Ok(expr),
      Ok(None) => self.grouping(ctx, asi),
      Err(err) => Err(err),
    }
  }

  pub fn func_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<FuncExpr>> {
    self.with_loc(|p| {
      let is_async = p.consume_if(TT::KeywordAsync).is_match();
      p.require(TT::KeywordFunction)?;
      let generator = p.consume_if(TT::Asterisk).is_match();
      let is_module = p.is_module();
      // The name of a named function expression is bound in the function-expression-name scope,
      // so `await`/`yield` should be reserved based on the function's own async/generator status.
      let name_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: if is_module { false } else { !is_async },
        yield_allowed: if is_module { false } else { !generator },
        await_expr_allowed: false,
        yield_expr_allowed: false,
      });
      let name = p.maybe_class_or_func_name(name_ctx);
      let func = p.with_loc(|p| {
        // TypeScript: generic type parameters
        let type_parameters = if !p.is_strict_ecmascript()
          && p.peek().typ == TT::ChevronLeft
          && p.is_start_of_type_arguments()
        {
          Some(p.type_parameters(ctx)?)
        } else {
          None
        };
        // Body may allow yield/await expressions; FormalParameters must not
        // (ECMA-262 §15.5.1 / §15.1.1 — Contains YieldExpression / AwaitExpression).
        let fn_ctx = ctx.with_rules(ParsePatternRules {
          await_allowed: if is_module { false } else { !is_async },
          yield_allowed: if is_module { false } else { !generator },
          await_expr_allowed: is_async,
          yield_expr_allowed: generator,
        });
        let param_ctx = fn_ctx.with_rules(fn_ctx.rules.for_formal_parameters());
        // Parameter defaults evaluate in the function's binding environment.
        let parameters = p.with_non_arrow_func_bindings(|p| p.func_params(param_ctx))?;
        // TypeScript: return type annotation - may be type predicate
        let return_type = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr_or_predicate(ctx)?)
        } else {
          None
        };
        let contains_use_strict =
          p.is_strict_ecmascript() && p.has_use_strict_directive_in_block_body()?;
        let simple_params = Parser::is_simple_parameter_list(&parameters);
        if p.is_strict_ecmascript() && contains_use_strict && !simple_params {
          return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
            "`use strict` directive not allowed with a non-simple parameter list",
          )));
        }

        let prev_strict_mode = p.strict_mode;
        if p.is_strict_ecmascript() && contains_use_strict && !p.is_strict_mode() {
          p.strict_mode += 1;
        }
        let res = (|| {
          p.validate_formal_parameters(name.as_ref(), &parameters, simple_params, false)?;
          p.parse_non_arrow_func_block_body(fn_ctx)
        })();
        p.strict_mode = prev_strict_mode;
        let body = res?.into();
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
      let prev_strict_mode = p.strict_mode;
      if p.is_strict_ecmascript() {
        p.strict_mode += 1;
      }
      let res = (|| {
        let name = p.maybe_class_or_func_name(ctx);
        if let Some(name) = name.as_ref() {
          p.validate_strict_binding_identifier_name(name.loc, &name.stx.name)?;
        }

        // TypeScript: generic type parameters
        let type_parameters = if !p.is_strict_ecmascript()
          && p.peek().typ == TT::ChevronLeft
          && p.is_start_of_type_arguments()
        {
          Some(p.type_parameters(ctx)?)
        } else {
          None
        };

        let extends = p
          .consume_if(TT::KeywordExtends)
          .and_then(|| p.class_heritage(ctx))?;

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

        let is_derived_class = extends.is_some();
        let prev_class_depth = p.class_is_derived.len();
        p.class_is_derived.push(is_derived_class);
        let members = p.class_body(ctx);
        p.class_is_derived.truncate(prev_class_depth);
        let members = members?;
        Ok(ClassExpr {
          decorators: Vec::new(),
          name,
          type_parameters,
          extends,
          implements,
          members,
        })
      })();
      p.strict_mode = prev_strict_mode;
      res
    })
  }

  pub fn class_expr_with_decorators(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ClassExpr>> {
    self.with_loc(|p| {
      let decorators = p.decorators(ctx)?;
      p.require(TT::KeywordClass)?.loc;
      let prev_strict_mode = p.strict_mode;
      if p.is_strict_ecmascript() {
        p.strict_mode += 1;
      }
      let res = (|| {
        let name = p.maybe_class_or_func_name(ctx);
        if let Some(name) = name.as_ref() {
          p.validate_strict_binding_identifier_name(name.loc, &name.stx.name)?;
        }

        // TypeScript: generic type parameters
        let type_parameters = if !p.is_strict_ecmascript()
          && p.peek().typ == TT::ChevronLeft
          && p.is_start_of_type_arguments()
        {
          Some(p.type_parameters(ctx)?)
        } else {
          None
        };

        let extends = p
          .consume_if(TT::KeywordExtends)
          .and_then(|| p.class_heritage(ctx))?;

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

        let is_derived_class = extends.is_some();
        let prev_class_depth = p.class_is_derived.len();
        p.class_is_derived.push(is_derived_class);
        let members = p.class_body(ctx);
        p.class_is_derived.truncate(prev_class_depth);
        let members = members?;
        Ok(ClassExpr {
          decorators,
          name,
          type_parameters,
          extends,
          implements,
          members,
        })
      })();
      p.strict_mode = prev_strict_mode;
      res
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
    let name = self.string(t.loc);
    // IdentifierReference / LabelIdentifier [Await]/[Yield]: StringValue checks
    // catch escaped forms (`\u0061wait` / `yi\u0065ld`) that lex as Identifier.
    // Strict reserved words similarly key off StringValue, not the raw escape spelling.
    let string_value = self.identifier_string_value(t.loc);
    if (!ctx.rules.await_allowed && string_value == "await")
      || (!ctx.rules.yield_allowed && string_value == "yield")
    {
      return Err(t.error(SyntaxErrorType::ExpectedSyntax("identifier")));
    }
    if self.is_strict_ecmascript()
      && self.is_strict_mode()
      && Parser::is_strict_mode_reserved_word(&string_value)
    {
      return Err(t.error(SyntaxErrorType::ExpectedSyntax("identifier")));
    }
    Ok(name)
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
          | TT::KeywordIntrinsic
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
        // Treat await/yield as operators only when they're allowed in the current context.
        //
        // - In scripts, `await`/`yield` are typically identifiers; parsing them as operators
        //   would accept invalid programs like `await 1` and `yield 1`.
        // - In modules, top-level `await` is allowed but `yield` is never allowed outside a
        //   generator function.
        match operator.name {
          OperatorName::Await => ctx.rules.await_expr_allowed,
          OperatorName::Yield => ctx.rules.yield_expr_allowed,
          _ => true,
        }
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
            let op_tok = p.consume_with_mode(LexMode::SlashIsRegex);
            let operator = match operator.name {
              OperatorName::Yield if p.peek().typ == TT::Asterisk => {
                let star_tok = p.peek();
                if star_tok.preceded_by_line_terminator {
                  return Err(star_tok.error(SyntaxErrorType::LineTerminatorAfterYield));
                }
                p.consume(); // *
                &OPERATORS[&OperatorName::YieldDelegated]
              }
              _ => *operator,
            };
            let next_min_prec =
              operator.precedence + (operator.associativity == Associativity::Left) as u8;

            let next_token = p.peek();
            let starts_assignment_expr = || {
              // Yield's operand is an AssignmentExpression (and is optional for
              // plain `yield`). Only treat the following token as the start of
              // an operand if it can actually begin an expression; otherwise
              // we should parse `yield` with no operand and let higher-level
              // expression parsing handle (and potentially reject) any
              // continuation operators like `?`, `||`, `.`, `(`, etc.
              let typ = next_token.typ;
              // Identifiers (including contextual keywords when allowed).
              is_valid_pattern_identifier(typ, ctx.rules)
                // Await/Yield expressions can start with their respective keywords even when
                // they aren't allowed as identifiers.
                || (typ == TT::KeywordAwait && ctx.rules.await_expr_allowed)
                || (typ == TT::KeywordYield && ctx.rules.yield_expr_allowed)
                // Primary expressions.
                || matches!(
                  typ,
                  TT::ParenthesisOpen
                    | TT::BracketOpen
                    | TT::BraceOpen
                    | TT::KeywordThis
                    | TT::KeywordSuper
                    | TT::KeywordFunction
                    | TT::KeywordClass
                    | TT::KeywordNew
                    | TT::KeywordImport
                    | TT::PrivateMember
                    | TT::LiteralBigInt
                    | TT::LiteralTrue
                    | TT::LiteralFalse
                    | TT::LiteralNull
                    | TT::LiteralNumber
                    | TT::LiteralRegex
                    | TT::LiteralString
                    | TT::LiteralTemplatePartString
                    | TT::LiteralTemplatePartStringEnd
                    | TT::Invalid
                )
                // `<` can start JSX elements or TypeScript angle-bracket
                // assertions in dialects that support them.
                || (typ == TT::ChevronLeft
                  && (p.allows_jsx() || p.allows_angle_bracket_type_assertions()))
                // Unary operators.
                || matches!(
                  typ,
                  TT::Plus
                    | TT::Hyphen
                    | TT::PlusPlus
                    | TT::HyphenHyphen
                    | TT::Exclamation
                    | TT::Tilde
                    | TT::KeywordDelete
                    | TT::KeywordTypeof
                    | TT::KeywordVoid
                )
                // In expression-operand context, `/` and `/=` begin a regular
                // expression literal (the lexer decides based on mode).
                || matches!(typ, TT::Slash | TT::SlashEquals)
                || (p.should_recover() && typ == TT::At)
            };

            let has_operand = match operator.name {
              // `yield` without an operand is valid. `yield` with an operand
              // requires no line terminator.
              OperatorName::Yield => {
                !next_token.preceded_by_line_terminator
                  && next_token.typ != TT::EOF
                  && next_token.typ != TT::Semicolon
                  && next_token.typ != TT::Comma
                  && next_token.typ != TT::ParenthesisClose
                  && next_token.typ != TT::BracketClose
                  && next_token.typ != TT::BraceClose
                  && !terminators.contains(&next_token.typ)
                  && starts_assignment_expr()
              }
              // `await` and `yield*` always require an operand. Line terminators are
              // allowed between the operator and its operand (except between `yield`
              // and `*`, checked above).
              OperatorName::YieldDelegated | OperatorName::Await => {
                next_token.typ != TT::EOF
                  && next_token.typ != TT::Semicolon
                  && next_token.typ != TT::Comma
                  && next_token.typ != TT::ParenthesisClose
                  && next_token.typ != TT::BracketClose
                  && next_token.typ != TT::BraceClose
                  && !terminators.contains(&next_token.typ)
                  && starts_assignment_expr()
              }
              _ => {
                if p.should_recover() {
                  // TypeScript-style recovery: allow missing operand for error recovery
                  // Accept semicolon, closing braces/brackets/parens as missing operand
                  next_token.typ != TT::Semicolon
                    && next_token.typ != TT::ParenthesisClose
                    && next_token.typ != TT::BracketClose
                    && next_token.typ != TT::BraceClose
                    && next_token.typ != TT::EOF
                    && !terminators.contains(&next_token.typ)
                } else {
                  true
                }
              }
            };

            let operand = if has_operand {
              if operator.name == OperatorName::New {
                // `new` has tricky precedence rules in ECMAScript: `new Foo().bar` should parse as
                // `(new Foo()).bar`, not `new (Foo().bar)`.
                //
                // `parse-js` represents `new Foo()` as a `UnaryExpr(New)` whose `argument` is a
                // `CallExpr` node (holding the constructor target and arguments). To preserve
                // correct chaining semantics, we must parse **only** the constructor target
                // (including member access within the callee, e.g. `Foo.bar`) and the optional
                // argument list, but we must *not* eagerly consume further member/call operators
                // after that argument list.
                //
                // Without this special-case, `new Foo().bar` would incorrectly build
                // `Unary(New, Member(Call(Foo()), "bar"))`, which evaluates `Foo()` as a *call*
                // before applying `new`, breaking real-world patterns like
                // `new URL("...").href` / `new URL("...").searchParams.get("q")`.

                // Parse the constructor target expression without consuming call syntax.
                let mut callee = p.expr_operand(ctx, terminators, asi)?;

                // Consume member access chains (`new Foo.bar()`).
                //
                // ECMA-262: `new`'s callee is a MemberExpression. An OptionalExpression
                // is not, so `?.` / `?.[]` / `?.()` cannot appear in this position
                // (`new a?.b`, `new a?.[b]`, `new a?.()` — SyntaxError; mirrors TS1209).
                // Parenthesized forms like `new (a?.b)` are fine: the chain is inside
                // PrimaryExpression and never reaches this loop as a `?.` token.
                loop {
                  match p.peek().typ {
                    TT::QuestionDot
                    | TT::QuestionDotBracketOpen
                    | TT::QuestionDotParenthesisOpen => {
                      return Err(p.peek().error(SyntaxErrorType::InvalidOptionalChainFromNew));
                    }
                    TT::Dot => {
                      p.consume();

                      let checkpoint = p.checkpoint();
                      let right_tok = p.consume();
                      let mut prop = String::new();
                      let mut right = right_tok.loc;
                      match right_tok.typ {
                        TT::Identifier | TT::PrivateMember => {
                          // IdentifierName StringValue: decode `\uXXXX` / `\u{…}` escapes.
                          p.report_bare_private_hash_if_needed(&right_tok);
                          prop = p.identifier_string_value(right);
                        }
                        t if KEYWORDS_MAPPING.contains_key(&t) => {
                          prop = p.identifier_string_value(right);
                        }
                        _ => {
                          if !p.should_recover() {
                            return Err(
                              right_tok.error(SyntaxErrorType::ExpectedSyntax("property name")),
                            );
                          }
                          if matches!(
                            right_tok.typ,
                            TT::BraceClose
                              | TT::ParenthesisClose
                              | TT::BracketClose
                              | TT::Semicolon
                              | TT::EOF
                          ) {
                            // Recovery: don't consume likely terminators.
                            p.restore_checkpoint(checkpoint);
                            right = callee.loc;
                            prop.clear();
                          }
                        }
                      }

                      callee = Node::new(
                        callee.loc + right,
                        MemberExpr {
                          optional_chaining: false,
                          left: callee,
                          right: prop,
                        },
                      )
                      .into_wrapped();
                      continue;
                    }
                    TT::BracketOpen => {
                      p.consume();

                      let member = if p.should_recover() {
                        if p.peek().typ == TT::BracketClose {
                          let loc = p.peek().loc;
                          p.create_synthetic_undefined(loc)
                        } else {
                          p.expr(ctx, [TT::BracketClose]).unwrap_or_else(|_| {
                            let loc = p.peek().loc;
                            p.create_synthetic_undefined(loc)
                          })
                        }
                      } else {
                        p.expr(ctx, [TT::BracketClose])?
                      };
                      let end = p.require(TT::BracketClose)?;

                      callee = Node::new(
                        callee.loc + end.loc,
                        ComputedMemberExpr {
                          optional_chaining: false,
                          object: callee,
                          member,
                        },
                      )
                      .into_wrapped();
                      continue;
                    }
                    _ => break,
                  }
                }

                // TypeScript: Allow explicit type arguments on constructor targets
                // (`new Foo<T>()`, `new Foo.Bar<T>()`).
                if p.is_typescript()
                  && p.peek().typ == TT::ChevronLeft
                  && p.is_start_of_type_arguments()
                {
                  if let Some((type_arguments, close_loc)) = p.rewindable(|p| {
                    p.require(TT::ChevronLeft)?;
                    let (type_arguments, close_loc) =
                      match p.ts_type_arguments_after_chevron_left(ctx) {
                        Ok(res) => res,
                        Err(_) => return Ok(None),
                      };

                    let next = p.peek();
                    let tagged_template = !next.preceded_by_line_terminator
                      && matches!(
                        next.typ,
                        TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd
                      );

                    if p.allow_bare_ts_type_args
                      || tagged_template
                      || Self::can_follow_type_arguments_in_expression(next.typ)
                    {
                      Ok(Some((type_arguments, close_loc)))
                    } else {
                      Ok(None)
                    }
                  })? {
                    callee = Node::new(
                      callee.loc + close_loc,
                      InstantiationExpr {
                        expression: Box::new(callee),
                        type_arguments,
                      },
                    )
                    .into_wrapped();
                  }
                }

                // Optional argument list (`new Foo(...)`).
                if p.peek().typ == TT::ParenthesisOpen {
                  p.consume(); // (
                  let arguments = p.call_args(ctx)?;
                  let end = p.require(TT::ParenthesisClose)?;
                  callee = Node::new(
                    callee.loc + end.loc,
                    CallExpr {
                      optional_chaining: false,
                      arguments,
                      callee,
                    },
                  )
                  .into_wrapped();
                }

                // `new super` / `new super()` are SyntaxErrors: SuperCall is not a
                // MemberExpression under NewExpression. `new super.x` / `new super[x]()`
                // use SuperProperty and are legal.
                if p.is_strict_ecmascript() {
                  let illegal_new_super = match callee.stx.as_ref() {
                    Expr::Super(_) => true,
                    Expr::Call(c) if matches!(c.stx.callee.stx.as_ref(), Expr::Super(_)) => true,
                    _ => false,
                  };
                  if illegal_new_super {
                    return Err(callee.error(SyntaxErrorType::ExpectedSyntax(
                      "new cannot be used with super",
                    )));
                  }
                }

                callee
              } else {
                p.expr_with_min_prec(ctx, next_min_prec, terminators, asi)?
              }
            } else {
              match operator.name {
                OperatorName::Await | OperatorName::YieldDelegated => {
                  return Err(
                    next_token.error(SyntaxErrorType::ExpectedSyntax("expression operand")),
                  );
                }
                _ => {
                  // For unary operators without operand, use `undefined` identifier for error recovery
                  p.create_synthetic_undefined(op_tok.loc)
                }
              }
            };

            if matches!(
              operator.name,
              OperatorName::PrefixIncrement | OperatorName::PrefixDecrement
            ) {
              p.validate_update_operand(&operand)?;
            }

            // ES strict mode (incl. modules): `delete IdentifierReference` is a syntax error.
            if operator.name == OperatorName::Delete
              && p.is_strict_ecmascript()
              && p.is_strict_mode()
            {
              if matches!(operand.stx.as_ref(), Expr::Id(_)) {
                return Err(op_tok.error(SyntaxErrorType::ExpectedSyntax(
                  "delete of an unqualified identifier in strict mode",
                )));
              }
            }

            Ok(UnaryExpr {
              operator: operator.name,
              argument: operand,
            })
          })?
          .into_wrapped(),
      );
    };

    // Check for async keyword first, before checking if it's a valid identifier.
    // Exception: `async => ...` should be treated as a parameter name, not async keyword.
    //
    // Per ECMAScript grammar, `async` only forms `async function` / async arrow
    // forms when there is no LineTerminator between `async` and the following token.
    if t0.typ == TT::KeywordAsync
      && t1.typ != TT::EqualsChevronRight
      && !t1.preceded_by_line_terminator
    {
      return Ok(match t1.typ {
        TT::ParenthesisOpen | TT::ChevronLeft => {
          self.arrow_parse_committed = false;
          match self.rewindable::<Node<Expr>, _>(|p| match p.arrow_func_expr(ctx, terminators) {
            Ok(expr) => Ok(Some(expr.into_wrapped())),
            Err(err) if p.arrow_parse_committed => Err(err),
            Err(err)
              if matches!(
                err.typ,
                SyntaxErrorType::LineTerminatorAfterArrowFunctionParameters
                  | SyntaxErrorType::InvalidRestParameter
              ) =>
            {
              Err(err)
            }
            Err(_) => Ok(None),
          })? {
            Some(expr) => expr,
            None => self.id_expr(ctx)?.into_wrapped(),
          }
        }
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
      return Ok(if t1.typ == TT::EqualsChevronRight {
        // Single-unparenthesised-parameter arrow function.
        self.arrow_func_expr(ctx, terminators)?.into_wrapped()
      } else {
        self.id_expr(ctx)?.into_wrapped()
      });
    };

    // Decorated class expression: `@dec class C {}`.
    if self.should_recover() && t0.typ == TT::At {
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
      // Bare PrivateIdentifier is not a PrimaryExpression. Legal `#id in ShiftExpression`
      // is handled in `expr_with_min_prec`; `. #id` / `?. #id` are member operators.
      // TypeScript recovery still materialises an IdExpr so downstream can diagnose.
      TT::PrivateMember => {
        let tok = self.peek();
        self.report_bare_private_hash_if_needed(&tok);
        if self.should_recover() {
          self
            .with_loc(|p| {
              let name = p.consume_as_string();
              Ok(IdExpr { name })
            })?
            .into_wrapped()
        } else {
          return Err(tok.error(SyntaxErrorType::InvalidPrivateIdentifier));
        }
      }
      // TypeScript recovery: allow keywords in expression position as identifier references.
      // This matches pattern recovery and keeps parsing moving for invalid programs like
      // `var x = [await];` in module contexts.
      t if self.should_recover() && KEYWORDS_MAPPING.contains_key(&t) => self
        .with_loc(|p| {
          let name = p.consume_as_string();
          Ok(IdExpr { name })
        })?
        .into_wrapped(),
      TT::Invalid => {
        let raw = self.bytes(t0.loc);
        if raw.starts_with("/*") {
          return Err(t0.error(SyntaxErrorType::UnterminatedMultilineComment));
        }
        if raw == "<!--" || raw == "-->" {
          return Err(t0.error(SyntaxErrorType::HtmlCommentInModule));
        }
        let starts_like_number = raw
          .chars()
          .next()
          .is_some_and(|c| c.is_ascii_digit() || c == '.');
        if starts_like_number {
          // Lexer marks a well-formed NumericLiteral Invalid when IdentifierStart follows
          // immediately (ECMA-262 §12.9.3); distinguish from truly malformed numbers.
          let after = Loc(t0.loc.1, self.source_range().1);
          let followed_by_ident_start = self
            .bytes(after)
            .chars()
            .next()
            .is_some_and(crate::lex::is_identifier_start);
          if followed_by_ident_start {
            return Err(t0.error(SyntaxErrorType::NumericLiteralFollowedByIdentifier));
          }
          if raw.ends_with('n') {
            return Err(t0.error(SyntaxErrorType::MalformedLiteralBigInt));
          }
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
    // ECMA-262 RelationalExpression[+In]: `PrivateIdentifier in ShiftExpression`.
    // Only legal at relational precedence (and below); ShiftExpression / Unary
    // positions must reject bare `#id` and nested `#a in #b in c`.
    let in_prec = OPERATORS[&OperatorName::In].precedence;
    if min_prec <= in_prec
      && self.peek().typ == TT::PrivateMember
      && !terminators.contains(&TT::KeywordIn)
    {
      let checkpoint = self.checkpoint();
      let name_tok = self.consume();
      let name = self.string(name_tok.loc);
      if self.peek().typ == TT::KeywordIn {
        // Only report after committing — this path peeks via consume+restore.
        self.report_bare_private_hash_if_needed(&name_tok);
        self.consume(); // `in`
        let right = self.expr_with_min_prec(ctx, in_prec + 1, terminators, asi)?;
        let left = Node::new(name_tok.loc, IdExpr { name }).into_wrapped();
        let private_in = Node::new(
          left.loc + right.loc,
          BinaryExpr {
            operator: OperatorName::In,
            left,
            right,
          },
        )
        .into_wrapped();
        return self.expr_with_min_prec_after_left(ctx, private_in, min_prec, terminators, asi);
      }
      self.restore_checkpoint(checkpoint);
    }

    let left = self.expr_operand(ctx, terminators, asi)?;
    self.expr_with_min_prec_after_left(ctx, left, min_prec, terminators, asi)
  }

  fn expr_with_min_prec_after_left<const N: usize>(
    &mut self,
    ctx: ParseCtx,
    mut left: Node<Expr>,
    min_prec: u8,
    terminators: [TT; N],
    asi: &mut Asi,
  ) -> SyntaxResult<Node<Expr>> {
    let asi_allowed = asi.can_end_with_asi && ctx.asi.allows_asi();
    let yield_precedence = OPERATORS[&OperatorName::Yield].precedence;

    // In ECMAScript, `yield` expressions are restricted productions: they can
    // only appear in positions that accept an `AssignmentExpression` unless
    // parenthesized. This forbids using bare `yield`/`yield*` as a subexpression
    // of higher-precedence operators (e.g. `1 + yield 2`, `+yield 1`, `2 ** yield`).
    if min_prec > yield_precedence
      && matches!(
        left.stx.as_ref(),
        Expr::Unary(unary)
          if matches!(unary.stx.operator, OperatorName::Yield | OperatorName::YieldDelegated)
      )
      && left.assoc.get::<ParenthesizedExpr>().is_none()
    {
      return Err(left.loc.error(
        SyntaxErrorType::ExpectedSyntax("parenthesized expression"),
        None,
      ));
    }

    // Arrow functions are AssignmentExpressions and therefore must be parenthesized when used as
    // a subexpression of higher-precedence operators (e.g. `1 + (x => x)`, not `1 + x => x`).
    if min_prec > yield_precedence
      && matches!(left.stx.as_ref(), Expr::ArrowFunc(_))
      && left.assoc.get::<ParenthesizedExpr>().is_none()
    {
      return Err(left.loc.error(
        SyntaxErrorType::ExpectedSyntax("parenthesized expression"),
        None,
      ));
    }

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
          self.validate_update_operand(&left)?;
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
        // We need to distinguish between non-null assertion (expr!) and
        // inequality operators (!= and !==).
        TT::Exclamation if self.is_typescript() && !t.preceded_by_line_terminator => {
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
        // Tagged templates allow line terminators between the tag expression and
        // the template literal (`tag\n\`x\``). ASI must not split in that case.
        TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd => {
          // However, `yield` expressions are restricted productions: an unparenthesized
          // `yield`/`yield*` cannot be used as a tag expression. If we encounter a template
          // literal after `yield` across a LineTerminator, treat it as an ASI boundary.
          if matches!(left.stx.as_ref(), Expr::Unary(unary) if matches!(unary.stx.operator, OperatorName::Yield | OperatorName::YieldDelegated))
            && left.assoc.get::<ParenthesizedExpr>().is_none()
          {
            if asi_allowed && t.preceded_by_line_terminator {
              self.restore_checkpoint(cp);
              asi.did_end_with_asi = true;
              break;
            }
            return Err(t.error(SyntaxErrorType::ExpectedSyntax("parenthesized expression")));
          }
          // UpdateExpression is not a MemberExpression, so it cannot be a tag.
          let is_update = match left.stx.as_ref() {
            Expr::UnaryPostfix(_) => true,
            Expr::Unary(u) => matches!(
              u.stx.operator,
              OperatorName::PrefixIncrement | OperatorName::PrefixDecrement
            ),
            _ => false,
          };
          if self.is_strict_ecmascript() && is_update {
            return Err(t.error(SyntaxErrorType::ExpectedSyntax(
              "tagged template after update expression",
            )));
          }
          // ECMA-262 OptionalChain early error: `?.`… TemplateLiteral /
          // OptionalChain TemplateLiteral.
          if is_optional_expression(&left) {
            return Err(t.error(SyntaxErrorType::OptionalChainTaggedTemplate));
          }
          let loc = t.loc;
          self.restore_checkpoint(cp);
          // ES2018: Tagged templates allow invalid escape sequences
          let function = left;
          let (parts, template_parts) = self.lit_template_parts_with_template_data(ctx, true)?;
          let mut node = Node::new(function.loc + loc, TaggedTemplateExpr { function, parts });
          node.assoc.set(template_parts);
          left = node.into_wrapped();
          continue;
        }
        // TypeScript: Type assertion: expr as Type or expr as const.
        // Precedence sits between relational (`in`) and equality (see
        // PRECEDENCE_LEVELS empty slot): `a in b as T` → `(a in b) as T`.
        TT::KeywordAs if self.is_typescript() => {
          let as_prec = OPERATORS[&OperatorName::In].precedence.saturating_sub(1);
          if as_prec < min_prec {
            self.restore_checkpoint(cp);
            break;
          }
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
        // TypeScript: Satisfies expression: expr satisfies Type (same prec as `as`).
        TT::KeywordSatisfies if self.is_typescript() => {
          let as_prec = OPERATORS[&OperatorName::In].precedence.saturating_sub(1);
          if as_prec < min_prec {
            self.restore_checkpoint(cp);
            break;
          }
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
        // TypeScript: Optional call with type arguments: fn?.<T>(x)
        // Type arguments come after `?.` (unlike normal generic calls where they come after the callee).
        TT::QuestionDot if self.is_typescript() => {
          let next = self.peek();
          // Match existing optional chaining call behavior (?.() token) by disallowing newlines here.
          if next.typ == TT::ChevronLeft && !next.preceded_by_line_terminator {
            if is_bare_new_expression(&left) {
              return Err(t.error(SyntaxErrorType::InvalidOptionalChainFromNew));
            }
            if let Some((type_arguments, close_loc, arguments, end_loc)) = self.rewindable(|p| {
              p.require(TT::ChevronLeft)?;
              let (type_arguments, close_loc) = match p.ts_type_arguments_after_chevron_left(ctx) {
                Ok(res) => res,
                Err(_) => return Ok(None),
              };

              if p.peek().typ != TT::ParenthesisOpen {
                return Ok(None);
              }

              p.consume(); // (
              let arguments = p.call_args(ctx)?;
              let end = p.require(TT::ParenthesisClose)?;

              Ok(Some((type_arguments, close_loc, arguments, end.loc)))
            })? {
              let callee = Node::new(
                left.loc + close_loc,
                InstantiationExpr {
                  expression: Box::new(left),
                  type_arguments,
                },
              )
              .into_wrapped();

              left = Node::new(
                callee.loc + end_loc,
                CallExpr {
                  optional_chaining: true,
                  callee,
                  arguments,
                },
              )
              .into_wrapped();
              continue;
            }
          }
        }
        // TypeScript: Instantiation expressions (`expr<T>`) for explicit type arguments in
        // expression position.
        TT::ChevronLeft => {
          if self.is_typescript()
            && matches!(
              *left.stx,
              Expr::Id(_)
                | Expr::Member(_)
                | Expr::ComputedMember(_)
                | Expr::Call(_)
                | Expr::Instantiation(_)
            )
          {
            if let Some((type_arguments, close_loc)) = self.rewindable(|p| {
              let (type_arguments, close_loc) = match p.ts_type_arguments_after_chevron_left(ctx) {
                Ok(res) => res,
                Err(_) => return Ok(None),
              };

              let next = p.peek();
              let tagged_template = !next.preceded_by_line_terminator
                && matches!(
                  next.typ,
                  TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd
                );

              if p.allow_bare_ts_type_args
                || tagged_template
                || Self::can_follow_type_arguments_in_expression(next.typ)
              {
                return Ok(Some((type_arguments, close_loc)));
              }

              Ok(None)
            })? {
              left = Node::new(
                left.loc + close_loc,
                InstantiationExpr {
                  expression: Box::new(left),
                  type_arguments,
                },
              )
              .into_wrapped();
              continue;
            }
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
          if self.should_recover() {
            // TypeScript-style recovery: Allow semicolons to terminate expressions.
            if t.typ == TT::Semicolon {
              self.restore_checkpoint(cp);
              break;
            };
            // TypeScript-style recovery: Trigger ASI when identifier/keyword follows expression.
            // Enables permissive parsing like "yield foo" -> "yield" + "foo" (two statements).
            if asi_allowed && (t.typ == TT::Identifier || KEYWORDS_MAPPING.contains_key(&t.typ)) {
              self.restore_checkpoint(cp);
              asi.did_end_with_asi = true;
              break;
            };
            // TypeScript-style recovery: Trigger ASI when we see tokens that typically start
            // new constructs.
            if asi_allowed
              && matches!(
                t.typ,
                TT::Colon | // Arrow function malformed type annotation: (a):
                TT::BraceOpen | // New object/block after expression
                TT::LiteralNumber | // Number after identifier: `await 1` where await is identifier
                TT::LiteralString | // String after expression
                TT::LiteralTrue | // Boolean after expression
                TT::LiteralFalse | // Boolean after expression
                TT::LiteralNull | // Null after expression
                TT::ChevronLeftSlash // JSX closing tag: </div> after JSX element with text children
              )
            {
              self.restore_checkpoint(cp);
              asi.did_end_with_asi = true;
              break;
            };
          }
          return Err(t.error(SyntaxErrorType::ExpectedSyntax("expression operator")));
        }
        Some(operator) => {
          if operator.precedence < min_prec {
            self.restore_checkpoint(cp);
            break;
          };

          // In ECMAScript, `yield` expressions are "restricted productions":
          // when used without parentheses, they can't be the left operand of
          // higher-precedence operators (e.g. `yield\n+1`, `yield.foo`,
          // `yield\n(1)`, `yield\n[0]`). In those cases we either insert an
          // automatic semicolon at a LineTerminator boundary (if allowed) or
          // report a syntax error requiring parentheses.
          if matches!(left.stx.as_ref(), Expr::Unary(unary) if matches!(unary.stx.operator, OperatorName::Yield | OperatorName::YieldDelegated))
            && left.assoc.get::<ParenthesizedExpr>().is_none()
            && operator.precedence > OPERATORS[&OperatorName::Yield].precedence
          {
            if asi_allowed && t.preceded_by_line_terminator {
              self.restore_checkpoint(cp);
              asi.did_end_with_asi = true;
              break;
            }
            return Err(t.error(SyntaxErrorType::ExpectedSyntax("parenthesized expression")));
          }

          let next_min_prec =
            operator.precedence + (operator.associativity == Associativity::Left) as u8;

          // ECMA-262: OptionalChain may follow MemberExpression / CallExpression, but not a
          // bare NewExpression (`new F` without Arguments). `new F()?.x` is legal (Arguments
          // make it a MemberExpression); `new F?.x` / `(new F)?.x` differ — the latter needs
          // parentheses. Unparenthesized `new` without a Call argument is rejected here.
          let is_optional_chain = matches!(
            operator.name,
            OperatorName::OptionalChainingCall
              | OperatorName::OptionalChainingMemberAccess
              | OperatorName::OptionalChainingComputedMemberAccess
          );
          if is_optional_chain && is_bare_new_expression(&left) {
            return Err(t.error(SyntaxErrorType::InvalidOptionalChainFromNew));
          }

          // ECMA-262 ShortCircuitExpression: CoalesceExpression and LogicalORExpression
          // are alternatives; `??` must not mix with `&&`/`||` without parentheses.
          if operator.name == OperatorName::NullishCoalescing && is_unparen_logical_and_or(&left) {
            return Err(t.error(SyntaxErrorType::MixedNullishLogicalOperators));
          }
          if matches!(
            operator.name,
            OperatorName::LogicalAnd | OperatorName::LogicalOr
          ) && is_unparen_nullish_coalesce(&left)
          {
            return Err(t.error(SyntaxErrorType::MixedNullishLogicalOperators));
          }

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
              // TypeScript-style recovery: Allow empty bracket expressions like `obj[]`.
              let member = if self.should_recover() {
                if self.peek().typ == TT::BracketClose {
                  let loc = self.peek().loc;
                  self.create_synthetic_undefined(loc)
                } else {
                  self.expr(ctx, [TT::BracketClose]).unwrap_or_else(|_| {
                    let loc = self.peek().loc;
                    self.create_synthetic_undefined(loc)
                  })
                }
              } else {
                self.expr(ctx, [TT::BracketClose])?
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
              // `?.` may be whitespace-separated from Arguments / `[` (lexer only fuses
              // `?.(` / `?.[` when adjacent). Spec OptionalChain allows `?. Arguments`.
              if operator.name == OperatorName::OptionalChainingMemberAccess {
                if self.peek().typ == TT::ParenthesisOpen {
                  self.consume(); // `(`
                  let arguments = self.call_args(ctx)?;
                  let end = self.require(TT::ParenthesisClose)?;
                  left = Node::new(
                    left.loc + end.loc,
                    CallExpr {
                      optional_chaining: true,
                      arguments,
                      callee: left,
                    },
                  )
                  .into_wrapped();
                  continue;
                }
                if self.peek().typ == TT::BracketOpen {
                  self.consume(); // `[`
                  let member = self.expr(ctx, [TT::BracketClose])?;
                  let end = self.require(TT::BracketClose)?;
                  left = Node::new(
                    left.loc + end.loc,
                    ComputedMemberExpr {
                      optional_chaining: true,
                      object: left,
                      member,
                    },
                  )
                  .into_wrapped();
                  continue;
                }
              }
              let checkpoint = self.checkpoint();
              let right_tok = self.consume();
              let mut prop = String::new();
              let mut right = right_tok.loc;
              match right_tok.typ {
                TT::Identifier | TT::PrivateMember => {
                  // IdentifierName StringValue: decode `\uXXXX` / `\u{…}` escapes.
                  self.report_bare_private_hash_if_needed(&right_tok);
                  prop = self.identifier_string_value(right);
                }
                t if KEYWORDS_MAPPING.contains_key(&t) => {
                  prop = self.identifier_string_value(right);
                }
                TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd
                  if operator.name == OperatorName::OptionalChainingMemberAccess =>
                {
                  // `a?.\`tpl\`` — OptionalChain: ?. TemplateLiteral.
                  return Err(right_tok.error(SyntaxErrorType::OptionalChainTaggedTemplate));
                }
                _ => {
                  if !self.should_recover() {
                    return Err(right_tok.error(SyntaxErrorType::ExpectedSyntax("property name")));
                  }
                  if matches!(
                    right_tok.typ,
                    TT::BraceClose
                      | TT::ParenthesisClose
                      | TT::BracketClose
                      | TT::Semicolon
                      | TT::EOF
                  ) {
                    // TypeScript-style recovery: if the next token is a likely
                    // terminator for the containing expression/block, don't
                    // consume it; instead, fabricate an empty property name and
                    // let the outer parser handle the terminator.
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
                // tsc `parseAssignmentExpressionOrHigher`: assignment is only
                // formed when the left operand is a LeftHandSideExpression.
                // Relational/`in`/etc. must stop before `=` so the statement
                // parser can report TS1005 ('; expected) and recover.
                if self.should_recover() && !Self::is_left_hand_side_expression(&left) {
                  self.restore_checkpoint(cp);
                  break;
                }
                left = lhs_expr_to_assign_target_with_recover(
                  left,
                  operator.name,
                  self.should_recover(),
                )?;
                self.validate_strict_assignment_target_expr(&left)?;
              };
              let right = self.expr_with_min_prec(ctx, next_min_prec, terminators, asi)?;
              // `??` RHS is BitwiseORExpression; Pratt may still fold a higher-prec
              // `&&` into the right operand — reject that mix without parentheses.
              if operator.name == OperatorName::NullishCoalescing
                && is_unparen_logical_and_or(&right)
              {
                return Err(t.error(SyntaxErrorType::MixedNullishLogicalOperators));
              }
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
      let start = p.require(TT::KeywordSuper)?;
      if p.is_strict_ecmascript() {
        match p.peek().typ {
          TT::Dot | TT::BracketOpen => {
            if p.super_prop_allowed == 0 {
              return Err(start.error(SyntaxErrorType::ExpectedSyntax(
                "super property access not allowed outside methods and class elements",
              )));
            }
          }
          TT::ParenthesisOpen => {
            if p.super_call_allowed == 0 {
              return Err(start.error(SyntaxErrorType::ExpectedSyntax(
                "super call not allowed outside derived constructors",
              )));
            }
          }
          _ => {
            return Err(start.error(SyntaxErrorType::ExpectedSyntax(
              "super property access or call",
            )));
          }
        }
      }
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
      let start = p.require(TT::KeywordNew)?;
      p.require(TT::Dot)?;
      let prop = p.require(TT::Identifier)?;
      if p.str(prop.loc) != "target" {
        return Err(prop.error(SyntaxErrorType::ExpectedSyntax("`target` property")));
      };
      if p.is_strict_ecmascript() && p.new_target_allowed == 0 {
        return Err(start.error(SyntaxErrorType::ExpectedSyntax(
          "new.target expression not allowed outside functions",
        )));
      }
      Ok(NewTarget {}.into())
    })
  }
}
