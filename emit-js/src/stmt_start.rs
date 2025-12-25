use std::fmt;

use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::{Expr, UnaryExpr};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::operator::OperatorName;
use parse_js::token::UNRESERVED_KEYWORD_STRS;

use crate::emitter::EmitResult;
use crate::expr::emit_expr;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Keyword {
  Async,
  Await,
  Class,
  Declare,
  Enum,
  Function,
  Import,
  Interface,
  Let,
  Module,
  Namespace,
  Type,
  Using,
  Abstract,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TokenKind {
  At,
  BraceOpen,
  BracketOpen,
  ParenthesisOpen,
  TemplateStart,
  StringLiteral,
  Keyword(Keyword),
  Identifier(String),
  Other,
}

#[derive(Clone, Debug)]
struct TokenPrefix {
  first: TokenKind,
  second: Option<TokenKind>,
}

pub(crate) fn expr_leading_token(expr: &Node<Expr>) -> TokenKind {
  expr_tokens(expr).first
}

pub(crate) fn expr_second_token_hint(expr: &Node<Expr>) -> Option<TokenKind> {
  expr_tokens(expr).second
}

pub fn expr_stmt_needs_parens(expr: &Node<Expr>) -> bool {
  let first = expr_leading_token(expr);
  let second = expr_second_token_hint(expr);

  match first {
    TokenKind::At => true,
    TokenKind::BraceOpen => true,
    TokenKind::Keyword(Keyword::Function | Keyword::Class) => true,
    TokenKind::Keyword(Keyword::Async) => {
      matches!(second, Some(TokenKind::Keyword(Keyword::Function)))
    }
    TokenKind::Keyword(Keyword::Abstract) => {
      matches!(second, Some(TokenKind::Keyword(Keyword::Class)))
    }
    TokenKind::Keyword(Keyword::Let | Keyword::Using) => match second {
      Some(TokenKind::BraceOpen | TokenKind::BracketOpen) => true,
      Some(TokenKind::Identifier(name)) if is_pattern_identifier_start(&name) => true,
      _ => false,
    },
    TokenKind::Keyword(Keyword::Await) => {
      matches!(second, Some(TokenKind::Keyword(Keyword::Using)))
    }
    TokenKind::Keyword(Keyword::Import) => !matches!(second, Some(TokenKind::ParenthesisOpen)),
    TokenKind::Keyword(Keyword::Interface | Keyword::Type | Keyword::Enum) => true,
    TokenKind::Keyword(Keyword::Namespace | Keyword::Module) => matches!(
      second,
      Some(TokenKind::Identifier(_) | TokenKind::StringLiteral)
    ),
    TokenKind::Keyword(Keyword::Declare) => !matches!(second, Some(TokenKind::TemplateStart)),
    _ => false,
  }
}

pub fn emit_expr_stmt_with<W: fmt::Write>(
  out: &mut W,
  expr: &Node<Expr>,
  mut emit_expr_fn: impl FnMut(&mut W, &Node<Expr>) -> EmitResult,
) -> EmitResult {
  let needs_parens = expr_stmt_needs_parens(expr);
  if needs_parens {
    write!(out, "(")?;
  }
  emit_expr_fn(out, expr)?;
  if needs_parens {
    write!(out, ")")?;
  }
  Ok(())
}

pub fn emit_expr_stmt<W, F>(out: &mut W, expr: &Node<Expr>, emit_type: F) -> EmitResult
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  let mut emit_type = emit_type;
  emit_expr_stmt_with(out, expr, |out, expr| emit_expr(out, expr, &mut emit_type))
}

fn expr_tokens(expr: &Node<Expr>) -> TokenPrefix {
  match expr.stx.as_ref() {
    Expr::Id(id) => prefix(token_from_identifier(&id.stx.name), None),
    Expr::LitStr(_) => prefix(TokenKind::StringLiteral, None),
    Expr::LitObj(_) | Expr::ObjPat(_) => prefix(TokenKind::BraceOpen, None),
    Expr::LitArr(_) | Expr::ArrPat(_) => prefix(TokenKind::BracketOpen, None),
    Expr::Func(func) => {
      if func.stx.func.stx.async_ {
        prefix(
          TokenKind::Keyword(Keyword::Async),
          Some(TokenKind::Keyword(Keyword::Function)),
        )
      } else {
        prefix(TokenKind::Keyword(Keyword::Function), None)
      }
    }
    Expr::Class(class) => {
      if class.stx.decorators.is_empty() {
        prefix(TokenKind::Keyword(Keyword::Class), None)
      } else {
        prefix(TokenKind::At, Some(TokenKind::Keyword(Keyword::Class)))
      }
    }
    Expr::ImportMeta(_) => prefix(TokenKind::Keyword(Keyword::Import), Some(TokenKind::Other)),
    Expr::Import(_) => prefix(
      TokenKind::Keyword(Keyword::Import),
      Some(TokenKind::ParenthesisOpen),
    ),
    Expr::Member(member) => prefix_with_fallback(&member.stx.left, TokenKind::Other),
    Expr::ComputedMember(member) => prefix_with_fallback(
      &member.stx.object,
      if member.stx.optional_chaining {
        TokenKind::Other
      } else {
        TokenKind::BracketOpen
      },
    ),
    Expr::Call(call) => prefix_with_fallback(
      &call.stx.callee,
      if call.stx.optional_chaining {
        TokenKind::Other
      } else {
        TokenKind::ParenthesisOpen
      },
    ),
    Expr::Binary(binary) => prefix_with_fallback(&binary.stx.left, TokenKind::Other),
    Expr::Cond(cond) => prefix_with_fallback(&cond.stx.test, TokenKind::Other),
    Expr::TaggedTemplate(tagged) => {
      prefix_with_fallback(&tagged.stx.function, TokenKind::TemplateStart)
    }
    Expr::TypeAssertion(assertion) => expr_tokens(&assertion.stx.expression),
    Expr::NonNullAssertion(non_null) => expr_tokens(&non_null.stx.expression),
    Expr::SatisfiesExpr(satisfies) => expr_tokens(&satisfies.stx.expression),
    Expr::Unary(unary) => unary_tokens(unary),
    Expr::UnaryPostfix(postfix) => prefix_with_fallback(&postfix.stx.argument, TokenKind::Other),
    Expr::ArrowFunc(_) => prefix(TokenKind::ParenthesisOpen, None),
    Expr::LitTemplate(_) => prefix(TokenKind::TemplateStart, None),
    _ => prefix(TokenKind::Other, None),
  }
}

fn unary_tokens(unary: &Node<UnaryExpr>) -> TokenPrefix {
  match unary.stx.operator {
    OperatorName::Await => {
      let arg_prefix = expr_tokens(&unary.stx.argument);
      prefix(TokenKind::Keyword(Keyword::Await), Some(arg_prefix.first))
    }
    _ => prefix(
      TokenKind::Other,
      Some(expr_tokens(&unary.stx.argument).first),
    ),
  }
}

fn prefix(first: TokenKind, second: Option<TokenKind>) -> TokenPrefix {
  TokenPrefix { first, second }
}

fn prefix_with_fallback(expr: &Node<Expr>, fallback: TokenKind) -> TokenPrefix {
  let prefix = expr_tokens(expr);
  if prefix.second.is_some() {
    prefix
  } else {
    TokenPrefix {
      first: prefix.first,
      second: Some(fallback),
    }
  }
}

fn token_from_identifier(name: &str) -> TokenKind {
  match name {
    "let" => TokenKind::Keyword(Keyword::Let),
    "using" => TokenKind::Keyword(Keyword::Using),
    "await" => TokenKind::Keyword(Keyword::Await),
    "abstract" => TokenKind::Keyword(Keyword::Abstract),
    "import" => TokenKind::Keyword(Keyword::Import),
    "interface" => TokenKind::Keyword(Keyword::Interface),
    "type" => TokenKind::Keyword(Keyword::Type),
    "enum" => TokenKind::Keyword(Keyword::Enum),
    "namespace" => TokenKind::Keyword(Keyword::Namespace),
    "module" => TokenKind::Keyword(Keyword::Module),
    "declare" => TokenKind::Keyword(Keyword::Declare),
    "class" => TokenKind::Keyword(Keyword::Class),
    "function" => TokenKind::Keyword(Keyword::Function),
    _ => TokenKind::Identifier(name.to_string()),
  }
}

fn is_pattern_identifier_start(name: &str) -> bool {
  if name.is_empty() {
    return false;
  }
  if name == "await" || name == "yield" {
    return true;
  }
  UNRESERVED_KEYWORD_STRS.contains(name) || is_valid_identifier_like(name)
}

fn is_valid_identifier_like(_name: &str) -> bool {
  // The parser has already validated identifier tokens; accept the remaining
  // strings as valid identifier-like values for pattern lookahead.
  true
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ContextualKeyword {
  Let,
  Using,
  AwaitUsing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
enum NextTokenAfterKeyword {
  None,
  Brace,
  Bracket,
  IdentLike,
  In,
  Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ContextualKeywordStart {
  kind: ContextualKeyword,
  next: NextTokenAfterKeyword,
}

fn contextual_keyword_from_name(name: &str) -> Option<ContextualKeyword> {
  match name {
    "let" => Some(ContextualKeyword::Let),
    "using" => Some(ContextualKeyword::Using),
    _ => None,
  }
}

fn contextual_keyword_start_from_expr(expr: &Expr) -> Option<ContextualKeywordStart> {
  match expr {
    Expr::Id(id) => contextual_keyword_from_name(&id.stx.name).map(|kind| ContextualKeywordStart {
      kind,
      next: NextTokenAfterKeyword::None,
    }),
    Expr::IdPat(id) => {
      contextual_keyword_from_name(&id.stx.name).map(|kind| ContextualKeywordStart {
        kind,
        next: NextTokenAfterKeyword::None,
      })
    }
    Expr::Unary(unary) if unary.stx.operator == OperatorName::Await => {
      let child = unary.stx.argument.stx.as_ref();
      if let Some(child_start) = contextual_keyword_start_from_expr(child) {
        if child_start.kind == ContextualKeyword::Using {
          Some(ContextualKeywordStart {
            kind: ContextualKeyword::AwaitUsing,
            next: child_start.next,
          })
        } else {
          None
        }
      } else {
        None
      }
    }
    Expr::Member(member) => {
      propagate_keyword_start(member.stx.left.stx.as_ref(), NextTokenAfterKeyword::Other)
    }
    Expr::ComputedMember(member) => propagate_keyword_start(
      member.stx.object.stx.as_ref(),
      if member.stx.optional_chaining {
        NextTokenAfterKeyword::Other
      } else {
        NextTokenAfterKeyword::Bracket
      },
    ),
    Expr::Call(call) => {
      propagate_keyword_start(call.stx.callee.stx.as_ref(), NextTokenAfterKeyword::Other)
    }
    Expr::Binary(binary) => propagate_keyword_start(
      binary.stx.left.stx.as_ref(),
      if binary.stx.operator == OperatorName::In {
        NextTokenAfterKeyword::In
      } else {
        NextTokenAfterKeyword::Other
      },
    ),
    Expr::Cond(cond) => {
      propagate_keyword_start(cond.stx.test.stx.as_ref(), NextTokenAfterKeyword::Other)
    }
    Expr::NonNullAssertion(non_null) => propagate_keyword_start(
      non_null.stx.expression.stx.as_ref(),
      NextTokenAfterKeyword::Other,
    ),
    Expr::TypeAssertion(assertion) => propagate_keyword_start(
      assertion.stx.expression.stx.as_ref(),
      NextTokenAfterKeyword::Other,
    ),
    Expr::SatisfiesExpr(satisfies) => propagate_keyword_start(
      satisfies.stx.expression.stx.as_ref(),
      NextTokenAfterKeyword::Other,
    ),
    _ => None,
  }
}

fn propagate_keyword_start(
  expr: &Expr,
  fallback_next: NextTokenAfterKeyword,
) -> Option<ContextualKeywordStart> {
  contextual_keyword_start_from_expr(expr).map(|mut start| {
    if start.next == NextTokenAfterKeyword::None {
      start.next = fallback_next;
    }
    start
  })
}

fn contextual_keyword_start_from_pat(pat: &Pat) -> Option<ContextualKeywordStart> {
  match pat {
    Pat::Id(id) => contextual_keyword_from_name(&id.stx.name).map(|kind| ContextualKeywordStart {
      kind,
      next: NextTokenAfterKeyword::None,
    }),
    Pat::AssignTarget(expr) => contextual_keyword_start_from_expr(expr.stx.as_ref()),
    Pat::Arr(_) | Pat::Obj(_) => None,
  }
}

pub(crate) fn for_init_expr_needs_parens(expr: &Node<Expr>) -> bool {
  contextual_keyword_start_from_expr(expr.stx.as_ref()).map_or(false, |start| match start.kind {
    ContextualKeyword::AwaitUsing => true,
    ContextualKeyword::Let | ContextualKeyword::Using => matches!(
      start.next,
      NextTokenAfterKeyword::Brace
        | NextTokenAfterKeyword::Bracket
        | NextTokenAfterKeyword::IdentLike
    ),
  })
}

pub(crate) fn for_inof_assign_needs_parens(pat: &Node<Pat>) -> bool {
  contextual_keyword_start_from_pat(pat.stx.as_ref()).map_or(false, |start| match start.kind {
    ContextualKeyword::AwaitUsing => true,
    ContextualKeyword::Let | ContextualKeyword::Using => matches!(
      start.next,
      NextTokenAfterKeyword::Brace
        | NextTokenAfterKeyword::Bracket
        | NextTokenAfterKeyword::IdentLike
        | NextTokenAfterKeyword::In
        | NextTokenAfterKeyword::None
    ),
  })
}
