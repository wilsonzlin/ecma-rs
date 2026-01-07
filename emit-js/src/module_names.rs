use crate::Emitter;
use parse_js::lex::{lex_next, LexMode, Lexer};
use parse_js::parse::expr::pat::{is_valid_pattern_identifier, ParsePatternRules};
use parse_js::token::TT;
use parse_js::Dialect;

/// Returns true when `name` can be emitted as a single `IdentifierName` token.
///
/// This is used for TypeScript/ES2022 "arbitrary module namespace identifiers",
/// where import/export specifiers may use either an `IdentifierName` or a string
/// literal.
///
/// This intentionally uses the parser's lexer rather than a naive ASCII check
/// so that escaped identifiers like `\u0061` are treated as valid.
pub(crate) fn is_identifier_name_token(name: &str) -> bool {
  let mut lexer = Lexer::new(name);
  let token = lex_next(&mut lexer, LexMode::Standard, Dialect::Ts);

  // `lex_next` skips whitespace and comments. Reject anything that isn't
  // exactly one token spanning the entire string.
  if token.loc.0 != 0 || token.loc.1 != name.len() {
    return false;
  }

  matches!(
    token.typ,
    TT::Identifier | TT::LiteralFalse | TT::LiteralTrue | TT::LiteralNull
  ) || token.typ.is_keyword()
}

pub(crate) fn emit_identifier_name_or_string_literal(em: &mut Emitter, name: &str) {
  if is_identifier_name_token(name) {
    em.write_identifier(name);
  } else {
    em.write_string_literal(name);
  }
}

/// Returns true when `name` can be emitted as a single token accepted by
/// `parse-js` as a module import/export alias identifier.
///
/// `parse-js` stores string-literal aliases as `IdPat { name: <string value> }`.
/// Even when the string is lexically a keyword (`while`, `await`, etc.), it may
/// not be valid in this position without quotes; this helper mirrors the
/// parser's `id_pat` validation for module-level patterns.
pub(crate) fn is_module_binding_identifier_token(name: &str) -> bool {
  let mut lexer = Lexer::new(name);
  let token = lex_next(&mut lexer, LexMode::Standard, Dialect::Ts);

  if token.loc.0 != 0 || token.loc.1 != name.len() {
    return false;
  }

  // Import/export declarations are only valid in modules, where `await` is not
  // permitted as an identifier.
  is_valid_pattern_identifier(
    token.typ,
    ParsePatternRules {
      await_allowed: false,
      yield_allowed: false,
      await_expr_allowed: true,
      yield_expr_allowed: false,
    },
  )
}

pub(crate) fn emit_module_binding_identifier_or_string_literal(em: &mut Emitter, name: &str) {
  if is_module_binding_identifier_token(name) {
    em.write_identifier(name);
  } else {
    em.write_string_literal(name);
  }
}
