use super::ParseCtx;
use super::Parser;
use crate::ast::class_or_object::ClassOrObjKey;
use crate::ast::expr::pat::ArrPat;
use crate::ast::expr::pat::ArrPatElem;
use crate::ast::expr::pat::ClassOrFuncName;
use crate::ast::expr::pat::IdPat;
use crate::ast::expr::pat::ObjPat;
use crate::ast::expr::pat::ObjPatProp;
use crate::ast::expr::pat::Pat;
use crate::ast::node::Node;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::KEYWORDS_MAPPING;
use crate::token::TT;
use crate::token::UNRESERVED_KEYWORDS;

#[derive(Clone, Copy)]
pub struct ParsePatternRules {
  // `await` is not allowed as an arrow function parameter or a parameter/variable inside an async function.
  pub await_allowed: bool,
  // `yield` is not allowed as a parameter/variable inside a generator function.
  pub yield_allowed: bool,
  // Whether `await` can start an `AwaitExpression` in the current context.
  pub await_expr_allowed: bool,
  // Whether `yield` can start a `YieldExpression` in the current context.
  pub yield_expr_allowed: bool,
}

impl ParsePatternRules {
  pub fn with_await_allowed(&self, await_allowed: bool) -> ParsePatternRules {
    Self {
      await_allowed,
      ..*self
    }
  }

  pub fn with_yield_allowed(&self, yield_allowed: bool) -> ParsePatternRules {
    Self {
      yield_allowed,
      ..*self
    }
  }
}

pub fn is_valid_pattern_identifier(typ: TT, _rules: ParsePatternRules) -> bool {
  match typ {
    TT::Identifier => true,
    TT::KeywordAwait => _rules.await_allowed,
    TT::KeywordYield => _rules.yield_allowed,
    t => UNRESERVED_KEYWORDS.contains(&t),
  }
}

/// Check if a token can be used as a class or function name
/// TypeScript allows type keywords as class/function names in error cases
pub fn is_valid_class_or_func_name(typ: TT, rules: ParsePatternRules) -> bool {
  if is_valid_pattern_identifier(typ, rules) {
    return true;
  }
  // Additionally allow TypeScript type keywords
  matches!(
    typ,
    TT::KeywordAny
      | TT::KeywordBooleanType
      | TT::KeywordNumberType
      | TT::KeywordStringType
      | TT::KeywordSymbolType
      | TT::KeywordVoid
      | TT::KeywordNever
      | TT::KeywordUndefinedType
      | TT::KeywordUnknown
      | TT::KeywordObjectType
      | TT::KeywordBigIntType
  )
}

impl<'a> Parser<'a> {
  pub fn maybe_class_or_func_name(&mut self, ctx: ParseCtx) -> Option<Node<ClassOrFuncName>> {
    self
      .consume_if_pred(|t| is_valid_class_or_func_name(t.typ, ctx.rules))
      .map(|t| {
        Node::new(
          t.loc,
          ClassOrFuncName {
            name: self.string(t.loc),
          },
        )
      })
  }

  /// Parses an identifier pattern.
  pub fn id_pat(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<IdPat>> {
    self.with_loc(|p| {
      let t = p.consume();
      if !is_valid_pattern_identifier(t.typ, ctx.rules) {
        return Err(t.error(SyntaxErrorType::ExpectedSyntax("identifier")));
      }
      Ok(IdPat {
        name: p.string(t.loc),
      })
    })
  }

  /// Parses an object pattern like `{ x, y: z, [computed]: value, ...rest }`.
  /// An object pattern may only contain one rest element, which must not have a trailing comma.
  pub fn obj_pat(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ObjPat>> {
    self.with_loc(|p| {
      p.require(TT::BraceOpen)?;
      let mut properties = Vec::new();
      let mut rest = None;
      while p.peek().typ != TT::BraceClose {
        // Check inside loop to ensure that it must come first or after a comma.
        // NOTE: No trailing comma allowed.
        if p.consume_if(TT::DotDotDot).is_match() {
          // TypeScript: For error recovery, allow binding patterns in rest properties
          // e.g., ({...{}} = {}), ({...[]} = {})
          // The type checker will validate these semantically
          rest = Some(p.pat(ctx)?);
          // TypeScript: For error recovery, allow trailing comma after rest element
          // even though it's semantically invalid (e.g., {...x,})
          // The type checker will catch this error
          if p.should_recover() {
            let _ = p.consume_if(TT::Comma);
          }
          break;
        };

        let prop = p.with_loc(|p| {
          let key = p.class_or_obj_key(ctx)?;
          let (shorthand, target) = if p.consume_if(TT::Colon).is_match() {
            // There's a colon, so there's a subpattern and it's not a shorthand.
            (false, p.pat(ctx)?)
          } else {
            // There's no colon, so it's a shorthand. The key must not be computed, and be a valid identifier name. (It could be a number, reserved keyword, etc., all of which are not allowed.)
            match &key {
              ClassOrObjKey::Computed(name) => {
                return Err(name.error(SyntaxErrorType::ExpectedSyntax(
                  "object pattern property subpattern",
                )));
              }
              ClassOrObjKey::Direct(n) => {
                if p.should_recover() {
                  // TypeScript-style recovery: Accept any keyword in shorthand
                  // properties (e.g., `{ while }`) and string literals that
                  // normalize to identifiers (e.g., `{ "while" }`).
                  if n.stx.tt != TT::Identifier
                    && n.stx.tt != TT::LiteralString
                    && !KEYWORDS_MAPPING.contains_key(&n.stx.tt)
                  {
                    return Err(n.error(SyntaxErrorType::ExpectedNotFound));
                  }
                } else if !is_valid_pattern_identifier(n.stx.tt, ctx.rules) {
                  return Err(n.error(SyntaxErrorType::ExpectedSyntax("identifier")));
                }
                // We've already ensured that this is a valid identifier, keyword, or string literal.
                let id_pat = n
                  .derive_stx(|n| IdPat {
                    name: n.key.clone(),
                  })
                  .into_wrapped();
                (true, id_pat)
              }
            }
          };
          // TypeScript-style recovery: skip optional marker (`?`) in destructuring
          // patterns (invalid syntax; helps with recovery).
          if p.should_recover() {
            let _ = p.consume_if(TT::Question);
          }

          let default_value = p
            .consume_if(TT::Equals)
            .and_then(|| p.expr(ctx, [TT::Comma, TT::BraceClose]))?;
          Ok(ObjPatProp {
            key,
            target,
            default_value,
            shorthand,
          })
        })?;
        properties.push(prop);
        // This will break if `}`.
        if !p.consume_if(TT::Comma).is_match() {
          break;
        };
      }
      p.require(TT::BraceClose)?;
      Ok(ObjPat { properties, rest })
    })
  }

  /// Parses an array pattern like `[a, b = c, ...rest]`.
  pub fn arr_pat(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ArrPat>> {
    self.with_loc(|p| {
      p.require(TT::BracketOpen)?;
      let mut elements = Vec::<Option<ArrPatElem>>::new();
      let mut rest = None;
      while p.peek().typ != TT::BracketClose {
        // Check inside loop to ensure that it must come first or after a comma.
        // NOTE: No trailing comma allowed.
        if p.consume_if(TT::DotDotDot).is_match() {
          rest = Some(p.pat(ctx)?);
          // TypeScript: For error recovery, allow initializer on rest element
          // even though it's semantically invalid (e.g., [...x = a])
          // The type checker will catch this error
          if p.should_recover() && p.consume_if(TT::Equals).is_match() {
            // Parse and discard the initializer
            p.expr(ctx, [TT::BracketClose])?;
          }
          // TypeScript: For error recovery, allow trailing comma after rest element
          // even though it's semantically invalid (e.g., [...x,])
          // The type checker will catch this error
          if p.should_recover() {
            let _ = p.consume_if(TT::Comma);
          }
          break;
        };

        // An unnamed element is allowed to ignore that element.
        if p.consume_if(TT::Comma).is_match() {
          elements.push(None);
        } else {
          let target = p.pat(ctx)?;
          let default_value = if p.consume_if(TT::Equals).is_match() {
            Some(p.expr(ctx, [TT::Comma, TT::BracketClose])?)
          } else {
            None
          };
          elements.push(Some(ArrPatElem {
            target,
            default_value,
          }));
          // This will break if `]`.
          if !p.consume_if(TT::Comma).is_match() {
            break;
          };
        };
      }
      p.require(TT::BracketClose)?;
      Ok(ArrPat { elements, rest })
    })
  }

  /// Parses any valid pattern.
  /// This function serves as the main entry point for parsing all types of patterns, including:
  /// * Identifier patterns (e.g., `x`)
  /// * Object patterns (e.g., `{ x, y }`)
  /// * Array patterns (e.g., `[a, b, ...rest]`)
  pub fn pat(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Pat>> {
    use crate::lex::KEYWORDS_MAPPING;
    let t = self.peek();
    let pat: Node<Pat> = match t.typ {
      t if is_valid_pattern_identifier(t, ctx.rules) => self.id_pat(ctx)?.into_wrapped(),
      TT::BraceOpen => self.obj_pat(ctx)?.into_wrapped(),
      TT::BracketOpen => self.arr_pat(ctx)?.into_wrapped(),
      // TypeScript: For error recovery, create synthetic identifier when pattern is missing
      // Handles cases like `var;`, `let;`, `const;`, `export var;`
      TT::Semicolon | TT::Comma | TT::EOF if self.should_recover() => Node::new(
        t.loc,
        IdPat {
          name: String::from(""),
        },
      )
      .into_wrapped(),
      // TypeScript: Allow any keyword as pattern identifier for error recovery
      // Examples: `var { while: while } = x` or `let [if] = arr`
      // The type checker will validate these semantically
      t if self.should_recover() && KEYWORDS_MAPPING.contains_key(&t) => self
        .with_loc(|p| {
          let name = p.consume_as_string();
          Ok(IdPat { name })
        })?
        .into_wrapped(),
      // TypeScript: Error recovery - private names in patterns/parameters
      // Examples: `const #foo = 3;` or `function f(#x: string) {}`
      // The type checker will catch these as semantic errors
      TT::PrivateMember if self.should_recover() => self
        .with_loc(|p| {
          let name = p.consume_as_string();
          Ok(IdPat { name })
        })?
        .into_wrapped(),
      // TypeScript: Error recovery - template literals as patterns
      // Example: `function f(`hello`) {}` - template literal used as parameter name
      // The type checker will catch this as a semantic error
      TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd if self.should_recover() => {
        self
          .with_loc(|p| {
            let name = p.consume_as_string();
            Ok(IdPat { name })
          })?
          .into_wrapped()
      }
      _ => return Err(t.error(SyntaxErrorType::ExpectedSyntax("pattern"))),
    };
    Ok(pat)
  }
}
