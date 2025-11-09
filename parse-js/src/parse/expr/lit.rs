use super::pat::is_valid_pattern_identifier;
use super::Asi;
use super::ParseCtx;
use super::Parser;
use crate::ast::class_or_object::ClassOrObjKey;
use crate::ast::class_or_object::ClassOrObjVal;
use crate::ast::class_or_object::ObjMember;
use crate::ast::class_or_object::ObjMemberType;
use crate::ast::expr::IdExpr;
use crate::ast::expr::lit::LitArrElem;
use crate::ast::expr::lit::LitArrExpr;
use crate::ast::expr::lit::LitBigIntExpr;
use crate::ast::expr::lit::LitBoolExpr;
use crate::ast::expr::lit::LitNullExpr;
use crate::ast::expr::lit::LitNumExpr;
use crate::ast::expr::lit::LitObjExpr;
use crate::ast::expr::lit::LitRegexExpr;
use crate::ast::expr::lit::LitStrExpr;
use crate::ast::expr::lit::LitTemplateExpr;
use crate::ast::expr::lit::LitTemplatePart;
use crate::ast::node::Node;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::LexMode;
use crate::num::JsNumber;
use crate::token::TT;
use core::str::FromStr;

fn parse_radix(raw: &str, radix: u32) -> Result<f64, ()> {
  u64::from_str_radix(raw, radix)
    .map_err(|_| ())
    // TODO This is lossy, but there is no TryFrom for converting from u64 to f64, and u32 cannot represent all possible JS values.
    .map(|v| v as f64)
}

pub fn normalise_literal_number(raw: &str) -> Option<JsNumber> {
  // TODO We assume that the Rust parser follows ECMAScript spec and that different representations
  // of the same value get parsed into the same f64 value/bit pattern (e.g. `5.1e10` and `0.51e11`).
  match raw {
    s if s.starts_with("0b") || s.starts_with("0B") => parse_radix(&s[2..], 2),
    s if s.starts_with("0o") || s.starts_with("0O") => parse_radix(&s[2..], 8),
    s if s.starts_with("0x") || s.starts_with("0X") => parse_radix(&s[2..], 16),
    s => f64::from_str(s).map_err(|_| ()),
  }
  .map(JsNumber)
  .ok()
}

pub fn normalise_literal_bigint(raw: &str) -> Option<String> {
  // TODO Use custom type like JsNumber.
  // TODO
  Some(raw.to_string())
}

pub fn normalise_literal_string_or_template_inner(mut raw: &str) -> Option<String> {
  let mut norm = String::new();
  while !raw.is_empty() {
    let Some(escape_pos) = raw.find('\\') else {
      norm.push_str(raw);
      break;
    };
    norm.push_str(&raw[..escape_pos]);
    raw = &raw[escape_pos + 1..];
    // https://mathiasbynens.be/notes/javascript-escapes
    // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String#escape_sequences
    // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Template_literals#tagged_templates_and_escape_sequences
    let first_char = raw.chars().next()?;
    let (skip, add): (usize, &str) = match first_char {
      '\n' => (1, ""),
      'b' => (1, "\x08"),
      'f' => (1, "\x0c"),
      'n' => (1, "\n"),
      'r' => (1, "\r"),
      't' => (1, "\t"),
      'v' => (1, "\x0b"),
      '0'..='7' => {
        // Octal escape.
        let mut len = 1;
        if raw
          .chars()
          .nth(len)
          .filter(|&c| ('0'..='7').contains(&c))
          .is_some()
        {
          len += 1;
          if raw
            .chars()
            .nth(len)
            .filter(|&c| ('0'..='7').contains(&c))
            .is_some()
          {
            len += 1;
          };
        };
        let octal_str = raw.chars().take(len).collect::<String>();
        let cp = u32::from_str_radix(&octal_str, 8).unwrap();
        let c = char::from_u32(cp).unwrap();
        let char_str = c.to_string();
        norm.push_str(&char_str);
        raw = &raw[octal_str.len()..];
        continue;
      }
      'x' => {
        // Hexadecimal escape.
        if raw.chars().count() < 3 {
          return None;
        };
        let hex_chars: String = raw.chars().skip(1).take(2).collect();
        if !hex_chars.chars().all(|c| c.is_ascii_hexdigit()) {
          return None;
        };
        let cp = u32::from_str_radix(&hex_chars, 16).unwrap();
        let c = char::from_u32(cp).unwrap();
        norm.push(c);
        raw = &raw[3..];
        continue;
      }
      'u' => {
        let second_char = raw.chars().nth(1);
        match second_char {
          Some('{') => {
            // Unicode code point escape.
            let Some(end_pos) = raw.find('}') else {
              return None;
            };
            if !(3..=8).contains(&end_pos) {
              return None;
            };
            let hex_chars = &raw[2..end_pos];
            let cp = u32::from_str_radix(hex_chars, 16).ok()?;
            let c = char::from_u32(cp)?;
            norm.push(c);
            raw = &raw[end_pos + 1..];
            continue;
          }
          Some(_) => {
            // Unicode escape.
            if raw.chars().count() < 5 {
              return None;
            };
            let hex_chars: String = raw.chars().skip(1).take(4).collect();
            let cp = u32::from_str_radix(&hex_chars, 16).ok()?;
            let c = char::from_u32(cp)?;
            norm.push(c);
            raw = &raw[5..];
            continue;
          }
          None => {
            return None;
          }
        }
      }
      c => {
        norm.push(c);
        raw = &raw[c.len_utf8()..];
        continue;
      }
    };
    norm.push_str(add);
    raw = &raw[skip..];
  }
  Some(norm)
}

pub fn normalise_literal_string(raw: &str) -> Option<String> {
  normalise_literal_string_or_template_inner(&raw[1..raw.len() - 1])
}

impl<'a> Parser<'a> {
  pub fn lit_arr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LitArrExpr>> {
    self.with_loc(|p| {
      p.require(TT::BracketOpen)?;
      let mut elements = Vec::<LitArrElem>::new();
      loop {
        if p.consume_if(TT::Comma).is_match() {
          elements.push(LitArrElem::Empty);
          continue;
        };
        if p.peek().typ == TT::BracketClose {
          break;
        };
        let rest = p.consume_if(TT::DotDotDot).is_match();
        let value = p.expr(ctx, [TT::Comma, TT::BracketClose])?;
        elements.push(if rest {
          LitArrElem::Rest(value)
        } else {
          LitArrElem::Single(value)
        });
        if p.peek().typ == TT::BracketClose {
          break;
        };
        p.require(TT::Comma)?;
      }
      p.require(TT::BracketClose)?;
      Ok(LitArrExpr {
        elements,
      })
    })
  }

  pub fn lit_bigint(&mut self) -> SyntaxResult<Node<LitBigIntExpr>> {
    self.with_loc(|p| {
      let value = p.lit_bigint_val()?;
      Ok(LitBigIntExpr { value })
    })
  }

  pub fn lit_bigint_val(&mut self) -> SyntaxResult<String> {
    let t = self.require(TT::LiteralBigInt)?;
    normalise_literal_bigint(self.str(t.loc))
      .ok_or_else(|| t.loc.error(SyntaxErrorType::MalformedLiteralBigInt, None))
  }

  pub fn lit_bool(&mut self) -> SyntaxResult<Node<LitBoolExpr>> {
    self.with_loc(|p| {
      if p.consume_if(TT::LiteralTrue).is_match() {
        Ok(LitBoolExpr { value: true })
      } else {
        p.require(TT::LiteralFalse)?;
        Ok(LitBoolExpr { value: false })
      }
    })
  }

  pub fn lit_null(&mut self) -> SyntaxResult<Node<LitNullExpr>> {
    self.with_loc(|p| {
      p.require(TT::LiteralNull)?;
      Ok(LitNullExpr {  })
    })
  }

  pub fn lit_num(&mut self) -> SyntaxResult<Node<LitNumExpr>> {
    self.with_loc(|p| {
      let value = p.lit_num_val()?;
      Ok(LitNumExpr { value })
    })
  }

  pub fn lit_num_val(&mut self) -> SyntaxResult<JsNumber> {
    let t = self.require(TT::LiteralNumber)?;
    normalise_literal_number(self.str(t.loc))
      .ok_or_else(|| t.loc.error(SyntaxErrorType::MalformedLiteralNumber, None))
  }

  pub fn lit_obj(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LitObjExpr>> {
    self.with_loc(|p| {
      p.require(TT::BraceOpen)?.loc;
      let members = p.list_with_loc(
        TT::Comma,
        TT::BraceClose,
        |p| {
          let rest = p.consume_if(TT::DotDotDot).is_match();
          if rest {
            let value = p.expr(ctx, [TT::Comma, TT::BraceClose])?;
            Ok(ObjMember {
              typ: ObjMemberType::Rest { val: value },
            })
          } else {
            let (key, value) = p.class_or_obj_member(
              ctx,
              TT::Colon,
              TT::Comma,
              &mut Asi::no(),
            )?;
            let typ = match value {
              ClassOrObjVal::Prop(None) => {
                // This property had no value, so it's a shorthand property. Therefore, check that it's a valid identifier name.
                let ClassOrObjKey::Direct(key) = key else {
                  unreachable!();
                };
                if !is_valid_pattern_identifier(key.stx.tt, ctx.rules) {
                  return Err(key.error(SyntaxErrorType::ExpectedNotFound));
                };
                ObjMemberType::Shorthand {
                  id: key.map_stx(|n| IdExpr { name: n.key }),
                }
              }
              _ => ObjMemberType::Valued { key, val: value },
            };
            Ok(ObjMember { typ })
          }
        }
      )?;
      Ok(LitObjExpr { members })
    })
  }

  pub fn lit_regex(&mut self) -> SyntaxResult<Node<LitRegexExpr>> {
    self.with_loc(|p| {
      let t = p.require_with_mode(TT::LiteralRegex, LexMode::SlashIsRegex)?;
      // TODO Parse, validate, flags.
      let value = p.string(t.loc);
      Ok(LitRegexExpr { value })
    })
  }

  pub fn lit_str(&mut self) -> SyntaxResult<Node<LitStrExpr>> {
    self.with_loc(|p| {
      let value = p.lit_str_val()?;
      Ok(LitStrExpr { value })
    })
  }

  /// Parses a literal string and returns the raw string value normalized (e.g. escapes decoded).
  /// Does *not* return a node; use `lit_str` for that.
  pub fn lit_str_val(&mut self) -> SyntaxResult<String> {
    let t = self.require(TT::LiteralString)?;
    normalise_literal_string(self.str(t.loc))
      .ok_or_else(|| t.loc.error(SyntaxErrorType::InvalidCharacterEscape, None))
  }

  pub fn lit_template(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LitTemplateExpr>> {
    self.with_loc(|p| {
      let parts = p.lit_template_parts(ctx)?;
      Ok(LitTemplateExpr { parts })
    })
  }

  // NOTE: The next token must definitely be LiteralTemplatePartString{,End}.
  pub fn lit_template_parts(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<LitTemplatePart>> {
    let t = self.consume();
    let is_end = match t.typ {
      TT::LiteralTemplatePartString => false,
      TT::LiteralTemplatePartStringEnd => true,
      _ => unreachable!(),
    };

    let mut parts = Vec::new();
    parts.push(LitTemplatePart::String(
      normalise_literal_string_or_template_inner(self.bytes(t.loc))
        .ok_or_else(|| t.loc.error(SyntaxErrorType::InvalidCharacterEscape, None))?,
    ));
    if !is_end {
      loop {
        let substitution = self.expr(ctx, [TT::BraceClose])?;
        self.require(TT::BraceClose)?;
        parts.push(LitTemplatePart::Substitution(substitution));
        let string = self.consume_with_mode(LexMode::TemplateStrContinue);
        if !matches!(string.typ, TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd) {
          return Err(string.error(SyntaxErrorType::ExpectedSyntax("template string part")));
        };
        parts.push(LitTemplatePart::String(
          normalise_literal_string_or_template_inner(self.bytes(string.loc)).ok_or_else(|| {
            string
              .loc
              .error(SyntaxErrorType::InvalidCharacterEscape, None)
          })?,
        ));
        if string.typ == TT::LiteralTemplatePartStringEnd {
          break;
        };
      }
    };

    Ok(parts)
  }
}
