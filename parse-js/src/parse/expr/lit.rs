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
use memchr::memchr;
use std::str::from_utf8_unchecked;

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
    s if s.starts_with("0o") || s.starts_with("0o") => parse_radix(&s[2..], 8),
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

pub fn normalise_literal_string_or_template_inner(mut raw: &[u8]) -> Option<String> {
  let mut norm = Vec::new();
  while !raw.is_empty() {
    let Some(escape_pos) = memchr(b'\\', raw) else {
      norm.extend_from_slice(raw);
      break;
    };
    norm.extend_from_slice(&raw[..escape_pos]);
    raw = &raw[escape_pos + 1..];
    // https://mathiasbynens.be/notes/javascript-escapes
    // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String#escape_sequences
    // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Template_literals#tagged_templates_and_escape_sequences
    let mut tmp = [0u8; 4];
    let (skip, add): (usize, &[u8]) = match raw[0] {
      b'\n' => (1, b""),
      b'b' => (1, b"\x08"),
      b'f' => (1, b"\x0c"),
      b'n' => (1, b"\n"),
      b'r' => (1, b"\r"),
      b't' => (1, b"\t"),
      b'v' => (1, b"\x0b"),
      b'0'..=b'7' => {
        // Octal escape.
        let mut len = 1;
        if raw
          .get(len)
          .filter(|&c| (b'0'..=b'7').contains(c))
          .is_some()
        {
          len += 1;
          if raw
            .get(len)
            .filter(|&c| (b'0'..=b'7').contains(c))
            .is_some()
          {
            len += 1;
          };
        };
        char::from_u32(
          u32::from_str_radix(unsafe { from_utf8_unchecked(&raw[..len]) }, 8).unwrap(),
        )
        .unwrap()
        .encode_utf8(&mut tmp);
        (len, tmp.as_slice())
      }
      b'x' => {
        // Hexadecimal escape.
        if raw.len() < 3 || !raw[1].is_ascii_hexdigit() || !raw[2].is_ascii_hexdigit() {
          return None;
        };
        char::from_u32(
          u32::from_str_radix(unsafe { from_utf8_unchecked(&raw[1..3]) }, 16).unwrap(),
        )
        .unwrap()
        .encode_utf8(&mut tmp);
        (3, tmp.as_slice())
      }
      b'u' => match raw.get(1) {
        Some(b'{') => {
          // Unicode code point escape.
          let Some(end_pos) = memchr(b'}', raw) else {
            return None;
          };
          if !(3..=8).contains(&end_pos) {
            return None;
          };
          let cp =
            u32::from_str_radix(unsafe { from_utf8_unchecked(&raw[2..end_pos]) }, 16).ok()?;
          let c = char::from_u32(cp)?;
          c.encode_utf8(&mut tmp);
          (end_pos + 1, tmp.as_slice())
        }
        Some(_) => {
          // Unicode escape.
          if raw.len() < 5 {
            return None;
          };
          let cp = u32::from_str_radix(unsafe { from_utf8_unchecked(&raw[1..5]) }, 16).ok()?;
          let c = char::from_u32(cp)?;
          c.encode_utf8(&mut tmp);
          (5, tmp.as_slice())
        }
        None => {
          return None;
        }
      },
      c => (1, {
        tmp[0] = c;
        &tmp[..1]
      }),
    };
    norm.extend_from_slice(add);
    raw = &raw[skip..];
  }
  // We return str instead of [u8] so that serialisation is easy and str methods are available.
  Some(String::from_utf8(norm).unwrap())
}

pub fn normalise_literal_string(raw: &str) -> Option<String> {
  normalise_literal_string_or_template_inner(&raw.as_bytes()[1..raw.len() - 1])
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
      let t = p.require(TT::LiteralRegex)?;
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
