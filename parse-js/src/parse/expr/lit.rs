use super::pat::is_valid_pattern_identifier;
use super::Asi;
use super::ParseCtx;
use super::Parser;
use crate::ast::class_or_object::ClassOrObjKey;
use crate::ast::class_or_object::ClassOrObjMemberDirectKey;
use crate::ast::class_or_object::ClassOrObjVal;
use crate::ast::class_or_object::ObjMember;
use crate::ast::class_or_object::ObjMemberType;
use crate::ast::expr::BinaryExpr;
use crate::ast::expr::Expr;
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
use crate::lex::KEYWORDS_MAPPING;
use crate::num::JsNumber;
use crate::operator::OperatorName;
use crate::token::TT;
use core::str::FromStr;

fn parse_radix(raw: &str, radix: u32) -> Result<f64, ()> {
  // Strip numeric separators (_) before parsing
  let stripped = raw.replace('_', "");
  match u64::from_str_radix(&stripped, radix) {
    Ok(v) => Ok(v as f64),
    Err(e) => {
      // Check if this is an overflow (number too large) vs invalid format
      use std::num::IntErrorKind;
      if e.kind() == &IntErrorKind::PosOverflow {
        // Number is too large to fit in u64, return Infinity
        Ok(f64::INFINITY)
      } else {
        // Invalid format (e.g., invalid digits for radix)
        Err(())
      }
    }
  }
}

pub fn normalise_literal_number(raw: &str) -> Option<JsNumber> {
  // TODO We assume that the Rust parser follows ECMAScript spec and that different representations
  // of the same value get parsed into the same f64 value/bit pattern (e.g. `5.1e10` and `0.51e11`).
  // Strip numeric separators (_) before parsing for decimal numbers
  let stripped;
  let to_parse = if raw.contains('_')
    && !raw.starts_with("0b")
    && !raw.starts_with("0B")
    && !raw.starts_with("0o")
    && !raw.starts_with("0O")
    && !raw.starts_with("0x")
    && !raw.starts_with("0X") {
    stripped = raw.replace('_', "");
    &stripped
  } else {
    raw
  };

  match to_parse {
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
            let hex_chars = &raw[2..end_pos];
            // Must have at least 1 hex digit
            if hex_chars.is_empty() || !hex_chars.chars().all(|c| c.is_ascii_hexdigit()) {
              return None;
            };
            let cp = u32::from_str_radix(hex_chars, 16).ok()?;
            // char::from_u32 validates that cp is a valid Unicode code point (<= 0x10FFFF)
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
              false, // Object literals don't have abstract methods
            )?;
            let typ = match value {
              ClassOrObjVal::Prop(None) => {
                // This property had no value, so it's a shorthand property. Therefore, check that it's a valid identifier name.
                let ClassOrObjKey::Direct(key) = key else {
                  // Computed properties cannot be shorthand
                  let loc = match key {
                    ClassOrObjKey::Computed(ref expr) => expr.loc,
                    _ => unreachable!(),
                  };
                  return Err(loc.error(SyntaxErrorType::ExpectedSyntax("property value"), None));
                };
                // TypeScript: Accept any keyword in shorthand property for error recovery (e.g., { while })
                // The type checker will validate this semantically.
                if key.stx.tt != TT::Identifier && !KEYWORDS_MAPPING.contains_key(&key.stx.tt) {
                  return Err(key.error(SyntaxErrorType::ExpectedNotFound));
                };
                // TypeScript: Check for definite assignment assertion (e.g., { a! })
                let _definite_assignment = p.consume_if(TT::Exclamation).is_match();
                // Check for default value (e.g., {c = 1})
                if p.consume_if(TT::Equals).is_match() {
                  // Parse the default value and create an assignment expression
                  let key_name = key.stx.key.clone();
                  let key_loc = key.loc;
                  let default_val = p.expr(ctx, [TT::Comma, TT::BraceClose])?;
                  let id_expr = Node::new(key_loc, IdExpr { name: key_name.clone() }).into_wrapped();
                  let bin_expr = Node::new(key_loc + default_val.loc, BinaryExpr {
                    operator: OperatorName::Assignment,
                    left: id_expr,
                    right: default_val,
                  }).into_wrapped();
                  ObjMemberType::Valued {
                    key: ClassOrObjKey::Direct(Node::new(key_loc, ClassOrObjMemberDirectKey {
                      key: key_name,
                      tt: TT::Identifier,
                    })),
                    val: ClassOrObjVal::Prop(Some(bin_expr))
                  }
                } else {
                  // No default value - this is a normal shorthand property
                  ObjMemberType::Shorthand {
                    id: key.map_stx(|n| IdExpr { name: n.key }),
                  }
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
  /// TypeScript: Allows invalid escape sequences (permissive parsing, semantic errors caught later)
  pub fn lit_str_val(&mut self) -> SyntaxResult<String> {
    let t = self.require(TT::LiteralString)?;
    // TypeScript: Allow invalid escapes (e.g., \u{110000} out of range)
    // Use empty string for invalid escapes to continue parsing
    Ok(normalise_literal_string(self.str(t.loc)).unwrap_or_else(|| String::new()))
  }

  pub fn lit_template(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<LitTemplateExpr>> {
    self.with_loc(|p| {
      let parts = p.lit_template_parts(ctx, false)?;
      Ok(LitTemplateExpr { parts })
    })
  }

  // NOTE: The next token must definitely be LiteralTemplatePartString{,End}.
  // ES2018: Tagged templates can have invalid escape sequences (cooked value is undefined, raw is available)
  // TypeScript: All templates allow invalid escapes (permissive parsing, semantic errors caught later)
  pub fn lit_template_parts(&mut self, ctx: ParseCtx, tagged: bool) -> SyntaxResult<Vec<LitTemplatePart>> {
    let t = self.consume();
    let is_end = match t.typ {
      TT::LiteralTemplatePartString => false,
      TT::LiteralTemplatePartStringEnd => true,
      _ => unreachable!(),
    };

    let mut parts = Vec::new();
    // ES2018: Tagged templates allow invalid escapes
    // TypeScript: All templates allow invalid escapes (permissive parsing)
    let first_str = normalise_literal_string_or_template_inner(self.bytes(t.loc)).unwrap_or_else(|| String::new());
    parts.push(LitTemplatePart::String(first_str));
    if !is_end {
      loop {
        let substitution = self.expr(ctx, [TT::BraceClose])?;
        self.require(TT::BraceClose)?;
        parts.push(LitTemplatePart::Substitution(substitution));
        let string = self.consume_with_mode(LexMode::TemplateStrContinue);
        if !matches!(string.typ, TT::LiteralTemplatePartString | TT::LiteralTemplatePartStringEnd) {
          return Err(string.error(SyntaxErrorType::ExpectedSyntax("template string part")));
        };
        // ES2018: Tagged templates allow invalid escapes
        // TypeScript: All templates allow invalid escapes (permissive parsing)
        let part_str = normalise_literal_string_or_template_inner(self.bytes(string.loc)).unwrap_or_else(|| String::new());
        parts.push(LitTemplatePart::String(part_str));
        if string.typ == TT::LiteralTemplatePartStringEnd {
          break;
        };
      }
    };

    Ok(parts)
  }
}
