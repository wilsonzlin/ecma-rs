use super::expr::pat::ParsePatternRules;
use super::expr::Asi;
use super::ParseCtx;
use super::Parser;
use crate::ast::class_or_object::ClassMember;
use crate::ast::class_or_object::ClassOrObjGetter;
use crate::ast::class_or_object::ClassOrObjMemberDirectKey;
use crate::ast::class_or_object::ClassOrObjKey;
use crate::ast::class_or_object::ClassOrObjMethod;
use crate::ast::class_or_object::ClassOrObjSetter;
use crate::ast::class_or_object::ClassOrObjVal;
use crate::ast::expr::Expr;
use crate::ast::func::Func;
use crate::ast::node::Node;
use crate::ast::stmt::decl::ParamDecl;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::KEYWORDS_MAPPING;
use crate::token::TT;

impl<'a> Parser<'a> {
  pub fn class_body(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<ClassMember>>> {
    self.require(TT::BraceOpen)?;
    let members = self.repeat_until_tt_with_loc(
      TT::BraceClose,
      |p| {
        // `static` must always come first if present.
        let static_ = p.consume_if(TT::KeywordStatic).match_loc();
        let (key, value) = p.class_or_obj_member(
          ctx,
          TT::Equals,
          TT::Semicolon,
          &mut Asi::can(),
        )?;
        p.consume_if(TT::Semicolon);
        Ok(ClassMember {
          key,
          static_: static_.is_some(),
          val: value,
        })
      },
    )?;
    self.require(TT::BraceClose)?;
    Ok(members)
  }

  /// Parses a class or object key like `a`, `'a'`, `#a`, `"a"`, `1`, `[1]`.
  pub fn class_or_obj_key(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<ClassOrObjKey> {
    Ok(if self.peek().typ == TT::BracketOpen {
      ClassOrObjKey::Computed({
        self.require(TT::BracketOpen).unwrap();
        let key = self.expr(ctx, [TT::BracketClose])?;
        self.require(TT::BracketClose)?;
        key
      })
    } else {
      ClassOrObjKey::Direct(self.with_loc(|p| {
        let t = p.peek();
        let key = match t.typ {
          TT::LiteralString => p.lit_str_val()?,
          TT::LiteralNumber => p.lit_num_val()?.to_string(),
          // There's no trailing `n`.
          TT::LiteralBigInt => p.lit_bigint_val()?.to_string(),
          TT::PrivateMember => p.consume_as_string(),
          TT::Identifier => p.consume_as_string(),
          // Any keyword is allowed as a key.
          t if KEYWORDS_MAPPING.contains_key(&t) => p.consume_as_string(),
          _ => return Err(t.error(SyntaxErrorType::ExpectedSyntax("keyword or identifier"))),
        };
        Ok(ClassOrObjMemberDirectKey { key, tt: t.typ })
      })?)
    })
  }

  /// Parses a class or object method like `a() {}`, `async a() {}`, `*a() {}`, `async *a() {}`.
  pub fn class_or_obj_method(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjMethod>)> {
    let is_async = self.consume_if(TT::KeywordAsync).is_match();
    let is_generator = self.consume_if(TT::Asterisk).is_match();
    let key = self.class_or_obj_key(ctx)?;
    let func = self.with_loc(|p| {
      let parameters = p.func_params(ctx)?;
      let body = p.parse_func_block_body(ctx.with_rules(ParsePatternRules {
        await_allowed: !is_async && ctx.rules.await_allowed,
        yield_allowed: !is_generator && ctx.rules.yield_allowed,
      }))?.into();
      Ok(Func {
        arrow: false,
        async_: is_async,
        generator: is_generator,
        parameters,
        body,
      })
    })?;
    let val = func.wrap(|func| ClassOrObjMethod { func });
    Ok((key, val))
  }

  pub fn class_or_obj_getter(&mut self, ctx: ParseCtx) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjGetter>)> {
    self.require(TT::KeywordGet)?;
    let key = self.class_or_obj_key(ctx)?;
    let func = self.with_loc(|p| {
      p.require(TT::ParenthesisOpen)?;
      p.require(TT::ParenthesisClose)?;
      let body = p.parse_func_block_body(ctx)?.into();
      Ok(Func {
        arrow: false,
        async_: false,
        generator: false,
        parameters: Vec::new(),
        body,
      })
    })?;
    let val = func.wrap(|func| ClassOrObjGetter { func });
    Ok((key, val))
  }

  pub fn class_or_obj_setter(&mut self, ctx: ParseCtx) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjSetter>)> {
    self.require(TT::KeywordSet)?;
    let key = self.class_or_obj_key(ctx)?;
    let func = self.with_loc(|p| {
      p.require(TT::ParenthesisOpen)?;
      let param = p.pat_decl(ctx)?;
      p.require(TT::ParenthesisClose)?;
      let body = p.parse_func_block_body(ctx)?.into();
      Ok(Func {
        arrow: false,
        async_: false,
        generator: false,
        parameters: vec![Node::new(param.loc, ParamDecl {
          rest: false,
          pattern: param,
          default_value: None,
        })],
        body,
      })
    })?;
    let val = func.wrap(|func| ClassOrObjSetter { func });
    Ok((key, val))
  }

  /// Parses a class or object property like `a`, `5 = 1`, `#a = 1`, `a: 1`, `a: 1;`, `a: 1\n`.
  pub fn class_or_obj_prop(
    &mut self,
    ctx: ParseCtx,
    // The delimiter between the key and value. For objects, this is `:`; for classes, this is `=`.
    value_delimiter: TT,
    statement_delimiter: TT,
    property_initialiser_asi: &mut Asi,
  ) -> SyntaxResult<(ClassOrObjKey, Option<Node<Expr>>)> {
    let key = self.class_or_obj_key(ctx)?;
    let has_init = match key {
      ClassOrObjKey::Direct(_) => match self.peek() {
        // Given `class A {1}`, `"1" in new A`.
        t if t.typ == TT::BraceClose => true,
        // Given `class A {1;}`, `"1" in new A`.
        t if t.typ == statement_delimiter => true,
        // Given `class A {1\n2}`, `"2" in new A`.
        t if property_initialiser_asi.can_end_with_asi && t.preceded_by_line_terminator => true,
        _ => false,
      },
      _ => false,
    };
    let initializer = has_init
      .then(|| {
        self.require(value_delimiter)?;
        Ok(self.expr_with_asi(
          ctx,
          [statement_delimiter, TT::BraceClose],
          property_initialiser_asi,
        )?)
      })
      .transpose()?;
    Ok((key, initializer))
  }

  // It's strictly one of these:
  // - <key> [ '=' <expr> ]? [ <asi> | ';' ]
  // - async? '*'? <key> '(' ...
  // - [ get | set ] <key> '(' ...
  // where <key> = <ident> | <keyword> | <str> | <num> | '[' <expr> ']'
  pub fn class_or_obj_member(
    &mut self,
    ctx: ParseCtx,
    value_delimiter: TT,
    statement_delimiter: TT,
    property_initialiser_asi: &mut Asi,
  ) -> SyntaxResult<(ClassOrObjKey, ClassOrObjVal)> {
    let (a, b, c, d) = self.peek_4();
    Ok(match (a.typ, b.typ, c.typ, d.typ) {
      // Method. Includes using "get" or "set" as the method's name.
      (TT::KeywordAsync, TT::Asterisk, _, TT::ParenthesisOpen)
      | (TT::KeywordAsync, _, TT::ParenthesisOpen, _)
      | (TT::Asterisk, _, TT::ParenthesisOpen, _)
      | (_, TT::ParenthesisOpen, _, _)
      => {
        let (k, v) = self.class_or_obj_method(ctx)?;
        (k, v.into())
      }
      // Getter.
      (TT::KeywordGet, _, TT::ParenthesisOpen, _) => {
        let (k, v) = self.class_or_obj_getter(ctx)?;
        (k, v.into())
      }
      // Setter.
      (TT::KeywordSet, _, TT::ParenthesisOpen, _) => {
        let (k, v) = self.class_or_obj_setter(ctx)?;
        (k, v.into())
      }
      // Assume it's a property.
      _ => {
        let (k, v) = self.class_or_obj_prop(ctx, value_delimiter, statement_delimiter, property_initialiser_asi)?;
        (k, v.into())
      }
    })
  }
}
