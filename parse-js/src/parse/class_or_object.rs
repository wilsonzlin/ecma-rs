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
    let mut members = Vec::new();
    loop {
      // Skip empty semicolons
      while self.consume_if(TT::Semicolon).is_match() {}
      // Check if we're at the end
      if self.peek().typ == TT::BraceClose {
        break;
      }
      let member = self.with_loc(|p| {
        // TypeScript: parse decorators for members
        let decorators = p.decorators(ctx)?;

        // Parse TypeScript modifiers in order:
        // [accessibility] [abstract] [override] [static] [readonly]

        // TypeScript: accessibility modifiers (public, private, protected)
        let accessibility = if p.consume_if(TT::KeywordPublic).is_match() {
          Some(crate::ast::stmt::decl::Accessibility::Public)
        } else if p.consume_if(TT::KeywordPrivate).is_match() {
          Some(crate::ast::stmt::decl::Accessibility::Private)
        } else if p.consume_if(TT::KeywordProtected).is_match() {
          Some(crate::ast::stmt::decl::Accessibility::Protected)
        } else {
          None
        };

        // TypeScript: abstract modifier
        let abstract_ = p.consume_if(TT::KeywordAbstract).is_match();

        // TypeScript: override modifier
        let override_ = p.consume_if(TT::KeywordOverride).is_match();

        // `static` must always come after other modifiers
        let static_ = if p.peek().typ == TT::KeywordStatic {
          let [_, next] = p.peek_n::<2>();
          if next.typ == TT::ParenthesisOpen {
            // `static()` - it's a method name, not a modifier
            false
          } else {
            p.consume_if(TT::KeywordStatic).is_match()
          }
        } else {
          false
        };

        // TypeScript: readonly modifier
        let readonly = p.consume_if(TT::KeywordReadonly).is_match();

        // TypeScript: check for index signature [key: type]: type
        let (key, value) = if p.peek().typ == TT::BracketOpen {
          let checkpoint = p.checkpoint();
          let _bracket = p.consume();
          // Check if this looks like an index signature (identifier : type])
          let looks_like_index_sig = if p.peek().typ == TT::Identifier {
            let [_, t2] = p.peek_n::<2>();
            t2.typ == TT::Colon
          } else {
            false
          };
          p.restore_checkpoint(checkpoint);

          if looks_like_index_sig {
            // Parse index signature
            let index_sig = p.with_loc(|p| {
              p.require(TT::BracketOpen)?;
              let parameter_name = p.require_identifier()?;
              p.require(TT::Colon)?;
              let parameter_type = p.type_expr(ctx)?;
              p.require(TT::BracketClose)?;
              p.require(TT::Colon)?;
              let type_annotation = p.type_expr(ctx)?;
              use crate::ast::class_or_object::ClassIndexSignature;
              Ok(ClassIndexSignature {
                parameter_name,
                parameter_type,
                type_annotation,
              })
            })?;
            // Fabricate a key (unused for index signatures) and wrap in IndexSignature variant
            use crate::ast::class_or_object::{ClassOrObjKey, ClassOrObjMemberDirectKey, ClassOrObjVal};
            use crate::loc::Loc;
            let dummy_key = ClassOrObjKey::Direct(Node::new(
              Loc(0, 0),
              ClassOrObjMemberDirectKey {
                key: String::new(),
                tt: TT::Identifier,
              }
            ));
            (dummy_key, ClassOrObjVal::IndexSignature(index_sig))
          } else {
            p.class_or_obj_member(
              ctx,
              TT::Equals,
              TT::Semicolon,
              &mut Asi::can(),
              abstract_,
            )?
          }
        } else {
          p.class_or_obj_member(
            ctx,
            TT::Equals,
            TT::Semicolon,
            &mut Asi::can(),
            abstract_,
          )?
        };

        // TypeScript: definite assignment assertion (! after key)
        let definite_assignment = p.consume_if(TT::Exclamation).is_match();

        // TypeScript: optional property (? after key)
        let optional = p.consume_if(TT::Question).is_match();

        // TypeScript: type annotation
        let type_annotation = if p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr(ctx)?)
        } else {
          None
        };

        p.consume_if(TT::Semicolon);
        Ok(ClassMember {
          decorators,
          key,
          static_,
          abstract_,
          readonly,
          optional,
          override_,
          definite_assignment,
          accessibility,
          type_annotation,
          val: value,
        })
      })?;
      members.push(member);
    }
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
    abstract_: bool,
  ) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjMethod>)> {
    let is_async = self.consume_if(TT::KeywordAsync).is_match();
    let is_generator = self.consume_if(TT::Asterisk).is_match();
    let key = self.class_or_obj_key(ctx)?;
    let func = self.with_loc(|p| {
      // TypeScript: generic type parameters
      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };
      let parameters = p.func_params(ctx)?;
      // TypeScript: return type annotation - may be type predicate
      let return_type = if p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr_or_predicate(ctx)?)
      } else {
        None
      };
      // TypeScript: abstract methods have no body
      let body = if abstract_ && p.peek().typ != TT::BraceOpen {
        p.consume_if(TT::Semicolon);
        None
      } else {
        Some(p.parse_func_block_body(ctx.with_rules(ParsePatternRules {
          await_allowed: !is_async && ctx.rules.await_allowed,
          yield_allowed: !is_generator && ctx.rules.yield_allowed,
        }))?.into())
      };
      Ok(Func {
        arrow: false,
        async_: is_async,
        generator: is_generator,
        type_parameters,
        parameters,
        return_type,
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
      // TypeScript: generic type parameters
      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };
      p.require(TT::ParenthesisOpen)?;
      p.require(TT::ParenthesisClose)?;
      // TypeScript: return type annotation - may be type predicate
      let return_type = if p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr_or_predicate(ctx)?)
      } else {
        None
      };
      // Getters are not generators or async, so yield/await can be used as identifiers
      let body = p.parse_func_block_body(ctx.with_rules(ParsePatternRules {
        await_allowed: true,
        yield_allowed: true,
      }))?.into();
      Ok(Func {
        arrow: false,
        async_: false,
        generator: false,
        type_parameters,
        parameters: Vec::new(),
        return_type,
        body: Some(body),
      })
    })?;
    let val = func.wrap(|func| ClassOrObjGetter { func });
    Ok((key, val))
  }

  pub fn class_or_obj_setter(&mut self, ctx: ParseCtx) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjSetter>)> {
    self.require(TT::KeywordSet)?;
    let key = self.class_or_obj_key(ctx)?;
    let func = self.with_loc(|p| {
      // TypeScript: generic type parameters
      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };
      p.require(TT::ParenthesisOpen)?;
      // Setters are not generators or async, so yield/await can be used as identifiers
      let setter_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: true,
        yield_allowed: true,
      });
      let pattern = p.pat_decl(setter_ctx)?;
      let default_value = p.consume_if(TT::Equals)
        .and_then(|| {
          p.expr(setter_ctx, [TT::ParenthesisClose])
        })?;
      let param_loc = pattern.loc;
      p.require(TT::ParenthesisClose)?;
      // Setters don't have return types
      let body = p.parse_func_block_body(setter_ctx)?.into();
      Ok(Func {
        arrow: false,
        async_: false,
        generator: false,
        type_parameters,
        parameters: vec![Node::new(param_loc, ParamDecl {
          decorators: Vec::new(),
          rest: false,
          optional: false,
          accessibility: None,
          readonly: false,
          pattern,
          type_annotation: None,
          default_value,
        })],
        return_type: None,
        body: Some(body),
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
        // Given `class A {1}`, `"1" in new A` - bare property with no initializer.
        t if t.typ == TT::BraceClose => false,
        // Given `class A {1;}`, `"1" in new A` - bare property with no initializer.
        t if t.typ == statement_delimiter => false,
        // Given `class A {1\n2}`, `"2" in new A` - bare property with no initializer.
        t if property_initialiser_asi.can_end_with_asi && t.preceded_by_line_terminator => false,
        // If we see the value delimiter, we have an initializer
        t if t.typ == value_delimiter => true,
        // Otherwise, bare property
        _ => false,
      },
      // Computed properties always check for delimiter
      ClassOrObjKey::Computed(_) => self.peek().typ == value_delimiter,
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
    abstract_: bool,
  ) -> SyntaxResult<(ClassOrObjKey, ClassOrObjVal)> {
    let [a, b, c, d] = self.peek_n();
    // Special case for computed keys: parse key first, then check what follows
    // Handle: [...], *[...], get [...], set [...]
    if a.typ == TT::BracketOpen
      || (a.typ == TT::Asterisk && b.typ == TT::BracketOpen)
      || (a.typ == TT::KeywordGet && b.typ == TT::BracketOpen)
      || (a.typ == TT::KeywordSet && b.typ == TT::BracketOpen) {
      // Check if this is a getter or setter with computed key
      let is_getter = a.typ == TT::KeywordGet;
      let is_setter = a.typ == TT::KeywordSet;
      if is_getter || is_setter {
        // Don't consume get/set here - the getter/setter functions will do it
        if is_getter {
          let (key, val) = self.class_or_obj_getter(ctx)?;
          return Ok((key, val.into()));
        } else {
          let (key, val) = self.class_or_obj_setter(ctx)?;
          return Ok((key, val.into()));
        }
      }
      // Otherwise it's a regular method or property
      let is_async = false;
      let is_generator = a.typ == TT::Asterisk;
      if is_generator {
        self.require(TT::Asterisk)?;
      }
      let key = self.class_or_obj_key(ctx)?;
      return Ok(if self.peek().typ == TT::ParenthesisOpen {
        let method = self.with_loc(|p| {
          let func = p.with_loc(|p| {
            // TypeScript: generic type parameters
            let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
              Some(p.type_parameters(ctx)?)
            } else {
              None
            };
            let parameters = p.func_params(ctx)?;
            // TypeScript: return type annotation
            let return_type = if p.consume_if(TT::Colon).is_match() {
              Some(p.type_expr_or_predicate(ctx)?)
            } else {
              None
            };
            // TypeScript: abstract methods have no body
            let body = if abstract_ && p.peek().typ != TT::BraceOpen {
              p.consume_if(TT::Semicolon);
              None
            } else {
              Some(p.parse_func_block_body(ctx.with_rules(ParsePatternRules {
                await_allowed: !is_async && ctx.rules.await_allowed,
                yield_allowed: !is_generator && ctx.rules.yield_allowed,
              }))?.into())
            };
            Ok(Func {
              arrow: false,
              async_: is_async,
              generator: is_generator,
              type_parameters,
              parameters,
              return_type,
              body,
            })
          })?;
          Ok(ClassOrObjMethod { func })
        })?;
        (key, ClassOrObjVal::Method(method))
      } else {
        let initializer = if self.peek().typ == value_delimiter {
          self.require(value_delimiter)?;
          Some(self.expr_with_asi(ctx, [statement_delimiter, TT::BraceClose], property_initialiser_asi)?)
        } else {
          None
        };
        (key, ClassOrObjVal::Prop(initializer))
      });
    }
    Ok(match (a.typ, b.typ, c.typ, d.typ) {
      // Method. Includes using "get" or "set" as the method's name.
      (TT::KeywordAsync, TT::Asterisk, _, TT::ParenthesisOpen)
      | (TT::KeywordAsync, _, TT::ParenthesisOpen, _)
      | (TT::Asterisk, _, TT::ParenthesisOpen, _)
      | (_, TT::ParenthesisOpen, _, _)
      => {
        let (k, v) = self.class_or_obj_method(ctx, abstract_)?;
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
