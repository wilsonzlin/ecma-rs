use super::expr::pat::ParsePatternRules;
use super::expr::Asi;
use super::ParseCtx;
use super::Parser;
use crate::ast::class_or_object::ClassIndexSignature;
use crate::ast::class_or_object::ClassMember;
use crate::ast::class_or_object::ClassOrObjGetter;
use crate::ast::class_or_object::ClassOrObjKey;
use crate::ast::class_or_object::ClassOrObjMemberDirectKey;
use crate::ast::class_or_object::ClassOrObjMethod;
use crate::ast::class_or_object::ClassOrObjSetter;
use crate::ast::class_or_object::ClassOrObjVal;
use crate::ast::expr::pat::IdPat;
use crate::ast::expr::Expr;
use crate::ast::func::Func;
use crate::ast::node::LeadingZeroDecimalLiteral;
use crate::ast::node::LegacyOctalEscapeSequence;
use crate::ast::node::LegacyOctalNumberLiteral;
use crate::ast::node::Node;
use crate::ast::stmt::decl::ParamDecl;
use crate::ast::stmt::decl::PatDecl;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::LexMode;
use crate::lex::KEYWORDS_MAPPING;
use crate::token::TT;

impl<'a> Parser<'a> {
  /// Parse a TypeScript index signature: `[key: T]: U`
  fn parse_index_signature(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ClassIndexSignature>> {
    self.with_loc(|p| {
      p.require(TT::BracketOpen)?;
      let parameter_name = p.require_identifier()?;
      p.require(TT::Colon)?;
      let parameter_type = p.type_expr(ctx)?;
      p.require(TT::BracketClose)?;
      p.require(TT::Colon)?;
      let type_annotation = p.type_expr(ctx)?;
      Ok(ClassIndexSignature {
        parameter_name,
        parameter_type,
        type_annotation,
      })
    })
  }

  fn probable_class_member_start(tt: TT) -> bool {
    matches!(
      tt,
      TT::At
        | TT::Asterisk
        | TT::BracketOpen
        | TT::BraceClose
        | TT::Identifier
        | TT::LiteralNumber
        | TT::LiteralString
        | TT::ParenthesisOpen
        | TT::PrivateMember
        | TT::KeywordConstructor
        | TT::KeywordGet
        | TT::KeywordSet
        | TT::KeywordAsync
        | TT::KeywordStatic
        | TT::KeywordReadonly
        | TT::KeywordAccessor
        | TT::KeywordPublic
        | TT::KeywordPrivate
        | TT::KeywordProtected
        | TT::KeywordAbstract
    )
  }

  /// Creates a synthetic empty key for special class members (static blocks, index signatures, generators).
  /// These members don't have real keys in the source code.
  fn create_synthetic_class_key(&self) -> ClassOrObjKey {
    use crate::ast::class_or_object::ClassOrObjKey;
    use crate::ast::class_or_object::ClassOrObjMemberDirectKey;
    use crate::loc::Loc;
    ClassOrObjKey::Direct(Node::new(
      Loc(0, 0),
      ClassOrObjMemberDirectKey {
        key: String::new(),
        tt: TT::Identifier,
      },
    ))
  }

  pub fn class_body(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<ClassMember>>> {
    self.class_body_with_context(ctx, false)
  }

  pub fn class_body_with_context(
    &mut self,
    ctx: ParseCtx,
    ambient: bool,
  ) -> SyntaxResult<Vec<Node<ClassMember>>> {
    self.require(TT::BraceOpen)?;
    let mut members = Vec::new();
    loop {
      // Skip empty semicolons
      while self.consume_if(TT::Semicolon).is_match() {}
      // Check if we're at the end
      if self.peek().typ == TT::BraceClose {
        break;
      }
      // TypeScript-style recovery: nested class declarations are not allowed,
      // but try to skip them so the rest of the class body can be parsed.
      let looks_like_nested_class = self.should_recover()
        && self.peek().typ == TT::KeywordClass
        && matches!(
          self.peek_n::<3>()[1].typ,
          TT::Identifier | TT::BraceOpen | TT::KeywordExtends
        );
      if looks_like_nested_class {
        // Skip the entire nested class declaration
        self.consume(); // consume 'class'
                        // Skip optional class name
        if self.peek().typ == TT::Identifier {
          self.consume();
        }
        // Skip optional type parameters
        if self.peek().typ == TT::ChevronLeft {
          let mut depth = 0;
          while self.peek().typ != TT::EOF {
            if self.peek().typ == TT::ChevronLeft {
              depth += 1;
              self.consume();
            } else if self.peek().typ == TT::ChevronRight {
              self.consume();
              depth -= 1;
              if depth == 0 {
                break;
              }
            } else if self.peek().typ == TT::BraceOpen {
              break;
            } else {
              self.consume();
            }
          }
        }
        // Skip optional extends clause
        if self.consume_if(TT::KeywordExtends).is_match() {
          // Skip until we reach the class body
          while self.peek().typ != TT::BraceOpen && self.peek().typ != TT::EOF {
            self.consume();
          }
        }
        // Skip optional implements clause
        if self.consume_if(TT::KeywordImplements).is_match() {
          // Skip until we reach the class body
          while self.peek().typ != TT::BraceOpen && self.peek().typ != TT::EOF {
            self.consume();
          }
        }
        // Skip the class body
        if self.peek().typ == TT::BraceOpen {
          let mut depth = 0;
          while self.peek().typ != TT::EOF {
            if self.peek().typ == TT::BraceOpen {
              depth += 1;
              self.consume();
            } else if self.peek().typ == TT::BraceClose {
              self.consume();
              depth -= 1;
              if depth == 0 {
                break;
              }
            } else {
              self.consume();
            }
          }
        }
        // Continue to next member
        continue;
      }
      let member = self.with_loc(|p| {
        // TypeScript-style recovery: parse decorators for members.
        let decorators = if p.should_recover() {
          p.decorators(ctx)?
        } else {
          Vec::new()
        };

        // Parse TypeScript modifiers in order:
        // [accessibility] [abstract] [override] [static] [readonly]

        // TypeScript: accessibility modifiers (public, private, protected)
        // Error recovery: allow duplicate modifiers
        let mut accessibility = None;
        while p.peek().typ == TT::KeywordPublic
          || p.peek().typ == TT::KeywordPrivate
          || p.peek().typ == TT::KeywordProtected
        {
          if p.consume_if(TT::KeywordPublic).is_match() {
            accessibility = Some(crate::ast::stmt::decl::Accessibility::Public);
          } else if p.consume_if(TT::KeywordPrivate).is_match() {
            accessibility = Some(crate::ast::stmt::decl::Accessibility::Private);
          } else if p.consume_if(TT::KeywordProtected).is_match() {
            accessibility = Some(crate::ast::stmt::decl::Accessibility::Protected);
          }
        }

        // TypeScript: abstract modifier
        // Error recovery: allow duplicate abstract modifiers
        let mut abstract_ = ambient;
        while p.consume_if(TT::KeywordAbstract).is_match() {
          abstract_ = true;
        }

        // TypeScript: override modifier
        // Error recovery: allow duplicate override modifiers
        let mut override_ = false;
        while p.consume_if(TT::KeywordOverride).is_match() {
          override_ = true;
        }

        // `static` must always come after other modifiers
        let static_ = if p.peek().typ == TT::KeywordStatic {
          let [_, next] = p.peek_n::<2>();
          if next.typ == TT::BraceOpen {
            // `static {}` - static initialization block
            p.consume(); // consume 'static'
            let block = p.with_loc(|p| {
              p.require(TT::BraceOpen)?;
              // Static blocks have their own break/continue/label scope; they cannot
              // target iteration statements or labels outside the block.
              let prev_in_iteration = p.in_iteration;
              let prev_in_switch = p.in_switch;
              let prev_labels = std::mem::take(&mut p.labels);
              let prev_new_target_allowed = p.new_target_allowed;
              let prev_super_prop_allowed = p.super_prop_allowed;
              let prev_super_call_allowed = p.super_call_allowed;
              p.in_iteration = 0;
              p.in_switch = 0;
              p.new_target_allowed += 1;
              p.super_prop_allowed += 1;
              p.super_call_allowed = 0;
              let body = p.stmts(ctx.non_top_level(), TT::BraceClose);
              p.in_iteration = prev_in_iteration;
              p.in_switch = prev_in_switch;
              p.new_target_allowed = prev_new_target_allowed;
              p.super_prop_allowed = prev_super_prop_allowed;
              p.super_call_allowed = prev_super_call_allowed;
              p.labels = prev_labels;
              let body = body?;
              p.require(TT::BraceClose)?;
              Ok(crate::ast::class_or_object::ClassStaticBlock { body })
            })?;
            use crate::ast::class_or_object::ClassOrObjVal;
            let dummy_key = p.create_synthetic_class_key();
            return Ok(ClassMember {
              decorators,
              key: dummy_key,
              static_: true,
              abstract_: false,
              readonly: false,
              accessor: false,
              optional: false,
              override_: false,
              definite_assignment: false,
              accessibility: None,
              type_annotation: None,
              val: ClassOrObjVal::StaticBlock(block),
            });
          } else if next.typ == TT::ParenthesisOpen {
            // `static()` - it's a method name, not a modifier
            false
          } else {
            p.consume_if(TT::KeywordStatic).is_match()
          }
        } else {
          false
        };

        // TypeScript: readonly modifier
        // Error recovery: allow duplicate readonly modifiers
        let mut readonly = false;
        while p.consume_if(TT::KeywordReadonly).is_match() {
          readonly = true;
        }

        // TypeScript/JavaScript: accessor modifier for auto-accessors
        // Error recovery: allow duplicate accessor modifiers
        let mut accessor = false;
        while p.consume_if(TT::KeywordAccessor).is_match() {
          accessor = true;
        }

        // TypeScript-style recovery: skip decorators in invalid positions
        // e.g., `public @dec get foo()` - decorator after modifier is invalid
        if p.should_recover() {
          while p.peek().typ == TT::At {
            let _ = p.decorators(ctx);
          }
        }

        // TypeScript: check for index signature [key: type]: type
        let (key, value, definite_assignment, optional, type_annotation) =
          if p.peek().typ == TT::BracketOpen {
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

            if looks_like_index_sig && !p.is_strict_ecmascript() {
              // Parse index signature
              let index_sig = p.parse_index_signature(ctx)?;
              // Fabricate a key (unused for index signatures) and wrap in IndexSignature variant
              use crate::ast::class_or_object::ClassOrObjVal;
              let dummy_key = p.create_synthetic_class_key();
              (
                dummy_key,
                ClassOrObjVal::IndexSignature(index_sig),
                false,
                false,
                None,
              )
            } else {
              // Computed property name: [expr]
              // Parse the computed key
              let key = p.class_or_obj_key(ctx)?;

              // TypeScript: definite assignment assertion (! after key)
              let definite_assignment =
                !p.is_strict_ecmascript() && p.consume_if(TT::Exclamation).is_match();

              // TypeScript: optional property (? after key)
              let optional = !p.is_strict_ecmascript() && p.consume_if(TT::Question).is_match();

              // TypeScript: type annotation (: type)
              let type_annotation =
                if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
                  Some(p.type_expr(ctx)?)
                } else {
                  None
                };

              // Now check for method/getter/setter or property initializer
              let value = p.class_member_value(ctx, &key, static_, abstract_)?;

              (key, value, definite_assignment, optional, type_annotation)
            }
          } else {
            // Check for special member types that need early detection:
            // async methods, generator methods, getters, setters
            let [t0, t1, t2] = p.peek_n();

            // Detect async generator: async *
            // Detect async method: async identifier/keyword (
            // Detect async method with computed property: async [
            // Detect generator: * identifier/keyword (
            // Detect generator with computed property: * [
            // Detect getter: get identifier/keyword [(
            // Detect setter: set identifier/keyword (
            let needs_special_handling = matches!(
              (t0.typ, t1.typ, t2.typ),
              (TT::KeywordAsync, TT::Asterisk, _)
                | (TT::KeywordAsync, TT::BracketOpen, _)
                | (TT::KeywordAsync, _, TT::ParenthesisOpen)
                | (TT::Asterisk, _, TT::ParenthesisOpen)
                | (TT::Asterisk, TT::BracketOpen, _)
                | (TT::KeywordGet, _, TT::ParenthesisOpen)
                | (TT::KeywordSet, _, TT::ParenthesisOpen)
            );

            if needs_special_handling {
              // Use the original class_or_obj_member for these special cases
              let (key, value) =
                p.class_or_obj_member(ctx, TT::Equals, TT::Semicolon, &mut Asi::can(), abstract_)?;
              (key, value, false, false, None)
            } else {
              // Parse class member with TypeScript syntax: key [!] [?] [: type] [= init]
              let key = p.class_or_obj_key(ctx)?;

              // TypeScript: definite assignment assertion (! after key)
              let definite_assignment =
                !p.is_strict_ecmascript() && p.consume_if(TT::Exclamation).is_match();

              // TypeScript: optional property (? after key)
              let optional = !p.is_strict_ecmascript() && p.consume_if(TT::Question).is_match();

              // TypeScript: type annotation (: type)
              let type_annotation =
                if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
                  Some(p.type_expr(ctx)?)
                } else {
                  None
                };

              // Now check for method/getter/setter or property initializer
              let value = p.class_member_value(ctx, &key, static_, abstract_)?;

              (key, value, definite_assignment, optional, type_annotation)
            }
          };

        let _ = p.consume_if(TT::Semicolon);
        Ok(ClassMember {
          decorators,
          key,
          static_,
          abstract_,
          readonly,
          accessor,
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

  /// Parses a class or object key like `a`, `'a'`, `#a`, `"a"`, `1`, `[1]`, `` `template` ``.
  pub fn class_or_obj_key(&mut self, ctx: ParseCtx) -> SyntaxResult<ClassOrObjKey> {
    Ok(if self.peek().typ == TT::BracketOpen {
      ClassOrObjKey::Computed({
        self.require(TT::BracketOpen).unwrap();
        let key = self.expr(ctx, [TT::BracketClose])?;
        self.require(TT::BracketClose)?;
        key
      })
    } else if self.peek().typ == TT::LiteralTemplatePartString
      || self.peek().typ == TT::LiteralTemplatePartStringEnd
    {
      // Template literal as property key: `foo` or `foo${expr}bar`
      ClassOrObjKey::Computed(self.lit_template(ctx)?.into_wrapped())
    } else {
      let t = self.peek();
      let loc = t.loc;
      let tt = t.typ;
      let mut legacy_escape = None;
      let key = match tt {
        TT::LiteralString => {
          let (_tok_loc, key, escape_loc) =
            self.lit_str_val_with_mode_and_legacy_escape(LexMode::Standard)?;
          legacy_escape = escape_loc;
          key
        }
        TT::LiteralNumber => self.lit_num_val()?.to_string(),
        // There's no trailing `n`.
        TT::LiteralBigInt => self.lit_bigint_val()?.to_string(),
        TT::PrivateMember => self.consume_as_string(),
        TT::Identifier => self.consume_as_string(),
        // Any keyword is allowed as a key.
        t if KEYWORDS_MAPPING.contains_key(&t) => self.consume_as_string(),
        // TypeScript-style recovery: allow asterisk as property key (malformed generator).
        TT::Asterisk if self.should_recover() => self.consume_as_string(),
        _ => return Err(t.error(SyntaxErrorType::ExpectedSyntax("keyword or identifier"))),
      };

      let mut direct = Node::new(loc, ClassOrObjMemberDirectKey { key, tt });
      if let Some(escape_loc) = legacy_escape {
        direct.assoc.set(LegacyOctalEscapeSequence(escape_loc));
      }
      if tt == TT::LiteralNumber {
        let raw = self.str(loc);
        if crate::num::is_legacy_octal_literal(raw) {
          direct.assoc.set(LegacyOctalNumberLiteral);
        } else if crate::num::is_leading_zero_decimal_literal(raw) {
          direct.assoc.set(LeadingZeroDecimalLiteral);
        }
      }
      ClassOrObjKey::Direct(direct)
    })
  }

  /// Parse class member value after key and optional type annotation have been parsed
  /// Determines if this is a method, getter, setter, or property initializer
  fn class_member_value(
    &mut self,
    ctx: ParseCtx,
    key: &ClassOrObjKey,
    static_: bool,
    abstract_: bool,
  ) -> SyntaxResult<ClassOrObjVal> {
    // Check what follows the key/type annotation
    let t = self.peek();

    // Check if this is a constructor method
    let is_constructor = !static_
      && match key {
        ClassOrObjKey::Direct(k) => k.stx.key == "constructor",
        _ => false,
      };

    match t.typ {
      // Method with type parameters or parenthesis
      TT::ChevronLeft | TT::ParenthesisOpen => {
        // Parse as method
        let method = self.with_loc(|p| {
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
            let is_module = p.is_module();
            let fn_ctx = ctx.with_rules(ParsePatternRules {
              await_allowed: !is_module,
              yield_allowed: !is_module,
              await_expr_allowed: false,
              yield_expr_allowed: false,
            });
            let parameters = p.func_params(fn_ctx)?;
            // TypeScript: return type annotation
            let return_type = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
              Some(p.type_expr_or_predicate(ctx)?)
            } else {
              None
            };
            let simple_params = Parser::is_simple_parameter_list(&parameters);
            let contains_use_strict = p.peek().typ == TT::BraceOpen
              && p.is_strict_ecmascript()
              && p.has_use_strict_directive_in_block_body()?;
            if p.is_strict_ecmascript() && contains_use_strict && !simple_params {
              return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
                "`use strict` directive not allowed with a non-simple parameter list",
              )));
            }

            let prev_strict_mode = p.strict_mode;
            if p.is_strict_ecmascript() && contains_use_strict && !p.is_strict_mode() {
              p.strict_mode += 1;
            }
            // TypeScript: method overload signatures and abstract methods have no body
            // Also check if next token could start a new member (for overloads without semicolons)
            let next_could_be_new_member = Self::probable_class_member_start(p.peek().typ);
            // For constructors, if next token is not an opening brace, it's an overload signature
            let constructor_without_body = is_constructor && p.peek().typ != TT::BraceOpen;

            let res = (|| {
              p.validate_formal_parameters(None, &parameters, simple_params, true)?;
              let body = if p.peek().typ == TT::Semicolon
                || (abstract_ && p.peek().typ != TT::BraceOpen)
                || (next_could_be_new_member && p.peek().typ != TT::BraceOpen)
                || constructor_without_body
              {
                let _ = p.consume_if(TT::Semicolon);
                None
              } else {
                let is_derived_class = p.class_is_derived.last().copied().unwrap_or(false);
                Some(
                  p.parse_method_block_body(fn_ctx, is_constructor && is_derived_class)?
                    .into(),
                )
              };
              Ok(body)
            })();
            p.strict_mode = prev_strict_mode;
            let body = res?;
            Ok(Func {
              arrow: false,
              async_: false,
              generator: false,
              type_parameters,
              parameters,
              return_type,
              body,
            })
          })?;
          Ok(ClassOrObjMethod { func })
        })?;
        Ok(ClassOrObjVal::Method(method))
      }
      // Property with initializer
      TT::Equals => {
        self.require(TT::Equals)?;
        let prev_new_target_allowed = self.new_target_allowed;
        let prev_super_prop_allowed = self.super_prop_allowed;
        let prev_super_call_allowed = self.super_call_allowed;
        self.new_target_allowed += 1;
        self.super_prop_allowed += 1;
        self.super_call_allowed = 0;
        let initializer = self.expr_with_asi(ctx, [TT::Semicolon, TT::BraceClose], &mut Asi::can());
        self.new_target_allowed = prev_new_target_allowed;
        self.super_prop_allowed = prev_super_prop_allowed;
        self.super_call_allowed = prev_super_call_allowed;
        let initializer = initializer?;
        Ok(ClassOrObjVal::Prop(Some(initializer)))
      }
      // Property without initializer
      _ => Ok(ClassOrObjVal::Prop(None)),
    }
  }

  /// Parses a class or object method like `a() {}`, `async a() {}`, `*a() {}`, `async *a() {}`.
  pub fn class_or_obj_method(
    &mut self,
    ctx: ParseCtx,
    abstract_: bool,
  ) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjMethod>)> {
    let is_async = self.consume_if(TT::KeywordAsync).is_match();
    let is_generator = self.consume_if(TT::Asterisk).is_match();

    // For anonymous methods like *(), async(), check if paren comes immediately
    let key = if self.peek().typ == TT::ParenthesisOpen {
      // Anonymous method - use empty string as key
      self.create_synthetic_class_key()
    } else {
      self.class_or_obj_key(ctx)?
    };
    let func = self.with_loc(|p| {
      // TypeScript: generic type parameters
      let type_parameters = if !p.is_strict_ecmascript()
        && p.peek().typ == TT::ChevronLeft
        && p.is_start_of_type_arguments()
      {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };
      let is_module = p.is_module();
      let fn_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: if is_module { false } else { !is_async },
        yield_allowed: if is_module { false } else { !is_generator },
        await_expr_allowed: is_async,
        yield_expr_allowed: is_generator,
      });
      let parameters = p.func_params(fn_ctx)?;
      // TypeScript: return type annotation - may be type predicate
      let return_type = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr_or_predicate(ctx)?)
      } else {
        None
      };
      let simple_params = Parser::is_simple_parameter_list(&parameters);
      let contains_use_strict = p.peek().typ == TT::BraceOpen
        && p.is_strict_ecmascript()
        && p.has_use_strict_directive_in_block_body()?;
      if p.is_strict_ecmascript() && contains_use_strict && !simple_params {
        return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
          "`use strict` directive not allowed with a non-simple parameter list",
        )));
      }

      let prev_strict_mode = p.strict_mode;
      if p.is_strict_ecmascript() && contains_use_strict && !p.is_strict_mode() {
        p.strict_mode += 1;
      }
      // TypeScript: method overload signatures and abstract methods have no body
      // Method overloads are indicated by a semicolon instead of a body
      let res = (|| {
        p.validate_formal_parameters(None, &parameters, simple_params, true)?;
        let body = if p.peek().typ == TT::Semicolon
          || (abstract_ && p.peek().typ != TT::BraceOpen)
          || (Self::probable_class_member_start(p.peek().typ) && p.peek().typ != TT::BraceOpen)
        {
          let _ = p.consume_if(TT::Semicolon);
          None
        } else {
          Some(p.parse_method_block_body(fn_ctx, false)?.into())
        };
        Ok(body)
      })();
      p.strict_mode = prev_strict_mode;
      let body = res?;
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

  pub fn class_or_obj_getter(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjGetter>)> {
    self.class_or_obj_getter_impl(ctx, false)
  }

  pub fn class_or_obj_getter_impl(
    &mut self,
    ctx: ParseCtx,
    abstract_: bool,
  ) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjGetter>)> {
    self.require(TT::KeywordGet)?;
    let key = self.class_or_obj_key(ctx)?;
    let func = self.with_loc(|p| {
      // TypeScript: generic type parameters
      let type_parameters = if !p.is_strict_ecmascript()
        && p.peek().typ == TT::ChevronLeft
        && p.is_start_of_type_arguments()
      {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };
      // TypeScript-style recovery: allow getters without parentheses.
      if p.peek().typ != TT::ParenthesisOpen {
        if p.should_recover() {
          return Ok(Func {
            arrow: false,
            async_: false,
            generator: false,
            type_parameters,
            parameters: Vec::new(),
            return_type: None,
            body: None,
          });
        }
        return Err(
          p.peek()
            .error(SyntaxErrorType::RequiredTokenNotFound(TT::ParenthesisOpen)),
        );
      }
      p.require(TT::ParenthesisOpen)?;

      // TypeScript: Check for optional `this` parameter in getter
      // Syntax: get x(this: Type): ReturnType
      let mut parameters = Vec::new();
      if !p.is_strict_ecmascript() && p.peek().typ == TT::KeywordThis {
        let [_, next] = p.peek_n::<2>();
        if next.typ == TT::Colon {
          // Parse this parameter: this: Type
          use crate::ast::expr::pat::IdPat;
          use crate::ast::expr::pat::Pat;
          use crate::ast::stmt::decl::ParamDecl;
          use crate::ast::stmt::decl::PatDecl;
          use crate::loc::Loc;
          p.consume(); // consume 'this'
          p.require(TT::Colon)?;
          let type_annotation = Some(p.type_expr(ctx)?);
          let this_pattern = Node::new(
            Loc(0, 0),
            PatDecl {
              pat: Node::new(
                Loc(0, 0),
                Pat::Id(Node::new(
                  Loc(0, 0),
                  IdPat {
                    name: String::from("this"),
                  },
                )),
              ),
            },
          );
          parameters.push(Node::new(
            Loc(0, 0),
            ParamDecl {
              decorators: Vec::new(),
              rest: false,
              optional: false,
              accessibility: None,
              readonly: false,
              pattern: this_pattern,
              type_annotation,
              default_value: None,
            },
          ));
        }
      }

      // ES2017+: Allow trailing comma in empty parameter list
      let _ = p.consume_if(TT::Comma);
      p.require(TT::ParenthesisClose)?;
      // TypeScript: return type annotation - may be type predicate
      let return_type = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr_or_predicate(ctx)?)
      } else {
        None
      };
      let simple_params = Parser::is_simple_parameter_list(&parameters);
      let contains_use_strict = p.peek().typ == TT::BraceOpen
        && p.is_strict_ecmascript()
        && p.has_use_strict_directive_in_block_body()?;
      if p.is_strict_ecmascript() && contains_use_strict && !simple_params {
        return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
          "`use strict` directive not allowed with a non-simple parameter list",
        )));
      }

      let prev_strict_mode = p.strict_mode;
      if p.is_strict_ecmascript() && contains_use_strict && !p.is_strict_mode() {
        p.strict_mode += 1;
      }
      // Getters are not generators or async, so yield/await can be used as identifiers
      // TypeScript: getter overload signatures and abstract getters have no body
      let res = (|| {
        p.validate_formal_parameters(None, &parameters, simple_params, true)?;
        let body = if p.peek().typ == TT::Semicolon || (abstract_ && p.peek().typ != TT::BraceOpen)
        {
          let _ = p.consume_if(TT::Semicolon);
          None
        } else {
          let is_module = p.is_module();
          Some(
            p.parse_method_block_body(
              ctx.with_rules(ParsePatternRules {
                await_allowed: !is_module,
                yield_allowed: !is_module,
                await_expr_allowed: false,
                yield_expr_allowed: false,
              }),
              false,
            )?
            .into(),
          )
        };
        Ok(body)
      })();
      p.strict_mode = prev_strict_mode;
      let body = res?;
      Ok(Func {
        arrow: false,
        async_: false,
        generator: false,
        type_parameters,
        parameters,
        return_type,
        body,
      })
    })?;
    let val = func.wrap(|func| ClassOrObjGetter { func });
    Ok((key, val))
  }

  pub fn class_or_obj_setter(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjSetter>)> {
    self.class_or_obj_setter_impl(ctx, false)
  }

  pub fn class_or_obj_setter_impl(
    &mut self,
    ctx: ParseCtx,
    abstract_: bool,
  ) -> SyntaxResult<(ClassOrObjKey, Node<ClassOrObjSetter>)> {
    self.require(TT::KeywordSet)?;
    let key = self.class_or_obj_key(ctx)?;
    let func = self.with_loc(|p| {
      // TypeScript: generic type parameters
      let type_parameters = if !p.is_strict_ecmascript()
        && p.peek().typ == TT::ChevronLeft
        && p.is_start_of_type_arguments()
      {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };
      // TypeScript-style recovery: allow setters without parentheses.
      if p.peek().typ != TT::ParenthesisOpen {
        if p.should_recover() {
          // Missing parentheses - create synthetic parameter for error recovery
          let loc = p.peek().loc;
          let synthetic_pattern = Node::new(
            loc,
            PatDecl {
              pat: Node::new(
                loc,
                IdPat {
                  name: String::from("_"),
                },
              )
              .into_wrapped(),
            },
          );
          let param_loc = synthetic_pattern.loc;
          return Ok(Func {
            arrow: false,
            async_: false,
            generator: false,
            type_parameters,
            parameters: vec![Node::new(
              param_loc,
              ParamDecl {
                decorators: Vec::new(),
                rest: false,
                optional: false,
                accessibility: None,
                readonly: false,
                pattern: synthetic_pattern,
                type_annotation: None,
                default_value: None,
              },
            )],
            return_type: None,
            body: None,
          });
        }
        return Err(
          p.peek()
            .error(SyntaxErrorType::RequiredTokenNotFound(TT::ParenthesisOpen)),
        );
      }
      p.require(TT::ParenthesisOpen)?;
      // Setters are not generators or async, so yield/await can be used as identifiers
      let is_module = p.is_module();
      let setter_ctx = ctx.with_rules(ParsePatternRules {
        await_allowed: !is_module,
        yield_allowed: !is_module,
        await_expr_allowed: false,
        yield_expr_allowed: false,
      });

      // TypeScript: Check for optional `this` parameter in setter
      // Syntax: set x(this: Type, value: ValueType)
      let mut parameters = Vec::new();
      if !p.is_strict_ecmascript() && p.peek().typ == TT::KeywordThis {
        let [_, next] = p.peek_n::<2>();
        if next.typ == TT::Colon {
          // Parse this parameter: this: Type
          use crate::ast::expr::pat::IdPat;
          use crate::ast::expr::pat::Pat;
          use crate::ast::stmt::decl::ParamDecl;
          use crate::ast::stmt::decl::PatDecl;
          use crate::loc::Loc;
          p.consume(); // consume 'this'
          p.require(TT::Colon)?;
          let type_annotation = Some(p.type_expr(ctx)?);
          let this_pattern = Node::new(
            Loc(0, 0),
            PatDecl {
              pat: Node::new(
                Loc(0, 0),
                Pat::Id(Node::new(
                  Loc(0, 0),
                  IdPat {
                    name: String::from("this"),
                  },
                )),
              ),
            },
          );
          parameters.push(Node::new(
            Loc(0, 0),
            ParamDecl {
              decorators: Vec::new(),
              rest: false,
              optional: false,
              accessibility: None,
              readonly: false,
              pattern: this_pattern,
              type_annotation,
              default_value: None,
            },
          ));
          // Consume comma after this parameter
          if p.consume_if(TT::Comma).is_match() {
            // Continue to parse value parameter
          }
        }
      }

      // TypeScript: Parse value parameter (or error recovery - allow setters with no parameter)
      let (pattern, type_annotation, default_value) = if p.peek().typ == TT::ParenthesisClose {
        if !p.should_recover() {
          return Err(
            p.peek()
              .error(SyntaxErrorType::ExpectedSyntax("setter parameter")),
          );
        }
        // Empty parameter list - create synthetic parameter for error recovery
        let loc = p.peek().loc;
        let synthetic_pattern = Node::new(
          loc,
          PatDecl {
            pat: Node::new(
              loc,
              IdPat {
                name: String::from("_"),
              },
            )
            .into_wrapped(),
          },
        );
        (synthetic_pattern, None, None)
      } else {
        let pattern = p.pat_decl(setter_ctx)?;
        // TypeScript: type annotation for setter parameter
        let type_annotation = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
          Some(p.type_expr(ctx)?)
        } else {
          None
        };
        let default_value = p
          .consume_if(TT::Equals)
          .and_then(|| p.expr(setter_ctx, [TT::ParenthesisClose]))?;
        (pattern, type_annotation, default_value)
      };
      let param_loc = pattern.loc;

      // Add the value parameter to the parameters list
      parameters.push(Node::new(
        param_loc,
        ParamDecl {
          decorators: Vec::new(),
          rest: false,
          optional: false,
          accessibility: None,
          readonly: false,
          pattern,
          type_annotation,
          default_value,
        },
      ));

      // ES2017+: Allow trailing comma in setter parameter list
      let _ = p.consume_if(TT::Comma);
      p.require(TT::ParenthesisClose)?;
      let simple_params = Parser::is_simple_parameter_list(&parameters);
      let contains_use_strict = p.peek().typ == TT::BraceOpen
        && p.is_strict_ecmascript()
        && p.has_use_strict_directive_in_block_body()?;
      if p.is_strict_ecmascript() && contains_use_strict && !simple_params {
        return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
          "`use strict` directive not allowed with a non-simple parameter list",
        )));
      }

      let prev_strict_mode = p.strict_mode;
      if p.is_strict_ecmascript() && contains_use_strict && !p.is_strict_mode() {
        p.strict_mode += 1;
      }
      // Setters don't have return types
      // TypeScript: setter overload signatures and abstract setters have no body
      let res = (|| {
        p.validate_formal_parameters(None, &parameters, simple_params, true)?;
        let body = if p.peek().typ == TT::Semicolon || (abstract_ && p.peek().typ != TT::BraceOpen)
        {
          let _ = p.consume_if(TT::Semicolon);
          None
        } else {
          Some(p.parse_method_block_body(setter_ctx, false)?.into())
        };
        Ok(body)
      })();
      p.strict_mode = prev_strict_mode;
      let body = res?;
      Ok(Func {
        arrow: false,
        async_: false,
        generator: false,
        type_parameters,
        parameters,
        return_type: None,
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
        if value_delimiter == TT::Equals {
          let prev_new_target_allowed = self.new_target_allowed;
          let prev_super_prop_allowed = self.super_prop_allowed;
          let prev_super_call_allowed = self.super_call_allowed;
          self.new_target_allowed += 1;
          self.super_prop_allowed += 1;
          self.super_call_allowed = 0;
          let expr = self.expr_with_asi(
            ctx,
            [statement_delimiter, TT::BraceClose],
            property_initialiser_asi,
          );
          self.new_target_allowed = prev_new_target_allowed;
          self.super_prop_allowed = prev_super_prop_allowed;
          self.super_call_allowed = prev_super_call_allowed;
          Ok(expr?)
        } else {
          Ok(self.expr_with_asi(
            ctx,
            [statement_delimiter, TT::BraceClose],
            property_initialiser_asi,
          )?)
        }
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

    // TypeScript-style recovery: index signatures in object literals (or with
    // misplaced accessibility modifiers).
    if self.should_recover() {
      let is_index_sig =
        (a.typ == TT::BracketOpen && b.typ == TT::Identifier && c.typ == TT::Colon)
          || (matches!(
            a.typ,
            TT::KeywordPublic | TT::KeywordPrivate | TT::KeywordProtected
          ) && b.typ == TT::BracketOpen
            && c.typ == TT::Identifier
            && d.typ == TT::Colon);
      if is_index_sig {
        // Consume optional accessibility modifier for error recovery
        if matches!(
          a.typ,
          TT::KeywordPublic | TT::KeywordPrivate | TT::KeywordProtected
        ) {
          self.consume();
        }
        let index_sig = self.parse_index_signature(ctx)?;
        let dummy_key = self.create_synthetic_class_key();
        return Ok((dummy_key, ClassOrObjVal::IndexSignature(index_sig)));
      }
    }

    // TypeScript-style recovery: Handle generator method without a name: `*{ }`.
    if self.should_recover() && a.typ == TT::Asterisk && b.typ == TT::BraceOpen {
      self.consume(); // consume *
                      // Create synthetic empty key
      let key = self.create_synthetic_class_key();
      // Consume the method body
      let method = self.with_loc(|p| {
        let func = p.with_loc(|p| {
          let parameters = Vec::new();
          let body = Some(p.parse_non_arrow_func_block_body(ctx)?.into());
          Ok(Func {
            arrow: false,
            async_: false,
            generator: true,
            type_parameters: None,
            parameters,
            return_type: None,
            body,
          })
        })?;
        Ok(ClassOrObjMethod { func })
      })?;
      return Ok((key, ClassOrObjVal::Method(method)));
    }

    // Special case for computed keys: parse key first, then check what follows
    // Handle: [...], *[...], get [...], set [...]
    if a.typ == TT::BracketOpen
      || (a.typ == TT::Asterisk && b.typ == TT::BracketOpen)
      || (a.typ == TT::KeywordGet && b.typ == TT::BracketOpen)
      || (a.typ == TT::KeywordSet && b.typ == TT::BracketOpen)
    {
      // Check if this is a getter or setter with computed key
      let is_getter = a.typ == TT::KeywordGet;
      let is_setter = a.typ == TT::KeywordSet;
      if is_getter || is_setter {
        // Don't consume get/set here - the getter/setter functions will do it
        if is_getter {
          let (key, val) = self.class_or_obj_getter_impl(ctx, abstract_)?;
          return Ok((key, val.into()));
        } else {
          let (key, val) = self.class_or_obj_setter_impl(ctx, abstract_)?;
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
            let type_parameters = if !p.is_strict_ecmascript()
              && p.peek().typ == TT::ChevronLeft
              && p.is_start_of_type_arguments()
            {
              Some(p.type_parameters(ctx)?)
            } else {
              None
            };
            let is_module = p.is_module();
            let fn_ctx = ctx.with_rules(ParsePatternRules {
              await_allowed: if is_module { false } else { !is_async },
              yield_allowed: if is_module { false } else { !is_generator },
              await_expr_allowed: is_async,
              yield_expr_allowed: is_generator,
            });
            let parameters = p.func_params(fn_ctx)?;
            // TypeScript: return type annotation
            let return_type = if !p.is_strict_ecmascript() && p.consume_if(TT::Colon).is_match() {
              Some(p.type_expr_or_predicate(ctx)?)
            } else {
              None
            };
            let simple_params = Parser::is_simple_parameter_list(&parameters);
            let contains_use_strict = p.peek().typ == TT::BraceOpen
              && p.is_strict_ecmascript()
              && p.has_use_strict_directive_in_block_body()?;
            if p.is_strict_ecmascript() && contains_use_strict && !simple_params {
              return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
                "`use strict` directive not allowed with a non-simple parameter list",
              )));
            }

            let prev_strict_mode = p.strict_mode;
            if p.is_strict_ecmascript() && contains_use_strict && !p.is_strict_mode() {
              p.strict_mode += 1;
            }
            // TypeScript: method overload signatures and abstract methods have no body
            // Method overloads are indicated by a semicolon instead of a body
            let res = (|| {
              p.validate_formal_parameters(None, &parameters, simple_params, true)?;
              let body =
                if p.peek().typ == TT::Semicolon || (abstract_ && p.peek().typ != TT::BraceOpen) {
                  let _ = p.consume_if(TT::Semicolon);
                  None
                } else {
                  Some(p.parse_method_block_body(fn_ctx, false)?.into())
                };
              Ok(body)
            })();
            p.strict_mode = prev_strict_mode;
            let body = res?;
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
          if value_delimiter == TT::Equals {
            let prev_new_target_allowed = self.new_target_allowed;
            let prev_super_prop_allowed = self.super_prop_allowed;
            let prev_super_call_allowed = self.super_call_allowed;
            self.new_target_allowed += 1;
            self.super_prop_allowed += 1;
            self.super_call_allowed = 0;
            let expr = self.expr_with_asi(
              ctx,
              [statement_delimiter, TT::BraceClose],
              property_initialiser_asi,
            );
            self.new_target_allowed = prev_new_target_allowed;
            self.super_prop_allowed = prev_super_prop_allowed;
            self.super_call_allowed = prev_super_call_allowed;
            Some(expr?)
          } else {
            Some(self.expr_with_asi(
              ctx,
              [statement_delimiter, TT::BraceClose],
              property_initialiser_asi,
            )?)
          }
        } else {
          None
        };
        (key, ClassOrObjVal::Prop(initializer))
      });
    }
    // Check if this looks like a method with type parameters: foo<T>(...)
    // We need to consume the identifier and check if next is <type-args>(
    let checkpoint = self.checkpoint();
    let has_type_params = if a.typ == TT::Identifier && b.typ == TT::ChevronLeft {
      self.consume(); // consume identifier
      let result = self.is_start_of_type_arguments();
      self.restore_checkpoint(checkpoint);
      result
    } else {
      false
    };

    Ok(match (a.typ, b.typ, c.typ, d.typ) {
      // Method. Includes using "get" or "set" as the method's name.
      (TT::KeywordAsync, TT::Asterisk, _, TT::ParenthesisOpen)
      | (TT::KeywordAsync, TT::BracketOpen, _, _)  // Async method with computed property: async [key]()
      | (TT::KeywordAsync, _, TT::ParenthesisOpen, _)
      | (TT::Asterisk, TT::ParenthesisOpen, _, _)  // Anonymous generator method: *()
      | (TT::Asterisk, _, TT::ParenthesisOpen, _)
      | (TT::Asterisk, TT::BracketOpen, _, _)  // Generator with computed property: *[key]()
      | (_, TT::ParenthesisOpen, _, _)
      => {
        let (k, v) = self.class_or_obj_method(ctx, abstract_)?;
        (k, v.into())
      }
      // Method with type parameters: foo<T>(...)
      _ if has_type_params => {
        let (k, v) = self.class_or_obj_method(ctx, abstract_)?;
        (k, v.into())
      }
      // Getter (may have invalid type parameters like get foo<T>())
      // Error recovery: also handle getters without parentheses like "get e"
      (TT::KeywordGet, _, TT::ParenthesisOpen, _) | (TT::KeywordGet, _, TT::ChevronLeft, _) => {
        let (k, v) = self.class_or_obj_getter_impl(ctx, abstract_)?;
        (k, v.into())
      }
      // Error recovery: getter without parentheses - detect "get <identifier/keyword/string/number>"
      (TT::KeywordGet, TT::Identifier, _, _)
      | (TT::KeywordGet, TT::LiteralString, _, _)
      | (TT::KeywordGet, TT::LiteralNumber, _, _)
      | (TT::KeywordGet, TT::LiteralBigInt, _, _)
      | (TT::KeywordGet, TT::PrivateMember, _, _)
        if c.typ != TT::ParenthesisOpen && c.typ != TT::ChevronLeft
      => {
        let (k, v) = self.class_or_obj_getter_impl(ctx, abstract_)?;
        (k, v.into())
      }
      // Error recovery: getter with keyword as name but no parentheses
      (TT::KeywordGet, _, _, _) if KEYWORDS_MAPPING.contains_key(&b.typ) && c.typ != TT::ParenthesisOpen && c.typ != TT::ChevronLeft => {
        let (k, v) = self.class_or_obj_getter_impl(ctx, abstract_)?;
        (k, v.into())
      }
      // Setter (may have invalid type parameters like set foo<T>(x))
      // Error recovery: also handle setters without parentheses like "set f"
      (TT::KeywordSet, _, TT::ParenthesisOpen, _) | (TT::KeywordSet, _, TT::ChevronLeft, _) => {
        let (k, v) = self.class_or_obj_setter_impl(ctx, abstract_)?;
        (k, v.into())
      }
      // Error recovery: setter without parentheses - detect "set <identifier/keyword/string/number>"
      (TT::KeywordSet, TT::Identifier, _, _)
      | (TT::KeywordSet, TT::LiteralString, _, _)
      | (TT::KeywordSet, TT::LiteralNumber, _, _)
      | (TT::KeywordSet, TT::LiteralBigInt, _, _)
      | (TT::KeywordSet, TT::PrivateMember, _, _)
        if c.typ != TT::ParenthesisOpen && c.typ != TT::ChevronLeft
      => {
        let (k, v) = self.class_or_obj_setter_impl(ctx, abstract_)?;
        (k, v.into())
      }
      // Error recovery: setter with keyword as name but no parentheses
      (TT::KeywordSet, _, _, _) if KEYWORDS_MAPPING.contains_key(&b.typ) && c.typ != TT::ParenthesisOpen && c.typ != TT::ChevronLeft => {
        let (k, v) = self.class_or_obj_setter_impl(ctx, abstract_)?;
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
