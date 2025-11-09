use super::{ParseCtx, Parser};
use crate::ast::expr::Expr;
use crate::ast::node::Node;
use crate::ast::type_expr::*;
use crate::error::{SyntaxErrorType, SyntaxResult};
use crate::token::TT;

impl<'a> Parser<'a> {
  /// Main entry point for parsing type expressions
  pub fn type_expr(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.type_union_or_intersection(ctx)
  }

  /// Parse union or intersection types (lowest precedence)
  /// T | U | V  or  T & U & V
  /// Note: Cannot mix | and & at same level without parentheses
  fn type_union_or_intersection(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let first = self.type_conditional(ctx)?;

    let t = self.peek().typ;
    if t != TT::Bar && t != TT::Ampersand {
      return Ok(first);
    }

    let is_union = t == TT::Bar;
    let mut types = vec![first];

    while self.consume_if(t).is_match() {
      types.push(self.type_conditional(ctx)?);
    }

    if types.len() == 1 {
      return Ok(types.into_iter().next().unwrap());
    }

    let start_loc = types[0].loc;
    if is_union {
      let union = Node::new(start_loc, TypeUnion { types });
      self.with_loc(|_| Ok(TypeExpr::UnionType(union)))
    } else {
      let intersection = Node::new(start_loc, TypeIntersection { types });
      self.with_loc(|_| Ok(TypeExpr::IntersectionType(intersection)))
    }
  }

  /// Parse conditional types: T extends U ? X : Y
  fn type_conditional(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    let check_type = self.type_array_or_postfix(ctx)?;

    if !self.consume_if(TT::KeywordExtends).is_match() {
      return Ok(check_type);
    }

    let extends_type = self.type_array_or_postfix(ctx)?;
    self.require(TT::Question)?;
    let true_type = self.type_expr(ctx)?;
    self.require(TT::Colon)?;
    let false_type = self.type_expr(ctx)?;

    let conditional = Node::new(
      start_loc,
      TypeConditional {
        check_type: Box::new(check_type),
        extends_type: Box::new(extends_type),
        true_type: Box::new(true_type),
        false_type: Box::new(false_type),
      },
    );
    self.with_loc(|_| Ok(TypeExpr::ConditionalType(conditional)))
  }

  /// Parse array types and indexed access types
  /// T[]  or  T[K]
  fn type_array_or_postfix(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let mut base = self.type_primary(ctx)?;

    loop {
      match self.peek().typ {
        TT::BracketOpen => {
          let start_loc = base.loc;
          self.consume();
          if self.consume_if(TT::BracketClose).is_match() {
            // Array type: T[]
            let array = Node::new(
              start_loc,
              TypeArray {
                element_type: Box::new(base),
              },
            );
            base = self.with_loc(|_| Ok(TypeExpr::ArrayType(array)))?;
          } else {
            // Indexed access: T[K]
            let index = self.type_expr(ctx)?;
            self.require(TT::BracketClose)?;
            let indexed = Node::new(
              start_loc,
              TypeIndexedAccess {
                object_type: Box::new(base),
                index_type: Box::new(index),
              },
            );
            base = self.with_loc(|_| Ok(TypeExpr::IndexedAccessType(indexed)))?;
          }
        }
        _ => break,
      }
    }

    Ok(base)
  }

  /// Parse primary type expressions
  fn type_primary(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let t = self.peek();

    match t.typ {
      // Primitive types
      TT::KeywordAny => {
        let loc = self.peek().loc;
        self.consume();
        let any = Node::new(loc, TypeAny {});
        self.with_loc(|_| Ok(TypeExpr::Any(any)))
      }
      TT::KeywordUnknown => {
        let loc = self.peek().loc;
        self.consume();
        let unknown = Node::new(loc, TypeUnknown {});
        self.with_loc(|_| Ok(TypeExpr::Unknown(unknown)))
      }
      TT::KeywordNever => {
        let loc = self.peek().loc;
        self.consume();
        let never = Node::new(loc, TypeNever {});
        self.with_loc(|_| Ok(TypeExpr::Never(never)))
      }
      TT::KeywordVoid => {
        let loc = self.peek().loc;
        self.consume();
        let void = Node::new(loc, TypeVoid {});
        self.with_loc(|_| Ok(TypeExpr::Void(void)))
      }
      TT::KeywordStringType => {
        let loc = self.peek().loc;
        self.consume();
        let string = Node::new(loc, TypeString {});
        self.with_loc(|_| Ok(TypeExpr::String(string)))
      }
      TT::KeywordNumberType => {
        let loc = self.peek().loc;
        self.consume();
        let number = Node::new(loc, TypeNumber {});
        self.with_loc(|_| Ok(TypeExpr::Number(number)))
      }
      TT::KeywordBooleanType => {
        let loc = self.peek().loc;
        self.consume();
        let boolean = Node::new(loc, TypeBoolean {});
        self.with_loc(|_| Ok(TypeExpr::Boolean(boolean)))
      }
      TT::KeywordBigIntType => {
        let loc = self.peek().loc;
        self.consume();
        let bigint = Node::new(loc, TypeBigInt {});
        self.with_loc(|_| Ok(TypeExpr::BigInt(bigint)))
      }
      TT::KeywordSymbolType => {
        let loc = self.peek().loc;
        self.consume();
        let symbol = Node::new(loc, TypeSymbol {});
        self.with_loc(|_| Ok(TypeExpr::Symbol(symbol)))
      }
      TT::KeywordObjectType => {
        let loc = self.peek().loc;
        self.consume();
        let object = Node::new(loc, TypeObject {});
        self.with_loc(|_| Ok(TypeExpr::Object(object)))
      }
      TT::KeywordUndefinedType => {
        let loc = self.peek().loc;
        self.consume();
        let undefined = Node::new(loc, TypeUndefined {});
        self.with_loc(|_| Ok(TypeExpr::Undefined(undefined)))
      }
      TT::LiteralNull => {
        let loc = self.peek().loc;
        self.consume();
        let null = Node::new(loc, TypeNull {});
        self.with_loc(|_| Ok(TypeExpr::Null(null)))
      }

      // Type reference or qualified name
      TT::Identifier => self.type_reference(ctx),

      // this type
      TT::KeywordThis => {
        let loc = self.peek().loc;
        self.consume();
        let this = Node::new(loc, TypeThis {});
        self.with_loc(|_| Ok(TypeExpr::ThisType(this)))
      }

      // typeof type query
      TT::KeywordTypeof => self.type_query(ctx),

      // keyof type
      TT::KeywordKeyof => self.keyof_type(ctx),

      // infer type
      TT::KeywordInfer => self.infer_type(ctx),

      // Object type literal: { x: T; y: U }
      TT::BraceOpen => self.object_type(ctx),

      // Tuple type: [T, U, ...V[]]
      TT::BracketOpen => self.tuple_type(ctx),

      // Parenthesized type or function type: (x: T) => U
      TT::ParenthesisOpen => self.paren_or_function_type(ctx),

      // new () => T  (constructor type)
      TT::KeywordNew => self.constructor_type(ctx),

      // Literal types
      TT::LiteralString => {
        let loc = self.peek().loc;
        let val = self.lit_str_val()?;
        let lit = Node::new(loc, TypeLiteral::String(val));
        self.with_loc(|_| Ok(TypeExpr::LiteralType(lit)))
      }
      TT::LiteralNumber => {
        let loc = self.peek().loc;
        let val = self.lit_num_val()?.to_string();
        let lit = Node::new(loc, TypeLiteral::Number(val));
        self.with_loc(|_| Ok(TypeExpr::LiteralType(lit)))
      }
      TT::LiteralBigInt => {
        let loc = self.peek().loc;
        let val = self.lit_bigint_val()?.to_string();
        let lit = Node::new(loc, TypeLiteral::BigInt(val));
        self.with_loc(|_| Ok(TypeExpr::LiteralType(lit)))
      }
      TT::LiteralTrue => {
        let loc = self.peek().loc;
        self.consume();
        let lit = Node::new(loc, TypeLiteral::Boolean(true));
        self.with_loc(|_| Ok(TypeExpr::LiteralType(lit)))
      }
      TT::LiteralFalse => {
        let loc = self.peek().loc;
        self.consume();
        let lit = Node::new(loc, TypeLiteral::Boolean(false));
        self.with_loc(|_| Ok(TypeExpr::LiteralType(lit)))
      }

      // import("module").Type
      TT::KeywordImport => self.import_type(ctx),

      // Template literal type
      TT::LiteralTemplatePartString => self.template_literal_type(ctx),

      _ => Err(t.error(SyntaxErrorType::ExpectedSyntax("type expression"))),
    }
  }

  /// Parse type reference with optional generic arguments
  /// Foo, Foo.Bar, Foo.Bar.Baz, Foo<T, U>
  fn type_reference(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    let name = self.parse_type_entity_name()?;
    let type_arguments = if self.is_start_of_type_arguments() {
      Some(self.type_arguments(ctx)?)
    } else {
      None
    };

    let reference = Node::new(
      start_loc,
      TypeReference {
        name,
        type_arguments,
      },
    );
    self.with_loc(|_| Ok(TypeExpr::TypeReference(reference)))
  }

  /// Parse entity name (can be qualified: A.B.C)
  fn parse_type_entity_name(&mut self) -> SyntaxResult<TypeEntityName> {
    let first = self.require_identifier()?;
    let mut name = TypeEntityName::Identifier(first);

    while self.consume_if(TT::Dot).is_match() {
      let right = self.require_identifier()?;
      name = TypeEntityName::Qualified(Box::new(TypeQualifiedName {
        left: name,
        right,
      }));
    }

    Ok(name)
  }

  /// Check if we're at the start of type arguments <...>
  /// This is tricky - need to disambiguate from < operator
  pub fn is_start_of_type_arguments(&mut self) -> bool {
    if self.peek().typ != TT::ChevronLeft {
      return false;
    }

    // Save position for backtracking
    let checkpoint = self.checkpoint();
    self.consume(); // <

    // Look for patterns that indicate type arguments:
    // <T>, <T,>, <T extends>, <T = Default>, etc.
    let next = self.peek();
    let looks_like_type = match next.typ {
      // Type keywords
      TT::KeywordAny
      | TT::KeywordUnknown
      | TT::KeywordNever
      | TT::KeywordVoid
      | TT::KeywordStringType
      | TT::KeywordNumberType
      | TT::KeywordBooleanType
      | TT::KeywordBigIntType
      | TT::KeywordSymbolType
      | TT::KeywordObjectType => true,

      // Opening brackets/braces for complex types
      TT::BracketOpen | TT::BraceOpen | TT::ParenthesisOpen => true,

      // Type operators
      TT::KeywordTypeof | TT::KeywordKeyof | TT::KeywordInfer => true,

      // Identifier followed by type-like punctuation
      TT::Identifier => {
        self.consume();
        matches!(
          self.peek().typ,
          TT::ChevronRight
            | TT::Comma
            | TT::KeywordExtends
            | TT::Equals
            | TT::Bar
            | TT::Ampersand
            | TT::Dot
            | TT::BracketOpen
        )
      }

      // Closing > immediately (empty type args or single T)
      TT::ChevronRight => true,

      _ => false,
    };

    self.restore_checkpoint(checkpoint);
    looks_like_type
  }

  /// Parse type arguments: <T, U, V>
  fn type_arguments(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<TypeExpr>>> {
    self.require(TT::ChevronLeft)?;
    let mut args = Vec::new();
    while !self.consume_if(TT::ChevronRight).is_match() {
      args.push(self.type_expr(ctx)?);
      if !self.consume_if(TT::Comma).is_match() {
        self.require(TT::ChevronRight)?;
        break;
      }
    }
    Ok(args)
  }

  /// Parse typeof type query: typeof foo, typeof foo.bar.baz
  fn type_query(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordTypeof)?;
    let expr_name = self.parse_type_entity_name()?;
    let query = Node::new(start_loc, TypeQuery { expr_name });
    self.with_loc(|_| Ok(TypeExpr::TypeQuery(query)))
  }

  /// Parse keyof type: keyof T
  fn keyof_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordKeyof)?;
    let type_expr = self.type_primary(ctx)?;
    let keyof = Node::new(
      start_loc,
      TypeKeyOf {
        type_expr: Box::new(type_expr),
      },
    );
    self.with_loc(|_| Ok(TypeExpr::KeyOfType(keyof)))
  }

  /// Parse infer type: infer R
  fn infer_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordInfer)?;
    let type_parameter = self.require_identifier()?;
    let infer = Node::new(start_loc, TypeInfer { type_parameter });
    self.with_loc(|_| Ok(TypeExpr::InferType(infer)))
  }

  /// Parse import type: import("module").Type<T>
  fn import_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordImport)?;
    self.require(TT::ParenthesisOpen)?;
    let module_specifier = self.lit_str_val()?;
    self.require(TT::ParenthesisClose)?;

    let (qualifier, type_arguments) = if self.consume_if(TT::Dot).is_match() {
      let qualifier = Some(self.parse_type_entity_name()?);
      let type_arguments = if self.is_start_of_type_arguments() {
        Some(self.type_arguments(ctx)?)
      } else {
        None
      };
      (qualifier, type_arguments)
    } else {
      (None, None)
    };

    let import = Node::new(
      start_loc,
      TypeImport {
        module_specifier,
        qualifier,
        type_arguments,
      },
    );
    self.with_loc(|_| Ok(TypeExpr::ImportType(import)))
  }

  /// Parse object type literal: { x: T; y?: U; readonly z: V }
  fn object_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::BraceOpen)?;
    let members = self.type_members(ctx)?;
    self.require(TT::BraceClose)?;
    let object = Node::new(start_loc, TypeObjectLiteral { members });
    self.with_loc(|_| Ok(TypeExpr::ObjectType(object)))
  }

  /// Parse type members (for object types and interfaces)
  pub fn type_members(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<TypeMember>>> {
    let mut members = Vec::new();

    while self.peek().typ != TT::BraceClose && self.peek().typ != TT::EOF {
      members.push(self.type_member(ctx)?);

      // Optional semicolon or comma separator
      if !self.consume_if(TT::Semicolon).is_match() {
        self.consume_if(TT::Comma);
      }
    }

    Ok(members)
  }

  /// Parse a single type member
  fn type_member(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeMember>> {
    let checkpoint = self.checkpoint();
    let readonly = self.consume_if(TT::KeywordReadonly).is_match();

    // Check for index signature: [key: string]: T
    if self.peek().typ == TT::BracketOpen {
      return self.index_signature(ctx, readonly);
    }

    // Check for call signature or constructor signature
    if self.peek().typ == TT::ParenthesisOpen || self.peek().typ == TT::ChevronLeft {
      // Try parsing as call signature
      if let Ok(sig) = self.call_signature(ctx) {
        return Ok(sig.wrap(TypeMember::CallSignature));
      }
      self.restore_checkpoint(checkpoint);
    }

    // Check for constructor signature
    if self.consume_if(TT::KeywordNew).is_match() {
      return self.construct_signature(ctx);
    }

    // Check for get/set accessors
    let is_get = self.consume_if(TT::KeywordGet).is_match();
    let is_set = !is_get && self.consume_if(TT::KeywordSet).is_match();

    // Parse property key
    let key = self.type_property_key(ctx)?;
    let optional = self.consume_if(TT::Question).is_match();

    if is_get {
      return self.get_accessor_signature(ctx, key);
    } else if is_set {
      return self.set_accessor_signature(ctx, key);
    }

    // Check if it's a method signature (has parentheses)
    if self.peek().typ == TT::ParenthesisOpen || self.peek().typ == TT::ChevronLeft {
      return self.method_signature(ctx, key, optional);
    }

    // It's a property signature
    self.property_signature(ctx, key, readonly, optional)
  }

  /// Parse type property key
  fn type_property_key(&mut self, ctx: ParseCtx) -> SyntaxResult<TypePropertyKey> {
    let t = self.peek();
    match t.typ {
      TT::Identifier => Ok(TypePropertyKey::Identifier(self.consume_as_string())),
      TT::LiteralString => Ok(TypePropertyKey::String(self.lit_str_val()?)),
      TT::LiteralNumber => Ok(TypePropertyKey::Number(self.lit_num_val()?.to_string())),
      TT::BracketOpen => {
        self.consume();
        let expr = self.expr(ctx, [TT::BracketClose])?;
        self.require(TT::BracketClose)?;
        Ok(TypePropertyKey::Computed(Box::new(expr)))
      }
      _ => {
        // Allow keywords as property names
        if crate::lex::KEYWORDS_MAPPING.contains_key(&t.typ) {
          Ok(TypePropertyKey::Identifier(self.consume_as_string()))
        } else {
          Err(t.error(SyntaxErrorType::ExpectedSyntax("property name")))
        }
      }
    }
  }

  /// Parse property signature
  fn property_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
    readonly: bool,
    optional: bool,
  ) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    let type_annotation = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr(ctx)?)
    } else {
      None
    };

    let prop = Node::new(
      start_loc,
      TypePropertySignature {
        readonly,
        optional,
        key,
        type_annotation,
      },
    );
    self.with_loc(|_| Ok(TypeMember::Property(prop)))
  }

  /// Parse method signature
  fn method_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
    optional: bool,
  ) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    let type_parameters = if self.peek().typ == TT::ChevronLeft && self.is_start_of_type_arguments()
    {
      Some(self.type_parameters(ctx)?)
    } else {
      None
    };

    self.require(TT::ParenthesisOpen)?;
    let parameters = self.function_type_parameters(ctx)?;
    self.require(TT::ParenthesisClose)?;

    let return_type = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr(ctx)?)
    } else {
      None
    };

    let method = Node::new(
      start_loc,
      TypeMethodSignature {
        optional,
        key,
        type_parameters,
        parameters,
        return_type,
      },
    );
    self.with_loc(|_| Ok(TypeMember::Method(method)))
  }

  /// Parse call signature
  fn call_signature(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeCallSignature>> {
    self.with_loc(|p| {
      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      p.require(TT::ParenthesisOpen)?;
      let parameters = p.function_type_parameters(ctx)?;
      p.require(TT::ParenthesisClose)?;

      let return_type = if p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr(ctx)?)
      } else {
        None
      };

      Ok(TypeCallSignature {
        type_parameters,
        parameters,
        return_type,
      })
    })
  }

  /// Parse constructor signature
  fn construct_signature(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    let type_parameters = if self.peek().typ == TT::ChevronLeft && self.is_start_of_type_arguments()
    {
      Some(self.type_parameters(ctx)?)
    } else {
      None
    };

    self.require(TT::ParenthesisOpen)?;
    let parameters = self.function_type_parameters(ctx)?;
    self.require(TT::ParenthesisClose)?;

    let return_type = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr(ctx)?)
    } else {
      None
    };

    let constructor = Node::new(
      start_loc,
      TypeConstructSignature {
        type_parameters,
        parameters,
        return_type,
      },
    );
    self.with_loc(|_| Ok(TypeMember::Constructor(constructor)))
  }

  /// Parse index signature
  fn index_signature(
    &mut self,
    ctx: ParseCtx,
    readonly: bool,
  ) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    self.require(TT::BracketOpen)?;
    let parameter_name = self.require_identifier()?;
    self.require(TT::Colon)?;
    let parameter_type = self.type_expr(ctx)?;
    self.require(TT::BracketClose)?;
    self.require(TT::Colon)?;
    let type_annotation = self.type_expr(ctx)?;

    let index = Node::new(
      start_loc,
      TypeIndexSignature {
        readonly,
        parameter_name,
        parameter_type,
        type_annotation,
      },
    );
    self.with_loc(|_| Ok(TypeMember::IndexSignature(index)))
  }

  /// Parse get accessor signature
  fn get_accessor_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
  ) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    self.require(TT::ParenthesisOpen)?;
    self.require(TT::ParenthesisClose)?;

    let return_type = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr(ctx)?)
    } else {
      None
    };

    let accessor = Node::new(start_loc, TypeGetAccessor { key, return_type });
    self.with_loc(|_| Ok(TypeMember::GetAccessor(accessor)))
  }

  /// Parse set accessor signature
  fn set_accessor_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
  ) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    self.require(TT::ParenthesisOpen)?;
    let parameter = self.function_type_parameter(ctx)?;
    self.require(TT::ParenthesisClose)?;

    let accessor = Node::new(start_loc, TypeSetAccessor { key, parameter });
    self.with_loc(|_| Ok(TypeMember::SetAccessor(accessor)))
  }

  /// Parse tuple type: [T, U, ...V[]]
  fn tuple_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::BracketOpen)?;
    let mut elements = Vec::new();
    while !self.consume_if(TT::BracketClose).is_match() {
      elements.push(self.tuple_element(ctx)?);
      if !self.consume_if(TT::Comma).is_match() {
        self.require(TT::BracketClose)?;
        break;
      }
    }
    let tuple = Node::new(start_loc, TypeTuple { elements });
    self.with_loc(|_| Ok(TypeExpr::TupleType(tuple)))
  }

  /// Parse tuple element
  fn tuple_element(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeTupleElement>> {
    self.with_loc(|p| {
      let rest = p.consume_if(TT::DotDotDot).is_match();

      // Check for named tuple element: name: Type or name?: Type
      let checkpoint = p.checkpoint();
      let label = if p.peek().typ == TT::Identifier {
        let name = p.consume_as_string();
        if p.peek().typ == TT::Colon || p.peek().typ == TT::Question {
          Some(name)
        } else {
          p.restore_checkpoint(checkpoint);
          None
        }
      } else {
        None
      };

      let optional = p.consume_if(TT::Question).is_match();

      if label.is_some() || optional {
        p.require(TT::Colon)?;
      }

      let type_expr = p.type_expr(ctx)?;

      Ok(TypeTupleElement {
        label,
        optional,
        rest,
        type_expr,
      })
    })
  }

  /// Parse parenthesized type or function type
  fn paren_or_function_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let checkpoint = self.checkpoint();

    // Try to parse as function type
    if let Ok(func_type) = self.try_function_type(ctx) {
      return Ok(func_type);
    }

    // Restore and parse as parenthesized type
    self.restore_checkpoint(checkpoint);
    let start_loc = self.peek().loc;
    self.require(TT::ParenthesisOpen)?;
    let type_expr = self.type_expr(ctx)?;
    self.require(TT::ParenthesisClose)?;
    let paren = Node::new(
      start_loc,
      TypeParenthesized {
        type_expr: Box::new(type_expr),
      },
    );
    self.with_loc(|_| Ok(TypeExpr::ParenthesizedType(paren)))
  }

  /// Try to parse function type: (x: T) => U
  fn try_function_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::ParenthesisOpen)?;
    let parameters = self.function_type_parameters(ctx)?;
    self.require(TT::ParenthesisClose)?;
    self.require(TT::EqualsChevronRight)?;
    let return_type = self.type_expr(ctx)?;

    let func = Node::new(
      start_loc,
      TypeFunction {
        type_parameters: None,
        parameters,
        return_type: Box::new(return_type),
      },
    );
    self.with_loc(|_| Ok(TypeExpr::FunctionType(func)))
  }

  /// Parse constructor type: new (x: T) => U
  fn constructor_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordNew)?;

    let type_parameters = if self.peek().typ == TT::ChevronLeft && self.is_start_of_type_arguments()
    {
      Some(self.type_parameters(ctx)?)
    } else {
      None
    };

    self.require(TT::ParenthesisOpen)?;
    let parameters = self.function_type_parameters(ctx)?;
    self.require(TT::ParenthesisClose)?;
    self.require(TT::EqualsChevronRight)?;
    let return_type = self.type_expr(ctx)?;

    let constructor = Node::new(
      start_loc,
      TypeConstructor {
        type_parameters,
        parameters,
        return_type: Box::new(return_type),
      },
    );
    self.with_loc(|_| Ok(TypeExpr::ConstructorType(constructor)))
  }

  /// Parse function type parameters
  fn function_type_parameters(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<Vec<Node<TypeFunctionParameter>>> {
    let mut params = Vec::new();

    while self.peek().typ != TT::ParenthesisClose && self.peek().typ != TT::EOF {
      params.push(self.function_type_parameter(ctx)?);

      if !self.consume_if(TT::Comma).is_match() {
        break;
      }
    }

    Ok(params)
  }

  /// Parse single function type parameter
  fn function_type_parameter(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeFunctionParameter>> {
    self.with_loc(|p| {
      let rest = p.consume_if(TT::DotDotDot).is_match();

      let name = if p.peek().typ == TT::Identifier {
        let checkpoint = p.checkpoint();
        let n = p.consume_as_string();
        // Check if followed by colon or question
        if p.peek().typ == TT::Colon || p.peek().typ == TT::Question {
          Some(n)
        } else {
          p.restore_checkpoint(checkpoint);
          None
        }
      } else {
        None
      };

      let optional = p.consume_if(TT::Question).is_match();

      if name.is_some() || optional {
        p.require(TT::Colon)?;
      }

      let type_expr = p.type_expr(ctx)?;

      Ok(TypeFunctionParameter {
        name,
        optional,
        rest,
        type_expr,
      })
    })
  }

  /// Parse type parameters: <T, U extends V, W = Default>
  pub fn type_parameters(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<TypeParameter>>> {
    self.require(TT::ChevronLeft)?;
    let mut params = Vec::new();
    while !self.consume_if(TT::ChevronRight).is_match() {
      params.push(self.type_parameter(ctx)?);
      if !self.consume_if(TT::Comma).is_match() {
        self.require(TT::ChevronRight)?;
        break;
      }
    }
    Ok(params)
  }

  /// Parse single type parameter
  fn type_parameter(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeParameter>> {
    self.with_loc(|p| {
      let name = p.require_identifier()?;

      let constraint = if p.consume_if(TT::KeywordExtends).is_match() {
        Some(Box::new(p.type_expr(ctx)?))
      } else {
        None
      };

      let default = if p.consume_if(TT::Equals).is_match() {
        Some(Box::new(p.type_expr(ctx)?))
      } else {
        None
      };

      Ok(TypeParameter {
        name,
        constraint,
        default,
      })
    })
  }

  /// Parse template literal type: `foo${T}bar`
  fn template_literal_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    let head = self.lit_template_part_str_val()?;
    let mut spans = Vec::new();

    loop {
      let type_expr = self.type_expr(ctx)?;
      let t = self.peek().typ;

      let literal = if t == TT::LiteralTemplatePartString {
        self.lit_template_part_str_val()?
      } else if t == TT::LiteralTemplatePartStringEnd {
        self.consume_as_string()
      } else {
        return Err(
          self
            .peek()
            .error(SyntaxErrorType::ExpectedSyntax("template literal continuation")),
        );
      };

      spans.push(self.with_loc(|_| {
        Ok(TypeTemplateLiteralSpan {
          type_expr,
          literal: literal.clone(),
        })
      })?);

      if t == TT::LiteralTemplatePartStringEnd {
        break;
      }
    }

    let template = Node::new(
      start_loc,
      TypeTemplateLiteral {
        head,
        spans,
      },
    );
    self.with_loc(|_| Ok(TypeExpr::TemplateLiteralType(template)))
  }

  /// Parse mapped type: { [K in keyof T]: T[K] }
  pub fn mapped_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::BraceOpen)?;

    // Parse readonly modifier: readonly, +readonly, -readonly
    let readonly_modifier = if self.consume_if(TT::KeywordReadonly).is_match() {
      Some(MappedTypeModifier::None)
    } else if self.consume_if(TT::Plus).is_match() && self.consume_if(TT::KeywordReadonly).is_match()
    {
      Some(MappedTypeModifier::Plus)
    } else if self.consume_if(TT::Hyphen).is_match()
      && self.consume_if(TT::KeywordReadonly).is_match()
    {
      Some(MappedTypeModifier::Minus)
    } else {
      None
    };

    self.require(TT::BracketOpen)?;
    let type_parameter = self.require_identifier()?;
    self.require(TT::KeywordIn)?;
    let constraint = self.type_expr(ctx)?;
    self.require(TT::BracketClose)?;

    // Parse optional modifier: ?, +?, -?
    let optional_modifier = if self.consume_if(TT::Question).is_match() {
      Some(MappedTypeModifier::None)
    } else if self.consume_if(TT::Plus).is_match() && self.consume_if(TT::Question).is_match() {
      Some(MappedTypeModifier::Plus)
    } else if self.consume_if(TT::Hyphen).is_match() && self.consume_if(TT::Question).is_match() {
      Some(MappedTypeModifier::Minus)
    } else {
      None
    };

    self.require(TT::Colon)?;
    let type_expr = self.type_expr(ctx)?;
    self.require(TT::BraceClose)?;

    let mapped = Node::new(
      start_loc,
      TypeMapped {
        readonly_modifier,
        type_parameter,
        constraint: Box::new(constraint),
        optional_modifier,
        type_expr: Box::new(type_expr),
      },
    );
    self.with_loc(|_| Ok(TypeExpr::MappedType(mapped)))
  }
}
