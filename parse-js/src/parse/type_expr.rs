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

    self.with_loc(|_| {
      Ok(if is_union {
        TypeExpr::UnionType(TypeUnion { types })
      } else {
        TypeExpr::IntersectionType(TypeIntersection { types })
      })
    })
  }

  /// Parse conditional types: T extends U ? X : Y
  fn type_conditional(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let check_type = self.type_array_or_postfix(ctx)?;

    if !self.consume_if(TT::KeywordExtends).is_match() {
      return Ok(check_type);
    }

    let extends_type = self.type_array_or_postfix(ctx)?;
    self.require(TT::Question)?;
    let true_type = self.type_expr(ctx)?;
    self.require(TT::Colon)?;
    let false_type = self.type_expr(ctx)?;

    self.with_loc(|_| {
      Ok(TypeExpr::ConditionalType(TypeConditional {
        check_type: Box::new(check_type),
        extends_type: Box::new(extends_type),
        true_type: Box::new(true_type),
        false_type: Box::new(false_type),
      }))
    })
  }

  /// Parse array types and indexed access types
  /// T[]  or  T[K]
  fn type_array_or_postfix(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let mut base = self.type_primary(ctx)?;

    loop {
      match self.peek().typ {
        TT::BracketOpen => {
          self.consume();
          if self.consume_if(TT::BracketClose).is_match() {
            // Array type: T[]
            base = self.with_loc(|_| {
              Ok(TypeExpr::ArrayType(TypeArray {
                element_type: Box::new(base),
              }))
            })?;
          } else {
            // Indexed access: T[K]
            let index = self.type_expr(ctx)?;
            self.require(TT::BracketClose)?;
            base = self.with_loc(|_| {
              Ok(TypeExpr::IndexedAccessType(TypeIndexedAccess {
                object_type: Box::new(base),
                index_type: Box::new(index),
              }))
            })?;
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
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Any(TypeAny {})))
      }
      TT::KeywordUnknown => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Unknown(TypeUnknown {})))
      }
      TT::KeywordNever => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Never(TypeNever {})))
      }
      TT::KeywordVoid => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Void(TypeVoid {})))
      }
      TT::KeywordStringType => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::String(TypeString {})))
      }
      TT::KeywordNumberType => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Number(TypeNumber {})))
      }
      TT::KeywordBooleanType => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Boolean(TypeBoolean {})))
      }
      TT::KeywordBigIntType => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::BigInt(TypeBigInt {})))
      }
      TT::KeywordSymbolType => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Symbol(TypeSymbol {})))
      }
      TT::KeywordObjectType => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Object(TypeObject {})))
      }
      TT::KeywordUndefinedType => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Undefined(TypeUndefined {})))
      }
      TT::LiteralNull => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::Null(TypeNull {})))
      }

      // Type reference or qualified name
      TT::Identifier => self.type_reference(ctx),

      // this type
      TT::KeywordThis => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::ThisType(TypeThis {})))
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
        let val = self.lit_str_val()?;
        self.with_loc(|_| Ok(TypeExpr::LiteralType(TypeLiteral::String(val))))
      }
      TT::LiteralNumber => {
        let val = self.lit_num_val()?.to_string();
        self.with_loc(|_| Ok(TypeExpr::LiteralType(TypeLiteral::Number(val))))
      }
      TT::LiteralBigInt => {
        let val = self.lit_bigint_val()?.to_string();
        self.with_loc(|_| Ok(TypeExpr::LiteralType(TypeLiteral::BigInt(val))))
      }
      TT::LiteralTrue => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::LiteralType(TypeLiteral::Boolean(true))))
      }
      TT::LiteralFalse => {
        self.consume();
        self.with_loc(|_| Ok(TypeExpr::LiteralType(TypeLiteral::Boolean(false))))
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
    self.with_loc(|p| {
      let name = p.parse_type_entity_name()?;
      let type_arguments = if p.is_start_of_type_arguments() {
        Some(p.type_arguments(ctx)?)
      } else {
        None
      };

      Ok(TypeExpr::TypeReference(TypeReference {
        name,
        type_arguments,
      }))
    })
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
    let args = self.list_with_loc(TT::Comma, TT::ChevronRight, |p| p.type_expr(ctx))?;
    self.require(TT::ChevronRight)?;
    Ok(args)
  }

  /// Parse typeof type query: typeof foo, typeof foo.bar.baz
  fn type_query(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordTypeof)?;
      let expr_name = p.parse_type_entity_name()?;
      Ok(TypeExpr::TypeQuery(TypeQuery { expr_name }))
    })
  }

  /// Parse keyof type: keyof T
  fn keyof_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordKeyof)?;
      let type_expr = p.type_primary(ctx)?;
      Ok(TypeExpr::KeyOfType(TypeKeyOf {
        type_expr: Box::new(type_expr),
      }))
    })
  }

  /// Parse infer type: infer R
  fn infer_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordInfer)?;
      let type_parameter = p.require_identifier()?;
      Ok(TypeExpr::InferType(TypeInfer { type_parameter }))
    })
  }

  /// Parse import type: import("module").Type<T>
  fn import_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordImport)?;
      p.require(TT::ParenthesisOpen)?;
      let module_specifier = p.lit_str_val()?;
      p.require(TT::ParenthesisClose)?;

      let (qualifier, type_arguments) = if p.consume_if(TT::Dot).is_match() {
        let qualifier = Some(p.parse_type_entity_name()?);
        let type_arguments = if p.is_start_of_type_arguments() {
          Some(p.type_arguments(ctx)?)
        } else {
          None
        };
        (qualifier, type_arguments)
      } else {
        (None, None)
      };

      Ok(TypeExpr::ImportType(TypeImport {
        module_specifier,
        qualifier,
        type_arguments,
      }))
    })
  }

  /// Parse object type literal: { x: T; y?: U; readonly z: V }
  fn object_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::BraceOpen)?;
      let members = p.type_members(ctx)?;
      p.require(TT::BraceClose)?;
      Ok(TypeExpr::ObjectType(TypeObjectLiteral { members }))
    })
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
    self.with_loc(|p| {
      let type_annotation = if p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr(ctx)?)
      } else {
        None
      };

      Ok(TypeMember::Property(TypePropertySignature {
        readonly,
        optional,
        key,
        type_annotation,
      }))
    })
  }

  /// Parse method signature
  fn method_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
    optional: bool,
  ) -> SyntaxResult<Node<TypeMember>> {
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

      Ok(TypeMember::Method(TypeMethodSignature {
        optional,
        key,
        type_parameters,
        parameters,
        return_type,
      }))
    })
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

      Ok(TypeMember::Constructor(TypeConstructSignature {
        type_parameters,
        parameters,
        return_type,
      }))
    })
  }

  /// Parse index signature
  fn index_signature(
    &mut self,
    ctx: ParseCtx,
    readonly: bool,
  ) -> SyntaxResult<Node<TypeMember>> {
    self.with_loc(|p| {
      p.require(TT::BracketOpen)?;
      let parameter_name = p.require_identifier()?;
      p.require(TT::Colon)?;
      let parameter_type = p.type_expr(ctx)?;
      p.require(TT::BracketClose)?;
      p.require(TT::Colon)?;
      let type_annotation = p.type_expr(ctx)?;

      Ok(TypeMember::IndexSignature(TypeIndexSignature {
        readonly,
        parameter_name,
        parameter_type,
        type_annotation,
      }))
    })
  }

  /// Parse get accessor signature
  fn get_accessor_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
  ) -> SyntaxResult<Node<TypeMember>> {
    self.with_loc(|p| {
      p.require(TT::ParenthesisOpen)?;
      p.require(TT::ParenthesisClose)?;

      let return_type = if p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr(ctx)?)
      } else {
        None
      };

      Ok(TypeMember::GetAccessor(TypeGetAccessor { key, return_type }))
    })
  }

  /// Parse set accessor signature
  fn set_accessor_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
  ) -> SyntaxResult<Node<TypeMember>> {
    self.with_loc(|p| {
      p.require(TT::ParenthesisOpen)?;
      let parameter = p.function_type_parameter(ctx)?;
      p.require(TT::ParenthesisClose)?;

      Ok(TypeMember::SetAccessor(TypeSetAccessor { key, parameter }))
    })
  }

  /// Parse tuple type: [T, U, ...V[]]
  fn tuple_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::BracketOpen)?;
      let elements = p.list_with_loc(TT::Comma, TT::BracketClose, |p| p.tuple_element(ctx))?;
      p.require(TT::BracketClose)?;
      Ok(TypeExpr::TupleType(TypeTuple { elements }))
    })
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
    self.with_loc(|p| {
      p.require(TT::ParenthesisOpen)?;
      let type_expr = p.type_expr(ctx)?;
      p.require(TT::ParenthesisClose)?;
      Ok(TypeExpr::ParenthesizedType(TypeParenthesized {
        type_expr: Box::new(type_expr),
      }))
    })
  }

  /// Try to parse function type: (x: T) => U
  fn try_function_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::ParenthesisOpen)?;
      let parameters = p.function_type_parameters(ctx)?;
      p.require(TT::ParenthesisClose)?;
      p.require(TT::EqualsChevronRight)?;
      let return_type = p.type_expr(ctx)?;

      Ok(TypeExpr::FunctionType(TypeFunction {
        type_parameters: None,
        parameters,
        return_type: Box::new(return_type),
      }))
    })
  }

  /// Parse constructor type: new (x: T) => U
  fn constructor_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordNew)?;

      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      p.require(TT::ParenthesisOpen)?;
      let parameters = p.function_type_parameters(ctx)?;
      p.require(TT::ParenthesisClose)?;
      p.require(TT::EqualsChevronRight)?;
      let return_type = p.type_expr(ctx)?;

      Ok(TypeExpr::ConstructorType(TypeConstructor {
        type_parameters,
        parameters,
        return_type: Box::new(return_type),
      }))
    })
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
    let params = self.list_with_loc(TT::Comma, TT::ChevronRight, |p| p.type_parameter(ctx))?;
    self.require(TT::ChevronRight)?;
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
    self.with_loc(|p| {
      let head = p.lit_template_part_str_val()?;
      let mut spans = Vec::new();

      loop {
        let type_expr = p.type_expr(ctx)?;
        let t = p.peek().typ;

        let literal = if t == TT::LiteralTemplatePartString {
          p.lit_template_part_str_val()?
        } else if t == TT::LiteralTemplatePartStringEnd {
          p.consume_as_string()
        } else {
          return Err(p.peek().error(SyntaxErrorType::ExpectedSyntax(
            "template literal continuation",
          )));
        };

        spans.push(
          p.with_loc(|_| {
            Ok(TypeTemplateLiteralSpan {
              type_expr,
              literal: literal.clone(),
            })
          })?,
        );

        if t == TT::LiteralTemplatePartStringEnd {
          break;
        }
      }

      Ok(TypeExpr::TemplateLiteralType(TypeTemplateLiteral {
        head,
        spans,
      }))
    })
  }

  /// Parse mapped type: { [K in keyof T]: T[K] }
  pub fn mapped_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    self.with_loc(|p| {
      p.require(TT::BraceOpen)?;

      // Parse readonly modifier: readonly, +readonly, -readonly
      let readonly_modifier = if p.consume_if(TT::KeywordReadonly).is_match() {
        Some(MappedTypeModifier::None)
      } else if p.consume_if(TT::Plus).is_match() && p.consume_if(TT::KeywordReadonly).is_match()
      {
        Some(MappedTypeModifier::Plus)
      } else if p.consume_if(TT::Hyphen).is_match()
        && p.consume_if(TT::KeywordReadonly).is_match()
      {
        Some(MappedTypeModifier::Minus)
      } else {
        None
      };

      p.require(TT::BracketOpen)?;
      let type_parameter = p.require_identifier()?;
      p.require(TT::KeywordIn)?;
      let constraint = p.type_expr(ctx)?;
      p.require(TT::BracketClose)?;

      // Parse optional modifier: ?, +?, -?
      let optional_modifier = if p.consume_if(TT::Question).is_match() {
        Some(MappedTypeModifier::None)
      } else if p.consume_if(TT::Plus).is_match() && p.consume_if(TT::Question).is_match() {
        Some(MappedTypeModifier::Plus)
      } else if p.consume_if(TT::Hyphen).is_match() && p.consume_if(TT::Question).is_match() {
        Some(MappedTypeModifier::Minus)
      } else {
        None
      };

      p.require(TT::Colon)?;
      let type_expr = p.type_expr(ctx)?;
      p.require(TT::BraceClose)?;

      Ok(TypeExpr::MappedType(TypeMapped {
        readonly_modifier,
        type_parameter,
        constraint: Box::new(constraint),
        optional_modifier,
        type_expr: Box::new(type_expr),
      }))
    })
  }
}
