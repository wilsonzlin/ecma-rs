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

  /// Parse type expression or type predicate for function return type
  /// Type predicates: `x is Type`, `asserts x`, `asserts x is Type`, `this is Type`
  pub fn type_expr_or_predicate(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    // Check for type predicate patterns
    let checkpoint = self.checkpoint();
    let start_loc = self.peek().loc;

    // Check for 'asserts' keyword
    let asserts = self.consume_if(TT::KeywordAsserts).is_match();

    // Try to parse parameter name
    if self.peek().typ == TT::Identifier || self.peek().typ == TT::KeywordThis {
      let is_this = self.peek().typ == TT::KeywordThis;
      let param_checkpoint = self.checkpoint();
      let param_loc = self.peek().loc; // Save location before consuming
      let parameter_name = if is_this {
        self.consume();
        "this".to_string()
      } else {
        self.require_identifier()?
      };

      // Check for 'is Type' after parameter name
      if self.consume_if(TT::KeywordIs).is_match() {
        // This is a type predicate: `x is Type` or `asserts x is Type`
        let type_annotation = Some(Box::new(self.type_expr(ctx)?));
        let end_loc = type_annotation.as_ref().unwrap().loc;
        use crate::loc::Loc;
        let outer_loc = Loc(start_loc.0, end_loc.1);
        let predicate = Node::new(start_loc, TypePredicate {
          asserts,
          parameter_name,
          type_annotation,
        });
        return Ok(Node::new(outer_loc, TypeExpr::TypePredicate(predicate)));
      } else if asserts {
        // This is `asserts x` without 'is Type'
        use crate::loc::Loc;
        let outer_loc = Loc(start_loc.0, param_loc.1);
        let predicate = Node::new(start_loc, TypePredicate {
          asserts: true,
          parameter_name,
          type_annotation: None,
        });
        return Ok(Node::new(outer_loc, TypeExpr::TypePredicate(predicate)));
      } else {
        // Not a type predicate, restore and parse as normal type
        self.restore_checkpoint(param_checkpoint);
      }
    }

    // Not a type predicate, restore and parse as normal type expression
    if asserts {
      self.restore_checkpoint(checkpoint);
    }
    self.type_union_or_intersection(ctx)
  }

  /// Parse union types (lowest precedence): T | U | V
  /// Each element of a union can be an intersection type
  fn type_union_or_intersection(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    // TypeScript allows leading | in union types: type A = | B | C
    let has_leading_bar = self.consume_if(TT::Bar).is_match();

    let first = self.type_intersection(ctx)?;

    // Check if there are more union members
    if !has_leading_bar && self.peek().typ != TT::Bar {
      return Ok(first);
    }

    let mut types = vec![first];
    while self.consume_if(TT::Bar).is_match() {
      types.push(self.type_intersection(ctx)?);
    }

    if types.len() == 1 {
      return Ok(types.into_iter().next().unwrap());
    }

    let start_loc = types[0].loc;
    let end_loc = types.last().unwrap().loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let union = Node::new(start_loc, TypeUnion { types });
    Ok(Node::new(outer_loc, TypeExpr::UnionType(union)))
  }

  /// Parse intersection types (higher precedence than union): T & U & V
  fn type_intersection(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    // TypeScript allows leading & in intersection types: type A = & B & C
    let has_leading_amp = self.consume_if(TT::Ampersand).is_match();

    let first = self.type_conditional(ctx)?;

    // Check if there are more intersection members
    if !has_leading_amp && self.peek().typ != TT::Ampersand {
      return Ok(first);
    }

    let mut types = vec![first];
    while self.consume_if(TT::Ampersand).is_match() {
      types.push(self.type_conditional(ctx)?);
    }

    if types.len() == 1 {
      return Ok(types.into_iter().next().unwrap());
    }

    let start_loc = types[0].loc;
    let end_loc = types.last().unwrap().loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let intersection = Node::new(start_loc, TypeIntersection { types });
    Ok(Node::new(outer_loc, TypeExpr::IntersectionType(intersection)))
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

    let end_loc = false_type.loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let conditional = Node::new(
      start_loc,
      TypeConditional {
        check_type: Box::new(check_type),
        extends_type: Box::new(extends_type),
        true_type: Box::new(true_type),
        false_type: Box::new(false_type),
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::ConditionalType(conditional)))
  }

  /// Parse array types and indexed access types
  /// T[]  or  T[K]
  fn type_array_or_postfix(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let mut base = self.type_primary(ctx)?;

    loop {
      let next_tok = self.peek();
      match next_tok.typ {
        TT::BracketOpen => {
          // Don't parse [..] as array/indexed access if it's on a new line
          // This prevents treating index signatures as indexed access types
          // in interface/object type contexts
          if next_tok.preceded_by_line_terminator {
            break;
          }

          let start_loc = base.loc;
          self.consume();
          if self.peek().typ == TT::BracketClose {
            // Array type: T[]
            let end_loc = self.peek().loc;
            self.consume();
            use crate::loc::Loc;
            let outer_loc = Loc(start_loc.0, end_loc.1);
            let array = Node::new(
              start_loc,
              TypeArray {
                readonly: false,
                element_type: Box::new(base),
              },
            );
            base = Node::new(outer_loc, TypeExpr::ArrayType(array));
          } else {
            // Indexed access: T[K]
            let index = self.type_expr(ctx)?;
            let end_loc = self.peek().loc;
            self.require(TT::BracketClose)?;
            use crate::loc::Loc;
            let outer_loc = Loc(start_loc.0, end_loc.1);
            let indexed = Node::new(
              start_loc,
              TypeIndexedAccess {
                object_type: Box::new(base),
                index_type: Box::new(index),
              },
            );
            base = Node::new(outer_loc, TypeExpr::IndexedAccessType(indexed));
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
        let inner = Node::new(loc, TypeAny {});
        Ok(Node::new(loc, TypeExpr::Any(inner)))
      }
      TT::KeywordUnknown => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeUnknown {});
        Ok(Node::new(loc, TypeExpr::Unknown(inner)))
      }
      TT::KeywordNever => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeNever {});
        Ok(Node::new(loc, TypeExpr::Never(inner)))
      }
      TT::KeywordVoid => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeVoid {});
        Ok(Node::new(loc, TypeExpr::Void(inner)))
      }
      TT::KeywordStringType => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeString {});
        Ok(Node::new(loc, TypeExpr::String(inner)))
      }
      TT::KeywordNumberType => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeNumber {});
        Ok(Node::new(loc, TypeExpr::Number(inner)))
      }
      TT::KeywordBooleanType => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeBoolean {});
        Ok(Node::new(loc, TypeExpr::Boolean(inner)))
      }
      TT::KeywordBigIntType => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeBigInt {});
        Ok(Node::new(loc, TypeExpr::BigInt(inner)))
      }
      TT::KeywordSymbolType => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeSymbol {});
        Ok(Node::new(loc, TypeExpr::Symbol(inner)))
      }
      TT::KeywordUnique => {
        // Check for "unique symbol"
        let start_loc = self.peek().loc;
        self.consume();
        if self.peek().typ == TT::KeywordSymbolType {
          let end_loc = self.peek().loc;
          self.consume();
          use crate::loc::Loc;
          let outer_loc = Loc(start_loc.0, end_loc.1);
          let inner = Node::new(start_loc, TypeUniqueSymbol {});
          Ok(Node::new(outer_loc, TypeExpr::UniqueSymbol(inner)))
        } else {
          return Err(self.peek().error(SyntaxErrorType::ExpectedSyntax("symbol after unique")));
        }
      }
      TT::KeywordObjectType => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeObject {});
        Ok(Node::new(loc, TypeExpr::Object(inner)))
      }
      TT::KeywordUndefinedType => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeUndefined {});
        Ok(Node::new(loc, TypeExpr::Undefined(inner)))
      }
      TT::LiteralNull => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeNull {});
        Ok(Node::new(loc, TypeExpr::Null(inner)))
      }

      // Type reference or qualified name
      TT::Identifier => self.type_reference(ctx),

      // readonly modifier for array and tuple types
      TT::KeywordReadonly => {
        let [_, next] = self.peek_n::<2>();
        // Check if followed by a type that can be readonly (primitives, identifiers, brackets, parens, etc.)
        // If followed by [, it's a readonly tuple type
        // Otherwise, parse the type and if it ends up being an array, mark it readonly
        if next.typ == TT::BracketOpen {
          // readonly [T, U] or readonly []
          self.consume(); // consume readonly
          let start_loc = self.peek().loc;
          self.require(TT::BracketOpen)?;
          let mut elements = Vec::new();
          let end_loc;
          loop {
            if self.peek().typ == TT::BracketClose {
              end_loc = self.peek().loc;
              self.consume();
              break;
            }
            elements.push(self.tuple_element(ctx)?);
            if !self.consume_if(TT::Comma).is_match() {
              end_loc = self.peek().loc;
              self.require(TT::BracketClose)?;
              break;
            }
          }
          use crate::loc::Loc;
          let outer_loc = Loc(start_loc.0, end_loc.1);
          let tuple = Node::new(start_loc, TypeTuple { readonly: true, elements });
          Ok(Node::new(outer_loc, TypeExpr::TupleType(tuple)))
        } else {
          // readonly T[] - consume readonly and parse the base type
          self.consume(); // consume readonly
          let start_loc = self.peek().loc;
          let mut base_type = self.type_primary(ctx)?;

          // Now check if it's followed by [] to make it an array type
          if self.peek().typ == TT::BracketOpen {
            let [_, bracket_next] = self.peek_n::<2>();
            if bracket_next.typ == TT::BracketClose {
              // It's T[] pattern
              self.consume(); // consume [
              let end_loc = self.peek().loc;
              self.consume(); // consume ]
              use crate::loc::Loc;
              let outer_loc = Loc(start_loc.0, end_loc.1);
              let array = Node::new(
                start_loc,
                TypeArray {
                  readonly: true,
                  element_type: Box::new(base_type),
                },
              );
              base_type = Node::new(outer_loc, TypeExpr::ArrayType(array));
            }
          }

          Ok(base_type)
        }
      }

      // Contextual keywords allowed as type identifiers
      TT::KeywordAwait | TT::KeywordYield | TT::KeywordAsync |
      TT::KeywordAs | TT::KeywordFrom | TT::KeywordOf | TT::KeywordGet | TT::KeywordSet | TT::KeywordConstructor |
      TT::KeywordAsserts | TT::KeywordDeclare | TT::KeywordImplements |
      TT::KeywordIs | TT::KeywordModule | TT::KeywordNamespace |
      TT::KeywordOverride | TT::KeywordPrivate | TT::KeywordProtected | TT::KeywordPublic |
      TT::KeywordSatisfies | TT::KeywordStatic | TT::KeywordUnique |
      TT::KeywordUsing | TT::KeywordOut | TT::KeywordLet |
      TT::KeywordSuper  // TypeScript: Error recovery - allow 'super' in type positions
      => self.type_reference(ctx),

      // this type
      TT::KeywordThis => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeThis {});
        Ok(Node::new(loc, TypeExpr::ThisType(inner)))
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

      // Generic function type: <T>(x: T) => U
      TT::ChevronLeft => self.try_function_type(ctx),

      // new () => T  (constructor type)
      // TypeScript: abstract new () => T (abstract constructor type)
      TT::KeywordNew => self.constructor_type(ctx),
      TT::KeywordAbstract => {
        // Check if this is 'abstract new' for abstract constructor type
        let [_, next] = self.peek_n::<2>();
        if next.typ == TT::KeywordNew {
          // Skip 'abstract' and parse constructor type
          self.consume(); // abstract
          self.constructor_type(ctx)
        } else {
          // Treat 'abstract' as a type identifier
          self.type_reference(ctx)
        }
      }

      // Literal types
      TT::LiteralString => {
        let loc = self.peek().loc;
        let val = self.lit_str_val()?;
        let inner = Node::new(loc, TypeLiteral::String(val));
        Ok(Node::new(loc, TypeExpr::LiteralType(inner)))
      }
      TT::LiteralNumber => {
        let loc = self.peek().loc;
        let val = self.lit_num_val()?.to_string();
        let inner = Node::new(loc, TypeLiteral::Number(val));
        Ok(Node::new(loc, TypeExpr::LiteralType(inner)))
      }
      // Negative numeric literals: -123 or -123n
      TT::Hyphen => {
        let start_loc = self.peek().loc;
        let [_, next] = self.peek_n::<2>();
        if next.typ == TT::LiteralNumber {
          self.consume(); // consume hyphen
          let num_val = self.lit_num_val()?.to_string();
          let val = format!("-{}", num_val);
          use crate::loc::Loc;
          let loc = Loc(start_loc.0, self.peek().loc.1);
          let inner = Node::new(loc, TypeLiteral::Number(val));
          Ok(Node::new(loc, TypeExpr::LiteralType(inner)))
        } else if next.typ == TT::LiteralBigInt {
          self.consume(); // consume hyphen
          let bigint_val = self.lit_bigint_val()?.to_string();
          let val = format!("-{}", bigint_val);
          use crate::loc::Loc;
          let loc = Loc(start_loc.0, self.peek().loc.1);
          let inner = Node::new(loc, TypeLiteral::BigInt(val));
          Ok(Node::new(loc, TypeExpr::LiteralType(inner)))
        } else {
          Err(self.peek().error(SyntaxErrorType::ExpectedSyntax("type expression")))
        }
      }
      TT::LiteralBigInt => {
        let loc = self.peek().loc;
        let val = self.lit_bigint_val()?.to_string();
        let inner = Node::new(loc, TypeLiteral::BigInt(val));
        Ok(Node::new(loc, TypeExpr::LiteralType(inner)))
      }
      TT::LiteralTrue => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeLiteral::Boolean(true));
        Ok(Node::new(loc, TypeExpr::LiteralType(inner)))
      }
      TT::LiteralFalse => {
        let loc = self.peek().loc;
        self.consume();
        let inner = Node::new(loc, TypeLiteral::Boolean(false));
        Ok(Node::new(loc, TypeExpr::LiteralType(inner)))
      }

      // import("module").Type
      TT::KeywordImport => self.import_type(ctx),

      // Template literal type
      TT::LiteralTemplatePartString => self.template_literal_type(ctx),

      // TypeScript: Error recovery - private names in type expressions
      // Example: `const x: C[#bar] = 3;` (indexed access with private name)
      // The type checker will catch this as a semantic error
      TT::PrivateMember => {
        let loc = self.peek().loc;
        let name = self.consume_as_string();
        let reference = Node::new(loc, TypeReference {
          name: TypeEntityName::Identifier(name),
          type_arguments: None,
        });
        Ok(Node::new(loc, TypeExpr::TypeReference(reference)))
      }

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

    let end_loc = if let Some(ref args) = type_arguments {
      args.last().map(|a| a.loc).unwrap_or(start_loc)
    } else {
      self.peek().loc
    };
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let reference = Node::new(
      start_loc,
      TypeReference {
        name,
        type_arguments,
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::TypeReference(reference)))
  }

  /// Parse entity name (can be qualified: A.B.C)
  fn parse_type_entity_name(&mut self) -> SyntaxResult<TypeEntityName> {
    let first = self.require_type_identifier()?;
    let mut name = TypeEntityName::Identifier(first);

    while self.consume_if(TT::Dot).is_match() {
      let right = self.require_type_identifier()?;
      name = TypeEntityName::Qualified(Box::new(TypeQualifiedName {
        left: name,
        right,
      }));
    }

    Ok(name)
  }

  /// Require an identifier or contextual keyword valid in type position
  fn require_type_identifier(&mut self) -> SyntaxResult<String> {
    let t = self.consume();
    match t.typ {
      TT::Identifier |
      TT::KeywordAwait | TT::KeywordYield | TT::KeywordAsync |
      TT::KeywordAs | TT::KeywordFrom | TT::KeywordOf | TT::KeywordGet | TT::KeywordSet | TT::KeywordConstructor |
      TT::KeywordAbstract | TT::KeywordAsserts | TT::KeywordDeclare | TT::KeywordImplements |
      TT::KeywordIs | TT::KeywordModule | TT::KeywordNamespace |
      TT::KeywordOverride | TT::KeywordPrivate | TT::KeywordProtected | TT::KeywordPublic |
      TT::KeywordReadonly | TT::KeywordSatisfies | TT::KeywordStatic | TT::KeywordUnique |
      TT::KeywordUsing | TT::KeywordOut | TT::KeywordLet |
      // Allow type keywords as identifiers in typeof queries like: typeof undefined, typeof this
      TT::KeywordUndefinedType | TT::KeywordThis |
      TT::KeywordSuper |  // TypeScript: Error recovery - allow 'super' as type identifier
      // TypeScript: Error recovery - allow reserved keywords in qualified type names
      // Examples: `x.void`, `typeof Controller.prototype.delete`, `typeof foo.var`
      TT::KeywordVoid | TT::KeywordDelete | TT::KeywordVar
      => Ok(self.string(t.loc)),
      _ => Err(t.error(SyntaxErrorType::ExpectedSyntax("type identifier")))
    }
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

      // Constructor types: new () => T, abstract new () => T
      TT::KeywordNew | TT::KeywordAbstract => true,

      // Readonly modifier: readonly T[]
      TT::KeywordReadonly => true,

      // TypeScript: Literal types (string, number, boolean, null, template literals, etc.)
      // Enables: Exclude<"a" | "b", "c">, MyType<123>, MyType<`foo${T}`>, etc.
      TT::LiteralString | TT::LiteralNumber | TT::LiteralBigInt
      | TT::LiteralTrue | TT::LiteralFalse | TT::LiteralNull
      | TT::LiteralTemplatePartString => true,

      // Identifier followed by type-like punctuation
      TT::Identifier => {
        self.consume();
        matches!(
          self.peek().typ,
          TT::ChevronLeft
            | TT::ChevronRight
            | TT::ChevronRightChevronRight
            | TT::ChevronRightChevronRightChevronRight
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
      // Also handle >> and >>> which will be split during parsing
      TT::ChevronRight | TT::ChevronRightChevronRight | TT::ChevronRightChevronRightChevronRight => true,

      _ => false,
    };

    self.restore_checkpoint(checkpoint);
    looks_like_type
  }

  /// Parse type arguments: <T, U, V>
  pub fn type_arguments(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<TypeExpr>>> {
    self.require(TT::ChevronLeft)?;
    let mut args = Vec::new();
    while !self.consume_if(TT::ChevronRight).is_match() {
      args.push(self.type_expr(ctx)?);
      if !self.consume_if(TT::Comma).is_match() {
        self.require_chevron_right()?;
        break;
      }
    }
    Ok(args)
  }

  /// Parse typeof type query: typeof foo, typeof foo.bar.baz, typeof import("module")
  fn type_query(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordTypeof)?;

    // Check if it's typeof import(...)
    let expr_name = if self.peek().typ == TT::KeywordImport {
      let import_expr = self.import_call(ctx)?;
      let end_loc = import_expr.loc;
      TypeEntityName::Import(import_expr)
    } else {
      self.parse_type_entity_name()?
    };

    let end_loc = self.peek().loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let query = Node::new(start_loc, TypeQuery { expr_name });
    Ok(Node::new(outer_loc, TypeExpr::TypeQuery(query)))
  }

  /// Parse keyof type: keyof T
  fn keyof_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordKeyof)?;
    let type_expr = self.type_primary(ctx)?;
    let end_loc = type_expr.loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let keyof = Node::new(
      start_loc,
      TypeKeyOf {
        type_expr: Box::new(type_expr),
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::KeyOfType(keyof)))
  }

  /// Parse infer type: infer R, infer R extends U
  fn infer_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::KeywordInfer)?;
    let type_parameter = self.require_type_identifier()?;

    // TypeScript: infer with extends clause
    let constraint = if self.consume_if(TT::KeywordExtends).is_match() {
      Some(Box::new(self.type_expr(ctx)?))
    } else {
      None
    };

    let end_loc = self.peek().loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let infer = Node::new(start_loc, TypeInfer { type_parameter, constraint });
    Ok(Node::new(outer_loc, TypeExpr::InferType(infer)))
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

    let end_loc = if let Some(ref args) = type_arguments {
      args.last().map(|a| a.loc).unwrap_or(self.peek().loc)
    } else {
      self.peek().loc
    };
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let import = Node::new(
      start_loc,
      TypeImport {
        module_specifier,
        qualifier,
        type_arguments,
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::ImportType(import)))
  }

  /// Parse object type literal: { x: T; y?: U; readonly z: V }
  /// or mapped type: { [K in keyof T]: T[K] }
  fn object_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::BraceOpen)?;

    // Check if this is a mapped type by looking ahead
    // Mapped types start with optional readonly/+readonly/-readonly, then [, then identifier in
    let checkpoint = self.checkpoint();

    // Skip optional readonly modifier
    if self.peek().typ == TT::KeywordReadonly {
      self.consume();
    } else if self.peek().typ == TT::Plus || self.peek().typ == TT::Hyphen {
      self.consume();
      if self.peek().typ == TT::KeywordReadonly {
        self.consume();
      }
    }

    // Check for [identifier in pattern
    let is_mapped_type = if self.peek().typ == TT::BracketOpen {
      self.consume(); // consume '['
      if self.peek().typ == TT::Identifier {
        let [_, t2] = self.peek_n::<2>();
        t2.typ == TT::KeywordIn
      } else {
        false
      }
    } else {
      false
    };

    self.restore_checkpoint(checkpoint);

    if is_mapped_type {
      // Parse as mapped type body (opening brace already consumed)
      return self.mapped_type_body(ctx, start_loc);
    }

    // Parse as regular object type
    let members = self.type_members(ctx)?;
    let end_loc = self.peek().loc;
    self.require(TT::BraceClose)?;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let object = Node::new(start_loc, TypeObjectLiteral { members });
    Ok(Node::new(outer_loc, TypeExpr::ObjectType(object)))
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

    // Check for index signature vs mapped property vs computed property
    // [key: string]: T vs [K in T]: V vs [Symbol.iterator]?: T
    if self.peek().typ == TT::BracketOpen {
      // Peek ahead: [, then identifier/keyword, then : or in
      let [_t0, t1, t2] = self.peek_n::<3>();
      // Check if t1 is identifier or keyword (keywords can be used as parameter names)
      let is_identifier_or_keyword = t1.typ == TT::Identifier ||
        crate::lex::KEYWORDS_MAPPING.contains_key(&t1.typ);

      if is_identifier_or_keyword {
        if t2.typ == TT::Colon {
          // Index signature: [key: string]: T
          return self.index_signature(ctx, readonly);
        } else if t2.typ == TT::KeywordIn {
          // Mapped type member: [K in keyof T]: V
          // Restore to before readonly was consumed, so mapped_type_member can parse it
          self.restore_checkpoint(checkpoint);
          return self.mapped_type_member(ctx);
        }
      }
      // Otherwise, it's a computed property key - fall through to parse it normally
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
    // But don't treat get/set as accessor keywords if followed by ? (optional method)
    let is_get = self.peek().typ == TT::KeywordGet && self.peek_n::<2>()[1].typ != TT::Question
      && self.consume_if(TT::KeywordGet).is_match();
    let is_set = !is_get && self.peek().typ == TT::KeywordSet && self.peek_n::<2>()[1].typ != TT::Question
      && self.consume_if(TT::KeywordSet).is_match();

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
      // TypeScript: Error recovery - private names in type/interface property signatures
      // Semantically invalid but accept for error recovery (e.g., `type A = { #foo: string }`)
      TT::PrivateMember => Ok(TypePropertyKey::Identifier(self.consume_as_string())),
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

    let end_loc = if let Some(ref ta) = type_annotation {
      ta.loc
    } else {
      self.peek().loc
    };
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let prop = Node::new(
      start_loc,
      TypePropertySignature {
        readonly,
        optional,
        key,
        type_annotation,
      },
    );
    Ok(Node::new(outer_loc, TypeMember::Property(prop)))
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

    // TypeScript: Support type predicates in method signatures
    let return_type = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr_or_predicate(ctx)?)
    } else {
      None
    };

    let end_loc = if let Some(ref rt) = return_type {
      rt.loc
    } else {
      self.peek().loc
    };
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
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
    Ok(Node::new(outer_loc, TypeMember::Method(method)))
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

      // TypeScript: Support type predicates in call signatures
      let return_type = if p.consume_if(TT::Colon).is_match() {
        Some(p.type_expr_or_predicate(ctx)?)
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

    // TypeScript: Support type predicates in constructor signatures
    let return_type = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr_or_predicate(ctx)?)
    } else {
      None
    };

    let end_loc = if let Some(ref rt) = return_type {
      rt.loc
    } else {
      self.peek().loc
    };
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let constructor = Node::new(
      start_loc,
      TypeConstructSignature {
        type_parameters,
        parameters,
        return_type,
      },
    );
    Ok(Node::new(outer_loc, TypeMember::Constructor(constructor)))
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

    let end_loc = type_annotation.loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let index = Node::new(
      start_loc,
      TypeIndexSignature {
        readonly,
        parameter_name,
        parameter_type,
        type_annotation,
      },
    );
    Ok(Node::new(outer_loc, TypeMember::IndexSignature(index)))
  }

  /// Parse get accessor signature
  fn get_accessor_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
  ) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    self.require(TT::ParenthesisOpen)?;
    // ES2017+: Allow trailing comma in empty parameter list
    let _ = self.consume_if(TT::Comma);
    self.require(TT::ParenthesisClose)?;

    // TypeScript: Support type predicates in get accessor signatures
    let return_type = if self.consume_if(TT::Colon).is_match() {
      Some(self.type_expr_or_predicate(ctx)?)
    } else {
      None
    };

    let end_loc = if let Some(ref rt) = return_type {
      rt.loc
    } else {
      self.peek().loc
    };
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let accessor = Node::new(start_loc, TypeGetAccessor { key, return_type });
    Ok(Node::new(outer_loc, TypeMember::GetAccessor(accessor)))
  }

  /// Parse set accessor signature
  fn set_accessor_signature(
    &mut self,
    ctx: ParseCtx,
    key: TypePropertyKey,
  ) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;
    self.require(TT::ParenthesisOpen)?;
    // TypeScript: Error recovery - allow setters with no parameter
    let parameter = if self.peek().typ == TT::ParenthesisClose {
      // Empty parameter list - create synthetic parameter for error recovery
      let loc = self.peek().loc;
      Node::new(loc, TypeFunctionParameter {
        rest: false,
        name: Some("_".to_string()),
        optional: false,
        type_expr: Node::new(loc, TypeExpr::Any(Node::new(loc, crate::ast::type_expr::TypeAny {}))),
      })
    } else {
      self.function_type_parameter(ctx)?
    };
    // ES2017+: Allow trailing comma in setter parameter list
    let _ = self.consume_if(TT::Comma);
    let end_loc = self.peek().loc;
    self.require(TT::ParenthesisClose)?;

    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let accessor = Node::new(start_loc, TypeSetAccessor { key, parameter });
    Ok(Node::new(outer_loc, TypeMember::SetAccessor(accessor)))
  }

  /// Parse tuple type: [T, U, ...V[]]
  fn tuple_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;
    self.require(TT::BracketOpen)?;
    let mut elements = Vec::new();
    let end_loc;
    loop {
      if self.peek().typ == TT::BracketClose {
        end_loc = self.peek().loc;
        self.consume();
        break;
      }
      elements.push(self.tuple_element(ctx)?);
      if !self.consume_if(TT::Comma).is_match() {
        end_loc = self.peek().loc;
        self.require(TT::BracketClose)?;
        break;
      }
    }
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let tuple = Node::new(start_loc, TypeTuple { readonly: false, elements });
    Ok(Node::new(outer_loc, TypeExpr::TupleType(tuple)))
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

      // For named elements, check for optional before colon: name?: Type
      let mut optional = p.consume_if(TT::Question).is_match();

      if label.is_some() || optional {
        p.require(TT::Colon)?;
      }

      let type_expr = p.type_expr(ctx)?;

      // For unnamed elements, check for optional after type: Type?
      if label.is_none() && !optional {
        optional = p.consume_if(TT::Question).is_match();
      }

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
    // Quick lookahead to avoid expensive parsing attempt for parenthesized types
    // This prevents exponential backtracking on deeply nested parentheses like ((((string))))
    if !self.looks_like_function_type() {
      // Parse as parenthesized type
      let start_loc = self.peek().loc;
      self.require(TT::ParenthesisOpen)?;
      let type_expr = self.type_expr(ctx)?;
      let end_loc = self.peek().loc;
      self.require(TT::ParenthesisClose)?;
      use crate::loc::Loc;
      let outer_loc = Loc(start_loc.0, end_loc.1);
      let paren = Node::new(
        start_loc,
        TypeParenthesized {
          type_expr: Box::new(type_expr),
        },
      );
      return Ok(Node::new(outer_loc, TypeExpr::ParenthesizedType(paren)));
    }

    // Parse as function type
    self.try_function_type(ctx)
  }

  /// Quick lookahead to check if this looks like a function type (has => after params)
  /// This avoids exponential backtracking on deeply nested parenthesized types
  fn looks_like_function_type(&mut self) -> bool {
    let checkpoint = self.checkpoint();

    // Skip optional type parameters <T, U>
    if self.peek().typ == TT::ChevronLeft {
      self.consume(); // <
      let mut depth = 1;
      while depth > 0 && self.peek().typ != TT::EOF {
        match self.peek().typ {
          TT::ChevronLeft => depth += 1,
          TT::ChevronRight => depth -= 1,
          TT::ChevronRightChevronRight => depth -= 2,
          TT::ChevronRightChevronRightChevronRight => depth -= 3,
          _ => {}
        }
        if depth > 0 {
          self.consume();
        }
      }
      if depth > 0 {
        self.restore_checkpoint(checkpoint);
        return false;
      }
      self.consume(); // consume the final >
    }

    // Must have opening paren
    if self.peek().typ != TT::ParenthesisOpen {
      self.restore_checkpoint(checkpoint);
      return false;
    }
    self.consume(); // (

    // Scan to find matching )
    let mut depth = 1;
    while depth > 0 && self.peek().typ != TT::EOF {
      match self.peek().typ {
        TT::ParenthesisOpen => depth += 1,
        TT::ParenthesisClose => {
          depth -= 1;
          if depth > 0 {
            self.consume();
          }
        }
        _ => {}
      }
      if depth > 0 {
        self.consume();
      }
    }

    if depth > 0 {
      // Didn't find matching paren
      self.restore_checkpoint(checkpoint);
      return false;
    }

    self.consume(); // consume the final )

    // Check if followed by =>
    let has_arrow = self.peek().typ == TT::EqualsChevronRight;

    self.restore_checkpoint(checkpoint);
    has_arrow
  }

  /// Try to parse function type: (x: T) => U or <T>(x: T) => U
  fn try_function_type(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
    let start_loc = self.peek().loc;

    // Optional type parameters: <T, U>
    let type_parameters = if self.peek().typ == TT::ChevronLeft && self.is_start_of_type_arguments() {
      Some(self.type_parameters(ctx)?)
    } else {
      None
    };

    self.require(TT::ParenthesisOpen)?;
    let parameters = self.function_type_parameters(ctx)?;
    self.require(TT::ParenthesisClose)?;
    self.require(TT::EqualsChevronRight)?;
    let return_type = self.type_expr_or_predicate(ctx)?;

    let end_loc = return_type.loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let func = Node::new(
      start_loc,
      TypeFunction {
        type_parameters,
        parameters,
        return_type: Box::new(return_type),
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::FunctionType(func)))
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
    let return_type = self.type_expr_or_predicate(ctx)?;

    let end_loc = return_type.loc;
    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let constructor = Node::new(
      start_loc,
      TypeConstructor {
        type_parameters,
        parameters,
        return_type: Box::new(return_type),
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::ConstructorType(constructor)))
  }

  /// Parse function type parameters
  fn function_type_parameters(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<Vec<Node<TypeFunctionParameter>>> {
    let mut params = Vec::new();

    // Check for `this` parameter as first parameter
    if self.peek().typ == TT::KeywordThis {
      let [_, next] = self.peek_n::<2>();
      if next.typ == TT::Colon {
        // Parse this parameter: this: Type
        params.push(self.with_loc(|p| {
          p.consume(); // consume 'this'
          p.require(TT::Colon)?;
          let type_expr = p.type_expr(ctx)?;
          Ok(TypeFunctionParameter {
            name: Some(String::from("this")),
            optional: false,
            rest: false,
            type_expr,
          })
        })?);

        // Check for comma before other parameters
        if self.peek().typ == TT::Comma {
          self.consume();
        }
      }
    }

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
      // TypeScript: Allow accessibility modifiers in type signatures for error recovery
      // e.g., `(public x, private y)` in interface (semantically invalid but syntactically parseable)
      if !p.consume_if(TT::KeywordPublic).is_match() {
        if !p.consume_if(TT::KeywordPrivate).is_match() {
          p.consume_if(TT::KeywordProtected);
        }
      }

      // TypeScript: Allow readonly modifier
      p.consume_if(TT::KeywordReadonly);

      let rest = p.consume_if(TT::DotDotDot).is_match();

      let name = if p.peek().typ == TT::Identifier {
        let checkpoint = p.checkpoint();
        let n = p.consume_as_string();
        // Check if followed by colon, question, or equals (for error recovery)
        if p.peek().typ == TT::Colon || p.peek().typ == TT::Question || p.peek().typ == TT::Equals {
          Some(n)
        } else {
          p.restore_checkpoint(checkpoint);
          None
        }
      } else {
        None
      };

      let optional = p.consume_if(TT::Question).is_match();

      // TypeScript: Allow default values in type signatures for error recovery
      // e.g., `(x = 1)` or `foo(x = 1)` in interface/type literal
      if p.peek().typ == TT::Equals {
        p.consume(); // consume '='
        // Parse and discard the default value expression
        let _ = p.expr(ctx, [TT::Comma, TT::ParenthesisClose]);
        // Type annotation is optional when there's a default value
        let type_expr = if p.consume_if(TT::Colon).is_match() {
          p.type_expr(ctx)?
        } else {
          // Create synthetic 'any' type
          use crate::loc::Loc;
          Node::new(p.peek().loc, TypeExpr::Any(Node::new(p.peek().loc, crate::ast::type_expr::TypeAny {})))
        };
        return Ok(TypeFunctionParameter {
          name,
          optional,
          rest,
          type_expr,
        });
      }

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
        self.require_chevron_right()?;
        break;
      }
    }
    Ok(params)
  }

  /// Parse single type parameter
  fn type_parameter(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeParameter>> {
    self.with_loc(|p| {
      // TypeScript: const type parameter
      let const_ = p.consume_if(TT::KeywordConst).is_match();

      // TypeScript: variance annotations (in, out, in out)
      use crate::ast::type_expr::Variance;
      let variance = if p.consume_if(TT::KeywordIn).is_match() {
        if p.consume_if(TT::KeywordOut).is_match() {
          Some(Variance::InOut)
        } else {
          Some(Variance::In)
        }
      } else if p.consume_if(TT::KeywordOut).is_match() {
        Some(Variance::Out)
      } else {
        None
      };

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
        const_,
        variance,
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

    let mut end_loc = start_loc;
    loop {
      let type_expr = self.type_expr(ctx)?;

      // Require the closing brace of the substitution
      self.require(TT::BraceClose)?;

      // Get the next template part in template continuation mode
      use crate::lex::LexMode;
      let t = self.consume_with_mode(LexMode::TemplateStrContinue);

      let literal = if t.typ == TT::LiteralTemplatePartString {
        self.string(t.loc).to_string()
      } else if t.typ == TT::LiteralTemplatePartStringEnd {
        end_loc = t.loc;
        self.string(t.loc).to_string()
      } else {
        return Err(
          t.error(SyntaxErrorType::ExpectedSyntax("template literal continuation")),
        );
      };

      let span_start = type_expr.loc;
      use crate::loc::Loc;
      let span_loc = Loc(span_start.0, t.loc.1);
      spans.push(Node::new(span_loc, TypeTemplateLiteralSpan {
        type_expr,
        literal: literal.clone(),
      }));

      if t.typ == TT::LiteralTemplatePartStringEnd {
        break;
      }
    }

    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let template = Node::new(
      start_loc,
      TypeTemplateLiteral {
        head,
        spans,
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::TemplateLiteralType(template)))
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

    // TypeScript: as clause for key remapping: [K in T as NewK]
    let name_type = if self.consume_if(TT::KeywordAs).is_match() {
      Some(Box::new(self.type_expr(ctx)?))
    } else {
      None
    };

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
    // Optional semicolon or comma before closing brace
    let _ = self.consume_if(TT::Semicolon).is_match() || self.consume_if(TT::Comma).is_match();
    let end_loc = self.peek().loc;
    self.require(TT::BraceClose)?;

    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let mapped = Node::new(
      start_loc,
      TypeMapped {
        readonly_modifier,
        type_parameter,
        constraint: Box::new(constraint),
        name_type,
        optional_modifier,
        type_expr: Box::new(type_expr),
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::MappedType(mapped)))
  }

  /// Parse mapped type body (after opening brace has been consumed)
  fn mapped_type_body(&mut self, ctx: ParseCtx, start_loc: crate::loc::Loc) -> SyntaxResult<Node<TypeExpr>> {
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

    // TypeScript: as clause for key remapping: [K in T as NewK]
    let name_type = if self.consume_if(TT::KeywordAs).is_match() {
      Some(Box::new(self.type_expr(ctx)?))
    } else {
      None
    };

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
    // Optional semicolon or comma before closing brace
    let _ = self.consume_if(TT::Semicolon).is_match() || self.consume_if(TT::Comma).is_match();
    let end_loc = self.peek().loc;
    self.require(TT::BraceClose)?;

    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let mapped = Node::new(
      start_loc,
      TypeMapped {
        readonly_modifier,
        type_parameter,
        constraint: Box::new(constraint),
        name_type,
        optional_modifier,
        type_expr: Box::new(type_expr),
      },
    );
    Ok(Node::new(outer_loc, TypeExpr::MappedType(mapped)))
  }

  /// Parse mapped type member in object type: [K in keyof T]: V
  fn mapped_type_member(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeMember>> {
    let start_loc = self.peek().loc;

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

    // TypeScript: as clause for key remapping: [K in T as NewK]
    let name_type = if self.consume_if(TT::KeywordAs).is_match() {
      Some(Box::new(self.type_expr(ctx)?))
    } else {
      None
    };

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

    // Type annotation is optional in mapped type members
    let (type_expr, end_loc) = if self.consume_if(TT::Colon).is_match() {
      let te = self.type_expr(ctx)?;
      let loc = te.loc;
      (Box::new(te), loc)
    } else {
      // No type annotation - create implicit 'any' type
      use crate::ast::type_expr::TypeAny;
      use crate::loc::Loc;
      let any_loc = Loc(self.peek().loc.0, self.peek().loc.0);
      let any_inner = Node::new(any_loc, TypeAny {});
      let any_type = Node::new(any_loc, TypeExpr::Any(any_inner));
      (Box::new(any_type), any_loc)
    };

    use crate::loc::Loc;
    let outer_loc = Loc(start_loc.0, end_loc.1);
    let mapped = Node::new(
      start_loc,
      TypeMapped {
        readonly_modifier,
        type_parameter,
        constraint: Box::new(constraint),
        name_type,
        optional_modifier,
        type_expr,
      },
    );
    Ok(Node::new(outer_loc, TypeMember::MappedProperty(mapped)))
  }
}
