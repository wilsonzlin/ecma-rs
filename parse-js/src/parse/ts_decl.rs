use super::{ParseCtx, Parser};
use crate::ast::expr::Expr;
use crate::ast::node::Node;
use crate::ast::stmt::Stmt;
use crate::ast::ts_stmt::*;
use crate::ast::type_expr::TypeExpr;
use crate::error::{SyntaxErrorType, SyntaxResult};
use crate::token::TT;

impl<'a> Parser<'a> {
  /// Parse interface declaration: interface Foo<T> extends Bar { }
  pub fn interface_decl(&mut self, ctx: ParseCtx, export: bool, declare: bool) -> SyntaxResult<Node<InterfaceDecl>> {
    self.with_loc(|p| {
      p.require(TT::KeywordInterface)?;
      // TypeScript allows type keywords as interface names in error cases
      let name = p.require_identifier_or_ts_keyword()?;

      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      let mut extends = Vec::new();
      if p.consume_if(TT::KeywordExtends).is_match() {
        loop {
          extends.push(p.type_expr(ctx)?);
          if !p.consume_if(TT::Comma).is_match() {
            break;
          }
        }
      }

      p.require(TT::BraceOpen)?;
      let members = p.type_members(ctx)?;
      p.require(TT::BraceClose)?;

      Ok(InterfaceDecl {
        export,
        declare,
        name,
        type_parameters,
        extends,
        members,
      })
    })
  }

  /// Parse type alias: type Foo<T> = Bar<T>
  pub fn type_alias_decl(&mut self, ctx: ParseCtx, export: bool, declare: bool) -> SyntaxResult<Node<TypeAliasDecl>> {
    self.with_loc(|p| {
      p.require(TT::KeywordType)?;
      // TypeScript allows type keywords as type alias names in error cases
      let name = p.require_identifier_or_ts_keyword()?;

      let type_parameters = if p.peek().typ == TT::ChevronLeft && p.is_start_of_type_arguments() {
        Some(p.type_parameters(ctx)?)
      } else {
        None
      };

      p.require(TT::Equals)?;
      let type_expr = p.type_expr(ctx)?;

      // Optional semicolon
      p.consume_if(TT::Semicolon);

      Ok(TypeAliasDecl {
        export,
        declare,
        name,
        type_parameters,
        type_expr,
      })
    })
  }

  /// Parse enum declaration: enum Color { Red, Green, Blue }
  pub fn enum_decl(&mut self, ctx: ParseCtx, export: bool, declare: bool, const_: bool) -> SyntaxResult<Node<EnumDecl>> {
    self.with_loc(|p| {
      p.require(TT::KeywordEnum)?;
      // TypeScript allows type keywords as enum names in error cases
      let name = p.require_identifier_or_ts_keyword()?;

      p.require(TT::BraceOpen)?;
      let members = p.list_with_loc(TT::Comma, TT::BraceClose, |p| p.enum_member(ctx))?;
      // BraceClose is already consumed by list_with_loc

      Ok(EnumDecl {
        export,
        declare,
        const_,
        name,
        members,
      })
    })
  }

  /// Parse enum member: Red = 1, Green = "green"
  fn enum_member(&mut self, ctx: ParseCtx) -> SyntaxResult<EnumMember> {
    // TypeScript allows string literals and numeric literals as enum member names
    let name = match self.peek().typ {
      TT::LiteralString => self.lit_str_val()?,
      TT::LiteralNumber => {
        let t = self.consume();
        self.str(t.loc).to_string()
      }
      _ => self.require_identifier()?,
    };

    let initializer = if self.consume_if(TT::Equals).is_match() {
      Some(self.expr(ctx, [TT::Comma, TT::BraceClose])?)
    } else {
      None
    };

    Ok(EnumMember { name, initializer })
  }

  /// Parse namespace declaration: namespace Foo { }
  pub fn namespace_decl(&mut self, ctx: ParseCtx, export: bool, declare: bool) -> SyntaxResult<Node<NamespaceDecl>> {
    self.namespace_decl_impl(ctx, export, declare, false)
  }

  /// Parse namespace declaration with optional keyword check
  /// For dotted paths like `namespace A.B.C`, we don't require the keyword before B and C
  fn namespace_decl_impl(&mut self, ctx: ParseCtx, export: bool, declare: bool, skip_keyword: bool) -> SyntaxResult<Node<NamespaceDecl>> {
    self.with_loc(|p| {
      // Accept both 'namespace' and 'module' keywords (unless this is part of a dotted path)
      if !skip_keyword {
        if !p.consume_if(TT::KeywordNamespace).is_match() {
          p.require(TT::KeywordModule)?;
        }
      }

      // TypeScript: Allow reserved keywords in dotted namespace paths
      // e.g., `declare namespace chrome.debugger {}` or `declare namespace test.class {}`
      // This is permissive parsing - semantic errors will be caught by type checker
      // Also allow keywords as namespace names for error recovery (e.g., `namespace debugger {}`)
      let t = p.consume();
      let name = if t.typ == TT::Identifier {
        p.string(t.loc)
      } else if crate::lex::KEYWORDS_MAPPING.contains_key(&t.typ) {
        // Allow any keyword as namespace name for error recovery
        p.string(t.loc)
      } else {
        return Err(t.error(SyntaxErrorType::ExpectedSyntax("identifier")));
      };

      // Check for nested namespace: namespace A.B { }
      let body = if p.consume_if(TT::Dot).is_match() {
        // For dotted paths, skip keyword check in recursive calls
        let nested = p.namespace_decl_impl(ctx, false, false, true)?;
        NamespaceBody::Namespace(Box::new(nested))
      } else {
        p.require(TT::BraceOpen)?;
        let statements = p.stmts(ctx, TT::BraceClose)?;
        p.require(TT::BraceClose)?;
        NamespaceBody::Block(statements)
      };

      Ok(NamespaceDecl {
        export,
        declare,
        name,
        body,
      })
    })
  }

  /// Parse module declaration: module "foo" { } or declare module "foo" { }
  pub fn module_decl(&mut self, ctx: ParseCtx, export: bool, declare: bool) -> SyntaxResult<Node<ModuleDecl>> {
    self.with_loc(|p| {
      p.require(TT::KeywordModule)?;

      let name = if p.peek().typ == TT::LiteralString {
        ModuleName::String(p.lit_str_val()?)
      } else {
        ModuleName::Identifier(p.require_identifier()?)
      };

      let body = if p.peek().typ == TT::BraceOpen {
        p.require(TT::BraceOpen)?;
        let statements = p.stmts(ctx, TT::BraceClose)?;
        p.require(TT::BraceClose)?;
        Some(statements)
      } else {
        // Ambient module can omit body
        None
      };

      Ok(ModuleDecl {
        export,
        declare,
        name,
        body,
      })
    })
  }

  /// Parse global augmentation: declare global { }
  pub fn global_decl(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<GlobalDecl>> {
    self.with_loc(|p| {
      // 'declare' already consumed
      // Consume 'global' identifier
      p.require(TT::Identifier)?;

      p.require(TT::BraceOpen)?;
      let body = p.stmts(ctx, TT::BraceClose)?;
      p.require(TT::BraceClose)?;

      Ok(GlobalDecl { body })
    })
  }

  /// Check if next tokens look like a TypeScript declaration
  pub fn is_typescript_declaration(&mut self) -> bool {
    matches!(
      self.peek().typ,
      TT::KeywordInterface
        | TT::KeywordType
        | TT::KeywordNamespace
        | TT::KeywordModule
        | TT::KeywordEnum
        | TT::KeywordDeclare
    )
  }

  /// Parse decorator: @decorator or @decorator(args)
  pub fn decorator(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<crate::ast::expr::Decorator>> {
    self.with_loc(|p| {
      p.require(TT::At)?;
      // Parse decorator expression with terminators for class member keywords
      // This prevents the decorator from consuming modifiers and member syntax
      use crate::parse::expr::Asi;
      use crate::token::TT;
      let mut asi = Asi::can();
      let expression = p.expr_with_min_prec(ctx, 1, [
        TT::KeywordStatic, TT::KeywordGet, TT::KeywordSet, TT::KeywordAsync,
        TT::KeywordPublic, TT::KeywordPrivate, TT::KeywordProtected,
        TT::KeywordAbstract, TT::KeywordReadonly, TT::KeywordOverride,
        TT::Asterisk, TT::At, TT::BracketOpen, TT::BraceClose, TT::Identifier
      ], &mut asi)?;
      Ok(crate::ast::expr::Decorator { expression })
    })
  }

  /// Parse decorators list
  pub fn decorators(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<Node<crate::ast::expr::Decorator>>> {
    let mut decorators = Vec::new();
    while self.peek().typ == TT::At {
      decorators.push(self.decorator(ctx)?);
    }
    Ok(decorators)
  }
}
