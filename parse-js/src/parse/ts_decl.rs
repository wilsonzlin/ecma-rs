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
      let name = p.require_identifier()?;

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
      let name = p.require_identifier()?;

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
      let name = p.require_identifier()?;

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
    let name = self.require_identifier()?;

    let initializer = if self.consume_if(TT::Equals).is_match() {
      Some(self.expr(ctx, [TT::Comma, TT::BraceClose])?)
    } else {
      None
    };

    Ok(EnumMember { name, initializer })
  }

  /// Parse namespace declaration: namespace Foo { }
  pub fn namespace_decl(&mut self, ctx: ParseCtx, export: bool, declare: bool) -> SyntaxResult<Node<NamespaceDecl>> {
    self.with_loc(|p| {
      // Accept both 'namespace' and 'module' keywords
      if !p.consume_if(TT::KeywordNamespace).is_match() {
        p.require(TT::KeywordModule)?;
      }

      let name = p.require_identifier()?;

      // Check for nested namespace: namespace A.B { }
      let body = if p.consume_if(TT::Dot).is_match() {
        let nested = p.namespace_decl(ctx, false, false)?;
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
      p.require(TT::KeywordModule)?; // Actually uses 'global' but we need a keyword for it
      // For now, parse as a special module

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
      let expression = p.expr(ctx, [])?;
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
