use super::expr::pat::is_valid_pattern_identifier;
use super::expr::Asi;
use super::ParseCtx;
use super::Parser;
use super::ParserCheckpoint;
use crate::ast::expr::pat::IdPat;
use crate::ast::expr::pat::Pat;
use crate::ast::expr::ImportExpr;
use crate::ast::expr::ImportMeta;
use crate::ast::import_export::ExportName;
use crate::ast::import_export::ExportNames;
use crate::ast::import_export::ImportName;
use crate::ast::import_export::ImportNames;
use crate::ast::import_export::ModuleExportImportName;
use crate::ast::node::Node;
use crate::ast::stmt::decl::PatDecl;
use crate::ast::stmt::ExportDefaultExprStmt;
use crate::ast::stmt::ExportListStmt;
use crate::ast::stmt::ImportStmt;
use crate::ast::stmt::Stmt;
use crate::ast::ts_stmt::ImportEqualsDecl;
use crate::ast::ts_stmt::ImportEqualsRhs;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::KEYWORDS_MAPPING;
use crate::parse::stmt::decl::VarDeclParseMode;
use crate::token::TT;

impl<'a> Parser<'a> {
  fn starts_with_type_only_import(&mut self, ctx: ParseCtx) -> bool {
    let [t0, t1, t2] = self.peek_n::<3>();
    if t0.typ != TT::KeywordType {
      return false;
    }
    if matches!(t1.typ, TT::BraceOpen | TT::Asterisk) {
      return true;
    }
    if !is_valid_pattern_identifier(t1.typ, ctx.rules) {
      return false;
    }
    matches!(t2.typ, TT::Comma | TT::KeywordFrom | TT::Equals)
  }

  fn starts_with_type_only_named_specifier(&mut self) -> bool {
    let [t0, t1] = self.peek_n::<2>();
    if t0.typ != TT::KeywordType {
      return false;
    }
    !matches!(t1.typ, TT::Comma | TT::BraceClose | TT::KeywordAs)
  }

  /// Parses `target`, `target as alias`, `default as alias`, `"target" as alias`.
  ///
  /// Note: "arbitrary module namespace identifiers" (string-literal module export names)
  /// apply to the imported/exported *name* positions, not local bindings. TypeScript
  /// still requires local import bindings to be identifiers, so string-literal
  /// aliases are only accepted in export positions (where the alias is an
  /// `IdentifierName`/string-literal, not a binding identifier).
  fn import_or_export_name(
    &mut self,
    ctx: ParseCtx,
    is_export: bool,
  ) -> SyntaxResult<(ModuleExportImportName, Node<IdPat>)> {
    let t0 = self.peek();
    #[rustfmt::skip]
    let (target, alias_is_required) = match t0.typ {
      TT::LiteralString => (ModuleExportImportName::Str(self.lit_str_val()?), true),
      t if is_valid_pattern_identifier(t, ctx.rules) => (ModuleExportImportName::Ident(self.consume_as_string()), false),
      // `default` is special: in exports it can be used without alias, but in imports it requires an alias
      TT::KeywordDefault if is_export => (ModuleExportImportName::Ident(self.consume_as_string()), false),
      // Any other keyword is allowed, but if reserved, an alias must be used.
      t if KEYWORDS_MAPPING.contains_key(&t) => (ModuleExportImportName::Ident(self.consume_as_string()), true),
      _ => return Err(t0.error(SyntaxErrorType::ExpectedNotFound)),
    };
    let alias = if self.consume_if(TT::KeywordAs).is_match() {
      // In exports, "default" is allowed as an alias name (e.g., export { a as default })
      // In imports, keywords cannot be used as alias names
      let t_alias = self.peek();
      if is_export && t_alias.typ == TT::KeywordDefault {
        self.consume();
        Node::new(
          t_alias.loc,
          IdPat {
            name: "default".to_string(),
          },
        )
      } else if is_export && t_alias.typ == TT::LiteralString {
        // ES2022: arbitrary module namespace identifiers - allow string literals
        // for *exported* names.
        let name = self.lit_str_val()?;
        Node::new(t_alias.loc, IdPat { name })
      } else {
        self.id_pat(ctx)?
      }
    } else if alias_is_required {
      return Err(t0.error(SyntaxErrorType::ExpectedNotFound));
    } else {
      // Create a "virtual" node representing the alias as if `a as a` was declared instead. (See AST for rationale.)
      Node::new(
        t0.loc,
        IdPat {
          name: target.as_str().to_string(),
        },
      )
    };
    Ok((target, alias))
  }

  pub fn import_call(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ImportExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordImport)?;
      p.require(TT::ParenthesisOpen)?;
      let module = p.expr(ctx, [TT::Comma, TT::ParenthesisClose])?;

      // Import attributes: import("module", { with: { type: "json" } })
      let attributes = if p.consume_if(TT::Comma).is_match() {
        // Allow trailing comma: import("module",)
        if p.peek().typ == TT::ParenthesisClose {
          None
        } else {
          Some(p.expr(ctx, [TT::ParenthesisClose])?)
        }
      } else {
        None
      };

      p.require(TT::ParenthesisClose)?;
      Ok(ImportExpr { module, attributes })
    })
  }

  pub fn import_meta(&mut self) -> SyntaxResult<Node<ImportMeta>> {
    self.with_loc(|p| {
      p.require(TT::KeywordImport)?;
      p.require(TT::Dot)?;
      let prop = p.require(TT::Identifier)?;
      if p.str(prop.loc) != "meta" {
        return Err(prop.error(SyntaxErrorType::ExpectedSyntax("`meta` property")));
      };
      Ok(ImportMeta {})
    })
  }

  /// Parses an import statement like:
  /// - `import "module"`
  /// - `import * as b from "module"`
  /// - `import {"b" as c, d, e as f, default as g} from "module"`
  /// - `import a from "module"`
  /// - `import a, * as b from "module"`
  /// - `import a, {"b" as c, d, e as f, default as g} from "module"`
  /// - TypeScript import equals: `import a = require("module")` or `import a = Foo.Bar`
  pub fn import_stmt(&mut self, ctx: ParseCtx, export: bool) -> SyntaxResult<Node<Stmt>> {
    if !ctx.top_level || ctx.in_namespace {
      return Err(self.peek().error(SyntaxErrorType::ExpectedSyntax(
        "import declarations must be at top level",
      )));
    }
    let start = self.checkpoint();
    self.require(TT::KeywordImport)?;

    // TypeScript: import type
    let type_only = if self.starts_with_type_only_import(ctx) {
      self.consume();
      true
    } else {
      false
    };
    let (default, can_have_names) = if is_valid_pattern_identifier(self.peek().typ, ctx.rules) {
      let alias = self.id_pat_decl(ctx)?;

      // TypeScript: import equals: import id = require("module") or import id = EntityName
      if self.peek().typ == TT::Equals {
        self.consume(); // =
        return self.import_equals_decl(export, type_only, alias, start);
      }

      (Some(alias), self.consume_if(TT::Comma).is_match())
    } else {
      (None, true)
    };
    let names = if !can_have_names {
      None
    } else if self.consume_if(TT::Asterisk).is_match() {
      self.require(TT::KeywordAs)?;
      let alias = self.id_pat_decl(ctx)?;
      Some(ImportNames::All(alias))
    } else if self.peek().typ == TT::BraceOpen {
      self.require(TT::BraceOpen)?;
      let names = self.list_with_loc(TT::Comma, TT::BraceClose, |p| {
        // TypeScript: per-specifier type-only import
        let type_only = if p.starts_with_type_only_named_specifier() {
          p.consume();
          true
        } else {
          false
        };
        let (target, alias) = p.import_or_export_name(ctx, false)?;
        let alias = alias.into_wrapped();
        let alias = alias.wrap(|pat| PatDecl { pat });
        Ok(ImportName {
          type_only,
          importable: target,
          alias,
        })
      })?;
      Some(ImportNames::Specific(names))
    } else {
      // No names - side-effect only import like `import "foo"`
      None
    };
    // For side-effect imports (import "foo"), there's no `from` keyword
    if default.is_some() || names.is_some() {
      self.require(TT::KeywordFrom)?;
    }
    let module = self.lit_str_val()?;

    // Import attributes: import ... from "module" with { type: "json" }
    let attributes = if self.consume_if(TT::KeywordWith).is_match() {
      Some(self.expr(ctx, [])?)
    } else {
      None
    };

    // Allow ASI - semicolon not required at EOF or before line terminator
    let t = self.peek();
    if t.typ != TT::EOF && !t.preceded_by_line_terminator {
      self.require(TT::Semicolon)?;
    } else {
      let _ = self.consume_if(TT::Semicolon);
    }

    let loc = self.since_checkpoint(&start);
    let import_stmt = Node::new(
      loc,
      ImportStmt {
        type_only,
        default,
        module,
        names,
        attributes,
      },
    );
    Ok(import_stmt.into_wrapped())
  }

  fn import_equals_decl(
    &mut self,
    export: bool,
    type_only: bool,
    alias: Node<PatDecl>,
    start: ParserCheckpoint,
  ) -> SyntaxResult<Node<Stmt>> {
    let name = match alias.stx.pat.stx.as_ref() {
      Pat::Id(id) => id.stx.name.clone(),
      _ => return Err(alias.error(SyntaxErrorType::ExpectedSyntax("identifier"))),
    };

    if self.peek().typ != TT::Identifier {
      return Err(self.peek().error(SyntaxErrorType::ExpectedNotFound));
    }

    let first_name = self.consume_as_string();
    let rhs = if first_name == "require" && self.peek().typ == TT::ParenthesisOpen {
      self.require(TT::ParenthesisOpen)?;
      let module = self.lit_str_val()?;
      self.require(TT::ParenthesisClose)?;
      ImportEqualsRhs::Require { module }
    } else {
      // import id = EntityName (e.g., import A = B.C.D)
      // Consume dotted name: identifier(.identifier)*
      let mut path = vec![first_name];
      while self.peek().typ == TT::Dot {
        self.consume(); // .
        let next = self.peek();
        if next.typ == TT::Identifier || KEYWORDS_MAPPING.contains_key(&next.typ) {
          path.push(self.consume_as_string());
        } else {
          // Error recovery: allow incomplete dotted names
          break;
        }
      }
      ImportEqualsRhs::EntityName { path }
    };

    // Allow ASI
    let t = self.peek();
    if t.typ != TT::EOF && !t.preceded_by_line_terminator {
      let _ = self.consume_if(TT::Semicolon);
    }

    let loc = self.since_checkpoint(&start);
    Ok(
      Node::new(
        loc,
        ImportEqualsDecl {
          export,
          type_only,
          name,
          rhs,
        },
      )
      .into_wrapped(),
    )
  }

  pub fn export_list_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ExportListStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordExport)?;
      // TypeScript: export type
      let type_only = p.consume_if(TT::KeywordType).is_match();
      let t = p.consume();
      let (names, from) = match t.typ {
        TT::BraceOpen => {
          let names = p.list_with_loc(TT::Comma, TT::BraceClose, |p| {
            // TypeScript: per-specifier type-only export
            let type_only = if p.starts_with_type_only_named_specifier() {
              p.consume();
              true
            } else {
              false
            };
            p.import_or_export_name(ctx, true)
              .map(|(target, alias)| ExportName {
                type_only,
                exportable: target,
                alias,
              })
          })?;
          let from = p.consume_if(TT::KeywordFrom).and_then(|| p.lit_str_val())?;
          if from.is_none() {
            // Local exports must refer to local bindings, which cannot be string
            // literals. Only re-exports (`export { ... } from "mod"`) may use
            // string-literal module export names on the left-hand side.
            for name in &names {
              if matches!(name.stx.exportable, ModuleExportImportName::Str(_)) {
                return Err(name.error(SyntaxErrorType::ExpectedSyntax("identifier")));
              }
            }
          }
          (ExportNames::Specific(names), from)
        }
        TT::Asterisk => {
          let alias = p.consume_if(TT::KeywordAs).and_then(|| {
            // ES2022: arbitrary module namespace identifiers - allow string literals
            let t = p.peek();
            if t.typ == TT::KeywordDefault {
              // `default` is allowed as an exported name (e.g. `export * as default from "mod"`),
              // but it is not a valid pattern identifier so we need to special-case it here.
              p.consume();
              Ok(Node::new(
                t.loc,
                IdPat {
                  name: "default".to_string(),
                },
              ))
            } else if t.typ == TT::LiteralString {
              let name = p.lit_str_val()?;
              Ok(Node::new(t.loc, IdPat { name }))
            } else {
              p.id_pat(ctx)
            }
          })?;
          p.require(TT::KeywordFrom)?;
          let from = p.lit_str_val()?;
          (ExportNames::All(alias), Some(from))
        }
        _ => return Err(t.error(SyntaxErrorType::ExpectedNotFound)),
      };

      // Export attributes: export ... from "module" with { type: "json" }
      let attributes = if p.consume_if(TT::KeywordWith).is_match() {
        Some(p.expr(ctx, [])?)
      } else {
        None
      };

      Ok(ExportListStmt {
        type_only,
        names,
        from,
        attributes,
      })
    })
  }

  pub fn export_default_expr_stmt(
    &mut self,
    ctx: ParseCtx,
  ) -> SyntaxResult<Node<ExportDefaultExprStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordExport)?;
      p.require(TT::KeywordDefault)?;
      let mut asi = Asi::can();
      let expression = p.expr_with_asi(ctx, [TT::Semicolon], &mut asi)?;
      Ok(ExportDefaultExprStmt { expression })
    })
  }

  // https://tc39.es/ecma262/#sec-exports
  // https://jakearchibald.com/2021/export-default-thing-vs-thing-as-default/
  pub fn export_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    if !ctx.top_level {
      return Err(self.peek().error(SyntaxErrorType::ExpectedSyntax(
        "export declarations must be at top level",
      )));
    }
    let [t0, t1, t2] = self.peek_n();
    // The first token should always be `export`, but it will be parsed in the subroutines and not here.
    assert_eq!(t0.typ, TT::KeywordExport);

    // TypeScript: export = expression (export assignment)
    if t1.typ == TT::Equals {
      return self
        .with_loc(|p| {
          p.require(TT::KeywordExport)?;
          p.require(TT::Equals)?;
          let expression = p.expr_with_asi(ctx, [TT::Semicolon], &mut super::expr::Asi::can())?;
          // Allow ASI
          let t = p.peek();
          if t.typ != TT::EOF && !t.preceded_by_line_terminator {
            p.require(TT::Semicolon)?;
          } else {
            let _ = p.consume_if(TT::Semicolon);
          }
          Ok(crate::ast::ts_stmt::ExportAssignmentDecl { expression })
        })
        .map(|node| node.into_wrapped());
    }

    // TypeScript: export as namespace Foo;
    if t1.typ == TT::KeywordAs && t2.typ == TT::KeywordNamespace {
      return self
        .with_loc(|p| {
          p.require(TT::KeywordExport)?;
          p.require(TT::KeywordAs)?;
          p.require(TT::KeywordNamespace)?;
          let name = p.require_identifier()?;
          let t = p.peek();
          if t.typ != TT::EOF && !t.preceded_by_line_terminator {
            let _ = p.consume_if(TT::Semicolon);
          }
          Ok(crate::ast::ts_stmt::ExportAsNamespaceDecl { name })
        })
        .map(|node| node.into_wrapped());
    }

    #[rustfmt::skip]
    let stmt: Node<Stmt> = match (t1.typ, t2.typ) {
      // `class` and `function` are treated as statements that are hoisted, not expressions; however, they can be unnamed, which gives them the name `default`.
      (TT::KeywordDefault, TT::KeywordAsync | TT::KeywordFunction) | (TT::KeywordAsync | TT::KeywordFunction, _) => self.func_decl(ctx)?.into_wrapped(),
      (TT::KeywordDefault, TT::KeywordClass) | (TT::KeywordClass | TT::KeywordAbstract, _) => self.class_decl(ctx)?.into_wrapped(),
      (TT::KeywordDefault, _) => self.export_default_expr_stmt(ctx)?.into_wrapped(),
      (TT::KeywordVar | TT::KeywordLet | TT::KeywordConst | TT::KeywordUsing | TT::KeywordAwait, _) => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_wrapped(),
      (TT::BraceOpen | TT::Asterisk, _) => self.export_list_stmt(ctx)?.into_wrapped(),
      // TypeScript: export type { ... } or export type * from "module" (type-only re-exports)
      (TT::KeywordType, TT::BraceOpen | TT::Asterisk) => self.export_list_stmt(ctx)?.into_wrapped(),
      // TypeScript: export import a = A (exported import alias)
      (TT::KeywordImport, _) => {
        self.consume(); // export
        self.import_stmt(ctx, true)?
      },
      // TypeScript: export interface, export type, export enum, export namespace, export declare
      (TT::KeywordInterface, _) => {
        self.consume(); // export
        self.interface_decl(ctx, true, false)?.into_wrapped()
      },
      (TT::KeywordType, _) => {
        self.consume(); // export
        self.type_alias_decl(ctx, true, false)?.into_wrapped()
      },
      (TT::KeywordEnum, _) => {
        self.consume(); // export
        self.enum_decl(ctx, true, false, false)?.into_wrapped()
      },
      (TT::KeywordNamespace, _) => {
        self.consume(); // export
        self.namespace_decl(ctx, true, false)?.into_wrapped()
      },
      // TypeScript: export @decorator class (decorator on exported class)
      // Error recovery: allow decorators after export
      (TT::At, _) => {
        self.consume(); // export
        // The class_decl function will handle the decorators
        self.class_decl(ctx)?.into_wrapped()
      },
      (TT::KeywordDeclare, _) => {
        // For "export declare", we need to handle it specially to pass export=true
        self.consume(); // export
        self.consume(); // declare
        let t = self.peek().typ;
        match t {
          TT::KeywordInterface => self.interface_decl(ctx, true, true)?.into_wrapped(),
          TT::KeywordType => self.type_alias_decl(ctx, true, true)?.into_wrapped(),
          TT::KeywordEnum => self.enum_decl(ctx, true, true, false)?.into_wrapped(),
          TT::KeywordNamespace | TT::KeywordModule => {
            // Check if it's a string module (declare module "foo")
            if t == TT::KeywordModule && self.peek_n::<2>()[1].typ == TT::LiteralString {
              self.module_decl(ctx, true, true)?.into_wrapped()
            } else {
              self.namespace_decl(ctx, true, true)?.into_wrapped()
            }
          },
          TT::KeywordClass => self.class_decl(ctx)?.into_wrapped(),
          TT::KeywordFunction => self.func_decl(ctx)?.into_wrapped(),
          TT::KeywordAsync if self.peek_n::<2>()[1].typ == TT::KeywordFunction => {
            self.consume(); // consume 'async'
            self.func_decl(ctx)?.into_wrapped()
          }
          TT::KeywordConst if self.peek_n::<2>()[1].typ == TT::KeywordEnum => {
            self.consume(); // consume 'const'
            self.enum_decl(ctx, true, true, true)?.into_wrapped()
          }
          TT::KeywordAbstract if self.peek_n::<2>()[1].typ == TT::KeywordClass => {
            self.consume(); // consume 'abstract'
            self.class_decl(ctx)?.into_wrapped()
          }
          TT::KeywordVar | TT::KeywordLet | TT::KeywordConst | TT::KeywordUsing | TT::KeywordAwait => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_wrapped(),
          _ => return Err(self.peek().error(SyntaxErrorType::ExpectedSyntax("declaration after export declare"))),
        }
      },
      _ => return Err(t0.error(SyntaxErrorType::ExpectedSyntax("exportable"))),
    };
    Ok(stmt)
  }
}

#[cfg(test)]
mod tests {
  use crate::{parse_with_options, Dialect, ParseOptions, SourceType};

  #[test]
  fn import_default_named_specifier_requires_alias() {
    let opts = ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    };
    assert!(parse_with_options("import { default } from \"mod\";", opts).is_err());
  }
}
