use crate::{ast::{expr::{pat::{IdPat, Pat}, Expr, ImportExpr, ImportMeta}, import_export::{ExportName, ExportNames, ImportName, ImportNames}, node::Node, stmt::{decl::PatDecl, ExportDefaultExprStmt, ExportListStmt, ImportStmt, Stmt}}, error::{SyntaxErrorType, SyntaxResult}, lex::KEYWORDS_MAPPING, parse::stmt::decl::VarDeclParseMode, token::TT};

use super::{expr::{Asi, lit::normalise_literal_string, pat::is_valid_pattern_identifier}, ParseCtx, Parser};

impl<'a> Parser<'a> {
  /// Parses `target`, `target as alias`, `default as alias`, `"target" as alias`.
  /// For exports, `default` can be used without an alias. For imports, it requires an alias.
  fn import_or_export_name(&mut self, ctx: ParseCtx, is_export: bool) -> SyntaxResult<(String, Node<IdPat>)> {
    let t0 = self.peek();
    #[rustfmt::skip]
    let (target, alias_is_required) = match t0.typ {
      TT::LiteralString => (self.lit_str_val()?, true),
      t if is_valid_pattern_identifier(t, ctx.rules) => (self.consume_as_string(), false),
      // `default` is special: in exports it can be used without alias, but in imports it requires an alias
      TT::KeywordDefault if is_export => (self.consume_as_string(), false),
      // Any other keyword is allowed, but if reserved, an alias must be used.
      t if KEYWORDS_MAPPING.contains_key(&t) => (self.consume_as_string(), true),
      _ => return Err(t0.error(SyntaxErrorType::ExpectedNotFound)),
    };
    let alias = if self.consume_if(TT::KeywordAs).is_match() {
      // In exports, "default" is allowed as an alias name (e.g., export { a as default })
      // In imports, keywords cannot be used as alias names
      let t_alias = self.peek();
      if is_export && t_alias.typ == TT::KeywordDefault {
        self.consume();
        Node::new(t_alias.loc, IdPat { name: "default".to_string() })
      } else {
        self.id_pat(ctx)?
      }
    } else if alias_is_required {
      return Err(t0.error(SyntaxErrorType::ExpectedNotFound));
    } else {
      // Create a "virtual" node representing the alias as if `a as a` was declared instead. (See AST for rationale.)
      Node::new(t0.loc, IdPat { name: target.clone() })
    };
    Ok((target, alias))
  }

  pub fn import_call(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ImportExpr>> {
    self.with_loc(|p| {
      p.require(TT::KeywordImport)?;
      p.require(TT::ParenthesisOpen)?;
      let module = p.expr(ctx, [TT::ParenthesisClose])?;
      p.require(TT::ParenthesisClose)?;
      Ok(ImportExpr { module })
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
  pub fn import_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ImportStmt>> {
    // TODO Ensure top-level.
    self.with_loc(|p| {
      p.require(TT::KeywordImport)?;
      let (default, can_have_names) =
        if p.peek().typ == TT::Identifier {
          let alias = p.id_pat_decl(ctx)?;
          (Some(alias), p.consume_if(TT::Comma).is_match())
        } else {
          (None, true)
        };
      let names = if !can_have_names {
        None
      } else if p.consume_if(TT::Asterisk).is_match() {
        p.require(TT::KeywordAs)?;
        let alias = p.id_pat_decl(ctx)?;
        Some(ImportNames::All(alias))
      } else if p.peek().typ == TT::BraceOpen {
        p.require(TT::BraceOpen)?;
        let names = p.list_with_loc(TT::Comma, TT::BraceClose, |p| {
          let (target, alias) = p.import_or_export_name(ctx, false)?;
          let alias = alias.into_wrapped();
          let alias = alias.wrap(|pat| PatDecl { pat });
          Ok(ImportName { importable: target, alias })
        })?;
        Some(ImportNames::Specific(names))
      } else {
        // No names - side-effect only import like `import "foo"`
        None
      };
      // For side-effect imports (import "foo"), there's no `from` keyword
      if default.is_some() || names.is_some() {
        p.require(TT::KeywordFrom)?;
      }
      let module = p.lit_str_val()?;
      // Allow ASI - semicolon not required at EOF or before line terminator
      let t = p.peek();
      if t.typ != TT::EOF && !t.preceded_by_line_terminator {
        p.require(TT::Semicolon)?;
      } else {
        p.consume_if(TT::Semicolon);
      }
      Ok(ImportStmt {
        default,
        module,
        names,
      })
    })
  }

  pub fn export_list_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ExportListStmt>> {
    self.with_loc(|p| {
      p.require(TT::KeywordExport)?;
      let t = p.consume();
      let stmt = match t.typ {
        TT::BraceOpen => {
          let names = p.list_with_loc(
            TT::Comma,
            TT::BraceClose,
            |p| p.import_or_export_name(ctx, true)
              .map(|(target, alias)| ExportName { exportable: target, alias }),
          )?;
          let from = p.consume_if(TT::KeywordFrom).and_then(|| p.lit_str_val())?;
          ExportListStmt {
            names: ExportNames::Specific(names),
            from,
          }
        }
        TT::Asterisk => {
          let alias = p.consume_if(TT::KeywordAs).and_then(|| p.id_pat(ctx))?;
          p.require(TT::KeywordFrom)?;
          let from = p.lit_str_val()?;
          ExportListStmt {
            names: ExportNames::All(alias),
            from: Some(from),
          }
        }
        _ => return Err(t.error(SyntaxErrorType::ExpectedNotFound)),
      };
      Ok(stmt)
    })
  }

  pub fn export_default_expr_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<ExportDefaultExprStmt>> {
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
    // TODO Ensure top-level.
    let [t0, t1, t2] = self.peek_n();
    // The first token should always be `export`, but it will be parsed in the subroutines and not here.
    assert_eq!(t0.typ, TT::KeywordExport);
    #[rustfmt::skip]
    let stmt: Node<Stmt> = match (t1.typ, t2.typ) {
      // `class` and `function` are treated as statements that are hoisted, not expressions; however, they can be unnamed, which gives them the name `default`.
      (TT::KeywordDefault, TT::KeywordAsync | TT::KeywordFunction) | (TT::KeywordAsync | TT::KeywordFunction, _) => self.func_decl(ctx)?.into_wrapped(),
      (TT::KeywordDefault, TT::KeywordClass) | (TT::KeywordClass, _) => self.class_decl(ctx)?.into_wrapped(),
      (TT::KeywordDefault, _) => self.export_default_expr_stmt(ctx)?.into_wrapped(),
      (TT::KeywordVar | TT::KeywordLet | TT::KeywordConst, _) => self.var_decl(ctx, VarDeclParseMode::Asi)?.into_wrapped(),
      (TT::BraceOpen | TT::Asterisk, _) => self.export_list_stmt(ctx)?.into_wrapped(),
      _ => return Err(t0.error(SyntaxErrorType::ExpectedSyntax("exportable"))),
    };
    Ok(stmt)
  }
}
