use crate::ast::expr::jsx::JsxAttr;
use crate::ast::expr::jsx::JsxAttrVal;
use crate::ast::expr::jsx::JsxElem;
use crate::ast::expr::jsx::JsxElemChild;
use crate::ast::expr::jsx::JsxElemName;
use crate::ast::expr::jsx::JsxExprContainer;
use crate::ast::expr::jsx::JsxMemberExpr;
use crate::ast::expr::jsx::JsxName;
use crate::ast::expr::jsx::JsxSpreadAttr;
use crate::ast::expr::jsx::JsxText;
use crate::ast::expr::IdExpr;
use crate::ast::node::Node;
use crate::error::SyntaxErrorType;
use crate::error::SyntaxResult;
use crate::lex::LexMode;
use crate::parse::ParseCtx;
use crate::parse::Parser;
use crate::token::TT;

impl<'a> Parser<'a> {
  /// Gets a token that can be used as a JSX name (attribute name, tag name part, etc.).
  /// JSX allows any identifier including JavaScript keywords.
  fn jsx_name_token(&mut self) -> SyntaxResult<crate::token::Token> {
    let tok = self.peek_with_mode(LexMode::JsxTag);
    // Accept identifiers and any keywords as JSX names
    if tok.typ == TT::Identifier || tok.typ.is_keyword() {
      self.consume_with_mode(LexMode::JsxTag);
      return Ok(tok);
    }

    // Error recovery: treat unexpected tokens as synthetic identifiers to keep parsing.
    self.consume_with_mode(LexMode::JsxTag);
    Ok(crate::token::Token {
      typ: TT::Identifier,
      loc: tok.loc,
      preceded_by_line_terminator: tok.preceded_by_line_terminator,
    })
  }

  pub fn jsx_name(&mut self) -> SyntaxResult<Node<JsxName>> {
    self.with_loc(|p| {
      let start = p.jsx_name_token()?;
      Ok(if p.consume_if(TT::Colon).is_match() {
        let name = p.jsx_name_token()?;
        JsxName {
          namespace: Some(p.string(start.loc)),
          name: p.string(name.loc),
        }
      } else {
        JsxName {
          namespace: None,
          name: p.string(start.loc),
        }
      })
    })
  }

  /// Parses a JSX element name like `div`, `ab-cd`, `MyComponent`, `a.b.c`, or `ns:div`.
  pub fn jsx_elem_name(&mut self) -> SyntaxResult<Option<JsxElemName>> {
    // Fragment: <>
    if self.peek_with_mode(LexMode::JsxTag).typ == TT::ChevronRight {
      return Ok(None);
    }
    let start_tok = self.jsx_name_token()?;
    let mut base_name = self.string(start_tok.loc);
    let mut base_loc = start_tok.loc;
    let mut path = Vec::<String>::new();

    if self
      .maybe_consume_with_mode(TT::Colon, LexMode::JsxTag)
      .is_match()
    {
      let name = self.jsx_name_token()?;
      base_name = format!("{}:{}", base_name, self.string(name.loc));
      base_loc += name.loc;
    }

    // Member expression after identifier or namespaced name: ns:component.path
    if !self.bytes(base_loc).contains('-') {
      while self
        .maybe_consume_with_mode(TT::Dot, LexMode::JsxTag)
        .is_match()
      {
        let part = self.require_with_mode(TT::Identifier, LexMode::JsxTag)?;
        base_loc += part.loc;
        path.push(self.string(part.loc));
      }
    }

    if !path.is_empty() {
      return Ok(Some(JsxElemName::Member(Node::new(
        base_loc,
        JsxMemberExpr {
          base: Node::new(base_loc, IdExpr { name: base_name }),
          path,
        },
      ))));
    }

    let is_identifier_component = base_name
      .chars()
      .next()
      .is_some_and(|c| !c.is_ascii_lowercase())
      && !base_name.contains('-')
      && !base_name.contains(':');
    let name = if is_identifier_component {
      JsxElemName::Id(Node::new(base_loc, IdExpr { name: base_name }))
    } else {
      let (namespace, name) = if let Some((ns, name)) = base_name.split_once(':') {
        (Some(ns.to_string()), name.to_string())
      } else {
        (None, base_name)
      };
      JsxElemName::Name(Node::new(base_loc, JsxName { namespace, name }))
    };
    Ok(Some(name))
  }

  /// Parses a JSX attribute value (comes after the equals sign).
  pub fn jsx_attr_val(&mut self, ctx: ParseCtx) -> SyntaxResult<JsxAttrVal> {
    let next = self.peek_with_mode(LexMode::JsxTag);
    if matches!(next.typ, TT::Slash | TT::ChevronRight) {
      return Err(next.error(SyntaxErrorType::ExpectedSyntax("JSX attribute value")));
    }

    // Attr values can be an element/fragment directly e.g. `a=<div/>`, or an expression in braces, or a string
    let val = if self.peek().typ == TT::ChevronLeft {
      // JSX element or fragment as attribute value
      let elem = self.jsx_elem(ctx)?;
      JsxAttrVal::Element(elem)
    } else if self.consume_if(TT::BraceOpen).is_match() {
      // Check for empty expression: <div prop={} />
      if self.peek().typ == TT::BraceClose {
        // Empty expression - create empty container
        let loc = self.peek().loc;
        self.consume(); // consume }
                        // For empty expressions, we still need a valid expression node
                        // Use an empty identifier or similar placeholder
        use crate::ast::expr::Expr;
        use crate::ast::expr::IdExpr;
        use crate::ast::node::Node;
        use crate::loc::Loc;
        let empty_expr = Node::new(
          Loc(loc.0, loc.0),
          Expr::Id(Node::new(
            Loc(loc.0, loc.0),
            IdExpr {
              name: String::new(),
            },
          )),
        );
        let expr = Node::new(
          loc,
          JsxExprContainer {
            spread: false,
            value: empty_expr,
          },
        );
        JsxAttrVal::Expression(expr)
      } else if self.peek().typ == TT::DotDotDot {
        // Error recovery: allow `{...expr}` in attribute values even though it's invalid
        self.consume(); // ...
        let value = self.expr(ctx, [TT::BraceClose])?;
        let expr = Node::new(
          value.loc,
          JsxExprContainer {
            spread: true,
            value,
          },
        );
        self.require(TT::BraceClose)?;
        JsxAttrVal::Expression(expr)
      } else {
        let value = self.expr(ctx, [TT::BraceClose])?;
        let expr = Node::new(
          value.loc,
          JsxExprContainer {
            spread: false,
            value,
          },
        );
        self.require(TT::BraceClose)?;
        JsxAttrVal::Expression(expr)
      }
    } else {
      JsxAttrVal::Text(self.with_loc(|p| {
        p.lit_str_val_with_mode(LexMode::JsxTag)
          .map(|value| JsxText { value })
      })?)
    };
    Ok(val)
  }

  /// Parses a JSX named attribute like `key="value"`. See `JsxAttr` for other attribute types.
  pub fn jsx_named_attr(&mut self, ctx: ParseCtx) -> SyntaxResult<JsxAttr> {
    let name = self.jsx_name()?;
    let value = self
      .consume_if(TT::Equals)
      .and_then(|| self.jsx_attr_val(ctx))?;
    Ok(JsxAttr::Named { name, value })
  }

  /// Parses a JSX spread attribute like `{...r.getProps(true)}`.
  pub fn jsx_spread_attr(&mut self, ctx: ParseCtx) -> SyntaxResult<JsxAttr> {
    self.require(TT::BraceOpen)?;
    let attr = self.with_loc(|p| {
      p.require(TT::DotDotDot)?;
      let value = p.expr(ctx, [TT::BraceClose])?;
      p.require(TT::BraceClose)?;
      Ok(JsxSpreadAttr { value })
    })?;
    Ok(JsxAttr::Spread { value: attr })
  }

  /// Parses JSX children between opening and closing tags, like text, other elements, and expressions.
  pub fn jsx_elem_children(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<JsxElemChild>> {
    let mut children = Vec::<JsxElemChild>::new();
    loop {
      let ahead = self.peek();
      if matches!(ahead.typ, TT::ChevronLeftSlash | TT::EOF) {
        break;
      }
      let text = self.require_with_mode(TT::JsxTextContent, LexMode::JsxTextContent)?;
      if !text.loc.is_empty() {
        children.push(JsxElemChild::Text(Node::new(
          text.loc,
          JsxText {
            value: self.string(text.loc),
          },
        )));
      }
      let next = self.peek();
      match next.typ {
        TT::ChevronLeftSlash | TT::EOF => break,
        TT::ChevronLeft => {
          let child = self.jsx_elem(ctx)?;
          children.push(JsxElemChild::Element(child));
        }
        TT::BraceOpen => {
          self.consume(); // {
          if self.peek().typ == TT::BraceClose {
            self.consume(); // }
          } else if self.peek().typ == TT::DotDotDot {
            self.consume();
            let value = self.expr(ctx, [TT::BraceClose])?;
            children.push(JsxElemChild::Expr(Node::new(
              value.loc,
              JsxExprContainer {
                spread: true,
                value,
              },
            )));
            let _ = self.consume_if(TT::BraceClose);
          } else {
            let value = self.expr(ctx, [TT::BraceClose]).unwrap_or_else(|_| {
              let loc = self.peek().loc;
              Node::new(
                loc,
                IdExpr {
                  name: String::new(),
                },
              )
              .into_wrapped()
            });
            children.push(JsxElemChild::Expr(Node::new(
              value.loc,
              JsxExprContainer {
                spread: false,
                value,
              },
            )));
            let _ = self.consume_if(TT::BraceClose);
          }
        }
        TT::BraceClose | TT::ChevronRight => break,
        _ => {
          // Consume unexpected tokens to avoid infinite loops.
          self.consume_with_mode(LexMode::JsxTag);
        }
      }
    }
    Ok(children)
  }

  pub fn jsx_elem_attrs(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<JsxAttr>> {
    let mut attrs = Vec::<JsxAttr>::new();
    while !matches!(
      self.peek_with_mode(LexMode::JsxTag).typ,
      TT::ChevronRight | TT::Slash | TT::EOF
    ) {
      let next = self.peek_with_mode(LexMode::JsxTag);
      if next.typ == TT::ChevronLeft {
        self.skip_jsx_type_arguments()?;
        continue;
      }
      attrs.push(if next.typ == TT::BraceOpen {
        self.jsx_spread_attr(ctx)?
      } else {
        self.jsx_named_attr(ctx)?
      });
    }
    Ok(attrs)
  }

  /// Skips over a sequence like `<T, U>` that appears inside a JSX tag name in JS files.
  fn skip_jsx_type_arguments(&mut self) -> SyntaxResult<()> {
    self.require_with_mode(TT::ChevronLeft, LexMode::JsxTag)?;
    let mut depth = 1usize;
    while depth > 0 {
      let tok = self.consume_with_mode(LexMode::JsxTag);
      match tok.typ {
        TT::ChevronLeft => depth += 1,
        TT::ChevronRight => {
          depth = depth.saturating_sub(1);
        }
        TT::EOF => break,
        _ => {}
      }
    }
    Ok(())
  }

  // https://facebook.github.io/jsx/
  pub fn jsx_elem(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<JsxElem>> {
    self.with_loc(|p| {
      p.require_with_mode(TT::ChevronLeft, LexMode::JsxTag)?;
      let tag_name = p.jsx_elem_name()?;
      let attributes = tag_name
        .is_some()
        .then(|| p.jsx_elem_attrs(ctx))
        .transpose()?
        .unwrap_or_default();
      if p
        .maybe_consume_with_mode(TT::Slash, LexMode::JsxTag)
        .is_match()
      {
        // Self closing.

        p.require_with_mode(TT::ChevronRight, LexMode::JsxTag)?;
        return Ok(JsxElem {
          name: tag_name,
          attributes,
          children: Vec::new(),
        });
      }

      p.require_with_mode(TT::ChevronRight, LexMode::JsxTag)?;
      let children = p.jsx_elem_children(ctx)?;
      let closing = p.require_with_mode(TT::ChevronLeftSlash, LexMode::JsxTag)?;
      let end_name = p.jsx_elem_name()?;
      let _ = (closing, end_name);
      p.require_with_mode(TT::ChevronRight, LexMode::JsxTag)?;
      Ok(JsxElem {
        name: tag_name,
        attributes,
        children,
      })
    })
  }
}
