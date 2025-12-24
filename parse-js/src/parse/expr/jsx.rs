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
      Ok(tok)
    } else {
      Err(
        tok.error(crate::error::SyntaxErrorType::RequiredTokenNotFound(
          TT::Identifier,
        )),
      )
    }
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
    // Try to get a JSX name token (identifier or keyword)
    let tok = self.peek_with_mode(LexMode::JsxTag);
    let is_name_token = tok.typ == TT::Identifier || tok.typ.is_keyword();
    if !is_name_token {
      // Fragment.
      return Ok(None);
    };
    let start = self.jsx_name_token()?.loc;

    let name = if self.consume_if(TT::Colon).is_match() {
      // Namespaced name.
      let name = self.jsx_name_token()?;
      JsxElemName::Name(Node::new(
        start + name.loc,
        JsxName {
          namespace: Some(self.string(start)),
          name: self.string(name.loc),
        },
      ))
    } else if self.peek().typ == TT::Dot && !self.str(start).contains('-') {
      // Member name.
      let mut path = Vec::new();
      let mut loc = start;
      while self.consume_if(TT::Dot).is_match() {
        let l = self.require(TT::Identifier)?.loc;
        path.push(self.string(l));
        loc += l;
      }
      JsxElemName::Member(Node::new(
        loc,
        JsxMemberExpr {
          base: Node::new(
            start,
            IdExpr {
              name: self.string(start),
            },
          ),
          path,
        },
      ))
    } else if !self
      .bytes(start)
      .chars()
      .next()
      .unwrap()
      .is_ascii_lowercase()
    {
      // User-defined component.
      JsxElemName::Id(Node::new(
        start,
        IdExpr {
          name: self.string(start),
        },
      ))
    } else {
      // Built-in component without namespace.
      JsxElemName::Name(Node::new(
        start,
        JsxName {
          namespace: None,
          name: self.string(start),
        },
      ))
    };
    Ok(Some(name))
  }

  /// Parses a JSX attribute value (comes after the equals sign).
  pub fn jsx_attr_val(&mut self, ctx: ParseCtx) -> SyntaxResult<JsxAttrVal> {
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
      JsxAttrVal::Text(self.with_loc(|p| p.lit_str_val().map(|value| JsxText { value }))?)
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
      let t = self.peek();
      match t.typ {
        TT::ChevronLeftSlash => {
          break;
        }
        TT::EOF => {
          return Err(t.error(SyntaxErrorType::UnexpectedEnd));
        }
        _ => {}
      };
      let text = self.require_with_mode(TT::JsxTextContent, LexMode::JsxTextContent)?;
      if !text.loc.is_empty() {
        children.push(JsxElemChild::Text(Node::new(
          text.loc,
          JsxText {
            value: self.string(text.loc),
          },
        )));
      };
      if self.peek().typ == TT::ChevronLeft {
        let child = self.jsx_elem(ctx)?;
        children.push(JsxElemChild::Element(child));
      };
      if self.consume_if(TT::BraceOpen).is_match() {
        // Allow empty expr: <div>{}</div>
        if self.peek().typ == TT::BraceClose {
          // Empty expression - skip it, don't add to children
          self.consume(); // consume }
        } else if self.peek().typ == TT::DotDotDot {
          // Spread children: <div>{...items}</div>
          // This is valid JSX - the spread creates multiple children from an array
          self.consume(); // consume ...
          let value = self.expr(ctx, [TT::BraceClose])?;
          children.push(JsxElemChild::Expr(Node::new(
            value.loc,
            JsxExprContainer {
              spread: true,
              value,
            },
          )));
          self.require(TT::BraceClose)?;
        } else {
          let value = self.expr(ctx, [TT::BraceClose])?;
          children.push(JsxElemChild::Expr(Node::new(
            value.loc,
            JsxExprContainer {
              spread: false,
              value,
            },
          )));
          self.require(TT::BraceClose)?;
        }
      };
    }
    Ok(children)
  }

  pub fn jsx_elem_attrs(&mut self, ctx: ParseCtx) -> SyntaxResult<Vec<JsxAttr>> {
    let mut attrs = Vec::<JsxAttr>::new();
    while !matches!(self.peek().typ, TT::ChevronRight | TT::Slash) {
      attrs.push(if self.peek().typ == TT::BraceOpen {
        self.jsx_spread_attr(ctx)?
      } else {
        self.jsx_named_attr(ctx)?
      });
    }
    Ok(attrs)
  }

  // https://facebook.github.io/jsx/
  pub fn jsx_elem(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<JsxElem>> {
    self.with_loc(|p| {
      p.require(TT::ChevronLeft)?;
      let tag_name = p.jsx_elem_name()?;
      let attributes = tag_name
        .is_some()
        .then(|| p.jsx_elem_attrs(ctx))
        .transpose()?
        .unwrap_or_default();
      if p.consume_if(TT::Slash).is_match() {
        // Self closing.

        p.require(TT::ChevronRight)?;
        return Ok(JsxElem {
          name: tag_name,
          attributes,
          children: Vec::new(),
        });
      }

      p.require(TT::ChevronRight)?;
      let children = p.jsx_elem_children(ctx)?;
      let closing = p.require(TT::ChevronLeftSlash)?;
      let end_name = p.jsx_elem_name()?;
      if tag_name != end_name {
        return Err(closing.error(SyntaxErrorType::JsxClosingTagMismatch));
      };
      p.require(TT::ChevronRight)?;
      Ok(JsxElem {
        name: tag_name,
        attributes,
        children,
      })
    })
  }
}
