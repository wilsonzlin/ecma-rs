use crate::{ast::{expr::{IdExpr, jsx::{JsxAttr, JsxAttrVal, JsxElem, JsxElemChild, JsxElemName, JsxExprContainer, JsxMemberExpr, JsxName, JsxSpreadAttr, JsxText}}, node::Node}, error::{SyntaxErrorType, SyntaxResult}, lex::LexMode, parse::{ParseCtx, Parser}, token::TT};


impl<'a> Parser<'a> {
  pub fn jsx_name(&mut self) -> SyntaxResult<Node<JsxName>> {
    self.with_loc(|p| {
      let start = p.require_with_mode(TT::Identifier, LexMode::JsxTag)?;
      Ok(if p.consume_if(TT::Colon).is_match() {
        let name = p.require_with_mode(TT::Identifier, LexMode::JsxTag)?;
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
    let Some(start) = self
      .maybe_consume_with_mode(TT::Identifier, LexMode::JsxTag)
      .match_loc()
    else {
      // Fragment.
      return Ok(None);
    };
    let name = if self.consume_if(TT::Colon).is_match() {
      // Namespaced name.
      let name = self.require_with_mode(TT::Identifier, LexMode::JsxTag)?;
      JsxElemName::Name(Node::new(start + name.loc, JsxName {
        namespace: Some(self.string(start)),
        name: self.string(name.loc),
      }))
    } else if self.peek().typ == TT::Dot && !self.str(start).contains('-') {
      // Member name.
      let mut path = Vec::new();
      let mut loc = start;
      while self.consume_if(TT::Dot).is_match() {
        let l = self.require(TT::Identifier)?.loc;
        path.push(self.string(l));
        loc += l;
      }
      JsxElemName::Member(Node::new(loc, JsxMemberExpr {
        base: Node::new(start, IdExpr {
          name: self.string(start),
        }),
        path,
      }))
    } else if !self.bytes(start).chars().next().unwrap().is_ascii_lowercase() {
      // User-defined component.
      JsxElemName::Id(Node::new(start, IdExpr {
        name: self.string(start),
      }))
    } else {
      // Built-in component without namespace.
      JsxElemName::Name(Node::new(start, JsxName {
        namespace: None,
        name: self.string(start),
      }))
    };
    Ok(Some(name))
  }

  /// Parses a JSX attribute value (comes after the equals sign).
  pub fn jsx_attr_val(&mut self, ctx: ParseCtx) -> SyntaxResult<JsxAttrVal> {
    // TODO Attr values can be an element or fragment directly e.g. `a=<div/>`.
    let val = if self.consume_if(TT::BraceOpen).is_match() {
      let value = self.expr(ctx, [TT::BraceClose])?;
      let expr = Node::new(value.loc, JsxExprContainer { value });
      self.require(TT::BraceClose)?;
      JsxAttrVal::Expression(expr)
    } else {
      JsxAttrVal::Text(self.with_loc(|p| p.lit_str_val().map(|value| JsxText { value }))?)
    };
    Ok(val)
  }

  /// Parses a JSX named attribute like `key="value"`. See `JsxAttr` for other attribute types.
  pub fn jsx_named_attr(&mut self, ctx: ParseCtx) -> SyntaxResult<JsxAttr> {
    let name = self.jsx_name()?;
    let value = self.consume_if(TT::Equals).and_then(|| self.jsx_attr_val(ctx))?;
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
      eprintln!("[JSX DEBUG] Loop start");
      let t = self.peek();
      eprintln!("[JSX DEBUG] Peeked: {:?} at [{}:{}]", t.typ, t.loc.0, t.loc.1);
      match t.typ {
        TT::ChevronLeftSlash => {
          eprintln!("[JSX DEBUG] Found closing tag, breaking");
          break;
        }
        TT::EOF => {
          return Err(t.error(SyntaxErrorType::UnexpectedEnd));
        }
        _ => {}
      };
      eprintln!("[JSX DEBUG] Lexing JsxTextContent");
      let text = self.require_with_mode(TT::JsxTextContent, LexMode::JsxTextContent)?;
      eprintln!("[JSX DEBUG] Got JsxTextContent: [{}:{}] empty={}", text.loc.0, text.loc.1, text.loc.is_empty());
      if !text.loc.is_empty() {
        children.push(JsxElemChild::Text(Node::new(text.loc, JsxText {
          value: self.string(text.loc),
        })));
      };
      eprintln!("[JSX DEBUG] Checking for child element");
      if self.peek().typ == TT::ChevronLeft {
        eprintln!("[JSX DEBUG] Found child element");
        let child = self.jsx_elem(ctx)?;
        children.push(JsxElemChild::Element(child));
      };
      eprintln!("[JSX DEBUG] Checking for expression");
      if self.consume_if(TT::BraceOpen).is_match() {
        eprintln!("[JSX DEBUG] Found expression");
        // TODO Allow empty expr.
        let value = self.expr(ctx, [TT::BraceClose])?;
        children.push(JsxElemChild::Expr(Node::new(value.loc, JsxExprContainer {
          value,
        })));
        self.require(TT::BraceClose)?;
      };
      eprintln!("[JSX DEBUG] End of loop iteration");
    };
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
    eprintln!("[JSX ELEM] Starting jsx_elem");
    self.with_loc(|p| {
      eprintln!("[JSX ELEM] Requiring ChevronLeft");
      p.require(TT::ChevronLeft)?;
      eprintln!("[JSX ELEM] Parsing tag name");
      let tag_name = p.jsx_elem_name()?;
      eprintln!("[JSX ELEM] Tag name parsed: {:?}", tag_name.as_ref().map(|_| "Some"));
      let attributes = tag_name
        .is_some()
        .then(|| p.jsx_elem_attrs(ctx))
        .transpose()?
        .unwrap_or_default();
      eprintln!("[JSX ELEM] Attributes parsed");
      if p.consume_if(TT::Slash).is_match() {
        // Self closing.
        eprintln!("[JSX ELEM] Self-closing element");
        p.require(TT::ChevronRight)?;
        return Ok(JsxElem {
          name: tag_name,
          attributes,
          children: Vec::new(),
        });
      }
      eprintln!("[JSX ELEM] Not self-closing, requiring ChevronRight");
      p.require(TT::ChevronRight)?;
      eprintln!("[JSX ELEM] Calling jsx_elem_children");
      let children = p.jsx_elem_children(ctx)?;
      eprintln!("[JSX ELEM] jsx_elem_children returned {} children", children.len());
      let closing = p.require(TT::ChevronLeftSlash)?;
      let end_name = p.jsx_elem_name()?;
      if tag_name != end_name {
        return Err(closing.error(SyntaxErrorType::JsxClosingTagMismatch));
      };
      p.require(TT::ChevronRight)?;
      eprintln!("[JSX ELEM] Successfully parsed jsx element");
      Ok(JsxElem {
        name: tag_name,
        attributes,
        children,
      })
    })
  }
}
