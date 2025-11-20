use super::Parser;
use crate::ast::node::Node;
use crate::error::SyntaxResult;
use crate::token::TT;
use derive_visitor::Drive;
use derive_visitor::DriveMut;

impl<'a> Parser<'a> {
  pub fn with_loc<S: Drive + DriveMut, F>(&mut self, f: F) -> SyntaxResult<Node<S>>
  where
    F: FnOnce(&mut Self) -> SyntaxResult<S>,
  {
    let start = self.checkpoint();
    let stx = f(self)?;
    Ok(Node::new(self.since_checkpoint(&start), stx))
  }

  pub fn repeat_while<S, F, W>(&mut self, w: W, f: F) -> SyntaxResult<Vec<S>>
  where
    F: Fn(&mut Self) -> SyntaxResult<S>,
    W: Fn(&mut Self) -> bool,
  {
    let mut nodes = Vec::new();
    while w(self) {
      nodes.push(f(self)?);
    }
    Ok(nodes)
  }

  pub fn repeat_while_with_loc<S: Drive + DriveMut, F, W>(
    &mut self,
    w: W,
    f: F,
  ) -> SyntaxResult<Vec<Node<S>>>
  where
    F: Fn(&mut Self) -> SyntaxResult<S>,
    W: Fn(&mut Self) -> bool,
  {
    self.repeat_while(w, |p| p.with_loc(|p| f(p)))
  }

  pub fn repeat_until_tt<S, F>(&mut self, tt: TT, f: F) -> SyntaxResult<Vec<S>>
  where
    F: Fn(&mut Self) -> SyntaxResult<S>,
  {
    self.repeat_while(|p| p.peek().typ != tt, f)
  }

  pub fn repeat_until_tt_with_loc<S: Drive + DriveMut, F>(
    &mut self,
    tt: TT,
    f: F,
  ) -> SyntaxResult<Vec<Node<S>>>
  where
    F: Fn(&mut Self) -> SyntaxResult<S>,
  {
    self.repeat_while_with_loc(|p| p.peek().typ != tt, f)
  }

  /// Parse a list of items separated by a delimiter until `close`, which will also be consumed.
  /// Allows for a trailing delimiter.
  pub fn list_with_loc<S: Drive + DriveMut, F>(
    &mut self,
    delim: TT,
    close: TT,
    f: F,
  ) -> SyntaxResult<Vec<Node<S>>>
  where
    F: Fn(&mut Self) -> SyntaxResult<S>,
  {
    let mut nodes = Vec::new();
    while !self.consume_if(close).is_match() {
      nodes.push(self.with_loc(&f)?);
      // We require either the delimiter or the close token.
      // If the delimiter exists, it can still immediately be followed by the close token (trailing delimiter).
      // If the delimiter does not exist, the close token must be present. This handles the case where the close token is present.
      if !self.consume_if(delim).is_match() {
        self.require(close)?;
        break;
      }
    }
    Ok(nodes)
  }

  /// Drives the parser with the closure and returns what it returns, undoing its changes if it returns None.
  pub fn rewindable<S, F>(&mut self, f: F) -> SyntaxResult<Option<S>>
  where
    F: FnOnce(&mut Self) -> SyntaxResult<Option<S>>,
  {
    let checkpoint = self.checkpoint();
    let stx = f(self)?;
    if stx.is_none() {
      self.restore_checkpoint(checkpoint);
    };
    Ok(stx)
  }

  /// Drives the parser with the closure and returns what it returns as a Node over the consumed range, undoing its changes if it returns None.
  pub fn rewindable_with_loc<S: Drive + DriveMut, F>(
    &mut self,
    f: F,
  ) -> SyntaxResult<Option<Node<S>>>
  where
    F: FnOnce(&mut Self) -> SyntaxResult<Option<S>>,
  {
    let checkpoint = self.checkpoint();
    let stx = f(self)?;
    let loc = self.since_checkpoint(&checkpoint);
    if stx.is_none() {
      self.restore_checkpoint(checkpoint);
    };
    Ok(stx.map(|stx| Node::new(loc, stx)))
  }
}
