use derive_visitor::{Drive, Visitor};
use parse_js::ast::expr::IdExpr;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use parse_js::error::SyntaxError;
use parse_js::loc::Loc;
use symbol_js::symbol::{Scope, Symbol};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirRoot {
  /// Placeholder: number of top-level statements parsed.
  pub stmt_count: usize,
  /// All identifier occurrences lowered from the source tree.
  pub idents: Vec<Ident>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
  pub name: String,
  pub symbol: Option<Symbol>,
  pub loc: Loc,
}

#[derive(Debug, thiserror::Error)]
pub enum LowerError {
  #[error("parse error: {0}")]
  Parse(#[from] SyntaxError),
  #[error("missing scope for {context} at {loc:?}")]
  MissingScope { loc: Loc, context: &'static str },
}

/// Lower a parsed top-level node into a placeholder HIR representation.
///
/// Callers should run `symbol_js::compute_symbols` before invoking this if
/// they want `Ident::symbol` populated. If the AST nodes lack associated scope
/// data, lowering will return `LowerError::MissingScope` instead of silently
/// treating identifiers as globals.
pub fn lower_top_level(top_level: &Node<TopLevel>) -> Result<HirRoot, LowerError> {
  let mut visitor = IdentCollector::default();
  top_level.drive(&mut visitor);

  if let Some(err) = visitor.error {
    return Err(err);
  }

  Ok(HirRoot {
    stmt_count: top_level.stx.body.len(),
    idents: visitor.idents,
  })
}

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;

#[derive(Default, Visitor)]
#[visitor(IdExprNode(enter), IdPatNode(enter))]
struct IdentCollector {
  idents: Vec<Ident>,
  error: Option<LowerError>,
}

impl IdentCollector {
  fn push_ident(
    &mut self,
    name: &str,
    loc: Loc,
    scope: Option<&Scope>,
    context: &'static str,
  ) {
    if self.error.is_some() {
      return;
    }

    let Some(scope) = scope else {
      self.error = Some(LowerError::MissingScope { loc, context });
      return;
    };

    let symbol = scope.find_symbol(name.to_string());
    self.idents.push(Ident {
      name: name.to_string(),
      symbol,
      loc,
    });
  }

  pub fn enter_id_expr_node(&mut self, node: &IdExprNode) {
    self.push_ident(&node.stx.name, node.loc, node.assoc.get::<Scope>(), "identifier expr");
  }

  pub fn enter_id_pat_node(&mut self, node: &IdPatNode) {
    self.push_ident(
      &node.stx.name,
      node.loc,
      node.assoc.get::<Scope>(),
      "identifier pattern",
    );
  }
}

/// Parse JS/TS source and produce a placeholder HIR root. The emphasis is on
/// non-panicking behavior; syntax errors are surfaced as `Err`.
pub fn lower_from_source(source: &str) -> Result<HirRoot, LowerError> {
  let parsed = parse_js::parse(source)?;
  lower_top_level(&parsed)
}

/// Fuzzing entry point to exercise parsing + lowering without panicking.
#[cfg(feature = "fuzzing")]
pub fn fuzz_lower(data: &[u8]) {
  let source = String::from_utf8_lossy(data);
  let _ = lower_from_source(&source);
}
