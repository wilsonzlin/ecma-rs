use derive_visitor::{DriveMut, VisitorMut};
use diagnostics::render::render_diagnostic;
use diagnostics::{Diagnostic, FileId, SimpleFiles};
use parse_js::{
  ast::{
    expr::{pat::IdPat, IdExpr},
    node::Node,
  },
  parse,
};
use semantic_js::{
  assoc::js::{declared_symbol, resolved_symbol, scope_id},
  js::{bind_js, ScopeId, SymbolId, TopLevelMode},
};

const SOURCE: &str = r#"
const top = 1;
const make = () => {
  let inner = top;
  return inner;
};
make();
"#;

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;

#[derive(Default, VisitorMut)]
#[visitor(IdPatNode(enter), IdExprNode(enter))]
struct Collect {
  decls: Vec<(u32, String, ScopeId, SymbolId)>,
  uses: Vec<(u32, String, ScopeId, Option<SymbolId>)>,
}

impl Collect {
  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    let scope = scope_id(&node.assoc).expect("scope attached");
    if let Some(symbol) = declared_symbol(&node.assoc) {
      self
        .decls
        .push((node.loc.0 as u32, node.stx.name.clone(), scope, symbol));
    }
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let scope = scope_id(&node.assoc).expect("scope attached");
    self.uses.push((
      node.loc.0 as u32,
      node.stx.name.clone(),
      scope,
      resolved_symbol(&node.assoc),
    ));
  }
}

fn main() {
  let mut ast = parse(SOURCE).expect("parse");
  let (sem, diagnostics) = bind_js(&mut ast, TopLevelMode::Module, FileId(0));

  if !diagnostics.is_empty() {
    render_diagnostics(diagnostics);
  }

  let mut collect = Collect::default();
  ast.drive_mut(&mut collect);

  collect
    .decls
    .sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
  collect
    .uses
    .sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));

  println!("== top scope symbols ==");
  for (name_id, symbol) in sem.scope_symbols(sem.top_scope()) {
    println!("  {}: {}", sem.name(name_id), symbol.raw());
  }

  println!();
  println!("== declarations ==");
  for (offset, name, scope, symbol) in &collect.decls {
    println!(
      "  decl {name}@{offset}: scope={} symbol={}",
      scope.raw(),
      symbol.raw()
    );
  }

  println!();
  println!("== identifier uses ==");
  for (offset, name, scope, symbol) in &collect.uses {
    let resolved = symbol.map(|id| id.raw());
    println!(
      "  use {name}@{offset}: scope={} resolved={resolved:?}",
      scope.raw()
    );
  }
}

fn render_diagnostics(diagnostics: Vec<Diagnostic>) {
  let mut files = SimpleFiles::new();
  files.add("example.js", SOURCE);
  for diagnostic in diagnostics {
    print!("{}", render_diagnostic(&files, &diagnostic));
  }
}
