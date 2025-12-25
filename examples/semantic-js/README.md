# semantic-js: JS mode examples

`semantic-js` replaces the old `symbol-js` APIs. Instead of calling the legacy
`compute_symbols` helper, bind and resolve a `parse-js` AST with
[`semantic_js::js::bind_js`], then read the attached IDs with the
[`semantic_js::assoc::js`] helpers.

The snippet below demonstrates how to:
- read the enclosing [`ScopeId`] for each node
- access the [`SymbolId`] created for declarations
- verify that identifier expressions resolve back to the expected declaration
- iterate over a scope's symbols deterministically via [`JsSemantics::scope_symbols`]

```rust
use std::collections::HashMap;

use derive_visitor::{DriveMut, VisitorMut};
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

type IdExprNode = Node<IdExpr>;
type IdPatNode = Node<IdPat>;

#[derive(Default, VisitorMut)]
#[visitor(IdPatNode(enter), IdExprNode(enter))]
struct Collect {
  decls: HashMap<String, (ScopeId, SymbolId)>,
  uses: Vec<(String, ScopeId, Option<SymbolId>)>,
}

impl Collect {
  fn enter_id_pat_node(&mut self, node: &mut IdPatNode) {
    let scope = scope_id(&node.assoc).expect("scope attached");
    if let Some(symbol) = declared_symbol(&node.assoc) {
      self.decls.insert(node.stx.name.clone(), (scope, symbol));
    }
  }

  fn enter_id_expr_node(&mut self, node: &mut IdExprNode) {
    let scope = scope_id(&node.assoc).expect("scope attached");
    self
      .uses
      .push((node.stx.name.clone(), scope, resolved_symbol(&node.assoc)));
  }
}

let mut ast = parse(
  r#"
    const top = 1;
    const make = () => {
      let inner = top;
      return inner;
    };
    make();
  "#,
)
.unwrap();

let (sem, _res) = bind_js(&mut ast, TopLevelMode::Module);

let mut collect = Collect::default();
ast.drive_mut(&mut collect);

for (name, _, resolved) in &collect.uses {
  let (_, decl_symbol) = collect.decls.get(name).expect("declaration exists");
  assert_eq!(resolved, &Some(*decl_symbol));
}

let top_symbols: Vec<_> = sem
  .scope_symbols(sem.top_scope())
  .map(|(name, symbol)| (sem.name(name).to_string(), symbol.index()))
  .collect();
assert_eq!(
  top_symbols,
  vec![
    ("top".to_string(), collect.decls["top"].1.index()),
    ("make".to_string(), collect.decls["make"].1.index())
  ]
);
```

This snippet is also available as a doctest in `semantic-js`'s crate
documentation (`cargo test -p semantic-js --doc`).
