use parse_js::parse;
use symbol_js::mangle;
use symbol_js::symbol::{Scope, Symbol};
use symbol_js::TopLevelMode;

fn find_symbol(scope: &Scope, name: &str) -> Option<Symbol> {
  if let Some(symbol) = scope.data().get_symbol(name) {
    return Some(symbol);
  }

  for child in scope.data().children() {
    if let Some(symbol) = find_symbol(child, name) {
      return Some(symbol);
    }
  }

  None
}

#[test]
fn avoids_shadowing_renamed_outer_bindings() {
  let source = "function outer(){ let foo=1; function inner(){ let bar = foo + 1; return bar; } return inner(); }";
  let mut node = parse(source).unwrap();
  let top_scope = symbol_js::compute_symbols(&mut node, TopLevelMode::Global);

  let symbol_foo = find_symbol(&top_scope, "foo").expect("symbol foo");
  let symbol_bar = find_symbol(&top_scope, "bar").expect("symbol bar");

  let mapping = mangle::mangle(&mut node, &top_scope);

  let foo_name = mapping.get(&symbol_foo).expect("foo should be mangled");
  let bar_name = mapping.get(&symbol_bar).expect("bar should be mangled");
  assert_ne!(
    foo_name, bar_name,
    "inner scope must not reuse the renamed outer binding name"
  );
}
