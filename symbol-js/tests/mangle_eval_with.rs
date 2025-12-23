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
fn direct_eval_marks_scope_chain_dynamic() {
  let source = "function f(){ var x=1; eval('x'); function g(){ var y=1; return y; } }";
  let mut node = parse(source).unwrap();
  let top_scope = symbol_js::compute_symbols(&mut node, TopLevelMode::Global);

  let symbol_x = find_symbol(&top_scope, "x").expect("symbol x");
  let symbol_y = find_symbol(&top_scope, "y").expect("symbol y");

  let mapping = mangle::mangle(&mut node, &top_scope);

  assert!(
    !mapping.contains_key(&symbol_x),
    "x should be pinned by direct eval"
  );
  let new_y = mapping.get(&symbol_y).expect("y should still be mangled");
  assert_ne!(new_y, "y");
}

#[test]
fn module_top_level_eval_pins_outer_scope() {
  let source = "let x=1; function f(){ eval('x'); }";
  let mut node = parse(source).unwrap();
  let top_scope = symbol_js::compute_symbols(&mut node, TopLevelMode::Module);

  let symbol_x = find_symbol(&top_scope, "x").expect("symbol x");

  let mapping = mangle::mangle(&mut node, &top_scope);

  assert!(
    !mapping.contains_key(&symbol_x),
    "top-level x must not be renamed when referenced by direct eval"
  );
}

#[test]
fn shadowed_eval_allows_mangling() {
  let source = "function f(){ let eval = (s)=>0; let x=1; eval('x'); }";
  let mut node = parse(source).unwrap();
  let top_scope = symbol_js::compute_symbols(&mut node, TopLevelMode::Global);

  let symbol_x = find_symbol(&top_scope, "x").expect("symbol x");

  let mapping = mangle::mangle(&mut node, &top_scope);

  let new_name = mapping.get(&symbol_x).expect("x should be mangled");
  assert_ne!(new_name, "x");
}

#[test]
fn with_statement_disables_mangling_on_chain() {
  let source = "function f(){ var x=1; with ({x:2}) { x; } }";
  let mut node = parse(source).unwrap();
  let top_scope = symbol_js::compute_symbols(&mut node, TopLevelMode::Global);

  let symbol_x = find_symbol(&top_scope, "x").expect("symbol x");

  let mapping = mangle::mangle(&mut node, &top_scope);

  assert!(
    !mapping.contains_key(&symbol_x),
    "with statement should pin surrounding scope names"
  );
}
