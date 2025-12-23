use symbol_js::symbol::{Scope, ScopeType, SymbolGenerator};

#[test]
fn find_symbol_returns_decl_scope() {
  let generator = SymbolGenerator::new();
  let global = Scope::new(generator.clone(), None, ScopeType::Global);
  global.data_mut().add_symbol("global".into());

  let func = global.create_child_scope(ScopeType::NonArrowFunction);
  func.data_mut().add_symbol("func".into());

  let block = func.create_child_scope(ScopeType::Block);
  block.data_mut().add_symbol("block".into());

  let inner = block.create_child_scope(ScopeType::Block);

  let (scope, _) = inner
    .find_symbol_up_to_with_scope("block".into(), |_| false)
    .expect("symbol in block scope");
  assert_eq!(scope, block);

  let (scope, _) = inner
    .find_symbol_up_to_with_scope("func".into(), |_| false)
    .expect("symbol in function scope");
  assert_eq!(scope, func);

  let (scope, _) = inner
    .find_symbol_up_to_with_scope("global".into(), |_| false)
    .expect("symbol in global scope");
  assert_eq!(scope, global);
}

#[test]
fn find_symbol_stops_at_matching_scope_predicate() {
  let generator = SymbolGenerator::new();
  let global = Scope::new(generator.clone(), None, ScopeType::Global);
  global.data_mut().add_symbol("name".into());

  let block = global.create_child_scope(ScopeType::Block);
  let inner = block.create_child_scope(ScopeType::ArrowFunction);

  assert!(
    inner
      .find_symbol_up_to_with_scope("name".into(), |t| t == ScopeType::Block)
      .is_none()
  );

  block.data_mut().add_symbol("name".into());

  let (scope, _) = inner
    .find_symbol_up_to_with_scope("name".into(), |t| t == ScopeType::Block)
    .expect("symbol in stopping scope");
  assert_eq!(scope, block);
}

#[test]
fn symbol_declaration_order_is_deterministic() {
  let generator = SymbolGenerator::new();
  let scope = Scope::new(generator, None, ScopeType::Global);

  {
    let mut data = scope.data_mut();
    data.add_symbol("first".into());
    data.add_symbol("second".into());
    data.add_symbol("first".into());
    data.add_symbol("third".into());
  }

  let names_once = { scope.data().symbol_names().clone() };
  assert_eq!(
    names_once,
    vec!["first".to_string(), "second".to_string(), "third".to_string()]
  );

  let names_again = scope.data().symbol_names().clone();
  assert_eq!(names_once, names_again);
}
