use vm_js::SourceTextModuleRecord;

#[test]
fn module_await_expression_sets_has_tla() {
  let record = SourceTextModuleRecord::parse("await 1; export {};").expect("parse module");
  assert!(record.has_tla);
}

#[test]
fn await_inside_async_function_does_not_set_has_tla() {
  let record = SourceTextModuleRecord::parse("async function f(){ await 1; } export {};")
    .expect("parse module");
  assert!(!record.has_tla);
}

#[test]
fn for_await_of_sets_has_tla() {
  let record = SourceTextModuleRecord::parse("for await (const x of y) {}").expect("parse module");
  assert!(record.has_tla);
}

#[test]
fn for_await_of_inside_function_does_not_set_has_tla() {
  let record = SourceTextModuleRecord::parse("async function g(){ for await (const x of y) {} } export {};")
    .expect("parse module");
  assert!(!record.has_tla);
}
