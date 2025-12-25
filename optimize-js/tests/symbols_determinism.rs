use optimize_js::{compile_source, TopLevelMode};
use serde_json::to_string;

#[test]
fn program_symbols_are_deterministic() {
  let source = r#"
    (() => {
      let a = 1;
      let b = 2;
      const c = a + b;
      (c + a + b);
    })();
  "#;

  let first = compile_source(source, TopLevelMode::Module, false)
    .expect("compile first")
    .symbols
    .expect("program symbols present");
  let second = compile_source(source, TopLevelMode::Module, false)
    .expect("compile second")
    .symbols
    .expect("program symbols present");

  let first_json = to_string(&first).expect("serialize first symbols");
  let second_json = to_string(&second).expect("serialize second symbols");

  assert_eq!(
    first_json, second_json,
    "symbol collection should be deterministic across runs"
  );
}
