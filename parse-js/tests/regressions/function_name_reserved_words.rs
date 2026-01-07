use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn ecma_module_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Module,
  }
}

#[test]
fn script_allows_generator_function_decl_named_yield() {
  parse_with_options("function* yield() {}", ecma_script_opts()).unwrap();
}

#[test]
fn script_allows_async_function_decl_named_await() {
  parse_with_options("async function await() {}", ecma_script_opts()).unwrap();
}

#[test]
fn script_allows_named_function_expr_named_await_inside_async_body() {
  // The function-expression name is scoped to the function itself, so it should not
  // inherit the enclosing async function's `await` restrictions.
  parse_with_options(
    "async function f() { let x = function await() {}; }",
    ecma_script_opts(),
  )
  .unwrap();
}

#[test]
fn script_allows_function_decl_named_await_inside_nested_non_async_scope() {
  // Nested non-async functions reset the `await` identifier restriction.
  parse_with_options(
    "async function f() { function g() { function await() {} } }",
    ecma_script_opts(),
  )
  .unwrap();
}

#[test]
fn script_allows_function_decl_named_yield_inside_nested_non_generator_scope() {
  // Nested non-generator functions reset the `yield` identifier restriction.
  parse_with_options(
    "function* f() { function g() { function yield() {} } }",
    ecma_script_opts(),
  )
  .unwrap();
}

#[test]
fn script_rejects_function_decl_named_await_inside_async_body() {
  assert!(
    parse_with_options(
      "async function f() { function await() {} }",
      ecma_script_opts()
    )
    .is_err()
  );
}

#[test]
fn script_rejects_function_decl_named_yield_inside_generator_body() {
  assert!(
    parse_with_options(
      "function* f() { function yield() {} }",
      ecma_script_opts()
    )
    .is_err()
  );
}

#[test]
fn script_rejects_async_function_expr_named_await() {
  assert!(
    parse_with_options("let x = async function await() {};", ecma_script_opts()).is_err()
  );
}

#[test]
fn script_rejects_generator_function_expr_named_yield() {
  assert!(
    parse_with_options("let x = function* yield() {};", ecma_script_opts()).is_err()
  );
}

#[test]
fn module_rejects_function_decl_named_await() {
  assert!(parse_with_options("function await() {}", ecma_module_opts()).is_err());
}

#[test]
fn module_rejects_named_function_expr_named_await() {
  assert!(parse_with_options(
    "let x = function await() {};",
    ecma_module_opts()
  )
  .is_err());
}
