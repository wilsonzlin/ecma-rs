use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn strict_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn assert_reject(src: &str) {
  assert!(
    parse_with_options(src, strict_script_opts()).is_err(),
    "expected strict ECMAScript parsing to reject: {src:?}"
  );
}

fn assert_accept(src: &str) {
  parse_with_options(src, strict_script_opts()).unwrap_or_else(|err| {
    panic!("expected strict ECMAScript parsing to accept {src:?}, got {err:?}")
  });
}

#[test]
fn strict_ecma_rejects_ts_only_syntax_and_recovery_paths() {
  // TS-only constructs.
  assert_reject("x as y;");
  assert_reject("a!;");
  assert_reject("let x: y;");
  assert_reject("function f(x: y) { return x; }");
  assert_reject("class C<T> {}");
  assert_reject("try {} catch (e: any) {}");

  // Recovery-only constructs that should be syntax errors in strict ECMAScript.
  assert_reject("();");
  assert_reject("({ [x] })");
  assert_reject("({ class C {} })");
  assert_reject("({ while })");
}

#[test]
fn strict_ecma_still_accepts_valid_js() {
  assert_accept("({ [x]: y, while: 1, class: 2 });");
  assert_accept("a != b; a !== b;");
  assert_accept("function f(x) { return x; }");
}
