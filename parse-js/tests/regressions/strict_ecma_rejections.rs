use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn strict_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn strict_module_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Module,
  }
}

fn assert_reject(src: &str) {
  assert!(
    parse_with_options(src, strict_script_opts()).is_err(),
    "expected strict ECMAScript parsing to reject: {src:?}"
  );
}

fn assert_reject_module(src: &str) {
  assert!(
    parse_with_options(src, strict_module_opts()).is_err(),
    "expected strict ECMAScript module parsing to reject: {src:?}"
  );
}

fn assert_accept(src: &str) {
  parse_with_options(src, strict_script_opts()).unwrap_or_else(|err| {
    panic!("expected strict ECMAScript parsing to accept {src:?}, got {err:?}")
  });
}

fn assert_accept_module(src: &str) {
  parse_with_options(src, strict_module_opts()).unwrap_or_else(|err| {
    panic!(
      "expected strict ECMAScript module parsing to accept {src:?}, got {err:?}"
    )
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

  // TypeScript-only import/export forms.
  assert_reject_module("import type { Foo } from \"mod\";");
  assert_reject_module("import { type Foo } from \"mod\";");
  assert_reject_module("export type * from \"mod\";");
  assert_reject_module("export = foo;");

  // TypeScript-only top-level declarations that would otherwise lex as JS keywords.
  assert_reject("enum E {}");
  assert_reject_module("export enum E {}");

  // Decorators are not part of ECMAScript.
  assert_reject("@dec class C {}");
  assert_reject("class C { @dec m() {} }");

  // Recovery-only constructs that should be syntax errors in strict ECMAScript.
  assert_reject("();");
  assert_reject("({ [x] })");
  assert_reject("({ class C {} })");
  assert_reject("({ while })");

  // Invalid assignment targets.
  assert_reject("foo() = 1;");
  assert_reject("1 = 2;");
  assert_reject("obj?.a = 1;");
  assert_reject("for (foo() of bar) {}");
  assert_reject("for ((a) of b) {}");
  assert_reject_module("import.meta = 1;");
}

#[test]
fn strict_ecma_still_accepts_valid_js() {
  assert_accept("({ [x]: y, while: 1, class: 2 });");
  assert_accept("a != b; a !== b;");
  assert_accept("for (a of b) {}");
  assert_accept("function f(x) { return x; }");

  // `type` remains a valid binding/import/export name in ECMAScript.
  assert_accept_module("import { type } from \"mod\";");
  assert_accept_module("export { type } from \"mod\";");
  assert_accept_module("import.meta;");
}
