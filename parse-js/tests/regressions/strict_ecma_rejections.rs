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
    panic!("expected strict ECMAScript module parsing to accept {src:?}, got {err:?}")
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

  // `await`/`yield` are context-sensitive in ECMAScript; strict parsing should not accept
  // them as expressions where they are not allowed.
  assert_reject("await 1;");
  assert_reject("yield 1;");
  assert_reject_module("function f() { await 1; }");
  assert_reject_module("var yield = 1;");
  assert_reject_module("yield;");

  // `return` is only valid within functions.
  assert_reject("return 1;");
  assert_reject_module("return 1;");

  // `break`/`continue` are only valid within the appropriate control-flow contexts,
  // and label resolution does not cross function/static-block boundaries.
  assert_reject("break;");
  assert_reject("continue;");
  assert_reject("break missing;");
  assert_reject("continue missing;");
  assert_reject("foo: { continue foo; }");
  assert_reject("a: a: while (true) {}");
  assert_reject("while (true) { function f() { break; } }");
  assert_reject("while (true) { class A { static { break; } } }");
  assert_reject_module("break;");
  assert_reject_module("continue;");

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
  assert_reject("for (var x = 1 of y) {}");
  assert_reject("for (let x = 1 of y) {}");
  assert_reject("for (const x = 1 of y) {}");
  assert_reject("for (var x, y of z) {}");
  assert_reject("for (let x, y of z) {}");
  assert_reject("for (const x, y of z) {}");
  assert_reject_module("import.meta = 1;");
}

#[test]
fn strict_ecma_still_accepts_valid_js() {
  assert_accept("({ [x]: y, while: 1, class: 2 });");
  assert_accept("a != b; a !== b;");
  assert_accept("for (a of b) {}");
  assert_accept("for (var x of y) {}");
  assert_accept("for (var x in y) {}");
  assert_accept("while (true) { break; }");
  assert_accept("switch (x) { default: break; }");
  assert_accept("foo: { break foo; }");
  assert_accept("foo: while (true) { continue foo; }");
  assert_accept("a: b: while (true) { continue a; }");
  assert_accept("function f(x) { return x; }");
  assert_accept("var f = await => await + 1;");
  assert_accept("async function g() { function f() { var await = 1; return await; } }");
  assert_accept("function* g() { function f() { var yield = 1; return yield; } }");

  // `type` remains a valid binding/import/export name in ECMAScript.
  assert_accept_module("import { type } from \"mod\";");
  assert_accept_module("export { type } from \"mod\";");
  assert_accept_module("import.meta;");
  assert_accept_module("await 1;");
}
