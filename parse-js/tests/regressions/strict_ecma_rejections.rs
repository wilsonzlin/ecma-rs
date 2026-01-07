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
  assert_reject("for await (const x of y) {}");
  assert_reject_module("function f() { for await (const x of y) {} }");

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
  assert_reject("import.meta;");
  assert_reject_module("with ({}) {}");
  assert_reject_module("delete x;");
  assert_reject_module("delete (x);");
  assert_reject_module("010;");
  assert_reject_module("08;");
  assert_reject_module(r"'\1';");
  assert_reject_module("import.meta = 1;");

  // `new.target` is only valid when a `new.target` binding exists (functions and class
  // field/static-block initialisers), not in global code.
  assert_reject("new.target;");
  assert_reject_module("new.target;");
  assert_reject("(() => new.target);");
  assert_reject("class A { [new.target] = 1 }");

  // `super` is only valid within methods/class element initialisers; `super()` is only
  // valid in derived constructors (and arrow functions nested within them).
  assert_reject("super.foo;");
  assert_reject("super();");
  assert_reject_module("super.foo;");
  assert_reject_module("super();");
  assert_reject("function f() { super.foo; }");
  assert_reject("class A { constructor() { super(); } }");
  assert_reject("class B {} class A extends B { m() { super(); } }");
  assert_reject("class B {} class A extends B { m() { (() => super())(); } }");
  assert_reject("class B {} class A extends B { x = super(); }");
  assert_reject("class B {} class A extends B { x = (() => super())(); }");
  assert_reject("class B {} class A extends B { static { super(); } }");
}

#[test]
fn strict_ecma_still_accepts_valid_js() {
  assert_accept("({ [x]: y, while: 1, class: 2 });");
  assert_accept("a != b; a !== b;");
  // `<` followed immediately by a regex literal begins with `</` and must not be lexed as a
  // JSX closing-tag token outside JSX contexts.
  assert_accept("1</b/.test('b');");
  assert_accept("for (a of b) {}");
  assert_accept("for (var x of y) {}");
  assert_accept("for (var x in y) {}");
  assert_accept("while (true) { break; }");
  assert_accept("switch (x) { default: break; }");
  assert_accept("foo: { break foo; }");
  assert_accept("foo: while (true) { continue foo; }");
  assert_accept("a: b: while (true) { continue a; }");
  assert_accept("function f() { new.target; }");
  assert_accept("function f() { (() => new.target)(); }");
  assert_accept("function f() { class A { [new.target] = 1 } }");
  assert_accept("class A { x = new.target; }");
  assert_accept("class A { x = (() => new.target)(); }");
  assert_accept("class A { static { new.target; } }");
  assert_accept("class A { m() { super.foo; } }");
  assert_accept("({ m() { super.foo; } });");
  assert_accept("class B {} class A extends B { constructor() { super(); } }");
  assert_accept("class B {} class A extends B { constructor() { (() => super())(); } }");
  assert_accept("class B {} class A extends B { x = super.foo; }");
  assert_accept("class A { x = super.foo; }");
  assert_accept("class B {} class A extends B { static { super.foo; } }");
  assert_accept("class A { static { super.foo; } }");
  assert_accept("with ({}) {}");
  assert_accept("delete x;");
  assert_accept("010;");
  assert_accept("08;");
  assert_accept(r"'\1';");
  assert_accept("function f(x) { return x; }");
  assert_accept("var f = await => await + 1;");
  assert_accept("async function g() { function f() { var await = 1; return await; } }");
  assert_accept("function* g() { function f() { var yield = 1; return yield; } }");

  // `type` remains a valid binding/import/export name in ECMAScript.
  assert_accept_module("import { type } from \"mod\";");
  assert_accept_module("export { type } from \"mod\";");
  assert_accept_module("import.meta;");
  assert_accept_module("await 1;");
  assert_accept("async function f() { for await (const x of y) {} }");
  assert_accept_module("for await (const x of y) {}");
  assert_accept_module("async function f() { for await (const x of y) {} }");
}
