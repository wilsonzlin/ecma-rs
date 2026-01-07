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

fn assert_reject_with_use_strict(src: &str) {
  let source = format!("'use strict'; {src}");
  assert!(
    parse_with_options(&source, strict_script_opts()).is_err(),
    "expected strict-mode ECMAScript parsing to reject: {source:?}"
  );
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
  assert_reject("({ *(){} })");
  assert_reject("({ async *(){} })");
  assert_reject("class C { *(){} }");
  assert_reject("class C { a b }");
  assert_reject("class C { a b(){} }");
  assert_reject("class C { a [foo](){} }");
  // `get`/`set` remain accessor modifiers across LineTerminators; missing `()` must be a
  // syntax error (it must not be parsed as two adjacent class fields).
  assert_reject("class C { get\nfoo }");
  assert_reject("class C { set\nfoo }");
  assert_reject("class C { get\n[foo] }");
  assert_reject("class C { set\n[foo] }");

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
fn strict_mode_directives_trigger_ecma_early_errors() {
  // Strict-mode-only statement restrictions.
  assert_reject_with_use_strict("with ({}) {}");
  assert_reject_with_use_strict("delete x;");
  assert_reject_with_use_strict("delete (x);");

  // Numeric literals and legacy octal escapes.
  assert_reject_with_use_strict("010;");
  assert_reject_with_use_strict("08;");
  assert_reject_with_use_strict(r"'\1';");

  // Strict-mode reserved words are not valid identifier references.
  assert_reject_with_use_strict("implements;");
  assert_reject_with_use_strict("interface;");
  assert_reject_with_use_strict("let;");
  assert_reject_with_use_strict("static;");
  assert_reject_with_use_strict("yield;");

  // `eval`/`arguments` are restricted assignment/update targets in strict mode.
  assert_reject_with_use_strict("eval = 1;");
  assert_reject_with_use_strict("eval++;");
  assert_reject_with_use_strict("++arguments;");
  assert_reject_with_use_strict("for (eval in obj) {}");
  assert_reject_with_use_strict("for (arguments of xs) {}");

  // Functions can become strict via their own directive prologue.
  assert_reject("function f(eval) { 'use strict'; }");
  assert_reject("function yield() { 'use strict'; }");
  assert_reject("function f(a, a) { 'use strict'; }");
  assert_reject("function f(a = 1) { 'use strict'; }");

  // Arrow functions and method definitions have stricter parameter rules.
  assert_reject("((a, a) => a);");
  assert_reject("({ m(a, a) {} });");
  assert_reject("((eval) => { 'use strict'; });");
  assert_reject("({ m(eval) { 'use strict'; } });");
}

#[test]
fn tagged_templates_do_not_create_directive_prologues() {
  // `use strict` must be a standalone string literal expression statement; when it is used as a
  // tagged template "tag", it does not enable strict mode.
  assert_accept("\"use strict\"\n`x`\nyield;");
}

#[test]
fn classes_are_strict_ecma_regions() {
  assert_reject("class yield {}");
  assert_reject("class eval {}");
  assert_reject("class A extends (eval = 1) {}");
  assert_reject("class A { m() { with ({}) {} } }");
  assert_reject("class A { m() { delete x; } }");
  assert_reject("class A { m() { 010; } }");
  assert_reject("class A { m() { 08; } }");
  assert_reject(r"class A { m() { '\1'; } }");
  assert_reject("class A { m() { eval = 1; } }");
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
  assert_accept("function yield() { return 1; }");
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
