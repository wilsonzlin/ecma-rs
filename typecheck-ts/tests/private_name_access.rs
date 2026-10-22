//! TS18013 / TS18014 — private-identifier visibility and nested shadowing.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(opts: CompilerOptions, src: &str) -> Vec<(String, u32, u32)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| {
      (
        d.code.as_str().to_string(),
        d.primary.range.start,
        d.primary.range.end,
      )
    })
    .collect();
  out.sort();
  out
}

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  diags(opts, src).into_iter().map(|(c, _, _)| c).collect()
}

fn opts() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts
}

#[test]
fn private_not_accessible_outside_defining_class_is_ts18013() {
  // Mirrors conformance `privateNameNotAccessibleOutsideDefiningClass.ts`.
  let src = r#"
class A {
  #foo: number = 3;
}
new A().#foo = 4;
"#;
  let c = codes(opts(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18013").count(), 1, "{c:?}");
}

#[test]
fn private_not_accessible_from_derived_class_is_ts18013() {
  // Mirrors conformance `privateNameFieldDerivedClasses.ts`.
  let src = r#"
class Base {
  #prop: number = 123;
  static method(x: Derived) {
    console.log(x.#prop);
  }
}
class Derived extends Base {
  static method(x: Derived) {
    console.log(x.#prop);
  }
}
"#;
  let c = codes(opts(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18013").count(), 1, "{c:?}");
}

#[test]
fn private_access_inside_defining_class_ok() {
  let src = r#"
class A {
  #foo = 1;
  m(a: A) { return a.#foo; }
}
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter().any(|x| x == "TS18013" || x == "TS18014"),
    "inside defining class must be ok: {c:?}"
  );
}

#[test]
fn private_cross_class_access_is_ts18013() {
  // Mirrors conformance `privateNameMethodAccess.ts` (B2 accessing A2).
  let src = r#"
class A2 {
  #method() { return ""; }
}
class B2 {
  m() {
    new A2().#method();
  }
}
"#;
  let c = codes(opts(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18013").count(), 1, "{c:?}");
}

#[test]
fn private_nested_class_shadowing_is_ts18014() {
  // Mirrors conformance `privateNameNestedClassFieldShadowing.ts`.
  let src = r#"
class Base {
  #x;
  constructor() {
    class Derived {
      #x;
      testBase(x: Base) {
        console.log(x.#x);
      }
      testDerived(x: Derived) {
        console.log(x.#x);
      }
    }
  }
}
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18014").count(),
    1,
    "expected one TS18014: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS18013"),
    "shadowing should be TS18014 not TS18013: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TC2008"),
    "nested class name must resolve as a type (no TC2008): {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2339"),
    "own private access on resolved nested class must not be TS2339: {c:?}"
  );
}

#[test]
fn ts18013_span_is_private_identifier() {
  let src = r#"
class A {
  #foo: number = 3;
}
new A().#foo = 4;
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS18013").collect();
  assert_eq!(hits.len(), 1, "{d:?}");
  let (_, start, end) = hits[0];
  let slice = &src[*start as usize..*end as usize];
  assert_eq!(
    slice, "#foo",
    "span should be the private name, got {slice:?}"
  );
}

#[test]
fn named_class_expression_outside_is_ts18013() {
  let src = r#"
const C = class Named {
  #method() { return 42; }
}
new Named().#method;
"#;
  let c = codes(opts(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18013").count(), 1, "{c:?}");
}

#[test]
fn anonymous_class_expression_new_outside_is_ts18013() {
  // Mirrors conformance `privateNameMethodClassExpression.ts` (direct `new C()`).
  let src = r#"
const C = class {
  #method() { return 42; }
  #field = 1;
}
new C().#method;
new C().#field;
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18013").count(),
    2,
    "expected TS18013 for #method and #field: {c:?}"
  );
}

#[test]
fn anonymous_class_expression_get_instance_outside_is_ts18013() {
  // Full conformance shape: factory returns instance; outside access is TS18013.
  let src = r#"
const C = class {
  #field = this.#method();
  #method() { return 42; }
  static getInstance() { return new C(); }
  getField() { return this.#field; }
}
C.getInstance().#method;
C.getInstance().#field;
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18013").count(),
    2,
    "expected TS18013 for #method and #field via getInstance: {c:?}"
  );
}

#[test]
fn named_class_expression_via_const_outside_is_ts18013() {
  let src = r#"
const C = class Named {
  #method() { return 42; }
}
new C().#method;
"#;
  let c = codes(opts(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18013").count(), 1, "{c:?}");
}

#[test]
fn static_private_on_anonymous_class_expression_is_ts18013() {
  // Mirrors conformance `privateNameStaticMethodClassExpression.ts`.
  let src = r#"
const C = class D {
  static #field = D.#method();
  static #method() { return 42; }
  static getClass() { return D; }
}
C.getClass().#method;
C.getClass().#field;
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18013").count(),
    2,
    "expected TS18013 for static #method and #field: {c:?}"
  );
}

#[test]
fn nested_method_access_shadowing_and_any_unknown() {
  // Mirrors conformance `privateNameNestedMethodAccess.ts`.
  let src = r#"
class C {
  #foo = 42;
  #bar() { new C().#baz; }
  get #baz() { return 42; }

  m() {
    return class D {
      #bar() {}
      constructor() {
        new C().#foo;
        new C().#bar; // TS18014
        new C().#baz;
        new D().#bar;
      }

      n(x: any) {
        x.#foo;
        x.#bar;
        x.#unknown; // TS2339
      }
    }
  }
}
"#;
  let d = diags(opts(), src);
  let c: Vec<_> = d.iter().map(|(c, _, _)| c.clone()).collect();
  assert_eq!(
    c.iter().filter(|x| *x == "TS18014").count(),
    1,
    "expected one TS18014 for shadowed #bar: {c:?}"
  );
  assert_eq!(
    c.iter().filter(|x| *x == "TS2339").count(),
    1,
    "expected one TS2339 for #unknown on any: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2304"),
    "named class expression D must resolve inside its body: {c:?}"
  );
  let ts18014 = d.iter().find(|(c, _, _)| c == "TS18014").unwrap();
  assert_eq!(&src[ts18014.1 as usize..ts18014.2 as usize], "#bar");
  let ts2339 = d.iter().find(|(c, _, _)| c == "TS2339").unwrap();
  assert_eq!(&src[ts2339.1 as usize..ts2339.2 as usize], "#unknown");
}

#[test]
fn named_class_expression_self_name_in_constructor() {
  // `return class D { constructor() { new D(); } }` — D is in scope.
  let src = r#"
class C {
  m() {
    return class D {
      constructor() {
        new D();
      }
    }
  }
}
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter().any(|x| x == "TS2304"),
    "named class expression must bind D in constructor: {c:?}"
  );
}

#[test]
fn undeclared_private_on_any_inside_class_is_ts2339() {
  // tsc: any-like + no lexical private → TS2339 (not silent, not TS18016).
  let src = r#"
class C {
  #bar = 1;
  m(x: any) {
    x.#bar;
    x.#unknown;
  }
}
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2339").count(),
    1,
    "expected TS2339 for #unknown on any: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS18016"),
    "inside class undeclared # on any is TS2339 not TS18016: {c:?}"
  );
}

#[test]
fn static_private_accessor_on_typeof_derived_is_ts2339() {
  // Mirrors conformance `privateNameStaticAccessorssDerivedClasses.ts`.
  // Private statics are not present on `typeof Derived`, so both Base and
  // Derived emit TS2339 (not TS18013) when reading `x.#prop`.
  let src = r#"
class Base {
  static get #prop(): number { return 123; }
  static method(x: typeof Derived) {
    console.log(x.#prop);
  }
}
class Derived extends Base {
  static method(x: typeof Derived) {
    console.log(x.#prop);
  }
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 2, "expected TS2339×2: {d:?}");
  for (_, start, end) in &hits {
    assert_eq!(&src[*start as usize..*end as usize], "#prop");
  }
  assert!(
    !d.iter().any(|(c, _, _)| c == "TS18013" || c == "TS18014"),
    "missing on typeof Derived must be TS2339, not accessibility: {d:?}"
  );
}

#[test]
fn static_private_accessor_own_access_ok() {
  // Negative control: defining-class static access must stay quiet.
  let src = r#"
class Base {
  static get #prop(): number { return 123; }
  static method() {
    console.log(Base.#prop);
    console.log(this.#prop);
  }
}
"#;
  let c = codes(opts(), src);
  assert!(
    !c.iter()
      .any(|x| x == "TS2339" || x == "TS18013" || x == "TS18014"),
    "own static private accessor access must be ok: {c:?}"
  );
}

#[test]
fn static_private_field_via_instance_this_is_ts2339() {
  // Mirrors conformance `privateNameStaticFieldAccess.ts`.
  let src = r#"
class A {
  static #myField = "hello world";
  constructor() {
    console.log(A.#myField);
    console.log(this.#myField);
  }
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected one TS2339: {d:?}");
  assert_eq!(&src[hits[0].1 as usize..hits[0].2 as usize], "#myField");
  assert!(
    !d.iter().any(|(c, _, _)| c == "TS18013"),
    "static private on instance this is nonexistent, not TS18013: {d:?}"
  );
}

#[test]
fn nested_class_decl_value_binding_and_shadowing_ts18014() {
  // Mirrors conformance `privateNamesInNestedClasses-1.ts`: nested `class B`
  // must resolve as a value (`new B()`) while shadowed outer `#foo` is TS18014.
  let src = r#"
class A {
  #foo = "A's #foo";
  method() {
    class B {
      #foo = "B's #foo";
      bar(a: any) {
        a.#foo;
      }
      baz(a: A) {
        a.#foo;
      }
      quux(b: B) {
        b.#foo;
      }
    }
    const a = new A();
    new B().bar(a);
    new B().baz(a);
    const b = new B();
    new B().quux(b);
  }
}
"#;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18014").count(),
    1,
    "expected one TS18014: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TS2304" || x == "TC3000"),
    "nested class B must resolve as a value (no TS2304/TC3000): {c:?}"
  );
}

#[test]
fn static_private_not_inherited_on_child_ctor_is_ts2339() {
  // Mirrors conformance `privateNamesConstructorChain-1.ts`.
  let src = r#"
class Parent {
  #foo = 3;
  static #bar = 5;
  accessChildProps() {
    new Child().#foo;
    Child.#bar;
  }
}
class Child extends Parent {
  #foo = "foo";
  #bar = "bar";
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected one TS2339: {d:?}");
  assert_eq!(&src[hits[0].1 as usize..hits[0].2 as usize], "#bar");
}

#[test]
fn private_names_excluded_from_keyof_are_ts2322() {
  // Mirrors conformance `privateNamesAndkeyof.ts`.
  let src = r##"
class A {
  #fooField = 3;
  #fooMethod() {}
  get #fooProp() { return 1; }
  set #fooProp(value: number) {}
  bar = 3;
  baz = 3;
}
let k: keyof A = "bar";
k = "baz";
k = "#fooField";
k = "#fooMethod";
k = "#fooProp";
k = "fooField";
k = "fooMethod";
k = "fooProp";
"##;
  let c = codes(opts(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2322").count(),
    6,
    "expected TS2322×6 for private/non-keys: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TC3000"),
    "keyof A must not be implicit any: {c:?}"
  );
}

#[test]
fn private_name_declaration_merging_new_returns_class_instance() {
  // Mirrors conformance `privateNameDeclarationMerging.ts`: class+interface
  // merge adds `new (): D`, but uncontextualized `new C()` still returns `C`
  // so `c.#x` is OK; only `d.#x` (receiver typed `D`) is TS2339.
  let src = r#"
class D {}
class C {
    #x;
    foo () {
        const c = new C();
        c.#x;     // OK
        const d: D = new C();
        d.#x;    // Error
    }
}
interface C {
    new (): D;
}
"#;
  let d = diags(opts(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected exactly one TS2339 on d.#x: {d:?}");
  let src_slice = &src[hits[0].1 as usize..hits[0].2 as usize];
  assert_eq!(
    src_slice, "#x",
    "primary span should be the private name: {hits:?}"
  );
  // Span must be the `d.#x` occurrence, not `c.#x`.
  let d_hash = src.find("d.#x").expect("d.#x") as u32;
  assert_eq!(
    hits[0].1,
    d_hash + 2,
    "TS2339 must be on d.#x, got {hits:?}"
  );
}
