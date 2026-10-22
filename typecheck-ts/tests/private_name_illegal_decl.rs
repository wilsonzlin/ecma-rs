//! TS18016 — private identifiers are not allowed outside class bodies
//! (object literals / type & interface signatures / ambient type literals;
//! any-like private *access* outside a class).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(opts: CompilerOptions, src: &str) -> Vec<(String, u32, u32, String)> {
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
        d.message.clone(),
      )
    })
    .collect();
  out.sort();
  out
}

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  diags(opts, src).into_iter().map(|(c, _, _, _)| c).collect()
}

fn es2015() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  // These tests exercise JS semantic checking (tsc `--checkJs`).
  opts.check_js = Some(true);
  opts
}

#[test]
fn object_literal_private_field_is_ts18016() {
  // Mirrors conformance `privateNameInObjectLiteral-1.ts`.
  let src = "const obj = {\n    #foo: 1\n};\n";
  let c = codes(es2015(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18016").count(), 1, "{c:?}");
  let d = diags(es2015(), src);
  let ts18016 = d.iter().find(|(c, _, _, _)| c == "TS18016").unwrap();
  let slice = &src[ts18016.1 as usize..ts18016.2 as usize];
  assert_eq!(
    slice, "#foo",
    "span should be the private name, got {slice:?}"
  );
}

#[test]
fn object_literal_private_method_is_ts18016() {
  // Mirrors conformance `privateNameInObjectLiteral-2.ts`.
  let src = "const obj = {\n    #foo() {\n\n    }\n};\n";
  let c = codes(es2015(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18016").count(), 1, "{c:?}");
}

#[test]
fn object_literal_private_getter_is_ts18016() {
  // Mirrors conformance `privateNameInObjectLiteral-3.ts`.
  let src = "const obj = {\n    get #foo() {\n        return \"\"\n    }\n};\n";
  let c = codes(es2015(), src);
  assert_eq!(c.iter().filter(|x| *x == "TS18016").count(), 1, "{c:?}");
  let d = diags(es2015(), src);
  let ts18016 = d.iter().find(|(c, _, _, _)| c == "TS18016").unwrap();
  let slice = &src[ts18016.1 as usize..ts18016.2 as usize];
  assert_eq!(
    slice, "#foo",
    "span should be the private name, got {slice:?}"
  );
}

#[test]
fn type_and_interface_private_signatures_are_ts18016() {
  // Mirrors conformance `privateNameAndPropertySignature.ts`.
  let src = r#"
type A = {
    #foo: string;
    #bar(): string;
}

interface B {
    #foo: string;
    #bar(): string;
}

declare const x: {
    #foo: number;
    bar: {
        #baz: string;
        #taz(): string;
    }
    #baz(): string;
};

declare const y: [{ qux: { #quux: 3 } }];
"#;
  let c = codes(es2015(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18016").count(),
    9,
    "nine illegal private decls: {c:?}"
  );
}

#[test]
fn prototype_object_literal_private_members_are_ts18016() {
  // Mirrors conformance `privateNameBadDeclaration.ts` (TS18016 subset).
  let src = r#"
function A() { }
A.prototype = {
  #x: 1,
  #m() {},
  get #p() { return "" }
}
class B { }
B.prototype = {
  #y: 2,
  #m() {},
  get #p() { return "" }
}
"#;
  let c = codes(es2015(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18016").count(),
    6,
    "six illegal private decls on prototypes: {c:?}"
  );
}

#[test]
fn function_prototype_private_access_is_ts18016_not_ts2339_on_prototype() {
  // Mirrors conformance `privateNameBadAssignment.ts`: `A.prototype.#no`.
  // Bare callables expose `Function.prototype: any`, so the private access is
  // any-like → TS18016 only (no rust_extra TS2339 on `prototype`).
  let src = r#"
function A() { }
A.prototype.#no = 2;
"#;
  let d = diags(es2015(), src);
  let c: Vec<_> = d.iter().map(|(c, _, _, _)| c.as_str()).collect();
  assert!(
    !c.iter().any(|x| *x == "TS2339"),
    "must not report Property 'prototype' does not exist: {d:?}"
  );
  assert_eq!(
    c.iter().filter(|x| **x == "TS18016").count(),
    1,
    "expected TS18016 on #no via any-like prototype: {d:?}"
  );
  let ts18016 = d.iter().find(|(c, _, _, _)| c == "TS18016").unwrap();
  assert_eq!(&src[ts18016.1 as usize..ts18016.2 as usize], "#no");
}

#[test]
fn outside_class_private_access_on_any_is_ts18016() {
  // Mirrors conformance `privateNameBadAssignment.ts` (TS18016 subset).
  let src = r#"
declare const exports: any;
exports.#nope = 1;
function A() { }
(null as any).#no = 2;
"#;
  let c = codes(es2015(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18016").count(),
    2,
    "two any-like outside-class private accesses: {c:?}"
  );
  let d = diags(es2015(), src);
  let slices: Vec<_> = d
    .iter()
    .filter(|(c, _, _, _)| c == "TS18016")
    .map(|(_, s, e, _)| &src[*s as usize..*e as usize])
    .collect();
  assert_eq!(
    slices,
    ["#nope", "#no"],
    "primary spans: {slices:?} from {d:?}"
  );
}

#[test]
fn outside_class_private_access_on_unresolved_is_ts18016() {
  // Unresolved names recover as any (tsc errorType) → TS18016 on the private.
  // `.ts` path (no CommonJS ambient seeding).
  let src = "exports.#nope = 1;\n";
  let d = diags(es2015(), src);
  let c: Vec<_> = d.iter().map(|(c, _, _, _)| c.as_str()).collect();
  assert!(c.contains(&"TS2304"), "unresolved exports: {c:?}");
  assert_eq!(
    c.iter().filter(|x| **x == "TS18016").count(),
    1,
    "expected TS18016 on unresolved any-like receiver: {c:?}"
  );
  let ts18016 = d.iter().find(|(c, _, _, _)| c == "TS18016").unwrap();
  assert_eq!(&src[ts18016.1 as usize..ts18016.2 as usize], "#nope");
}

#[test]
fn checkjs_exports_private_access_is_ts2304_and_ts18016() {
  // Mirrors conformance `privateNameJsBadAssignment.js` (checkJs): private
  // `exports.#nope` must not seed CommonJS `exports` — TS2304 + TS18016.
  use typecheck_ts::lib_support::FileKind;
  use typecheck_ts::{Host, HostError};

  struct JsHost {
    inner: MemoryHost,
  }
  impl Host for JsHost {
    fn file_text(&self, file: &FileKey) -> Result<std::sync::Arc<str>, HostError> {
      self.inner.file_text(file)
    }
    fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
      self.inner.resolve(from, specifier)
    }
    fn compiler_options(&self) -> CompilerOptions {
      self.inner.compiler_options()
    }
    fn file_kind(&self, file: &FileKey) -> FileKind {
      assert_eq!(self.inner.file_kind(file), FileKind::Js);
      FileKind::Js
    }
  }

  let mut opts = es2015();
  opts.no_default_lib = true;
  let mut host = JsHost {
    inner: MemoryHost::with_options(opts),
  };
  let key = FileKey::new("privateNameJsBadAssignment.js");
  let src = "exports.#nope = 1;\n";
  host.inner.insert(key.clone(), src);
  let program = Program::new(host, vec![key]);
  let mut d: Vec<_> = program
    .check()
    .into_iter()
    .map(|diag| {
      (
        diag.code.as_str().to_string(),
        diag.primary.range.start,
        diag.primary.range.end,
        diag.message.clone(),
      )
    })
    .collect();
  d.sort();
  let c: Vec<_> = d.iter().map(|(c, _, _, _)| c.as_str()).collect();
  assert!(
    c.contains(&"TS2304"),
    "checkJs must not seed exports for exports.#…: {d:?}"
  );
  assert_eq!(
    c.iter().filter(|x| **x == "TS18016").count(),
    1,
    "expected TS18016: {d:?}"
  );
  let ts18016 = d.iter().find(|(c, _, _, _)| c == "TS18016").unwrap();
  assert_eq!(&src[ts18016.1 as usize..ts18016.2 as usize], "#nope");
}

#[test]
fn inside_class_private_access_on_any_with_lexical_no_ts18016() {
  // tsc: any-like + lexically scoped private → allow (no TS18016).
  let src = r#"
class C {
  #bar = 6;
  m(o: any) {
    o.#bar = 6;
  }
}
"#;
  let c = codes(es2015(), src);
  assert!(
    !c.iter().any(|x| x == "TS18016"),
    "lexical private on any inside class must not be TS18016: {c:?}"
  );
}

#[test]
fn undeclared_private_on_class_constructor_is_ts2339() {
  // Mirrors conformance `privateNameBadAssignment.ts`: `B.#foo`.
  let src = r#"
class B {}
B.#foo = 3;
"#;
  let d = diags(es2015(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected one TS2339: {d:?}");
  let slice = &src[hits[0].1 as usize..hits[0].2 as usize];
  assert_eq!(
    slice, "#foo",
    "span should be the private name, got {slice:?}"
  );
  assert!(
    hits[0].3.contains("#foo"),
    "message should mention #foo: {}",
    hits[0].3
  );
}

#[test]
fn undeclared_private_on_this_is_ts2339() {
  // Mirrors `privateNameBadAssignment.ts` / `privateNameBadDeclaration.ts`.
  let src = r#"
class C {
  #bar = 6;
  constructor() {
    this.#foo = 3;
  }
}
"#;
  let d = diags(es2015(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected one TS2339: {d:?}");
  let slice = &src[hits[0].1 as usize..hits[0].2 as usize];
  assert_eq!(
    slice, "#foo",
    "span should be the private name, got {slice:?}"
  );
  assert!(
    !d.iter()
      .any(|(c, _, _, _)| c == "TS18013" || c == "TS18016"),
    "undeclared on concrete this must be TS2339 only: {d:?}"
  );
}

#[test]
fn undeclared_private_on_empty_class_this_is_ts2339() {
  // Mirrors `privateNameBadDeclaration.ts`: class with no privates, `this.#z`.
  let src = r#"
class C {
  constructor() {
    this.#z = 3;
  }
}
"#;
  let d = diags(es2015(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected one TS2339: {d:?}");
  let slice = &src[hits[0].1 as usize..hits[0].2 as usize];
  assert_eq!(
    slice, "#z",
    "span should be the private name, got {slice:?}"
  );
}

#[test]
fn undeclared_private_read_on_instance_is_ts2339() {
  let src = r#"
class C {
  m() {
    return this.#missing;
  }
}
"#;
  let d = diags(es2015(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected one TS2339: {d:?}");
  assert_eq!(&src[hits[0].1 as usize..hits[0].2 as usize], "#missing");
}
