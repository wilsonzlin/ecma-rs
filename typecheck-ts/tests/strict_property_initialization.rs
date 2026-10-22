//! TS2564 / TS2565 under `strictPropertyInitialization` + `strictNullChecks`.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes_with(opts: CompilerOptions, src: &str) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| matches!(d.code.as_str(), "TS2564" | "TS2565"))
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

fn spi_on() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.strict_property_initialization = true;
  opts.no_implicit_any = false;
  opts
}

fn spi_off() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.strict_property_initialization = false;
  opts
}

#[test]
fn missing_initializer_is_ts2564() {
  let src = r#"
class C {
  a: number;
  b: number | undefined;
  c: number | null;
  d?: number;
}
"#;
  let c = codes_with(spi_on(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2564").count(),
    2,
    "a and c (null≠undefined) should TS2564; b/d exempt: {c:?}"
  );
  assert!(codes_with(spi_off(), src).is_empty());
}

#[test]
fn private_fields_checked() {
  let src = r#"
class C {
  #f: number;
  #g: number | undefined;
}
"#;
  let c = codes_with(spi_on(), src);
  assert_eq!(c, vec!["TS2564".to_string()], "only #f: {c:?}");
}

#[test]
fn initializer_and_ctor_assignment_ok() {
  let src = r#"
class C4 {
  a = 0;
  b: number = 0;
}
class C5 {
  a: number;
  #b: number;
  constructor() {
    this.a = 0;
    this.#b = 0;
  }
}
"#;
  assert!(
    codes_with(spi_on(), src).is_empty(),
    "{:?}",
    codes_with(spi_on(), src)
  );
}

#[test]
fn early_return_requires_assignment_on_all_paths() {
  let src = r#"
class C6 {
  a: number;
  #b: number;
  constructor(cond: boolean) {
    if (cond) {
      return;
    }
    this.a = 0;
    this.#b = 0;
  }
}
class C7 {
  a: number;
  #b: number;
  constructor(cond: boolean) {
    if (cond) {
      this.a = 1;
      this.#b = 1;
      return;
    }
    this.a = 0;
    this.#b = 1;
  }
}
"#;
  let c = codes_with(spi_on(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2564").count(),
    2,
    "C6 a/#b error; C7 ok: {c:?}"
  );
}

#[test]
fn string_literal_keys_not_checked() {
  let src = r#"
class C8 {
  a: number;
  "b": number;
  0: number;
}
"#;
  let c = codes_with(spi_on(), src);
  assert_eq!(c, vec!["TS2564".to_string()], "only identifier a: {c:?}");
}

#[test]
fn abstract_and_ambient_exempt() {
  let src = r#"
declare class C2 {
  a: number;
}
abstract class C9 {
  abstract a: number;
}
"#;
  assert!(codes_with(spi_on(), src).is_empty());
}

#[test]
fn used_before_assigned_is_ts2565() {
  let src = r#"
class C10 {
  a: number;
  b: number;
  c?: number;
  #d: number;
  constructor() {
    let x = this.a;
    this.a = this.b;
    this.b = this.#d;
    this.b = x;
    this.#d = x;
    let y = this.c;
  }
}
"#;
  let c = codes_with(spi_on(), src);
  let n2565 = c.iter().filter(|x| *x == "TS2565").count();
  assert_eq!(n2565, 3, "a, b, #d used before assign: {c:?}");
  // a/b/#d are assigned on all paths by the end → no TS2564.
  assert!(
    !c.iter().any(|x| x == "TS2564"),
    "ctor assigns all required props: {c:?}"
  );
}

#[test]
fn requires_strict_null_checks() {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = false;
  opts.strict_property_initialization = true;
  let src = "class C { a: number; }";
  assert!(
    codes_with(opts, src).is_empty(),
    "SPI without strictNullChecks is a no-op"
  );
}

fn all_codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn ctor_this_prop_and_string_enum_no_tc3000() {
  // Mirrors SPI fixture leftovers: `let x = this.a` / `let y = this.c` and
  // string enum members must not produce TC3000 under `@strict` (noImplicitAny).
  let mut opts = spi_on();
  opts.no_implicit_any = true;
  let src = r#"
class C10 {
  a: number;
  b: number;
  c?: number;
  constructor() {
    let x = this.a;
    this.a = this.b;
    this.b = x;
    let y = this.c;
  }
}
enum E {
  A = "A",
  B = "B"
}
class C13 {
  [E.A]: number;
  constructor() {
    this[E.A] = 1;
  }
}
"#;
  let c = all_codes(opts, src);
  assert!(
    !c.iter().any(|x| x == "TC3000"),
    "no TC3000 on ctor this.prop / string enum: {c:?}"
  );
  assert_eq!(
    c.iter().filter(|x| *x == "TS2565").count(),
    2,
    "a and b used before assign: {c:?}"
  );
}

#[test]
fn method_and_field_initializer_this_prop_no_tc3000() {
  // Non-ctor instance `this` / static `this` must resolve members so
  // `let x = this.a` is not unknown→TC3000 under noImplicitAny.
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  let src = r#"
class C {
  a: number = 1;
  b = this.a;
  m() {
    let x = this.a;
    return x;
  }
  static s: number = 2;
  static t = this.s;
  static sm() {
    let z = this.s;
    return z;
  }
}
"#;
  let c = all_codes(opts, src);
  assert!(
    !c.iter().any(|x| x == "TC3000"),
    "no TC3000 on method/field/static this.prop: {c:?}"
  );
}

#[test]
fn class_getter_setter_no_spurious_tc3000() {
  // Accessors are function-bodied members: infer from return / annotated
  // params. `get g()` itself must not be TC3000 under noImplicitAny.
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  let src = r#"
class C {
  a: number = 1;
  get g() {
    return this.a;
  }
  set h(v: number) {
    this.a = v;
  }
  get i(): number {
    return this.a;
  }
  m() {
    let x = this.g;
    let y = this.i;
    return x + y;
  }
}
"#;
  let c = all_codes(opts.clone(), src);
  assert!(
    !c.iter().any(|x| x == "TC3000"),
    "no spurious TC3000 on getters/setters: {c:?}"
  );

  // Paired getter supplies contextual type for the setter parameter.
  let src_paired = r#"
class E {
  a: number = 1;
  get g() { return this.a; }
  set g(v) { this.a = v; }
}
"#;
  let paired = all_codes(opts.clone(), src_paired);
  assert!(
    !paired.iter().any(|x| x == "TC3000"),
    "getter+setter pair must not TC3000 on setter param: {paired:?}"
  );

  // Unannotated setter params remain genuine --noImplicitAny (tsc TS7006).
  let src_bad_setter = r#"
class D {
  a: number = 1;
  set h(v) {
    this.a = v;
  }
}
"#;
  let bad = all_codes(opts, src_bad_setter);
  assert!(
    bad.iter().any(|x| x == "TC3000"),
    "unannotated setter param still TC3000: {bad:?}"
  );
}

#[test]
fn static_block_assigned_fields_no_spurious_tc3000() {
  // Unannotated static fields initialized in static blocks must infer (tsc:
  // classStaticBlockUseBeforeDef1) — no TC3000 on `x`/`y`/`z` or `<static_block>`.
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  opts.use_define_for_class_fields = true;
  opts.target = typecheck_ts::lib_support::ScriptTarget::EsNext;
  let src = r#"
class C {
  static x;
  static {
    this.x = 1;
  }
  static y = this.x;
  static z;
  static {
    this.z = this.y;
  }
}
"#;
  let c = all_codes(opts, src);
  assert!(
    !c.iter().any(|x| x == "TC3000"),
    "no TC3000 on static-block-initialized fields: {c:?}"
  );
}

#[test]
fn static_block_use_before_field_decl_is_ts2729() {
  // Static block before the field declaration: tsc TS2729 on the write.
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = true;
  opts.use_define_for_class_fields = true;
  opts.target = typecheck_ts::lib_support::ScriptTarget::EsNext;
  let src = r#"
class C {
  static {
    this.x = 1;
  }
  static x;
}
"#;
  let c = all_codes(opts, src);
  assert!(
    !c.iter().any(|x| x == "TC3000"),
    "no spurious TC3000 when field is assigned in earlier static block: {c:?}"
  );
  assert!(
    c.iter().any(|x| x == "TS2729"),
    "expected TS2729 use-before-initialization: {c:?}"
  );
}
