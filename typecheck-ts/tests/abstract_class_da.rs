//! Abstract-class property definite-assignment / initialization flow vs tsc:
//! - TS2715: abstract instance properties cannot be accessed via `this` during
//!   class initialization (constructor body / instance field initializer).
//! - Nested functions inside those contexts remain allowed.
//! - Concrete overrides in a derived class clear the TS2715 for that name.
//! - TS1267: abstract properties cannot have initializers.
//! - Abstract *methods* are not subject to TS2715.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| matches!(d.code.as_str(), "TS2715" | "TS1267" | "TS2729" | "TS2454"))
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

fn messages(src: &str, code: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .filter(|d| d.code.as_str() == code)
    .map(|d| d.message.clone())
    .collect();
  out.sort();
  out
}

#[test]
fn abstract_prop_read_in_constructor_is_ts2715() {
  let src = r#"
abstract class C {
  abstract prop: string;
  constructor() {
    this.prop;
  }
}
"#;
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2715"),
    "expected TS2715 for this.prop in ctor: {c:?}"
  );
  assert!(
    messages(src, "TS2715")
      .iter()
      .any(|m| m.contains("Abstract property 'prop'") && m.contains("class 'C'")),
    "message should name prop + class: {:?}",
    messages(src, "TS2715")
  );
}

#[test]
fn abstract_prop_write_in_constructor_is_ts2715() {
  let src = r#"
abstract class C {
  abstract prop: string;
  constructor() {
    this.prop = "x";
  }
}
"#;
  assert!(
    codes(src).iter().any(|x| x == "TS2715"),
    "expected TS2715 for this.prop = …: {:?}",
    codes(src)
  );
}

#[test]
fn abstract_prop_in_field_initializer_is_ts2715() {
  let src = r#"
abstract class C {
  abstract prop: string;
  other = this.prop;
}
"#;
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2715"),
    "expected TS2715 for field init this.prop: {c:?}"
  );
  assert!(
    c.iter().any(|x| x == "TS2729"),
    "tsc also emits TS2729 for abstract prop in field init: {c:?}"
  );
}

#[test]
fn nested_function_may_read_abstract_prop() {
  let src = r#"
abstract class C {
  abstract prop: string;
  constructor() {
    const inner = () => this.prop;
    void inner;
  }
  fn = () => this.prop;
}
"#;
  assert!(
    !codes(src).iter().any(|x| x == "TS2715"),
    "nested functions must not TS2715: {:?}",
    codes(src)
  );
}

#[test]
fn abstract_method_call_in_constructor_ok() {
  let src = r#"
abstract class C {
  abstract m(): void;
  constructor() {
    this.m();
  }
}
"#;
  assert!(
    !codes(src).iter().any(|x| x == "TS2715"),
    "abstract methods are not TS2715: {:?}",
    codes(src)
  );
}

#[test]
fn other_instance_access_ok() {
  let src = r#"
abstract class C {
  abstract prop: string;
  constructor(other: C) {
    other.prop;
  }
}
"#;
  assert!(
    !codes(src).iter().any(|x| x == "TS2715"),
    "other.prop is not class-init this-access: {:?}",
    codes(src)
  );
}

#[test]
fn derived_still_abstract_prop_is_ts2715() {
  let src = r#"
abstract class Base {
  abstract prop: string;
}
abstract class Derived extends Base {
  constructor() {
    super();
    this.prop;
  }
}
"#;
  assert!(
    codes(src).iter().any(|x| x == "TS2715"),
    "inherited unresolved abstract prop: {:?}",
    codes(src)
  );
}

#[test]
fn concrete_override_clears_ts2715() {
  let src = r#"
abstract class Base {
  abstract prop: string;
}
class Impl extends Base {
  prop = "";
  constructor() {
    super();
    this.prop;
  }
}
"#;
  assert!(
    !codes(src).iter().any(|x| x == "TS2715"),
    "concrete override clears TS2715: {:?}",
    codes(src)
  );
}

#[test]
fn object_binding_from_this_in_ctor_is_ts2715() {
  let src = r#"
abstract class C {
  abstract x: string;
  abstract y: string;
  constructor() {
    let { x, y: y1 } = this;
    void x; void y1;
  }
}
"#;
  let c = codes(src);
  let n2715 = c.iter().filter(|x| *x == "TS2715").count();
  assert!(
    n2715 >= 2,
    "each abstract binding element should TS2715: {c:?}"
  );
}

#[test]
fn abstract_prop_with_initializer_is_ts1267() {
  let src = r#"
abstract class C {
  abstract prop = 1;
}
"#;
  assert_eq!(
    codes(src),
    vec!["TS1267".to_string()],
    "abstractPropertyInitializer: {:?}",
    codes(src)
  );
}
