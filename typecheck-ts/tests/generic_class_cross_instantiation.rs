//! Regression: dual instantiations of a generic class used as method parameter
//! types must not stack-overflow during member-property lookup.
//!
//! Minimal shape of upstream
//! `classes/members/privateNames/privateNamesInGenericClasses.ts`:
//! methods taking `C<number>` and `C<string>` that read a field on the
//! parameter. The post-check `lookup_interned_property_type` path used to
//! recurse forever when `expand_ref` returned an in-progress `Ref`.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn generic_class_cross_instantiation_member_lookup_terminates() {
  let source = r#"
class C<T> {
  foo: T;
  baz(x: C<number>) { return x.foo; }
  quux(x: C<string>) { return x.foo; }
}
"#;
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    strict_null_checks: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key]);
  // Must return (not abort). Diagnostic contents are not the focus here.
  let _ = program.check();
}

#[test]
fn private_names_in_generic_classes_terminates() {
  let source = r#"
class C<T> {
  #foo: T;
  #method(): T { return this.#foo; }
  get #prop(): T { return this.#foo; }
  set #prop(value: T) { this.#foo = value; }
  bar(x: C<T>) { return x.#foo; }
  baz(x: C<number>) { return x.#foo; }
  quux(x: C<string>) { return x.#foo; }
}
declare let a: C<number>;
declare let b: C<string>;
a = b;
b = a;
"#;
  let key = FileKey::new("main.ts");
  let mut host = MemoryHost::with_options(CompilerOptions {
    strict_null_checks: true,
    ..Default::default()
  });
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key]);
  let _ = program.check();
}
