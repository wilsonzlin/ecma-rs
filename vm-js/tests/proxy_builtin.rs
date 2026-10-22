//! Minimal `%Proxy%` global: typeof shape, revocable, and [[Set]] trap via prototype chain.

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn eval(src: &str) -> Value {
  new_runtime().exec_script(src).unwrap()
}

fn assert_true(src: &str) {
  assert_eq!(eval(src), Value::Bool(true), "expected `{src}` to be true");
}

#[test]
fn typeof_proxy_matches_target_callability() {
  assert_true(r#"typeof new Proxy({}, {}) === "object""#);
  assert_true(r#"typeof new Proxy(function () {}, {}) === "function""#);
}

#[test]
fn revoked_proxy_preserves_typeof() {
  assert_true(
    r#"
      const rp1 = Proxy.revocable({}, {});
      rp1.revoke();
      const rp2 = Proxy.revocable(function () {}, {});
      rp2.revoke();
      typeof rp1.proxy === "object" && typeof rp2.proxy === "function"
    "#,
  );
}

#[test]
fn proxy_set_trap_on_prototype_chain_from_primitive_put() {
  // Shape of language/types/reference/put-value-prop-base-primitive.js
  assert_true(
    r#"
      var count = 0;
      var spy = new Proxy({}, { set: function () { count += 1; return true; } });
      Object.setPrototypeOf(Number.prototype, spy);
      0..test262 = null;
      count === 1
    "#,
  );
}

#[test]
fn proxy_requires_new() {
  assert_true(
    r#"
      let threw = false;
      try { Proxy({}, {}); } catch (e) { threw = e instanceof TypeError; }
      threw
    "#,
  );
}

#[test]
fn regexp_exec_stub_returns_null() {
  assert_true(r#"RegExp("0").exec("1") === null"#);
  assert_true(r#"typeof RegExp("0").exec("1") === "object""#);
}

#[test]
fn reflect_construct_sets_new_target() {
  // Shape of language/expressions/optional-chaining/new-target-optional-call.js
  assert_true(
    r#"
      let called = false;
      function Base() { called = true; }
      function Foo() { new.target?.(); }
      Reflect.construct(Foo, [], Base);
      called === true
    "#,
  );
}
