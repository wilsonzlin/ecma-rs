//! Regression tests for `ToString` / `ToPrimitive` (§7.1.1 / §7.1.17) and
//! `Object.prototype.propertyIsEnumerable` (§20.1.3.5) — the harness helpers
//! (`propertyHelper.js`) depend on both.

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn rt() -> JsRuntime {
  JsRuntime::new(
    Vm::new(VmOptions::default()),
    Heap::new(HeapLimits::new(16 * 1024 * 1024, 16 * 1024 * 1024)),
  )
  .unwrap()
}

fn eval(rt: &mut JsRuntime, src: &str) -> Value {
  rt.exec_script(src)
    .unwrap_or_else(|e| panic!("eval `{src}` failed: {e}"))
}

fn as_str(rt: &JsRuntime, v: Value) -> String {
  match v {
    Value::String(s) => rt.heap().get_string(s).unwrap().to_utf8_lossy(),
    other => panic!("expected string, got {other:?}"),
  }
}

#[test]
fn string_constructor_uses_to_primitive() {
  let mut rt = rt();
  let v = eval(&mut rt, r#"String({toString:function(){return "T"}})"#);
  assert_eq!(as_str(&rt, v), "T");

  // String hint prefers `toString` over `valueOf`.
  let v = eval(
    &mut rt,
    r#"String({valueOf:function(){return 7}, toString:function(){return "T"}})"#,
  );
  assert_eq!(as_str(&rt, v), "T");

  // Without a custom `Function.prototype.toString`, callable objects fall through to
  // `Object.prototype.toString` → `"[object Function]"`.
  let v = eval(&mut rt, r#"String(Number)"#);
  assert_eq!(as_str(&rt, v), "[object Function]");
}

#[test]
fn array_join_stringifies_object_elements() {
  let mut rt = rt();
  let v = eval(&mut rt, r#"[Number].join(";")"#);
  assert_eq!(as_str(&rt, v), "[object Function]");

  let v = eval(
    &mut rt,
    r#"[{toString:function(){return "a"}}, {toString:function(){return "b"}}].join("-")"#,
  );
  assert_eq!(as_str(&rt, v), "a-b");
}

#[test]
fn property_is_enumerable_reads_own_descriptor() {
  let mut rt = rt();
  assert_eq!(
    eval(
      &mut rt,
      r#"Object.prototype.propertyIsEnumerable.call(Number, "EPSILON")"#
    ),
    Value::Bool(false)
  );
  assert_eq!(
    eval(
      &mut rt,
      r#"Object.prototype.propertyIsEnumerable.call({a:1}, "a")"#
    ),
    Value::Bool(true)
  );
  // Inherited properties are not own → false (no `Object.create` dependency).
  assert_eq!(
    eval(
      &mut rt,
      r#"(function(){ var p={a:1}; var o={}; o.__proto__=p; return Object.prototype.propertyIsEnumerable.call(o,"a"); })()"#
    ),
    Value::Bool(false)
  );
}

#[test]
fn wrapper_objects_to_primitive_for_number_and_equality() {
  let mut rt = rt();
  assert_eq!(eval(&mut rt, "Number(new Number())"), Value::Number(0.0));
  assert_eq!(
    eval(&mut rt, "Number(new Boolean(true))"),
    Value::Number(1.0)
  );
  assert_eq!(
    eval(&mut rt, "(new Boolean(true) == true)"),
    Value::Bool(true)
  );
  assert_eq!(eval(&mut rt, "(new Boolean(true) == 1)"), Value::Bool(true));
  assert_eq!(
    eval(&mut rt, "(new Boolean(true) == \"1\")"),
    Value::Bool(true)
  );
  assert_eq!(
    eval(&mut rt, "(true != new Boolean(true))"),
    Value::Bool(false)
  );
  // Object==Object is reference equality — distinct wrappers are never equal (§7.2.14).
  assert_eq!(
    eval(&mut rt, "(new Boolean(true) == new Boolean(true))"),
    Value::Bool(false)
  );
}

#[test]
fn number_epsilon_property_helper_shape() {
  // Compact form of built-ins/Number/EPSILON.js + propertyHelper checks.
  let mut rt = rt();
  let v = eval(
    &mut rt,
    r#"
    (function(){
      if (!(Number.EPSILON > 0)) return "value";
      var d = Object.getOwnPropertyDescriptor(Number, "EPSILON");
      if (d.writable !== false || d.enumerable !== false || d.configurable !== false) return "desc";
      if (Object.prototype.propertyIsEnumerable.call(Number, "EPSILON") !== false) return "enum";
      return "ok";
    })()
    "#,
  );
  assert_eq!(as_str(&rt, v), "ok");
}
