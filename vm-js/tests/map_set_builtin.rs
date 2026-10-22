//! Minimal `%Map%` / `%Set%`: constructor, get/set/has/delete/size, SameValueZero, iteration.

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
fn map_basic_get_set_has_delete_size() {
  assert_true(
    r#"
      const m = new Map();
      m.set("a", 1);
      m.set("b", 2);
      m.size === 2 && m.get("a") === 1 && m.has("b") && m.delete("a") && m.size === 1 && !m.has("a")
    "#,
  );
}

#[test]
fn map_requires_new_and_same_value_zero() {
  assert_true(
    r#"
      let threw = false;
      try { Map(); } catch (e) { threw = e instanceof TypeError; }
      const m = new Map();
      m.set(NaN, "nan");
      m.set(-0, "zero");
      threw && m.get(NaN) === "nan" && m.get(0) === "zero" && m.size === 2
    "#,
  );
}

#[test]
fn map_iterable_constructor_and_iteration() {
  // Note: `for (const|let … of …)` still hits a lexical-binding re-init gap in the
  // resumable for-of path; use `var` / forEach here to assert Map iteration itself.
  assert_true(
    r#"
      const m = new Map([["x", 1], ["y", 2]]);
      let keys = [];
      for (var k of m.keys()) keys.push(k);
      let vals = [];
      for (var v of m.values()) vals.push(v);
      let entries = [];
      for (var e of m) entries.push(e[0] + ":" + e[1]);
      m.size === 2 && keys.join(",") === "x,y" && vals.join(",") === "1,2"
        && entries.join(",") === "x:1,y:2"
    "#,
  );
}

#[test]
fn set_basic_add_has_delete_size_and_iteration() {
  assert_true(
    r#"
      const s = new Set([1, 2, 2, 3]);
      s.add(4);
      let values = [];
      for (var v of s) values.push(v);
      s.size === 4 && s.has(2) && s.delete(2) && !s.has(2) && values.join(",") === "1,2,3,4"
    "#,
  );
}

#[test]
fn set_stores_null_and_undefined() {
  assert_true(
    r#"
      const s = new Set();
      s.add(null);
      s.add(undefined);
      s.has(null) && s.has(undefined) && s.size === 2
    "#,
  );
}

#[test]
fn set_composition_methods() {
  assert_true(
    r#"
      const a = new Set([1, 2]);
      const b = new Set([2, 3]);
      const u = [...a.union(b)];
      const i = [...a.intersection(b)];
      const d = [...a.difference(b)];
      const s = [...a.symmetricDifference(b)];
      u.join(",") === "1,2,3"
        && i.join(",") === "2"
        && d.join(",") === "1"
        && s.join(",") === "1,3"
        && a.isSubsetOf(new Set([1, 2, 3]))
        && a.isSupersetOf(new Set([1]))
        && a.isDisjointFrom(new Set([4]))
        && !a.isDisjointFrom(b)
    "#,
  );
}

#[test]
fn map_for_each_order() {
  assert_true(
    r#"
      const m = new Map([["a", 1], ["b", 2]]);
      const seen = [];
      m.forEach((v, k) => { seen.push(k + ":" + v); });
      seen.join(",") === "a:1,b:2"
    "#,
  );
}

#[test]
fn weakmap_object_and_symbol_keys() {
  assert_true(
    r#"
      const wm = new WeakMap();
      const o = {};
      const s = Symbol("k");
      wm.set(o, 1);
      wm.set(s, 2);
      let threw = false;
      try { wm.set(1, 3); } catch (e) { threw = e instanceof TypeError; }
      let threwFor = false;
      try { wm.set(Symbol.for("reg"), 4); } catch (e) { threwFor = e instanceof TypeError; }
      wm.get(o) === 1 && wm.get(s) === 2 && wm.has(o) && wm.delete(s) && !wm.has(s)
        && threw && threwFor && Symbol.keyFor(Symbol.for("reg")) === "reg"
    "#,
  );
}

#[test]
fn weakset_add_has_delete() {
  assert_true(
    r#"
      const ws = new WeakSet();
      const o = {};
      ws.add(o);
      let threw = false;
      try { ws.add(null); } catch (e) { threw = e instanceof TypeError; }
      ws.has(o) && ws.delete(o) && !ws.has(o) && threw
    "#,
  );
}

#[test]
fn typed_array_and_weakref_as_map_set_keys() {
  assert_true(
    r#"
      const i32 = new Int32Array([0, 1]);
      const u32 = new Uint32Array([0, 1]);
      const bi64 = new BigInt64Array([1n, 9007199254740991n]);
      const bu64 = new BigUint64Array([1n, 9007199254740991n]);
      const wr = new WeakRef({});
      const m = new Map([[i32, 1], [u32, 2], [bi64, 3], [bu64, 4], [wr, 5]]);
      const s = new Set([i32, u32, bi64, bu64, wr]);
      m.get(i32) === 1 && m.get(wr) === 5 && m.has(u32) && m.delete(bi64) && !m.has(bi64)
        && s.has(bu64) && s.has(wr) && s.size === 5
        && i32.length === 2 && i32[0] === 0 && i32[1] === 1
        && wr.deref() !== undefined
    "#,
  );
}
