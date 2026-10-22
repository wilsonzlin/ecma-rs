//! Sync generator semantics: yield both directions, return/throw injection, finally blocks,
//! for-of integration, yield* delegation, prototype wiring, and GC across suspension.

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(8 * 1024 * 1024, 8 * 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn exec(src: &str) -> Result<Value, VmError> {
  new_runtime().exec_script(src)
}

fn exec_num(src: &str) -> f64 {
  match exec(src) {
    Ok(Value::Number(n)) => n,
    other => panic!("expected number result, got {other:?}"),
  }
}

fn exec_str(src: &str) -> String {
  let mut rt = new_runtime();
  match rt.exec_script(src) {
    Ok(Value::String(s)) => rt.heap().get_string(s).unwrap().to_utf8_lossy(),
    other => panic!("expected string result, got {other:?}"),
  }
}

fn exec_bool(src: &str) -> bool {
  match exec(src) {
    Ok(Value::Bool(b)) => b,
    other => panic!("expected bool result, got {other:?}"),
  }
}

// ---------------------------------------------------------------------------
// Basic yield sequencing
// ---------------------------------------------------------------------------

#[test]
fn generator_yields_values_in_order_and_completes() {
  let n = exec_num(
    r#"
      function* g() { yield 1; yield 2; return 3; }
      var it = g();
      var a = it.next(); // {1, false}
      var b = it.next(); // {2, false}
      var c = it.next(); // {3, true}
      var d = it.next(); // {undefined, true}
      (a.value === 1 && a.done === false ? 1 : 0) +
      (b.value === 2 && b.done === false ? 10 : 0) +
      (c.value === 3 && c.done === true ? 100 : 0) +
      (d.value === undefined && d.done === true ? 1000 : 0)
    "#,
  );
  assert_eq!(n, 1111.0);
}

#[test]
fn generator_body_does_not_start_until_first_next() {
  let n = exec_num(
    r#"
      var started = 0;
      function* g() { started = 1; yield 1; }
      var it = g();
      var before = started;
      it.next();
      before * 10 + started
    "#,
  );
  assert_eq!(n, 1.0); // before=0, after=1
}

#[test]
fn next_argument_becomes_yield_expression_value() {
  let n = exec_num(
    r#"
      function* g() {
        var x = yield 1;
        var y = yield x + 1;
        return x * 100 + y;
      }
      var it = g();
      it.next();        // runs to first yield; value 1
      var b = it.next(5);  // x = 5; yields 6
      var c = it.next(7);  // y = 7; returns 507
      b.value * 1000 + c.value
    "#,
  );
  assert_eq!(n, 6507.0);
}

#[test]
fn first_next_argument_is_ignored() {
  let n = exec_num(
    r#"
      function* g() { var x = yield 1; return x; }
      var it = g();
      it.next(99); // ignored
      it.next(42).value
    "#,
  );
  assert_eq!(n, 42.0);
}

// ---------------------------------------------------------------------------
// Yield in expression positions / evaluation order
// ---------------------------------------------------------------------------

#[test]
fn yield_inside_binary_expression() {
  let n = exec_num(
    r#"
      function* g() { return 10 + (yield 1) + 100; }
      var it = g();
      it.next();
      it.next(5).value
    "#,
  );
  assert_eq!(n, 115.0);
}

#[test]
fn yield_inside_call_arguments_preserves_order() {
  let s = exec_str(
    r#"
      var log = "";
      function record(a, b, c) { log += "call(" + a + "," + b + "," + c + ")"; return 0; }
      function* g() { record("a", yield 1, "c"); }
      var it = g();
      log += "s" + it.next().value;
      it.next("B");
      log
    "#,
  );
  assert_eq!(s, "s1call(a,B,c)");
}

#[test]
fn yield_inside_array_literal() {
  let n = exec_num(
    r#"
      function* g() { var a = [1, yield 0, 3]; return a[0] * 100 + a[1] * 10 + a[2]; }
      var it = g();
      it.next();
      it.next(2).value
    "#,
  );
  assert_eq!(n, 123.0);
}

#[test]
fn yield_spread_arr_single_collects_iterable() {
  // Mirrors test262 yield-spread-arr-single: `yield [...yield]`.
  let n = exec_num(
    r#"
      function* g() { yield [...yield]; }
      var it = g();
      it.next();
      var item = it.next(['a', 'b', 'c']);
      var v = item.value;
      (v !== null && Array.isArray(v) && v.length === 3 &&
        v[0] === 'a' && v[1] === 'b' && v[2] === 'c' && item.done === false) ? 1 : 0
    "#,
  );
  assert_eq!(n, 1.0);
}

#[test]
fn yield_spread_arr_multiple_nested_yields() {
  // Mirrors test262 yield-spread-arr-multiple: `yield [...yield yield]`.
  let n = exec_num(
    r#"
      function* g() { yield [...yield yield]; }
      var it = g();
      it.next();
      var item = it.next(['a', 'b', 'c']);
      item = it.next(item.value);
      var v = item.value;
      (Array.isArray(v) && v.length === 3 &&
        v[0] === 'a' && v[1] === 'b' && v[2] === 'c') ? 1 : 0
    "#,
  );
  assert_eq!(n, 1.0);
}

#[test]
fn array_literal_spread_alongside_yield_element() {
  // Suspend-free spread + yielded Single element in the same array literal.
  let n = exec_num(
    r#"
      function* g() { return [0, ...[1, 2], yield, 4]; }
      var it = g();
      it.next();
      var a = it.next(3).value;
      // [0, 1, 2, 3, 4]
      a[0] * 10000 + a[1] * 1000 + a[2] * 100 + a[3] * 10 + a[4]
    "#,
  );
  assert_eq!(n, 1234.0);
}

#[test]
fn yield_spread_obj_merges_enumerable_own_props() {
  // Mirrors test262 yield-spread-obj: `yield { ...yield, y: 1, ...yield yield }`.
  let n = exec_num(
    r#"
      function* g() {
        yield { ...yield, y: 1, ...yield yield };
      }
      var it = g();
      it.next();
      it.next({ x: 42 });
      it.next({ x: 'lol' });
      var item = it.next({ y: 39 });
      var v = item.value;
      (v.x === 42 && v.y === 39 && Object.keys(v).length === 2 && item.done === false) ? 1 : 0
    "#,
  );
  assert_eq!(n, 1.0);
}

#[test]
fn yield_inside_computed_member_key() {
  let n = exec_num(
    r#"
      function* g() { return [10, 20, 30][yield]; }
      var it = g();
      it.next();
      it.next(1).value
    "#,
  );
  assert_eq!(n, 20.0);
}

#[test]
fn optional_computed_member_short_circuits_before_yield_key() {
  let n = exec_num(
    r#"
      function* g() {
        return undefined?.[yield 99];
      }
      var it = g();
      var r = it.next();
      (r.value === undefined && r.done === true) ? 1 : 0
    "#,
  );
  assert_eq!(n, 1.0);
}

#[test]
fn optional_member_then_computed_propagates_short_circuit() {
  // `undefined?.arr[yield]` must not evaluate the key (chain short-circuit).
  let n = exec_num(
    r#"
      function* g() {
        return undefined?.arr[yield 99];
      }
      var it = g();
      var r = it.next();
      (r.value === undefined && r.done === true) ? 1 : 0
    "#,
  );
  assert_eq!(n, 1.0);
}

#[test]
fn yield_in_conditional_and_logical_positions() {
  let n = exec_num(
    r#"
      function* g() {
        var a = (yield 1) ? 10 : 20;
        var b = (yield 2) || 5;
        return a + b;
      }
      var it = g();
      it.next();
      it.next(true);   // a = 10
      it.next(0).value // b = 5 → 15
    "#,
  );
  assert_eq!(n, 15.0);
}

#[test]
fn yield_inside_while_loop_accumulates() {
  let n = exec_num(
    r#"
      function* g() {
        var sum = 0;
        var i = 0;
        while (i < 3) {
          sum += yield i;
          i += 1;
        }
        return sum;
      }
      var it = g();
      it.next();      // yields 0
      it.next(10);    // yields 1
      it.next(20);    // yields 2
      it.next(30).value
    "#,
  );
  assert_eq!(n, 60.0);
}

#[test]
fn yield_inside_for_loop_with_let_binding() {
  let n = exec_num(
    r#"
      function* g() {
        var total = 0;
        for (let i = 0; i < 3; i++) {
          total += yield i;
        }
        return total;
      }
      var it = g();
      it.next();
      it.next(1);
      it.next(2);
      it.next(3).value
    "#,
  );
  assert_eq!(n, 6.0);
}

// ---------------------------------------------------------------------------
// return() / throw() injection
// ---------------------------------------------------------------------------

#[test]
fn return_at_suspended_start_completes_without_running_body() {
  let n = exec_num(
    r#"
      var ran = 0;
      function* g() { ran = 1; yield 1; }
      var it = g();
      var r = it.return(7);
      (r.value === 7 && r.done === true ? 1 : 0) * 10 + ran
    "#,
  );
  assert_eq!(n, 10.0);
}

#[test]
fn return_at_suspended_yield_runs_finally() {
  let n = exec_num(
    r#"
      var cleanup = 0;
      function* g() {
        try { yield 1; yield 2; }
        finally { cleanup = 1; }
      }
      var it = g();
      it.next();
      var r = it.return(9);
      (r.value === 9 && r.done === true ? 1 : 0) * 10 + cleanup
    "#,
  );
  assert_eq!(n, 11.0);
}

#[test]
fn yield_in_finally_defers_return_completion() {
  let n = exec_num(
    r#"
      function* g() {
        try { yield 1; }
        finally { yield 2; }
      }
      var it = g();
      it.next();          // {1, false}
      var a = it.return(9);  // enters finally → {2, false}
      var b = it.next();     // finally done → return completion resumes → {9, true}
      (a.value === 2 && a.done === false ? 1 : 0) * 10 +
      (b.value === 9 && b.done === true ? 1 : 0)
    "#,
  );
  assert_eq!(n, 11.0);
}

#[test]
fn throw_at_suspended_start_completes_generator() {
  let n = exec_num(
    r#"
      function* g() { yield 1; }
      var it = g();
      var caught = 0;
      try { it.throw(42); } catch (e) { caught = e; }
      var after = it.next();
      caught * 10 + (after.done === true ? 1 : 0)
    "#,
  );
  assert_eq!(n, 421.0);
}

#[test]
fn throw_at_suspended_yield_is_catchable_inside_body() {
  let n = exec_num(
    r#"
      function* g() {
        var x = 0;
        try { yield 1; } catch (e) { x = e; }
        yield x + 1;
      }
      var it = g();
      it.next();
      it.throw(41).value
    "#,
  );
  assert_eq!(n, 42.0);
}

#[test]
fn throw_uncaught_in_body_propagates_and_completes() {
  let n = exec_num(
    r#"
      function* g() { yield 1; }
      var it = g();
      it.next();
      var caught = 0;
      try { it.throw(7); } catch (e) { caught = e; }
      caught * 10 + (it.next().done ? 1 : 0)
    "#,
  );
  assert_eq!(n, 71.0);
}

#[test]
fn next_after_completion_returns_done_undefined() {
  let b = exec_bool(
    r#"
      function* g() { return 1; }
      var it = g();
      it.next();
      var r = it.next();
      r.done === true && r.value === undefined
    "#,
  );
  assert!(b);
}

#[test]
fn reentrant_next_throws_type_error() {
  let s = exec_str(
    r#"
      var it;
      function* g() { yield it.next(); }
      it = g();
      var msg = "";
      try { it.next(); } catch (e) { msg = e instanceof TypeError ? "TypeError" : "other"; }
      msg
    "#,
  );
  assert_eq!(s, "TypeError");
}

// ---------------------------------------------------------------------------
// try/catch/finally across suspension
// ---------------------------------------------------------------------------

#[test]
fn finally_runs_when_generator_completes_normally() {
  let n = exec_num(
    r#"
      var log = 0;
      function* g() {
        try { yield 1; } finally { log += 1; }
        return 2;
      }
      var it = g();
      it.next();
      var r = it.next();
      log * 10 + r.value
    "#,
  );
  assert_eq!(n, 12.0);
}

#[test]
fn catch_across_suspension_handles_thrown_value() {
  let n = exec_num(
    r#"
      function* g() {
        try {
          yield 1;
          throw 5;
        } catch (e) {
          yield e + 1;
        }
        return 100;
      }
      var it = g();
      it.next();          // {1}
      var a = it.next();  // throw 5 caught → yield 6
      var b = it.next();  // return 100
      a.value * 1000 + b.value
    "#,
  );
  assert_eq!(n, 6100.0);
}

// ---------------------------------------------------------------------------
// for-of / iterator protocol integration
// ---------------------------------------------------------------------------

#[test]
fn for_of_iterates_generator_values() {
  let n = exec_num(
    r#"
      function* g() { yield 1; yield 2; yield 3; }
      var sum = 0;
      for (var v of g()) { sum += v; }
      sum
    "#,
  );
  assert_eq!(n, 6.0);
}

#[test]
fn for_of_ignores_generator_return_value() {
  let n = exec_num(
    r#"
      function* g() { yield 1; return 99; }
      var sum = 0;
      for (var v of g()) { sum += v; }
      sum
    "#,
  );
  assert_eq!(n, 1.0);
}

#[test]
fn for_of_break_closes_generator_running_finally() {
  let n = exec_num(
    r#"
      var closed = 0;
      function* g() {
        try { yield 1; yield 2; yield 3; }
        finally { closed = 1; }
      }
      var sum = 0;
      for (var v of g()) { sum += v; if (v === 2) break; }
      sum * 10 + closed
    "#,
  );
  assert_eq!(n, 31.0);
}

#[test]
fn spread_of_generator_collects_values() {
  let n = exec_num(
    r#"
      function* g() { yield 1; yield 2; }
      var a = [...g()];
      a.length * 100 + a[0] * 10 + a[1]
    "#,
  );
  assert_eq!(n, 212.0);
}

#[test]
fn generator_is_its_own_iterator_via_symbol_iterator() {
  let b = exec_bool(
    r#"
      function* g() { yield 1; }
      var it = g();
      it[Symbol.iterator]() === it
    "#,
  );
  assert!(b);
}

// ---------------------------------------------------------------------------
// yield* delegation
// ---------------------------------------------------------------------------

#[test]
fn yield_star_delegates_to_inner_generator() {
  let n = exec_num(
    r#"
      function* inner() { yield 1; yield 2; return 3; }
      function* outer() {
        var r = yield* inner();
        yield r + 10;
      }
      var it = outer();
      var a = it.next(); // 1
      var b = it.next(); // 2
      var c = it.next(); // inner returns 3 → yields 13
      a.value * 100 + b.value * 10 + (c.value - 10)
    "#,
  );
  assert_eq!(n, 123.0);
}

#[test]
fn yield_star_delegates_over_array() {
  let n = exec_num(
    r#"
      function* g() { yield* [1, 2, 3]; }
      var sum = 0;
      for (var v of g()) sum += v;
      sum
    "#,
  );
  assert_eq!(n, 6.0);
}

#[test]
fn yield_star_forwards_next_arguments_to_inner() {
  let n = exec_num(
    r#"
      function* inner() {
        var x = yield 1;
        yield x * 2;
      }
      function* outer() { yield* inner(); }
      var it = outer();
      it.next();
      it.next(21).value
    "#,
  );
  assert_eq!(n, 42.0);
}

#[test]
fn yield_star_forwards_throw_to_inner_catch() {
  let n = exec_num(
    r#"
      function* inner() {
        try { yield 1; } catch (e) { yield e + 1; }
      }
      function* outer() { yield* inner(); }
      var it = outer();
      it.next();
      it.throw(41).value
    "#,
  );
  assert_eq!(n, 42.0);
}

// ---------------------------------------------------------------------------
// Function-object shape / prototype wiring
// ---------------------------------------------------------------------------

#[test]
fn generator_object_prototype_is_functions_prototype_property() {
  let b = exec_bool(
    r#"
      function* g() {}
      Object.getPrototypeOf(g()) === g.prototype
    "#,
  );
  assert!(b);
}

#[test]
fn generator_function_length_and_name() {
  let s = exec_str(
    r#"
      function* g(a, b) {}
      g.name + ":" + g.length
    "#,
  );
  assert_eq!(s, "g:2");
}

#[test]
fn generator_function_is_not_a_constructor() {
  let s = exec_str(
    r#"
      function* g() {}
      var msg = "none";
      try { new g(); } catch (e) { msg = e instanceof TypeError ? "TypeError" : "other"; }
      msg
    "#,
  );
  assert_eq!(s, "TypeError");
}

#[test]
fn generator_expression_and_object_method_forms_work() {
  let n = exec_num(
    r#"
      var ge = function* () { yield 1; };
      var obj = { *m() { yield 2; } };
      ge().next().value * 10 + obj.m().next().value
    "#,
  );
  assert_eq!(n, 12.0);
}

#[test]
fn generator_methods_shared_via_prototype_chain() {
  let b = exec_bool(
    r#"
      function* a() {}
      function* b() {}
      var pa = Object.getPrototypeOf(Object.getPrototypeOf(a()));
      var pb = Object.getPrototypeOf(Object.getPrototypeOf(b()));
      pa === pb && typeof pa.next === "function"
    "#,
  );
  assert!(b);
}

// ---------------------------------------------------------------------------
// Closures, this, and GC across suspension
// ---------------------------------------------------------------------------

#[test]
fn generator_closes_over_outer_variables() {
  let n = exec_num(
    r#"
      function make(base) {
        return function* () { yield base + 1; yield base + 2; };
      }
      var it = make(10)();
      it.next().value * 100 + it.next().value
    "#,
  );
  assert_eq!(n, 1112.0);
}

#[test]
fn generator_this_binding_from_method_call() {
  let n = exec_num(
    r#"
      var obj = {
        x: 7,
        *m() { yield this.x; }
      };
      obj.m().next().value
    "#,
  );
  assert_eq!(n, 7.0);
}

#[test]
fn suspended_generator_state_survives_gc() {
  // Force full collections while the generator is suspended: the frames' values and captured
  // environments must be traced through the generator heap object (host-data tracing rule).
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(8 * 1024 * 1024, 8 * 1024 * 1024));
  let mut rt = JsRuntime::new(vm, heap).unwrap();
  rt.exec_script(
    r#"
      function* g() {
        var kept = "keep-" + "me";
        var arr = [1, 2, 3];
        yield 1;
        yield kept.length + arr.length;
      }
      var it = g();
      it.next();
    "#,
  )
  .unwrap();
  let runs_before = rt.heap().gc_runs();
  rt.heap_mut().collect_garbage();
  rt.heap_mut().collect_garbage();
  assert_eq!(rt.heap().gc_runs(), runs_before + 2);
  let v = rt.exec_script("it.next().value").unwrap();
  assert_eq!(v, Value::Number(10.0));
  // Completion after GC: generator finishes cleanly.
  let done = rt.exec_script("it.next().done").unwrap();
  assert_eq!(done, Value::Bool(true));
}

#[test]
fn many_interleaved_generators() {
  let n = exec_num(
    r#"
      function* counter(start) {
        var i = start;
        while (true) { i = (yield i) === undefined ? i + 1 : i; }
      }
      var a = counter(0), b = counter(100);
      var sum = 0;
      for (var i = 0; i < 5; i++) {
        sum += a.next().value + b.next().value;
      }
      sum
    "#,
  );
  // a: 0+1+2+3+4 = 10; b: 100..104 = 510 → 520
  assert_eq!(n, 520.0);
}

#[test]
fn generator_next_on_non_generator_throws_type_error() {
  let s = exec_str(
    r#"
      function* g() {}
      var next = Object.getPrototypeOf(Object.getPrototypeOf(g())).next;
      var msg = "none";
      try { next.call({}); } catch (e) { msg = e instanceof TypeError ? "TypeError" : "other"; }
      msg
    "#,
  );
  assert_eq!(s, "TypeError");
}

#[test]
fn generator_body_with_unscopables() {
  let n = exec_num(
    r#"
      var v = 1;
      globalThis[Symbol.unscopables] = { v: true };
      function* g(x) {
        with (globalThis) {
          if (v !== undefined) return 0;
        }
        var v = x;
        with (globalThis) {
          if (v !== 10) return 0;
          v = 20;
        }
        return (v === 20 && globalThis.v === 1) ? 1 : 0;
      }
      g(10).next().value
    "#,
  );
  assert_eq!(n, 1.0);
}

#[test]
fn generator_yield_inside_with() {
  let n = exec_num(
    r#"
      var o = { x: 1 };
      function* g() {
        with (o) {
          yield x;
          x = 2;
          yield x;
        }
      }
      var it = g();
      var a = it.next().value;
      var b = it.next().value;
      it.next();
      (a === 1 && b === 2 && o.x === 2) ? 1 : 0
    "#,
  );
  assert_eq!(n, 1.0);
}
