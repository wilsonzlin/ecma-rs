//! Async generators + `for await`: yield/await dual-path, promise-returning next, and
//! for-await over async iterables (@@asyncIterator).

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(8 * 1024 * 1024, 8 * 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

/// Runs `setup`, drains microtasks, then evaluates `probe` and returns its value.
fn run_and_probe(setup: &str, probe: &str) -> (JsRuntime, Value) {
  let mut rt = new_runtime();
  rt.exec_script(setup).unwrap();
  rt.vm.perform_microtask_checkpoint(&mut rt.heap).unwrap();
  let v = rt.exec_script(probe).unwrap();
  (rt, v)
}

fn probe_num(setup: &str, probe: &str) -> f64 {
  match run_and_probe(setup, probe).1 {
    Value::Number(n) => n,
    other => panic!("expected number, got {other:?}"),
  }
}

fn probe_str(setup: &str, probe: &str) -> String {
  let (rt, v) = run_and_probe(setup, probe);
  match v {
    Value::String(s) => rt.heap().get_string(s).unwrap().to_utf8_lossy(),
    other => panic!("expected string, got {other:?}"),
  }
}

#[test]
fn async_generator_next_returns_promise_for_yielded_value() {
  let s = probe_str(
    r#"
      var out = "";
      async function* g() { yield 1; yield 2; return 3; }
      var it = g();
      it.next().then(function (a) {
        return it.next().then(function (b) {
          return it.next().then(function (c) {
            out = [a.value, a.done, b.value, b.done, c.value, c.done].join(",");
          });
        });
      });
    "#,
    "out",
  );
  assert_eq!(s, "1,false,2,false,3,true");
}

#[test]
fn async_generator_body_does_not_start_until_first_next() {
  let n = probe_num(
    r#"
      var started = 0;
      async function* g() { started = 1; yield 1; }
      var it = g();
      var before = started;
      it.next();
    "#,
    "before * 10 + started",
  );
  // before=0; after next()+drain, started=1
  assert_eq!(n, 1.0);
}

#[test]
fn await_inside_async_generator_interleaves_with_promises() {
  // Mirrors language/expressions/await/async-generator-interleaved.js shape.
  // Drain twice: first tick runs the await-resume + the `1` then-handler; second finishes.
  let mut rt = new_runtime();
  rt.exec_script(
    r#"
      var actual = [];
      async function pushAwait() { actual.push("await"); }
      async function* callAsync() {
        await pushAwait();
        await pushAwait();
        return 0;
      }
      callAsync().next();
      new Promise(function (resolve) {
        actual.push(1);
        resolve();
      }).then(function () {
        actual.push(2);
      });
    "#,
  )
  .unwrap();
  rt.vm.perform_microtask_checkpoint(&mut rt.heap).unwrap();
  rt.vm.perform_microtask_checkpoint(&mut rt.heap).unwrap();
  let v = rt.exec_script("actual.join(',')").unwrap();
  let s = match v {
    Value::String(s) => rt.heap().get_string(s).unwrap().to_utf8_lossy(),
    other => panic!("expected string, got {other:?}"),
  };
  assert_eq!(s, "await,1,await,2");
}

#[test]
fn yield_of_promise_is_unwrapped_before_delivery() {
  let n = probe_num(
    r#"
      var got = 0;
      async function* g() { yield Promise.resolve(42); }
      g().next().then(function (r) { got = r.value; });
    "#,
    "got",
  );
  assert_eq!(n, 42.0);
}

#[test]
fn next_argument_becomes_yield_expression_value() {
  let n = probe_num(
    r#"
      var out = 0;
      async function* g() {
        var x = yield 1;
        return x + 1;
      }
      var it = g();
      it.next().then(function () {
        return it.next(5);
      }).then(function (r) { out = r.value; });
    "#,
    "out",
  );
  assert_eq!(n, 6.0);
}

#[test]
fn async_generator_throw_rejects_pending_next_when_uncaught() {
  let s = probe_str(
    r#"
      var out = "";
      async function* g() { yield 1; }
      var it = g();
      it.next().then(function () {
        return it.throw("boom");
      }).then(
        function () { out = "resolved"; },
        function (e) { out = "rejected:" + e; }
      );
    "#,
    "out",
  );
  assert_eq!(s, "rejected:boom");
}

#[test]
fn for_await_over_async_generator_collects_values() {
  let n = probe_num(
    r#"
      var sum = 0;
      async function* nums() { yield 1; yield 2; yield 3; }
      async function run() {
        for await (const n of nums()) { sum += n; }
      }
      run();
    "#,
    "sum",
  );
  assert_eq!(n, 6.0);
}

#[test]
fn for_await_over_manual_async_iterable() {
  let n = probe_num(
    r#"
      var sum = 0;
      var obj = {
        [Symbol.asyncIterator]() {
          return {
            i: 0,
            next() {
              if (this.i < 3) {
                return Promise.resolve({ value: this.i++, done: false });
              }
              return Promise.resolve({ done: true });
            }
          };
        }
      };
      async function run() {
        for await (const n of obj) { sum += n; }
      }
      run();
    "#,
    "sum",
  );
  assert_eq!(n, 3.0);
}

#[test]
fn for_await_over_sync_array_via_create_async_from_sync_iterator() {
  // No @@asyncIterator: GetIterator + CreateAsyncFromSyncIterator (§7.4.2 / §7.4.11).
  let n = probe_num(
    r#"
      var sum = 0;
      async function run() {
        for await (const n of [1, 2, 3]) { sum += n; }
      }
      run();
    "#,
    "sum",
  );
  assert_eq!(n, 6.0);
}

#[test]
fn for_await_over_sync_generator() {
  let n = probe_num(
    r#"
      var sum = 0;
      function* nums() { yield 10; yield 20; yield 30; }
      async function run() {
        for await (const n of nums()) { sum += n; }
      }
      run();
    "#,
    "sum",
  );
  assert_eq!(n, 60.0);
}

#[test]
fn switch_case_block_scopes_async_generator_declaration() {
  // Negative ReferenceError: async generator decl is CaseBlock-scoped.
  let mut rt = new_runtime();
  let err = rt
    .exec_script("switch (0) { default: async function * x() {} } x;")
    .unwrap_err();
  match err {
    vm_js::VmError::Throw(_) | vm_js::VmError::ThrowWithStack { .. } => {}
    other => panic!("expected thrown ReferenceError, got {other:?}"),
  }
}

#[test]
fn async_generator_instance_inherits_async_generator_prototype_methods() {
  let n = probe_num(
    r#"
      async function* g() {}
      var it = g();
      var ok = typeof it.next === "function"
        && typeof it.return === "function"
        && typeof it.throw === "function"
        && typeof it[Symbol.asyncIterator] === "function"
        && it[Symbol.asyncIterator]() === it;
    "#,
    "ok ? 1 : 0",
  );
  assert_eq!(n, 1.0);
}
