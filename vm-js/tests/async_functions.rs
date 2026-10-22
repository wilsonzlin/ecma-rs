//! Async function semantics: result promises, await resume (fulfil + reject), try/catch/finally
//! across suspension, and microtask-driven sequencing.

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
fn async_function_returns_promise_resolved_with_return_value() {
  let s = probe_str(
    r#"
      var out = "pending";
      async function f() { return 42; }
      var p = f();
      var isPromise = p instanceof Promise;
      p.then(function (v) { out = "value:" + v + ":" + isPromise; });
    "#,
    "out",
  );
  assert_eq!(s, "value:42:true");
}

#[test]
fn async_function_body_runs_synchronously_until_first_await() {
  let n = probe_num(
    r#"
      var log = 0;
      async function f() { log = 1; await 0; log = 2; }
      f();
      var syncLog = log; // await suspends before log = 2
    "#,
    "syncLog * 10 + log",
  );
  // syncLog = 1 (synchronous part ran), log = 2 after drain.
  assert_eq!(n, 12.0);
}

#[test]
fn await_plain_value_resumes_with_value() {
  let s = probe_str(
    r#"
      var out = "";
      async function f() {
        var v = await 7;
        return v + 1;
      }
      f().then(function (v) { out = "got:" + v; });
    "#,
    "out",
  );
  assert_eq!(s, "got:8");
}

#[test]
fn await_resolved_promise_resumes_with_resolution() {
  let s = probe_str(
    r#"
      var out = "";
      async function f() {
        var v = await Promise.resolve(5);
        return v * 2;
      }
      f().then(function (v) { out = "got:" + v; });
    "#,
    "out",
  );
  assert_eq!(s, "got:10");
}

#[test]
fn await_rejected_promise_throws_into_catch() {
  let s = probe_str(
    r#"
      var out = "";
      async function f() {
        try {
          await Promise.reject("boom");
          out = "not-reached";
        } catch (e) {
          out = "caught:" + e;
        }
      }
      f();
    "#,
    "out",
  );
  assert_eq!(s, "caught:boom");
}

#[test]
fn uncaught_await_rejection_rejects_result_promise() {
  let s = probe_str(
    r#"
      var out = "";
      async function f() { await Promise.reject("bad"); }
      f().then(
        function () { out = "fulfilled"; },
        function (e) { out = "rejected:" + e; }
      );
    "#,
    "out",
  );
  assert_eq!(s, "rejected:bad");
}

#[test]
fn thrown_error_before_await_rejects_result_promise() {
  let s = probe_str(
    r#"
      var out = "";
      async function f() { throw "early"; }
      f().catch(function (e) { out = "rejected:" + e; });
    "#,
    "out",
  );
  assert_eq!(s, "rejected:early");
}

#[test]
fn finally_runs_across_await_on_rejection() {
  let s = probe_str(
    r#"
      var out = "";
      async function f() {
        try {
          await Promise.reject("x");
        } finally {
          out += "finally;";
        }
      }
      f().catch(function (e) { out += "rejected:" + e; });
    "#,
    "out",
  );
  assert_eq!(s, "finally;rejected:x");
}

#[test]
fn multiple_awaits_sequence_in_order() {
  let s = probe_str(
    r#"
      var out = "";
      async function f() {
        out += "a";
        await 0;
        out += "b";
        await 0;
        out += "c";
        return "done";
      }
      f().then(function (v) { out += ":" + v; });
      out += "1";
    "#,
    "out",
  );
  assert_eq!(s, "a1bc:done");
}

#[test]
fn await_in_loop_accumulates() {
  let n = probe_num(
    r#"
      var result = 0;
      async function f() {
        var sum = 0;
        for (let i = 1; i <= 4; i++) {
          sum += await i;
        }
        return sum;
      }
      f().then(function (v) { result = v; });
    "#,
    "result",
  );
  assert_eq!(n, 10.0);
}

#[test]
fn async_function_expression_and_arrow_forms() {
  let s = probe_str(
    r#"
      var out = "";
      var fe = async function () { return "fe:" + (await 1); };
      var ar = async () => "ar:" + (await 2);
      fe().then(function (v) { out += v + ";"; });
      ar().then(function (v) { out += v; });
    "#,
    "out",
  );
  assert_eq!(s, "fe:1;ar:2");
}

#[test]
fn async_arrow_captures_lexical_this() {
  let s = probe_str(
    r#"
      var out = "";
      var obj = {
        tag: "T",
        run: function () {
          var self = this;
          var f = async () => this.tag + ":" + (await 1);
          return f();
        }
      };
      obj.run().then(function (v) { out = v; });
    "#,
    "out",
  );
  assert_eq!(s, "T:1");
}

#[test]
fn await_result_of_another_async_function() {
  let s = probe_str(
    r#"
      var out = "";
      async function inner() { await 0; return 5; }
      async function outer() {
        var v = await inner();
        return v * 3;
      }
      outer().then(function (v) { out = "v:" + v; });
    "#,
    "out",
  );
  assert_eq!(s, "v:15");
}

#[test]
fn await_thenable_object_is_assimilated() {
  let s = probe_str(
    r#"
      var out = "";
      var thenable = {
        then: function (resolve) { resolve("assimilated"); }
      };
      async function f() { return await thenable; }
      f().then(function (v) { out = v; });
    "#,
    "out",
  );
  assert_eq!(s, "assimilated");
}

#[test]
fn async_function_is_not_a_constructor() {
  let mut rt = new_runtime();
  let v = rt
    .exec_script(
      r#"
        async function f() {}
        var msg = "none";
        try { new f(); } catch (e) { msg = e instanceof TypeError ? "TypeError" : "other"; }
        msg
      "#,
    )
    .unwrap();
  let Value::String(s) = v else {
    panic!("expected string, got {v:?}")
  };
  assert_eq!(
    rt.heap().get_string(s).unwrap().to_utf8_lossy(),
    "TypeError"
  );
}

#[test]
fn async_function_result_promise_identity_and_state() {
  // Without draining microtasks the promise must still be pending for a body with an await.
  let mut rt = new_runtime();
  rt.exec_script(
    r#"
      var settled = "no";
      async function f() { await 0; }
      f().then(function () { settled = "yes"; });
    "#,
  )
  .unwrap();
  let v = rt.exec_script("settled").unwrap();
  let Value::String(s) = v else {
    panic!("expected string, got {v:?}")
  };
  assert_eq!(rt.heap().get_string(s).unwrap().to_utf8_lossy(), "no");

  rt.vm.perform_microtask_checkpoint(&mut rt.heap).unwrap();
  let v = rt.exec_script("settled").unwrap();
  let Value::String(s) = v else {
    panic!("expected string, got {v:?}")
  };
  assert_eq!(rt.heap().get_string(s).unwrap().to_utf8_lossy(), "yes");
}

#[test]
fn suspended_async_state_survives_gc() {
  let mut rt = new_runtime();
  rt.exec_script(
    r#"
      var out = "";
      async function f() {
        var kept = "keep-" + "async";
        await 0;
        return kept.length;
      }
      f().then(function (v) { out = "len:" + v; });
    "#,
  )
  .unwrap();
  rt.heap_mut().collect_garbage();
  rt.heap_mut().collect_garbage();
  rt.vm.perform_microtask_checkpoint(&mut rt.heap).unwrap();
  let v = rt.exec_script("out").unwrap();
  let Value::String(s) = v else {
    panic!("expected string, got {v:?}")
  };
  assert_eq!(rt.heap().get_string(s).unwrap().to_utf8_lossy(), "len:10");
}

#[test]
fn async_function_default_param_tdz_rejects_promise() {
  // FDI TDZ must reject the result promise, not throw from the call
  // (test262 dflt-params-ref-self).
  let s = probe_str(
    r#"
      var out = "pending";
      var threw = false;
      async function f(x = x) {}
      try {
        f().then(
          function () { out = "resolved"; },
          function (e) { out = e.name === "ReferenceError" ? "reject" : "other:" + e.name; }
        );
      } catch (e) { threw = true; out = "sync"; }
      if (threw) out = "sync";
    "#,
    "out",
  );
  assert_eq!(s, "reject");
}
