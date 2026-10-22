use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn object_destructuring_binds_properties() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var {a,b} = {a:1,b:2}; a+b === 3"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_supports_renaming() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var {a:x} = {a:5}; x === 5"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_supports_defaults() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var {a=1} = {}; a === 1"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_supports_rest() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var {a,...r} = {a:1,b:2}; r.b === 2 && r.a === undefined"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_binds_elements_and_holes() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var [x,,y] = [1,2,3]; x===1 && y===3"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_supports_defaults() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var [x=1] = []; x===1"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_supports_rest() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var [x,...r] = [1,2,3]; r.length===2"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_assignment_binds_properties() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var a; var b; ({a,b} = {a:1,b:2}); a+b === 3"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_assignment_can_assign_to_member() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o = {}; ({a:o.x} = {a:1}); o.x === 1"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_assignment_supports_holes_and_rest() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var x; var y; var r; ([x,,y,...r] = [1,2,3,4,5]); x===1 && y===3 && r.length===2 && r[0]===4"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn catch_param_supports_destructuring() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"try { throw {x:1}; } catch({x}) { x }"#)
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn object_destructuring_string_key_preserves_unpaired_surrogate() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o = {"\uD800": 1}; var {"\uD800": x} = o; x"#)
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn array_destructuring_closes_iterator_when_not_exhausted() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var closes = 0;
      var iter = {};
      iter[Symbol.iterator] = function () {
        return {
          next: function () { return { value: 1, done: false }; },
          return: function () { closes += 1; return {}; }
        };
      };
      var [x] = iter;
      closes === 1 && x === 1
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_elision_advances_iterator() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var first = 0, second = 0;
      function* g() { first += 1; yield; second += 1; }
      var [,] = g();
      first === 1 && second === 0
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_default_sets_anonymous_function_name() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var [fn = function () {}] = []; fn.name === 'fn'"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_honors_overridden_array_iterator() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var saved = Array.prototype[Symbol.iterator];
      Array.prototype[Symbol.iterator] = function* () {
        if (this.length > 0) yield this[0];
        if (this.length > 1) yield this[1];
        if (this.length > 2) yield 42;
      };
      var [x, y, z] = [1, 2, 3];
      Array.prototype[Symbol.iterator] = saved;
      x === 1 && y === 2 && z === 42
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_rest_consumes_iterator() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var iter = (function* () { yield 1; yield 2; yield 3; })();
      var [...xs] = iter;
      xs.length === 3 && xs[2] === 3 && iter.next().done === true
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn generator_param_array_pattern_closes_iterator() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var closes = 0;
      var iter = {};
      iter[Symbol.iterator] = function () {
        return {
          next: function () { return { value: null, done: false }; },
          return: function () { closes += 1; return {}; }
        };
      };
      var f = function* ([x]) { return x; };
      f(iter).next();
      closes === 1
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}
