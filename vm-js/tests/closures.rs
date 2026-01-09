use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn closure_captures_param() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("function make(x){ return function(){ return x; }; } var f = make(3); f()")
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn closure_mutates_captured_binding() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("function make(){ let x = 1; return function(){ x = 2; return x; }; } make()()")
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn closure_capture_survives_gc() {
  let mut rt = new_runtime();
  rt
    .exec_script("function make(){ let x = {a:3}; return function(){ return x.a; }; } var f = make();")
    .unwrap();

  rt.heap.collect_garbage();

  let value = rt.exec_script("f()").unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn function_decl_closure_captures_lexical_binding() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("function make(){ let x = 1; function inner(){ return x; } return inner; } make()()")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn arrow_captures_lexical_this_across_calls_and_gc() -> Result<(), VmError> {
  let mut rt = new_runtime();

  // Note: use a parenthesized parameter list to match the subset of arrow syntax supported by the
  // parser.
  rt.exec_script("function makeArrow(){ return (x) => this; }")?;
  let make_arrow = rt.exec_script("makeArrow")?;
  let make_arrow_root = rt.heap.add_root(make_arrow)?;

  let (this_obj, arrow_root) = {
    let mut scope = rt.heap.scope();

    let this_obj = scope.alloc_object()?;
    // Root the this value while calling `makeArrow`; the call itself may allocate while creating
    // the returned arrow.
    scope.push_root(Value::Object(this_obj))?;

    let make_arrow = scope
      .heap()
      .get_root(make_arrow_root)
      .expect("makeArrow root missing");
    let arrow = rt
      .vm
      .call(&mut scope, make_arrow, Value::Object(this_obj), &[])?;
    let arrow_root = scope.heap_mut().add_root(arrow)?;
    (this_obj, arrow_root)
  };

  // After dropping stack roots, `this_obj` is only reachable through the arrow's captured this.
  rt.heap.collect_garbage();
  assert!(
    rt.heap.is_valid_object(this_obj),
    "arrow should keep captured lexical this alive across GC"
  );

  {
    let arrow = rt.heap.get_root(arrow_root).expect("arrow root missing");
    let mut scope = rt.heap.scope();
    let value = rt.vm.call(&mut scope, arrow, Value::Undefined, &[])?;
    assert_eq!(value, Value::Object(this_obj));
  }

  rt.heap.remove_root(make_arrow_root);
  rt.heap.remove_root(arrow_root);
  Ok(())
}

#[test]
fn arrow_captures_lexical_new_target_across_calls_and_gc() -> Result<(), VmError> {
  let mut rt = new_runtime();

  // Return a constructor function that returns an arrow capturing `new.target`.
  //
  // Use a non-constructor object as `new_target` so the captured value cannot be kept alive via the
  // constructed `this` object's prototype chain; the only GC edge should be the arrow's captured
  // lexical `new.target`.
  //
  // Note: use a parenthesized parameter list to match the subset of arrow syntax supported by the
  // parser.
  let outer = rt.exec_script("(function outer(){ return (x) => new.target; })")?;
  let outer_root = rt.heap.add_root(outer)?;

  let new_target = rt.exec_script("({})")?;
  let Value::Object(new_target_obj) = new_target else {
    panic!("expected new_target to evaluate to an object, got {new_target:?}");
  };
  let new_target_root = rt.heap.add_root(new_target)?;

  let arrow_root = {
    let mut scope = rt.heap.scope();
    let outer = scope.heap().get_root(outer_root).expect("outer root missing");
    let new_target = scope
      .heap()
      .get_root(new_target_root)
      .expect("new_target root missing");
    let arrow = rt.vm.construct(&mut scope, outer, &[], new_target)?;
    scope.heap_mut().add_root(arrow)?
  };

  // `new_target_obj` is no longer rooted directly; it should stay alive via the arrow's captured
  // lexical `new.target`.
  rt.heap.remove_root(outer_root);
  rt.heap.remove_root(new_target_root);
  rt.heap.collect_garbage();
  assert!(
    rt.heap.is_valid_object(new_target_obj),
    "arrow should keep captured lexical new.target alive across GC"
  );

  {
    let arrow = rt.heap.get_root(arrow_root).expect("arrow root missing");
    let mut scope = rt.heap.scope();
    let value = rt.vm.call(&mut scope, arrow, Value::Undefined, &[])?;
    assert_eq!(value, Value::Object(new_target_obj));
  }

  rt.heap.remove_root(arrow_root);
  Ok(())
}

#[test]
fn arrow_functions_are_not_constructable() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"try { new ((x) => x); } catch(e) { e.name === "TypeError" }"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}
