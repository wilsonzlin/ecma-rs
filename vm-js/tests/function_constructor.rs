use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn function_constructor_empty_call_and_construct() {
  let mut rt = runtime();
  let v = rt
    .exec_script("typeof Function() === 'function' && typeof new Function() === 'function'")
    .unwrap();
  assert_eq!(v, Value::Bool(true));
}

#[test]
fn function_constructor_name_is_anonymous() {
  let mut rt = runtime();
  let v = rt.exec_script("Function().name").unwrap();
  match v {
    Value::String(s) => {
      let text = rt.heap().get_string(s).unwrap().to_utf8_lossy();
      assert_eq!(text, "anonymous");
    }
    other => panic!("expected string, got {other:?}"),
  }
}

#[test]
fn function_constructor_with_body_returns_value() {
  let mut rt = runtime();
  let v = rt.exec_script("Function('return 42')()").unwrap();
  assert_eq!(v, Value::Number(42.0));
}

#[test]
fn function_constructor_with_params_and_body() {
  let mut rt = runtime();
  let v = rt
    .exec_script("Function('a', 'b', 'return a + b')(2, 3)")
    .unwrap();
  assert_eq!(v, Value::Number(5.0));
}

#[test]
fn function_constructor_comma_separated_params_in_one_arg() {
  let mut rt = runtime();
  let v = rt
    .exec_script("Function('a, b', 'return a * b')(4, 5)")
    .unwrap();
  assert_eq!(v, Value::Number(20.0));
}

#[test]
fn function_constructor_make_constructor_and_instanceof() {
  let mut rt = runtime();
  let v = rt
    .exec_script(
      r#"
      var F = Function('name', 'this.name = name;');
      var o = new F('root');
      o instanceof F && o.name === 'root' && F instanceof Function
      "#,
    )
    .unwrap();
  assert_eq!(v, Value::Bool(true));
}

#[test]
fn function_constructor_instanceof_non_object_is_false() {
  let mut rt = runtime();
  let v = rt
    .exec_script(
      r#"
      var F = Function('this.x = 1');
      (1 instanceof F) === false &&
        ('s' instanceof F) === false &&
        (null instanceof F) === false &&
        (undefined instanceof F) === false
      "#,
    )
    .unwrap();
  assert_eq!(v, Value::Bool(true));
}

#[test]
fn function_constructor_prototype_not_object_throws_typeerror() {
  let mut rt = runtime();
  let v = rt
    .exec_script(
      r#"
      var F = new Function;
      F.prototype = undefined;
      var threw = false;
      try { ({} instanceof F); } catch (e) { threw = e instanceof TypeError; }
      threw
      "#,
    )
    .unwrap();
  assert_eq!(v, Value::Bool(true));
}

#[test]
fn function_constructor_invalid_body_throws_syntax_error() {
  let mut rt = runtime();
  let err = rt.exec_script("Function('}')").unwrap_err();
  match err {
    VmError::Throw(Value::Object(_))
    | VmError::ThrowWithStack {
      value: Value::Object(_),
      ..
    } => {}
    other => panic!("expected thrown SyntaxError object, got {other:?}"),
  }
}

#[test]
fn function_constructor_new_instance_constructor_property() {
  let mut rt = runtime();
  let v = rt
    .exec_script(
      r#"
      var F = Function('this.prop = 1;');
      var instance = new F;
      instance.constructor === F && instance.prop === 1
      "#,
    )
    .unwrap();
  assert_eq!(v, Value::Bool(true));
}

#[test]
fn function_constructor_truthy_for_boolean_coercion() {
  let mut rt = runtime();
  let v = rt
    .exec_script("Boolean(new Function()) === true && !(new Function()) === false")
    .unwrap();
  assert_eq!(v, Value::Bool(true));
}
