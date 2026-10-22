use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn assert_utf8(rt: &JsRuntime, value: Value, expected: &str) {
  let Value::String(s) = value else {
    panic!("expected string, got {value:?}");
  };
  assert_eq!(rt.heap().get_string(s).unwrap().to_utf8_lossy(), expected);
}

#[test]
fn class_declaration_construct_and_method() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      class C {
        constructor(x) { this.x = x; }
        m() { return this.x; }
      }
      new C(7).m()
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(7.0));
}

#[test]
fn class_declaration_name_and_non_call() {
  let mut rt = new_runtime();
  let name = rt.exec_script("class Foo {}; Foo.name").unwrap();
  assert_utf8(&rt, name, "Foo");

  let err = rt.exec_script("class Bar {}; Bar()").unwrap_err();
  match err {
    VmError::Throw(_) | VmError::ThrowWithStack { .. } => {}
    other => panic!("expected TypeError throw, got {other:?}"),
  }
}

#[test]
fn anonymous_class_expression_named_evaluation_from_destructuring() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      const [cls = class {}, xCls = class X {}, xCls2 = class { static name() {} }] = [];
      cls.name === 'cls'
        && xCls.name === 'X'
        && typeof xCls2.name === 'function'
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn class_expression_assignment_name() {
  let mut rt = new_runtime();
  // NamedEvaluation is wired: `var cls = class {}` infers `cls` as the class
  // name (ECMA-262), and a static `name` method overrides the built-in.
  let value = rt
    .exec_script(
      r#"
      var xCls = class x {};
      var cls = class {};
      var xCls2 = class { static name() {} };
      xCls.name === 'x'
        && cls.name === 'cls'
        && typeof xCls2.name === 'function'
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn switch_case_block_scopes_class_declaration() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script("switch (0) { default: class x {} } x;")
    .unwrap_err();
  match err {
    VmError::Throw(_) | VmError::ThrowWithStack { .. } => {}
    other => panic!("expected ReferenceError throw, got {other:?}"),
  }
}

#[test]
fn class_static_method() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      class C {
        static s() { return 11; }
      }
      C.s()
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(11.0));
}

#[test]
fn class_static_block_runs_and_binds_this() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var seen;
      class C {
        static { seen = this; this.flag = 1; }
      }
      seen === C && C.flag === 1
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn class_static_block_allows_await_identifier_in_nested_generator() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var await = 0;
      var fromParam, fromBody;
      class C {
        static {
          (function * (x = fromParam = await) {
            fromBody = await;
          })().next();
        }
      }
      fromParam === 0 && fromBody === 0
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn named_class_expression_binding_is_immutable_inside() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var C = class D {
        m() { return D.name; }
      };
      new C().m()
      "#,
    )
    .unwrap();
  assert_utf8(&rt, value, "D");
}

#[test]
fn class_extends_default_constructor_and_instanceof() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      class A {}
      class B extends A {}
      var b = new B();
      b instanceof B && b instanceof A && Object.getPrototypeOf(B) === A
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn class_extends_explicit_super_call_binds_this() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      class A {
        constructor(x) { this.x = x; }
      }
      class B extends A {
        constructor(x) {
          super(x);
          this.y = this.x + 1;
        }
      }
      new B(7).y
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(8.0));
}

#[test]
fn class_extends_super_call_optional_member() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var ok = false;
      class A {}
      class B extends A {
        constructor() {
          ok = super()?.a === undefined;
        }
      }
      new B();
      ok
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn class_extends_super_property_optional_call() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      var called = false;
      var context;
      class Base {
        method() {
          called = true;
          context = this;
        }
      }
      class Foo extends Base {
        method() {
          super.method?.();
        }
      }
      var foo = new Foo();
      foo.method();
      called && foo === context
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn derived_constructor_must_call_super_before_this() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script(
      r#"
      class A {}
      class B extends A {
        constructor() { this.x = 1; }
      }
      new B()
      "#,
    )
    .unwrap_err();
  match err {
    VmError::Throw(_) | VmError::ThrowWithStack { .. } => {}
    other => panic!("expected ReferenceError throw, got {other:?}"),
  }
}

#[test]
fn private_field_in_presence() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      class C {
        #field;
        static isNameIn(value) { return #field in value; }
      }
      C.isNameIn({}) === false && C.isNameIn(new C()) === true
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_method_in_presence_without_calling() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      let count = 0;
      class C {
        #method() { count += 1; }
        static isNameIn(value) { return #method in value; }
      }
      C.isNameIn({}) === false
        && C.isNameIn(new C()) === true
        && count === 0
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_accessor_in_presence_without_calling() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      let count = 0;
      class C {
        get #accessor() { count += 1; }
        static isNameIn(value) { return #accessor in value; }
      }
      C.isNameIn({}) === false
        && C.isNameIn(new C()) === true
        && count === 0
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_name_shadowing_nested_class() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      let Child;
      class Parent {
        #field;
        static init() {
          Child = class {
            #field;
            static isNameIn(value) { return #field in value; }
          };
        }
      }
      Parent.init();
      Child.isNameIn(new Parent()) === false
        && Child.isNameIn(new Child()) === true
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_in_rhs_non_object_throws_typeerror() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      let caught = null;
      class C {
        #field;
        constructor() {
          try { #field in ({} << 0); } catch (e) { caught = e; }
        }
      }
      new C();
      caught !== null && caught.constructor === TypeError
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_in_rhs_unresolvable_throws_referenceerror() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      let caught = null;
      class C {
        #field;
        constructor() {
          try { #field in test262unresolvable; } catch (e) { caught = e; }
        }
      }
      new C();
      caught !== null && caught.constructor === ReferenceError
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_in_rhs_await_as_identifier() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      let value;
      function await() { return value; }
      class C {
        #field;
        static isNameIn() { return #field in await(null); }
      }
      value = new C();
      let a = C.isNameIn();
      value = {};
      let b = C.isNameIn();
      a === true && b === false
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_in_rhs_yield() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"
      class C {
        #field;
        static *isNameIn() { return #field in (yield); }
      }
      let iter1 = C.isNameIn();
      iter1.next();
      let a = iter1.next(new C()).value;
      let iter2 = C.isNameIn();
      iter2.next();
      let b = iter2.next({}).value;
      a === true && b === false
      "#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn private_in_rhs_await_present() {
  let mut rt = new_runtime();
  rt.exec_script(
    r#"
    var out = "pending";
    class C {
      #field;
      static async isNameIn(value) { return #field in await(value); }
    }
    C.isNameIn(new C())
      .then(function (r1) {
        return C.isNameIn({}).then(function (r2) {
          out = (r1 === true && r2 === false) ? "ok" : "bad";
        });
      })
      .catch(function () { out = "err"; });
    "#,
  )
  .unwrap();
  rt.vm.perform_microtask_checkpoint(&mut rt.heap).unwrap();
  let out = rt.exec_script("out").unwrap();
  assert_utf8(&rt, out, "ok");
}
