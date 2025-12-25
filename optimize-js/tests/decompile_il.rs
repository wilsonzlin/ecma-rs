use num_bigint::BigInt;
use optimize_js::decompile::il::{
  lower_arg, lower_call_inst, lower_prop_assign_inst, node, FnEmitter, VarInit, VarNamer,
};
use optimize_js::il::inst::{Arg, Const, Inst};
use parse_js::num::JsNumber;
use serde_json::{json, to_value};
use symbol_js::symbol::Symbol;

struct TestNamer;

impl VarNamer for TestNamer {
  fn name_var(&self, var: u32) -> String {
    format!("t{var}")
  }

  fn name_foreign(&self, symbol: Symbol) -> String {
    format!("f{}", symbol.raw_id())
  }

  fn name_unknown(&self, name: &str) -> String {
    format!("u{name}")
  }
}

struct TestFns;

impl FnEmitter for TestFns {
  fn emit_function(&self, id: usize) -> parse_js::ast::node::Node<parse_js::ast::expr::Expr> {
    node(parse_js::ast::expr::Expr::Id(node(
      parse_js::ast::expr::IdExpr {
        name: format!("fn{id}"),
      },
    )))
  }
}

#[test]
fn lowers_undefined_to_void_zero() {
  let expr = lower_arg(&TestNamer, &TestFns, &Arg::Const(Const::Undefined));
  assert_eq!(
    to_value(expr).unwrap(),
    json!({
      "$t": "Unary",
      "operator": "Void",
      "argument": {
        "$t": "LitNum",
        "value": 0.0
      }
    })
  );
}

#[test]
fn lowers_bigint_literal() {
  let expr = lower_arg(
    &TestNamer,
    &TestFns,
    &Arg::Const(Const::BigInt(BigInt::from(1234))),
  );
  assert_eq!(
    to_value(expr).unwrap(),
    json!({
      "$t": "LitBigInt",
      "value": "1234n"
    })
  );
}

#[test]
fn lowers_builtin_chain() {
  let expr = lower_arg(
    &TestNamer,
    &TestFns,
    &Arg::Builtin("Array.prototype.forEach".into()),
  );
  assert_eq!(
    to_value(expr).unwrap(),
    json!({
      "$t": "Member",
      "optional_chaining": false,
      "left": {
        "$t": "Member",
        "optional_chaining": false,
        "left": {
          "$t": "Id",
          "name": "Array"
        },
        "right": "prototype"
      },
      "right": "forEach"
    })
  );
}

#[test]
fn prop_assign_prefers_direct_member() {
  let inst = Inst::prop_assign(
    Arg::Var(0),
    Arg::Const(Const::Str("foo".into())),
    Arg::Const(Const::Num(JsNumber(1.0))),
  );
  let stmt = lower_prop_assign_inst(&TestNamer, &TestFns, &inst).unwrap();
  assert_eq!(
    to_value(stmt).unwrap(),
    json!({
      "$t": "Expr",
      "expr": {
        "$t": "Binary",
        "operator": "Assignment",
        "left": {
          "$t": "Member",
          "optional_chaining": false,
          "left": { "$t": "Id", "name": "t0" },
          "right": "foo"
        },
        "right": {
          "$t": "LitNum",
          "value": 1.0
        }
      }
    })
  );
}

#[test]
fn prop_assign_uses_computed_for_invalid_identifier() {
  let inst = Inst::prop_assign(
    Arg::Var(0),
    Arg::Const(Const::Str("foo-bar".into())),
    Arg::Const(Const::Bool(true)),
  );
  let stmt = lower_prop_assign_inst(&TestNamer, &TestFns, &inst).unwrap();
  assert_eq!(
    to_value(stmt).unwrap(),
    json!({
      "$t": "Expr",
      "expr": {
        "$t": "Binary",
        "operator": "Assignment",
        "left": {
          "$t": "ComputedMember",
          "optional_chaining": false,
          "object": { "$t": "Id", "name": "t0" },
          "member": { "$t": "LitStr", "value": "foo-bar" }
        },
        "right": {
          "$t": "LitBool",
          "value": true
        }
      }
    })
  );
}

#[test]
fn call_with_this_falls_back_to_call_helper() {
  let inst = Inst::call(Some(3), Arg::Var(1), Arg::Var(2), Vec::new(), Vec::new());
  let stmt = lower_call_inst(
    &TestNamer,
    &TestFns,
    &inst,
    None,
    None,
    None,
    VarInit::Assign,
  )
  .expect("lower call");
  assert_eq!(
    to_value(stmt).unwrap(),
    json!({
      "$t": "Expr",
      "expr": {
        "$t": "Binary",
        "operator": "Assignment",
        "left": { "$t": "Id", "name": "t3" },
        "right": {
          "$t": "Call",
          "optional_chaining": false,
          "callee": {
            "$t": "Member",
            "optional_chaining": false,
            "left": { "$t": "Id", "name": "t1" },
            "right": "call"
          },
          "arguments": [
            {
              "spread": false,
              "value": { "$t": "Id", "name": "t2" }
            }
          ]
        }
      }
    })
  );
}
