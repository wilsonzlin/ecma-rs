use num_bigint::BigInt;
use optimize_js::eval::consteval::{
  coerce_str_to_num, js_cmp, js_div, js_loose_eq, maybe_eval_const_bin_expr,
  maybe_eval_const_builtin_call, maybe_eval_const_un_expr,
};
use optimize_js::il::inst::Const::{BigInt as ConstBigInt, Num as ConstNum, Str as ConstStr};
use optimize_js::il::inst::{BinOp, UnOp};
use parse_js::num::JsNumber as JN;
use std::cmp::Ordering;

#[test]
fn number_builtin_matches_string_to_number() {
  let eval_number = |s: &str| match maybe_eval_const_builtin_call("Number", &[ConstStr(s.into())]) {
    Some(ConstNum(JN(v))) => v,
    other => panic!("unexpected eval result for {s:?}: {other:?}"),
  };

  assert_eq!(eval_number("  "), 0.0);
  assert_eq!(eval_number("0x10"), 16.0);
  assert_eq!(eval_number("0b10"), 2.0);
  assert_eq!(eval_number("0o10"), 8.0);

  let inf = eval_number("Infinity");
  assert!(inf.is_infinite() && inf.is_sign_positive());
  assert!(eval_number("not a number").is_nan());
}

#[test]
fn bigint_and_string_comparisons_follow_string_to_bigint() {
  assert!(js_loose_eq(
    &ConstBigInt(BigInt::from(1)),
    &ConstStr("1".into())
  ));
  assert!(js_loose_eq(
    &ConstBigInt(BigInt::from(-1)),
    &ConstStr("-1".into())
  ));
  assert!(!js_loose_eq(
    &ConstBigInt(BigInt::from(1)),
    &ConstStr("1.0".into())
  ));
  assert!(!js_loose_eq(
    &ConstBigInt(BigInt::from(1)),
    &ConstStr("1n".into())
  ));
  assert_eq!(
    js_cmp(&ConstBigInt(BigInt::from(3)), &ConstStr(" 4 ".into())),
    Some(Ordering::Less)
  );
}

#[test]
fn negative_zero_is_preserved_through_division() {
  let neg_zero = coerce_str_to_num("-0");
  match neg_zero {
    v if v == 0.0 => assert!(v.is_sign_negative()),
    _ => panic!("expected -0 from string coercion"),
  }

  assert_eq!(js_div(1.0, neg_zero), f64::NEG_INFINITY);
  assert_eq!(js_div(-1.0, neg_zero), f64::INFINITY);
  assert!(js_loose_eq(&ConstNum(JN(0.0)), &ConstStr("-0".into())));
}

#[test]
fn bitwise_and_shift_ops_follow_to_int32_semantics() {
  let one = ConstNum(JN(1.0));
  let two = ConstNum(JN(2.0));
  assert_eq!(
    maybe_eval_const_bin_expr(BinOp::Shl, &one, &two),
    Some(ConstNum(JN(4.0)))
  );

  let minus_one = ConstNum(JN(-1.0));
  let zero = ConstNum(JN(0.0));
  assert_eq!(
    maybe_eval_const_bin_expr(BinOp::UShr, &minus_one, &zero),
    Some(ConstNum(JN(4294967295.0)))
  );

  let fractional = ConstNum(JN(1.9));
  assert_eq!(
    maybe_eval_const_bin_expr(BinOp::BitOr, &fractional, &zero),
    Some(ConstNum(JN(1.0)))
  );

  let shift_32 = ConstNum(JN(32.0));
  assert_eq!(
    maybe_eval_const_bin_expr(BinOp::Shl, &one, &shift_32),
    Some(ConstNum(JN(1.0)))
  );

  assert_eq!(
    maybe_eval_const_un_expr(UnOp::BitNot, &zero),
    Some(ConstNum(JN(-1.0)))
  );
}
