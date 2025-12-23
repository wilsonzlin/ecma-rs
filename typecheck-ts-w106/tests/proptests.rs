use proptest::prelude::*;
use typecheck_ts::check;

fn arb_source() -> impl Strategy<Value = String> {
  prop::collection::vec(any::<char>(), 0..96).prop_map(|chars| chars.into_iter().collect())
}

proptest! {
  #[test]
  fn check_never_panics(src in arb_source()) {
    let _ = check(&src);
    // Success criteria: termination without unwinding.
  }
}
