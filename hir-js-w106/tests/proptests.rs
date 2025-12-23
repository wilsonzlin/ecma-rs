use hir_js::lower_from_source;
use proptest::prelude::*;

fn arb_source() -> impl Strategy<Value = String> {
  // Keep samples small to ensure fast termination.
  prop::collection::vec(any::<char>(), 0..64).prop_map(|chars| chars.into_iter().collect())
}

proptest! {
  #[test]
  fn lowering_never_panics(src in arb_source()) {
    let _ = lower_from_source(&src);
    // We only care that it terminates without unwinding; parse errors are fine.
  }
}
