use parse_js::error::SyntaxErrorType;
use parse_js::{parse_with_options_cancellable, Dialect, ParseOptions, SourceType};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

#[test]
fn parse_with_options_cancellable_reports_cancelled_when_flag_is_set() {
  let cancel = Arc::new(AtomicBool::new(true));
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let err = parse_with_options_cancellable("let x = 1;", opts, cancel).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::Cancelled);
}

#[test]
fn parse_with_options_cancellable_parses_successfully_when_not_cancelled() {
  let cancel = Arc::new(AtomicBool::new(false));
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  assert!(parse_with_options_cancellable("let x = 1;", opts, cancel).is_ok());
}

