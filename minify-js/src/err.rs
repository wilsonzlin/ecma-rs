use parse_js::error::SyntaxError;
use parse_js::loc::Loc;
use std::str::Utf8Error;

#[derive(Clone, Debug)]
pub enum MinifyError {
  Syntax(SyntaxError),
  UseBeforeDecl(Loc),
  InvalidUtf8(Utf8Error),
}
