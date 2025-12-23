use parse_js::error::SyntaxError;
use parse_js::loc::Loc;

#[derive(Clone, Debug)]
pub enum MinifyError {
  Syntax(SyntaxError),
  UseBeforeDecl(Loc),
}
