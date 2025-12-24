use ast::node::Node;
use ast::stx::TopLevel;
use error::{SyntaxError, SyntaxResult};
use lex::Lexer;
use parse::Parser;

pub mod ast;
pub mod char;
pub mod error;
pub mod lex;
pub mod loc;
pub mod num;
pub mod operator;
pub mod parse;
pub mod token;
pub mod util;

#[derive(Clone, Copy, Debug)]
pub enum ParseMode {
  TypeScript,
  Tsx,
}

#[derive(Clone, Copy, Debug)]
pub struct ParseOptions {
  pub mode: ParseMode,
}

impl Default for ParseOptions {
  fn default() -> Self {
    ParseOptions {
      mode: ParseMode::TypeScript,
    }
  }
}

#[derive(Debug)]
pub struct ParseOutput {
  pub result: SyntaxResult<Node<TopLevel>>,
  pub diagnostics: Vec<SyntaxError>,
}

pub fn parse_with_options(source: &str, options: ParseOptions) -> ParseOutput {
  let _mode = options.mode;
  let lexer = Lexer::new(source);
  let mut parser = Parser::new(lexer);
  let result = parser.parse_top_level();
  let diagnostics = match &result {
    Ok(_) => Vec::new(),
    Err(err) => vec![err.clone()],
  };
  ParseOutput {
    result,
    diagnostics,
  }
}

pub fn parse(source: &str) -> SyntaxResult<Node<TopLevel>> {
  parse_with_options(source, ParseOptions::default()).result
}
