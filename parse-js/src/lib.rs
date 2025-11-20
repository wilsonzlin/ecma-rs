use ast::node::Node;
use ast::stx::TopLevel;
use error::SyntaxResult;
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

pub fn parse(source: &str) -> SyntaxResult<Node<TopLevel>> {
  let lexer = Lexer::new(source);
  let mut parser = Parser::new(lexer);
  parser.parse_top_level()
}
