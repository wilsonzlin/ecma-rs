use emit_js::{emit_top_level_stmt, EmitOptions, Emitter};
use parse_js::ast::expr::lit::LitArrElem;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::num::JsNumber;
use parse_js::operator::OperatorName;
use parse_js::parse;

fn numeric_expr_value(expr: &Node<Expr>) -> JsNumber {
  match expr.stx.as_ref() {
    Expr::LitNum(num) => num.stx.value,
    Expr::Unary(unary) if unary.stx.operator == OperatorName::UnaryNegation => {
      let inner = numeric_expr_value(&unary.stx.argument);
      JsNumber(-inner.0)
    }
    Expr::Unary(unary) if unary.stx.operator == OperatorName::UnaryPlus => {
      numeric_expr_value(&unary.stx.argument)
    }
    other => panic!("unexpected numeric expression: {:?}", other),
  }
}

fn array_values(expr: &Node<Expr>) -> Vec<JsNumber> {
  match expr.stx.as_ref() {
    Expr::LitArr(arr) => arr
      .stx
      .elements
      .iter()
      .map(|elem| match elem {
        LitArrElem::Single(expr) => numeric_expr_value(expr),
        other => panic!("unexpected array element: {:?}", other),
      })
      .collect(),
    other => panic!("expected array literal, got {:?}", other),
  }
}

fn collect_array_literals(ast: &Node<TopLevel>) -> Vec<Vec<JsNumber>> {
  let mut arrays = Vec::new();
  for stmt in &ast.stx.body {
    if let Stmt::VarDecl(decl) = stmt.stx.as_ref() {
      for declarator in &decl.stx.declarators {
        if let Some(initializer) = &declarator.initializer {
          arrays.push(array_values(initializer));
        }
      }
    }
  }
  arrays
}

#[test]
fn emitter_roundtrips_large_numeric_literals() {
  let source = "
    const nums=[1e400,1.7976931348623157e308,5e-324,0x1fffffffffffff];
    const neg=[-1e400,-0];
  ";
  let parsed = parse(source).expect("parse source program");
  let mut emitter = Emitter::new(EmitOptions::minified());
  emit_top_level_stmt(&mut emitter, parsed.stx.as_ref()).expect("emit program");
  let output = String::from_utf8(emitter.into_bytes()).expect("emitter output is UTF-8");

  assert!(
    !output.contains("inf") && !output.contains("NaN"),
    "emitted output must avoid invalid float spellings: {output}"
  );

  let reparsed = parse(&output).expect("reparse emitted program");

  let original_arrays = collect_array_literals(&parsed);
  let reparsed_arrays = collect_array_literals(&reparsed);
  assert_eq!(original_arrays.len(), reparsed_arrays.len());

  for (original, reparsed) in original_arrays.iter().zip(reparsed_arrays.iter()) {
    let original_bits: Vec<u64> = original.iter().map(|n| n.to_bits()).collect();
    let reparsed_bits: Vec<u64> = reparsed.iter().map(|n| n.to_bits()).collect();
    assert_eq!(original_bits, reparsed_bits);
  }
}
