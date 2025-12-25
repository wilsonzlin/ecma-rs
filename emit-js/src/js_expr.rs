use parse_js::ast::expr::{
  lit::{LitBoolExpr, LitNumExpr, LitRegexExpr, LitStrExpr},
  ArrowFuncExpr, BinaryExpr, CallExpr, ComputedMemberExpr, CondExpr, Expr, IdExpr, MemberExpr,
  UnaryExpr, UnaryPostfixExpr,
};
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::operator::{Associativity, OperatorName, OPERATORS};

use crate::js_pat;
use crate::Emitter;

const CALL_MEMBER_PRECEDENCE: u8 = 18; // Matches OperatorName::Call/MemberAccess precedence.
const PRIMARY_PRECEDENCE: u8 = CALL_MEMBER_PRECEDENCE + 1;
const ARROW_PRECEDENCE: u8 = 3; // Matches assignment-expression precedence.

#[derive(Debug)]
pub enum JsEmitError {
  Unsupported(&'static str),
}

pub type JsEmitResult = Result<(), JsEmitError>;

struct JsExprEmitter<'a> {
  out: &'a mut Emitter,
}

impl<'a> JsExprEmitter<'a> {
  fn emit_expr(&mut self, expr: &Node<Expr>) -> JsEmitResult {
    self.emit_expr_with_min_prec(expr, 1)
  }

  fn emit_expr_with_min_prec(&mut self, expr: &Node<Expr>, min_prec: u8) -> JsEmitResult {
    let prec = expr_precedence(expr)?;
    let needs_parens = prec < min_prec;

    if needs_parens {
      self.out.write_punct("(");
    }
    self.emit_expr_no_parens(expr)?;
    if needs_parens {
      self.out.write_punct(")");
    }

    Ok(())
  }

  fn emit_expr_no_parens(&mut self, expr: &Node<Expr>) -> JsEmitResult {
    match expr.stx.as_ref() {
      Expr::ArrowFunc(func) => self.emit_arrow_func(func),
      Expr::Binary(binary) => self.emit_binary(binary),
      Expr::Call(call) => self.emit_call(call),
      Expr::ComputedMember(member) => self.emit_computed_member(member),
      Expr::Cond(cond) => self.emit_cond(cond),
      Expr::Id(id) => self.emit_id(id),
      Expr::LitBool(lit) => self.emit_lit_bool(lit),
      Expr::LitNum(lit) => self.emit_lit_num(lit),
      Expr::LitRegex(lit) => self.emit_lit_regex(lit),
      Expr::LitStr(lit) => self.emit_lit_str(lit),
      Expr::Member(member) => self.emit_member(member),
      Expr::Unary(unary) => self.emit_unary(unary),
      Expr::UnaryPostfix(unary) => self.emit_unary_postfix(unary),
      Expr::This(_) => {
        self.out.write_keyword("this");
        Ok(())
      }
      Expr::Super(_) => {
        self.out.write_keyword("super");
        Ok(())
      }
      Expr::ImportMeta(_) => {
        self.out.write_identifier("import");
        self.out.write_punct(".");
        self.out.write_identifier("meta");
        Ok(())
      }
      Expr::NewTarget(_) => {
        self.out.write_identifier("new");
        self.out.write_punct(".");
        self.out.write_identifier("target");
        Ok(())
      }
      Expr::LitNull(_) => {
        self.out.write_keyword("null");
        Ok(())
      }
      _ => Err(JsEmitError::Unsupported("expression kind not supported")),
    }
  }

  fn emit_arrow_func(&mut self, arrow: &Node<ArrowFuncExpr>) -> JsEmitResult {
    let func = &arrow.stx.func;
    let func = func.stx.as_ref();

    if func.generator {
      return Err(JsEmitError::Unsupported(
        "generator functions are not supported by JS emitter",
      ));
    }
    if func.type_parameters.is_some() {
      return Err(JsEmitError::Unsupported(
        "type parameters are not supported by JS emitter",
      ));
    }
    if func.return_type.is_some() {
      return Err(JsEmitError::Unsupported(
        "type annotations are not supported by JS emitter",
      ));
    }

    if func.async_ {
      self.out.write_keyword("async");
    }

    js_pat::emit_js_param_list(self.out, &func.parameters)?;

    self.out.write_punct("=>");

    let Some(body) = &func.body else {
      return Err(JsEmitError::Unsupported("arrow function body is missing"));
    };

    match body {
      FuncBody::Expression(expr) => self.emit_expr(expr),
      FuncBody::Block(_) => Err(JsEmitError::Unsupported(
        "block bodies are not supported by JS emitter",
      )),
    }
  }

  fn emit_binary(&mut self, binary: &Node<BinaryExpr>) -> JsEmitResult {
    let op = OPERATORS
      .get(&binary.stx.operator)
      .ok_or(JsEmitError::Unsupported("unknown operator"))?;
    let left_needs_parens = binary.stx.operator == OperatorName::Exponentiation
      && needs_parens_for_exponentiation_base(&binary.stx.left);
    if left_needs_parens {
      self.out.write_punct("(");
      self.emit_expr_no_parens(&binary.stx.left)?;
      self.out.write_punct(")");
    } else {
      self.emit_expr_with_min_prec(&binary.stx.left, op.precedence)?;
    }

    emit_binary_operator(self.out, binary.stx.operator)?;

    let right_prec = op.precedence + (op.associativity == Associativity::Left) as u8;
    self.emit_expr_with_min_prec(&binary.stx.right, right_prec)
  }

  fn emit_call(&mut self, call: &Node<CallExpr>) -> JsEmitResult {
    self.emit_expr_with_min_prec(&call.stx.callee, call_member_precedence())?;
    if call.stx.optional_chaining {
      self.out.write_punct("?.");
    }
    self.out.write_punct("(");
    for (idx, arg) in call.stx.arguments.iter().enumerate() {
      if idx > 0 {
        self.out.write_punct(",");
      }
      if arg.stx.spread {
        self.out.write_punct("...");
      }
      self.emit_expr_with_min_prec(&arg.stx.value, 1)?;
    }
    self.out.write_punct(")");
    Ok(())
  }

  fn emit_member(&mut self, member: &Node<MemberExpr>) -> JsEmitResult {
    if member.stx.optional_chaining {
      self.emit_expr_with_min_prec(&member.stx.left, call_member_precedence())?;
      self.out.write_punct("?.");
    } else if let Expr::LitNum(num) = member.stx.left.stx.as_ref() {
      let rendered = render_number(num);
      self.out.write_number(&rendered);
      if requires_trailing_dot(&rendered) {
        self.out.write_punct(".");
      }
      self.out.write_punct(".");
    } else {
      self.emit_expr_with_min_prec(&member.stx.left, call_member_precedence())?;
      self.out.write_punct(".");
    }
    self.out.write_identifier(&member.stx.right);
    Ok(())
  }

  fn emit_computed_member(&mut self, member: &Node<ComputedMemberExpr>) -> JsEmitResult {
    self.emit_expr_with_min_prec(&member.stx.object, call_member_precedence())?;
    if member.stx.optional_chaining {
      self.out.write_punct("?.");
    }
    self.out.write_punct("[");
    self.emit_expr_with_min_prec(&member.stx.member, 1)?;
    self.out.write_punct("]");
    Ok(())
  }

  fn emit_cond(&mut self, cond: &Node<CondExpr>) -> JsEmitResult {
    let cond_prec = OPERATORS[&OperatorName::Conditional].precedence;
    let assignment_prec = assignment_precedence();
    self.emit_expr_with_min_prec(&cond.stx.test, cond_prec + 1)?;
    self.out.write_punct("?");
    self.emit_expr_with_min_prec(&cond.stx.consequent, assignment_prec)?;
    self.out.write_punct(":");
    self.emit_expr_with_min_prec(&cond.stx.alternate, assignment_prec)
  }

  fn emit_unary(&mut self, unary: &Node<UnaryExpr>) -> JsEmitResult {
    let op_prec = operator_precedence(unary.stx.operator)?;
    emit_unary_operator(self.out, unary.stx.operator)?;
    if matches!(
      unary.stx.argument.stx.as_ref(),
      Expr::Binary(inner) if inner.stx.operator == OperatorName::Exponentiation
    ) {
      self.out.write_punct("(");
      self.emit_expr_no_parens(&unary.stx.argument)?;
      self.out.write_punct(")");
      return Ok(());
    }
    self.emit_expr_with_min_prec(&unary.stx.argument, op_prec)
  }

  fn emit_unary_postfix(&mut self, unary: &Node<UnaryPostfixExpr>) -> JsEmitResult {
    let op_prec = operator_precedence(unary.stx.operator)?;
    self.emit_expr_with_min_prec(&unary.stx.argument, op_prec)?;
    emit_unary_operator(self.out, unary.stx.operator)
  }

  fn emit_id(&mut self, id: &Node<IdExpr>) -> JsEmitResult {
    if id.stx.name == "undefined" {
      self.out.write_keyword("void");
      self.out.write_number("0");
      return Ok(());
    }
    self.out.write_identifier(&id.stx.name);
    Ok(())
  }

  fn emit_lit_bool(&mut self, lit: &Node<LitBoolExpr>) -> JsEmitResult {
    self
      .out
      .write_keyword(if lit.stx.value { "true" } else { "false" });
    Ok(())
  }

  fn emit_lit_num(&mut self, lit: &Node<LitNumExpr>) -> JsEmitResult {
    let rendered = render_number(lit);
    self.out.write_number(&rendered);
    Ok(())
  }

  fn emit_lit_regex(&mut self, lit: &Node<LitRegexExpr>) -> JsEmitResult {
    self.out.write_str(&lit.stx.value);
    Ok(())
  }

  fn emit_lit_str(&mut self, lit: &Node<LitStrExpr>) -> JsEmitResult {
    self.out.write_string_literal(&lit.stx.value);
    Ok(())
  }
}

pub fn emit_js_expr(out: &mut Emitter, expr: &Node<Expr>) -> JsEmitResult {
  let mut emitter = JsExprEmitter { out };
  emitter.emit_expr(expr)
}

fn render_number(lit: &Node<LitNumExpr>) -> String {
  lit.stx.value.to_string()
}

fn call_member_precedence() -> u8 {
  let prec = OPERATORS[&OperatorName::Call].precedence;
  debug_assert_eq!(prec, CALL_MEMBER_PRECEDENCE);
  prec
}

fn assignment_precedence() -> u8 {
  let prec = OPERATORS[&OperatorName::Assignment].precedence;
  debug_assert_eq!(prec, ARROW_PRECEDENCE);
  prec
}

fn operator_precedence(op: OperatorName) -> Result<u8, JsEmitError> {
  OPERATORS
    .get(&op)
    .map(|op| op.precedence)
    .ok_or(JsEmitError::Unsupported("unknown operator"))
}

fn expr_precedence(expr: &Node<Expr>) -> Result<u8, JsEmitError> {
  match expr.stx.as_ref() {
    Expr::ArrowFunc(_) => Ok(assignment_precedence()),
    Expr::Binary(binary) => operator_precedence(binary.stx.operator),
    Expr::Call(_) => Ok(call_member_precedence()),
    Expr::ComputedMember(_) => Ok(call_member_precedence()),
    Expr::Cond(_) => Ok(OPERATORS[&OperatorName::Conditional].precedence),
    Expr::Id(_)
    | Expr::LitBool(_)
    | Expr::LitNum(_)
    | Expr::LitRegex(_)
    | Expr::LitStr(_)
    | Expr::LitNull(_)
    | Expr::This(_)
    | Expr::Super(_)
    | Expr::ImportMeta(_)
    | Expr::NewTarget(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::Member(_) => Ok(call_member_precedence()),
    Expr::Unary(unary) => operator_precedence(unary.stx.operator),
    Expr::UnaryPostfix(unary) => operator_precedence(unary.stx.operator),
    _ => Err(JsEmitError::Unsupported("expression kind not supported")),
  }
}

fn needs_parens_for_exponentiation_base(expr: &Node<Expr>) -> bool {
  matches!(expr.stx.as_ref(), Expr::Unary(_) | Expr::UnaryPostfix(_))
}

enum OperatorToken {
  Keyword(&'static str),
  Punct(&'static str),
}

fn emit_binary_operator(out: &mut Emitter, operator: OperatorName) -> JsEmitResult {
  let token = match operator {
    OperatorName::Addition => OperatorToken::Punct("+"),
    OperatorName::Subtraction => OperatorToken::Punct("-"),
    OperatorName::Multiplication => OperatorToken::Punct("*"),
    OperatorName::Division => OperatorToken::Punct("/"),
    OperatorName::Remainder => OperatorToken::Punct("%"),
    OperatorName::Exponentiation => OperatorToken::Punct("**"),
    OperatorName::LessThan => OperatorToken::Punct("<"),
    OperatorName::LessThanOrEqual => OperatorToken::Punct("<="),
    OperatorName::GreaterThan => OperatorToken::Punct(">"),
    OperatorName::GreaterThanOrEqual => OperatorToken::Punct(">="),
    OperatorName::Equality => OperatorToken::Punct("=="),
    OperatorName::Inequality => OperatorToken::Punct("!="),
    OperatorName::StrictEquality => OperatorToken::Punct("==="),
    OperatorName::StrictInequality => OperatorToken::Punct("!=="),
    OperatorName::BitwiseAnd => OperatorToken::Punct("&"),
    OperatorName::BitwiseOr => OperatorToken::Punct("|"),
    OperatorName::BitwiseXor => OperatorToken::Punct("^"),
    OperatorName::BitwiseLeftShift => OperatorToken::Punct("<<"),
    OperatorName::BitwiseRightShift => OperatorToken::Punct(">>"),
    OperatorName::BitwiseUnsignedRightShift => OperatorToken::Punct(">>>"),
    OperatorName::LogicalAnd => OperatorToken::Punct("&&"),
    OperatorName::LogicalOr => OperatorToken::Punct("||"),
    OperatorName::NullishCoalescing => OperatorToken::Punct("??"),
    OperatorName::In => OperatorToken::Keyword("in"),
    OperatorName::Instanceof => OperatorToken::Keyword("instanceof"),
    OperatorName::Comma => OperatorToken::Punct(","),
    OperatorName::Assignment => OperatorToken::Punct("="),
    OperatorName::AssignmentAddition => OperatorToken::Punct("+="),
    OperatorName::AssignmentBitwiseAnd => OperatorToken::Punct("&="),
    OperatorName::AssignmentBitwiseLeftShift => OperatorToken::Punct("<<="),
    OperatorName::AssignmentBitwiseOr => OperatorToken::Punct("|="),
    OperatorName::AssignmentBitwiseRightShift => OperatorToken::Punct(">>="),
    OperatorName::AssignmentBitwiseUnsignedRightShift => OperatorToken::Punct(">>>="),
    OperatorName::AssignmentBitwiseXor => OperatorToken::Punct("^="),
    OperatorName::AssignmentDivision => OperatorToken::Punct("/="),
    OperatorName::AssignmentExponentiation => OperatorToken::Punct("**="),
    OperatorName::AssignmentLogicalAnd => OperatorToken::Punct("&&="),
    OperatorName::AssignmentLogicalOr => OperatorToken::Punct("||="),
    OperatorName::AssignmentMultiplication => OperatorToken::Punct("*="),
    OperatorName::AssignmentNullishCoalescing => OperatorToken::Punct("??="),
    OperatorName::AssignmentRemainder => OperatorToken::Punct("%="),
    OperatorName::AssignmentSubtraction => OperatorToken::Punct("-="),
    _ => {
      return Err(JsEmitError::Unsupported(
        "operator not supported in JS emitter",
      ))
    }
  };

  match token {
    OperatorToken::Keyword(keyword) => out.write_keyword(keyword),
    OperatorToken::Punct(punct) => out.write_punct(punct),
  }
  Ok(())
}

fn emit_unary_operator(out: &mut Emitter, operator: OperatorName) -> JsEmitResult {
  let token = match operator {
    OperatorName::LogicalNot => OperatorToken::Punct("!"),
    OperatorName::BitwiseNot => OperatorToken::Punct("~"),
    OperatorName::UnaryPlus => OperatorToken::Punct("+"),
    OperatorName::UnaryNegation => OperatorToken::Punct("-"),
    OperatorName::PrefixIncrement => OperatorToken::Punct("++"),
    OperatorName::PrefixDecrement => OperatorToken::Punct("--"),
    OperatorName::PostfixIncrement => OperatorToken::Punct("++"),
    OperatorName::PostfixDecrement => OperatorToken::Punct("--"),
    OperatorName::Typeof => OperatorToken::Keyword("typeof"),
    OperatorName::Void => OperatorToken::Keyword("void"),
    OperatorName::Delete => OperatorToken::Keyword("delete"),
    OperatorName::Await => OperatorToken::Keyword("await"),
    _ => {
      return Err(JsEmitError::Unsupported(
        "operator not supported in JS emitter",
      ))
    }
  };

  match token {
    OperatorToken::Keyword(keyword) => out.write_keyword(keyword),
    OperatorToken::Punct(punct) => out.write_punct(punct),
  }
  Ok(())
}

fn requires_trailing_dot(rendered: &str) -> bool {
  let mut bytes = rendered.as_bytes();
  if bytes.starts_with(b"-") {
    bytes = &bytes[1..];
  }
  bytes.iter().all(|b| b.is_ascii_digit())
}
