use std::fmt;

use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType};
use parse_js::ast::expr::jsx::JsxElem;
use parse_js::ast::expr::{
  lit::{
    LitArrElem, LitArrExpr, LitBigIntExpr, LitBoolExpr, LitNumExpr, LitObjExpr, LitRegexExpr,
    LitStrExpr, LitTemplatePart,
  },
  ArrowFuncExpr, BinaryExpr, CallArg, CallExpr, ClassExpr, ComputedMemberExpr, CondExpr, Expr,
  FuncExpr, IdExpr, ImportExpr, MemberExpr, TaggedTemplateExpr, UnaryExpr, UnaryPostfixExpr,
};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::operator::{OperatorName, OPERATORS};

use crate::emitter::{with_node_context, EmitError, EmitOptions, EmitResult};
use crate::escape::emit_string_literal;
use crate::precedence::{
  child_min_prec_for_binary, expr_prec, needs_parens, starts_with_optional_chaining, Prec, Side,
  CALL_MEMBER_PRECEDENCE,
};
use crate::Emitter;

pub struct ExprEmitter<'a, W, F>
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  pub(crate) out: &'a mut W,
  pub(crate) emit_type: F,
  pub(crate) opts: EmitOptions,
}

impl<'a, W, F> ExprEmitter<'a, W, F>
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  pub fn new(out: &'a mut W, emit_type: F, opts: EmitOptions) -> Self {
    Self {
      out,
      emit_type,
      opts,
    }
  }

  pub fn emit_expr(&mut self, expr: &Node<Expr>) -> EmitResult {
    with_node_context(expr.loc, || {
      self.emit_expr_with_min_prec(expr, Prec::new(1))
    })
  }

  fn sep(&self) -> &'static str {
    if self.opts.minify {
      ""
    } else {
      " "
    }
  }

  pub(crate) fn emit_expr_with_min_prec(
    &mut self,
    expr: &Node<Expr>,
    min_prec: Prec,
  ) -> EmitResult {
    with_node_context(expr.loc, || {
      let prec = expr_prec(expr);
      let wrap = needs_parens(prec, min_prec);

      if wrap {
        write!(self.out, "(")?;
      }
      self.emit_expr_no_parens(expr)?;
      if wrap {
        write!(self.out, ")")?;
      }

      Ok(())
    })
  }

  fn emit_expr_no_parens(&mut self, expr: &Node<Expr>) -> EmitResult {
    with_node_context(expr.loc, || match expr.stx.as_ref() {
      Expr::Id(id) => self.emit_id(id),
      Expr::This(_) => self.emit_this(),
      Expr::Super(_) => self.emit_super(),
      Expr::NewTarget(_) => self.emit_new_target(),
      Expr::ImportMeta(_) => self.emit_import_meta(),
      Expr::LitNum(num) => self.emit_lit_num(num),
      Expr::LitBool(lit) => self.emit_lit_bool(lit),
      Expr::LitNull(_) => self.emit_lit_null(),
      Expr::LitBigInt(lit) => self.emit_lit_big_int(lit),
      Expr::LitStr(lit) => self.emit_lit_str(lit),
      Expr::LitRegex(lit) => self.emit_lit_regex(lit),
      Expr::LitTemplate(lit) => self.emit_template_literal(&lit.stx.parts),
      Expr::LitArr(arr) => self.emit_lit_arr(arr),
      Expr::LitObj(obj) => self.emit_lit_obj(obj),
      Expr::JsxElem(elem) => self.emit_jsx_elem(elem),
      Expr::Func(func) => self.emit_func_expr(func),
      Expr::Class(class) => self.emit_class_expr(class),
      Expr::Import(import_expr) => self.emit_import_expr(import_expr),
      Expr::ArrowFunc(arrow) => self.emit_arrow_func(arrow),
      Expr::ArrPat(arr) => self.emit_array_pattern(arr),
      Expr::IdPat(id) => self.emit_id_pattern(id),
      Expr::ObjPat(obj) => self.emit_object_pattern(obj),
      Expr::Unary(unary) => self.emit_unary(unary),
      Expr::UnaryPostfix(unary) => self.emit_unary_postfix(unary),
      Expr::Binary(binary) => self.emit_binary(binary),
      Expr::Cond(cond) => self.emit_cond(cond),
      Expr::Call(call) => self.emit_call(call),
      Expr::Member(member) => self.emit_member(member),
      Expr::ComputedMember(member) => self.emit_computed_member(member),
      Expr::TaggedTemplate(tagged) => self.emit_tagged_template(tagged),
      Expr::NonNullAssertion(non_null) => self.emit_non_null_assertion(non_null),
      Expr::TypeAssertion(assertion) => self.emit_type_assertion(assertion),
      Expr::SatisfiesExpr(satisfies) => self.emit_satisfies_expr(satisfies),
      _ => Err(EmitError::unsupported("expression kind not supported")),
    })
  }

  // TypeScript requires parentheses when `as`/`satisfies` are used as receivers of call/member access.
  fn emit_memberish_receiver(&mut self, expr: &Node<Expr>) -> EmitResult {
    match expr.stx.as_ref() {
      Expr::TypeAssertion(_) | Expr::SatisfiesExpr(_) => {
        write!(self.out, "(")?;
        self.emit_expr_no_parens(expr)?;
        write!(self.out, ")")?;
        Ok(())
      }
      _ => self.emit_expr_with_min_prec(expr, CALL_MEMBER_PRECEDENCE),
    }
  }

  fn emit_id(&mut self, id: &Node<IdExpr>) -> EmitResult {
    with_node_context(id.loc, || {
      if id.stx.name == "undefined" {
        self.out.write_str("void 0")?;
      } else {
        self.out.write_str(&id.stx.name)?;
      }
      Ok(())
    })
  }

  fn emit_this(&mut self) -> EmitResult {
    self.out.write_str("this")?;
    Ok(())
  }

  fn emit_super(&mut self) -> EmitResult {
    self.out.write_str("super")?;
    Ok(())
  }

  fn emit_new_target(&mut self) -> EmitResult {
    self.out.write_str("new.target")?;
    Ok(())
  }

  fn emit_import_meta(&mut self) -> EmitResult {
    self.out.write_str("import.meta")?;
    Ok(())
  }

  fn emit_lit_num(&mut self, lit: &Node<LitNumExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      write!(self.out, "{}", lit.stx.value)?;
      Ok(())
    })
  }

  fn emit_lit_bool(&mut self, lit: &Node<LitBoolExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      self
        .out
        .write_str(if lit.stx.value { "true" } else { "false" })?;
      Ok(())
    })
  }

  fn emit_lit_null(&mut self) -> EmitResult {
    self.out.write_str("null")?;
    Ok(())
  }

  fn emit_lit_big_int(&mut self, lit: &Node<LitBigIntExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      write!(self.out, "{}n", lit.stx.value)?;
      Ok(())
    })
  }

  fn emit_lit_str(&mut self, lit: &Node<LitStrExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      let mut buf = Vec::new();
      emit_string_literal(
        &mut buf,
        &lit.stx.value,
        self.opts.quote_style,
        self.opts.minify,
      );
      self
        .out
        .write_str(std::str::from_utf8(&buf).expect("string literal escape output is UTF-8"))?;
      Ok(())
    })
  }

  fn emit_lit_regex(&mut self, lit: &Node<LitRegexExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      let mut buf = Vec::new();
      crate::escape::emit_regex_literal(&mut buf, &lit.stx.value);
      self
        .out
        .write_str(std::str::from_utf8(&buf).expect("regex literal escape output is UTF-8"))?;
      Ok(())
    })
  }

  fn emit_jsx_elem(&mut self, elem: &Node<JsxElem>) -> EmitResult {
    with_node_context(elem.loc, || {
      let mut emitter = Emitter::default();
      crate::jsx::emit_jsx_elem(&mut emitter, elem)?;
      let rendered = std::str::from_utf8(emitter.as_bytes()).expect("JSX emitter output is UTF-8");
      self.out.write_str(rendered).map_err(EmitError::from)?;
      Ok(())
    })
  }

  fn emit_pattern_fragment(&mut self, f: impl FnOnce(&mut Emitter) -> EmitResult) -> EmitResult {
    let mut emitter = Emitter::new(self.opts);
    f(&mut emitter)?;
    let rendered =
      std::str::from_utf8(emitter.as_bytes()).expect("pattern emitter output is UTF-8");
    self.out.write_str(rendered).map_err(EmitError::from)?;
    Ok(())
  }

  fn emit_array_pattern(&mut self, arr: &Node<parse_js::ast::expr::pat::ArrPat>) -> EmitResult {
    with_node_context(arr.loc, || {
      self.emit_pattern_fragment(|em| crate::pat::emit_array_pattern(em, arr))
    })
  }

  fn emit_id_pattern(&mut self, id: &Node<parse_js::ast::expr::pat::IdPat>) -> EmitResult {
    with_node_context(id.loc, || {
      self.emit_pattern_fragment(|em| crate::pat::emit_id_pattern(em, id))
    })
  }

  fn emit_object_pattern(&mut self, obj: &Node<parse_js::ast::expr::pat::ObjPat>) -> EmitResult {
    with_node_context(obj.loc, || {
      self.emit_pattern_fragment(|em| crate::pat::emit_object_pattern(em, obj))
    })
  }

  fn emit_lit_arr(&mut self, arr: &Node<LitArrExpr>) -> EmitResult {
    with_node_context(arr.loc, || {
      self.out.write_char('[')?;
      for (idx, elem) in arr.stx.elements.iter().enumerate() {
        if idx > 0 {
          self.out.write_char(',')?;
        }
        match elem {
          LitArrElem::Single(expr) => self.emit_expr_with_min_prec(expr, Prec::new(1))?,
          LitArrElem::Rest(expr) => {
            self.out.write_str("...")?;
            self.emit_expr_with_min_prec(expr, Prec::new(1))?;
          }
          LitArrElem::Empty => {}
        }
      }
      self.out.write_char(']')?;
      Ok(())
    })
  }

  fn emit_lit_obj(&mut self, obj: &Node<LitObjExpr>) -> EmitResult {
    with_node_context(obj.loc, || {
      self.out.write_char('{')?;
      for (idx, member) in obj.stx.members.iter().enumerate() {
        if idx > 0 {
          self.out.write_char(',')?;
          self.out.write_str(self.sep())?;
        }
        self.emit_obj_member(member)?;
      }
      self.out.write_char('}')?;
      Ok(())
    })
  }

  fn emit_obj_member(&mut self, member: &Node<ObjMember>) -> EmitResult {
    with_node_context(member.loc, || match &member.stx.typ {
      ObjMemberType::Valued { key, val } => self.emit_obj_valued_member(key, val),
      ObjMemberType::Shorthand { id } => {
        self.out.write_str(&id.stx.name)?;
        Ok(())
      }
      ObjMemberType::Rest { val } => {
        self.out.write_str("...")?;
        self.emit_expr_with_min_prec(val, Prec::new(1))
      }
    })
  }

  fn emit_obj_valued_member(&mut self, key: &ClassOrObjKey, val: &ClassOrObjVal) -> EmitResult {
    match val {
      ClassOrObjVal::Prop(Some(expr)) => {
        self.emit_pattern_fragment(|em| crate::pat::emit_class_or_object_key(em, key))?;
        self.out.write_char(':')?;
        self.out.write_str(self.sep())?;
        self.emit_expr_with_min_prec(expr, Prec::new(1))
      }
      ClassOrObjVal::Prop(None) => Err(EmitError::unsupported("object property missing value")),
      _ => Err(EmitError::unsupported("object member kind not supported")),
    }
  }

  fn emit_func_expr(&mut self, func: &Node<FuncExpr>) -> EmitResult {
    with_node_context(func.loc, || {
      let func = func.stx.as_ref();
      let details = func.func.stx.as_ref();
      if details.async_ {
        self.out.write_str("async")?;
        self.out.write_str(self.sep())?;
      }
      self.out.write_str("function")?;
      if details.generator {
        self.out.write_char('*')?;
      }
      if let Some(name) = &func.name {
        if !self.opts.minify {
          self.out.write_str(" ")?;
        }
        self.out.write_str(&name.stx.name)?;
      }
      self.emit_func_signature(&func.func)?;
      self.emit_func_body(&func.func)
    })
  }

  fn emit_func_signature(&mut self, func: &Node<Func>) -> EmitResult {
    with_node_context(func.loc, || {
      let func = func.stx.as_ref();
      let mut type_params = String::new();
      crate::ts_type::emit_type_parameters(&mut type_params, func.type_parameters.as_deref());
      self.out.write_str(&type_params)?;

      self.out.write_char('(')?;
      for (idx, param) in func.parameters.iter().enumerate() {
        if idx > 0 {
          self.out.write_char(',')?;
          self.out.write_str(self.sep())?;
        }
        self.emit_pattern_fragment(|em| crate::pat::emit_param_decl(em, param))?;
      }
      self.out.write_char(')')?;

      if let Some(return_type) = &func.return_type {
        self.out.write_char(':')?;
        self.out.write_str(self.sep())?;
        self.emit_type(return_type)?;
      }

      Ok(())
    })
  }

  fn emit_func_body(&mut self, func: &Node<Func>) -> EmitResult {
    with_node_context(func.loc, || match &func.stx.body {
      Some(FuncBody::Block(stmts)) => {
        self.out.write_char('{')?;
        if !stmts.is_empty() {
          return Err(EmitError::unsupported(
            "function body statements not supported",
          ));
        }
        self.out.write_char('}')?;
        Ok(())
      }
      Some(FuncBody::Expression(_)) => Err(EmitError::unsupported(
        "expression bodies not supported in function expressions",
      )),
      None => Err(EmitError::unsupported("function body missing")),
    })
  }

  fn emit_class_expr(&mut self, class: &Node<ClassExpr>) -> EmitResult {
    with_node_context(class.loc, || {
      let class = class.stx.as_ref();
      if !class.decorators.is_empty() {
        return Err(EmitError::unsupported("class decorators not supported"));
      }
      self.out.write_str("class")?;
      if let Some(name) = &class.name {
        write!(self.out, " {}", name.stx.name)?;
      }

      let mut type_params = String::new();
      crate::ts_type::emit_type_parameters(&mut type_params, class.type_parameters.as_deref());
      self.out.write_str(&type_params)?;

      if let Some(extends) = &class.extends {
        self.out.write_str(" extends ")?;
        self.emit_expr_with_min_prec(extends, Prec::new(1))?;
      }
      if !class.implements.is_empty() {
        self.out.write_str(" implements ")?;
        for (idx, ty) in class.implements.iter().enumerate() {
          if idx > 0 {
            self.out.write_str(", ")?;
          }
          self.emit_type(ty)?;
        }
      }

      self.out.write_str(" {")?;
      if !class.members.is_empty() {
        return Err(EmitError::unsupported("class members not supported"));
      }
      self.out.write_str("}")?;
      Ok(())
    })
  }

  fn emit_import_expr(&mut self, import: &Node<ImportExpr>) -> EmitResult {
    with_node_context(import.loc, || {
      self.out.write_str("import(")?;
      self.emit_expr_with_min_prec(&import.stx.module, Prec::new(1))?;
      if let Some(attrs) = &import.stx.attributes {
        self.out.write_char(',')?;
        self.out.write_str(self.sep())?;
        self.emit_expr_with_min_prec(attrs, Prec::new(1))?;
      }
      self.out.write_char(')')?;
      Ok(())
    })
  }

  fn emit_arrow_func(&mut self, arrow: &Node<ArrowFuncExpr>) -> EmitResult {
    with_node_context(arrow.loc, || {
      let func = arrow.stx.func.stx.as_ref();
      if !func.arrow {
        return Err(EmitError::unsupported(
          "non-arrow function in arrow expression",
        ));
      }
      if func.generator {
        return Err(EmitError::unsupported(
          "generator arrow function not supported",
        ));
      }

      if func.async_ {
        self.out.write_str("async")?;
        self.out.write_str(self.sep())?;
      }

      self.emit_func_signature(&arrow.stx.func)?;

      if self.opts.minify {
        self.out.write_str("=>")?;
      } else {
        self.out.write_str(" => ")?;
      }
      match func.body.as_ref() {
        Some(FuncBody::Expression(expr)) => {
          let needs_parens = is_comma_expression(expr.stx.as_ref()) || expr_starts_with_brace(expr);
          if needs_parens {
            self.out.write_char('(')?;
          }
          self.emit_expr_with_min_prec(expr, Prec::new(1))?;
          if needs_parens {
            self.out.write_char(')')?;
          }
          Ok(())
        }
        Some(FuncBody::Block(stmts)) => {
          self.out.write_char('{')?;
          if !stmts.is_empty() {
            return Err(EmitError::unsupported(
              "arrow function block body emission not supported",
            ));
          }
          self.out.write_char('}')?;
          Ok(())
        }
        None => Err(EmitError::unsupported("arrow function missing body")),
      }
    })
  }

  fn emit_unary(&mut self, unary: &Node<UnaryExpr>) -> EmitResult {
    with_node_context(unary.loc, || {
      if unary.stx.operator == OperatorName::New {
        return self.emit_new_expr(&unary.stx.argument);
      }

      let op_txt = unary_operator_text(unary.stx.operator)?;
      self.out.write_str(op_txt)?;
      let prec = Prec::new(
        OPERATORS
          .get(&unary.stx.operator)
          .ok_or(EmitError::unsupported("unknown operator"))?
          .precedence,
      );
      let needs_parens = matches!(
        unary.stx.argument.stx.as_ref(),
        Expr::Binary(binary) if binary.stx.operator == OperatorName::Exponentiation
      );
      if needs_parens {
        write!(self.out, "(")?;
        self.emit_expr_with_min_prec(&unary.stx.argument, Prec::LOWEST)?;
        write!(self.out, ")")?;
        Ok(())
      } else {
        self.emit_expr_with_min_prec(&unary.stx.argument, prec)
      }
    })
  }

  fn emit_new_expr(&mut self, argument: &Node<Expr>) -> EmitResult {
    write!(self.out, "new ")?;

    match argument.stx.as_ref() {
      Expr::Call(call) => {
        if call.stx.optional_chaining {
          write!(self.out, "(")?;
          self.emit_call(call)?;
          write!(self.out, ")")?;
          return Ok(());
        }

        let callee = &call.stx.callee;
        if starts_with_optional_chaining(callee) {
          write!(self.out, "(")?;
          self.emit_memberish_receiver(callee)?;
          write!(self.out, ")")?;
        } else {
          self.emit_memberish_receiver(callee)?;
        }

        write!(self.out, "(")?;

        for (idx, arg) in call.stx.arguments.iter().enumerate() {
          if idx > 0 {
            self.out.write_char(',')?;
            self.out.write_str(self.sep())?;
          }
          let CallArg { spread, value } = arg.stx.as_ref();
          if *spread {
            write!(self.out, "...")?;
          }
          self.emit_expr_with_min_prec(value, Prec::new(1))?;
        }

        write!(self.out, ")")?;
        Ok(())
      }
      _ => {
        if starts_with_optional_chaining(argument) {
          write!(self.out, "(")?;
          self.emit_expr_with_min_prec(argument, CALL_MEMBER_PRECEDENCE)?;
          write!(self.out, ")")?;
        } else {
          self.emit_expr_with_min_prec(argument, CALL_MEMBER_PRECEDENCE)?;
        }
        Ok(())
      }
    }
  }

  fn emit_unary_postfix(&mut self, unary: &Node<UnaryPostfixExpr>) -> EmitResult {
    with_node_context(unary.loc, || {
      let prec = Prec::new(
        OPERATORS
          .get(&unary.stx.operator)
          .ok_or(EmitError::unsupported("unknown operator"))?
          .precedence,
      );
      self.emit_expr_with_min_prec(&unary.stx.argument, prec)?;
      match unary.stx.operator {
        OperatorName::PostfixIncrement => write!(self.out, "++")?,
        OperatorName::PostfixDecrement => write!(self.out, "--")?,
        _ => return Err(EmitError::unsupported("unknown postfix operator")),
      }
      Ok(())
    })
  }

  fn emit_binary(&mut self, binary: &Node<BinaryExpr>) -> EmitResult {
    with_node_context(binary.loc, || {
      let op_txt = binary_operator_text(binary.stx.operator)?;
      let left_min_prec = child_min_prec_for_binary(binary.stx.operator, Side::Left);
      let right_min_prec = child_min_prec_for_binary(binary.stx.operator, Side::Right);

      let force_left_parens = binary.stx.operator == OperatorName::Exponentiation
        && matches!(binary.stx.left.stx.as_ref(), Expr::Unary(_));

      let force_left_parens = force_left_parens
        || (binary.stx.operator == OperatorName::NullishCoalescing
          && is_logical_and_or(&binary.stx.left))
        || ((binary.stx.operator == OperatorName::LogicalAnd
          || binary.stx.operator == OperatorName::LogicalOr)
          && is_nullish(&binary.stx.left));

      let force_right_parens = (binary.stx.operator == OperatorName::NullishCoalescing
        && is_logical_and_or(&binary.stx.right))
        || ((binary.stx.operator == OperatorName::LogicalAnd
          || binary.stx.operator == OperatorName::LogicalOr)
          && is_nullish(&binary.stx.right));

      if force_left_parens {
        self.emit_wrapped(&binary.stx.left, Prec::LOWEST)?;
      } else {
        self.emit_expr_with_min_prec(&binary.stx.left, left_min_prec)?;
      }
      if binary.stx.operator == OperatorName::Comma {
        self.out.write_char(',')?;
        self.out.write_str(self.sep())?;
      } else {
        if self.opts.minify {
          self.out.write_str(op_txt)?;
        } else {
          write!(self.out, " {} ", op_txt)?;
        }
      }
      if force_right_parens {
        self.emit_wrapped(&binary.stx.right, Prec::LOWEST)
      } else {
        self.emit_expr_with_min_prec(&binary.stx.right, right_min_prec)
      }
    })
  }

  fn emit_cond(&mut self, cond: &Node<CondExpr>) -> EmitResult {
    with_node_context(cond.loc, || {
      let prec = Prec::new(OPERATORS[&OperatorName::Conditional].precedence);
      self.emit_expr_with_min_prec(&cond.stx.test, prec.tighter())?;
      if self.opts.minify {
        self.out.write_char('?')?;
      } else {
        write!(self.out, " ? ")?;
      }
      self.emit_expr_with_min_prec(&cond.stx.consequent, prec)?;
      if self.opts.minify {
        self.out.write_char(':')?;
      } else {
        write!(self.out, " : ")?;
      }
      self.emit_expr_with_min_prec(&cond.stx.alternate, prec)
    })
  }

  fn emit_call(&mut self, call: &Node<CallExpr>) -> EmitResult {
    with_node_context(call.loc, || {
      self.emit_memberish_receiver(&call.stx.callee)?;
      if call.stx.optional_chaining {
        write!(self.out, "?.(")?;
      } else {
        write!(self.out, "(")?;
      }
      for (i, arg) in call.stx.arguments.iter().enumerate() {
        if i > 0 {
          self.out.write_char(',')?;
          self.out.write_str(self.sep())?;
        }
        let CallArg { spread, value } = arg.stx.as_ref();
        if *spread {
          write!(self.out, "...")?;
        }
        self.emit_expr_with_min_prec(value, Prec::new(1))?;
      }
      write!(self.out, ")")?;
      Ok(())
    })
  }

  fn emit_member(&mut self, member: &Node<MemberExpr>) -> EmitResult {
    with_node_context(member.loc, || {
      if member.stx.optional_chaining {
        self.emit_memberish_receiver(&member.stx.left)?;
        write!(self.out, "?.")?;
      } else if let Expr::LitNum(num) = member.stx.left.stx.as_ref() {
        let rendered = num.stx.value.to_string();
        self.out.write_str(&rendered)?;
        if requires_trailing_dot(&rendered) {
          self.out.write_char('.')?;
        }
        self.out.write_char('.')?;
      } else {
        self.emit_memberish_receiver(&member.stx.left)?;
        self.out.write_char('.')?;
      }
      self.out.write_str(&member.stx.right)?;
      Ok(())
    })
  }

  fn emit_computed_member(&mut self, member: &Node<ComputedMemberExpr>) -> EmitResult {
    with_node_context(member.loc, || {
      self.emit_memberish_receiver(&member.stx.object)?;
      if member.stx.optional_chaining {
        write!(self.out, "?.[")?;
      } else {
        write!(self.out, "[")?;
      }
      self.emit_expr_with_min_prec(&member.stx.member, Prec::new(1))?;
      write!(self.out, "]")?;
      Ok(())
    })
  }

  fn emit_tagged_template(&mut self, tagged: &Node<TaggedTemplateExpr>) -> EmitResult {
    with_node_context(tagged.loc, || {
      self.emit_memberish_receiver(&tagged.stx.function)?;
      self.emit_template_literal(&tagged.stx.parts)
    })
  }

  fn emit_template_literal(&mut self, parts: &[LitTemplatePart]) -> EmitResult {
    let mut raw = String::new();
    raw.push('`');
    for (idx, part) in parts.iter().enumerate() {
      match part {
        LitTemplatePart::String(raw_part) => {
          let is_first = idx == 0;
          let is_last = idx == parts.len().saturating_sub(1);
          let cooked = crate::cooked_template_segment(raw_part, is_first, is_last);
          let mut buf = Vec::new();
          crate::emit_template_literal_segment(&mut buf, cooked);
          raw.push_str(std::str::from_utf8(&buf).expect("template literal escape output is UTF-8"));
        }
        LitTemplatePart::Substitution(expr) => {
          raw.push_str("${");
          self.out.write_str(&raw)?;
          raw.clear();
          self.emit_expr_with_min_prec(expr, Prec::LOWEST)?;
          raw.push('}');
        }
      }
    }
    raw.push('`');
    self.out.write_str(&raw)?;
    Ok(())
  }

  pub(crate) fn emit_type(&mut self, ty: &Node<TypeExpr>) -> EmitResult {
    with_node_context(ty.loc, || {
      (self.emit_type)(&mut self.out, ty).map_err(EmitError::from)
    })
  }

  fn emit_wrapped(&mut self, expr: &Node<Expr>, min_prec: Prec) -> EmitResult {
    write!(self.out, "(")?;
    self.emit_expr_with_min_prec(expr, min_prec)?;
    write!(self.out, ")")?;
    Ok(())
  }
}

pub fn emit_expr_with_options<W, F>(
  out: &mut W,
  expr: &Node<Expr>,
  emit_type: F,
  opts: EmitOptions,
) -> EmitResult
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  let mut emitter = ExprEmitter::new(out, emit_type, opts);
  emitter.emit_expr(expr)
}

pub fn emit_expr<W, F>(out: &mut W, expr: &Node<Expr>, emit_type: F) -> EmitResult
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  emit_expr_with_options(out, expr, emit_type, EmitOptions::canonical())
}

pub fn emit_expr_with_emitter(out: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  struct EmitterWriteAdapter<'a> {
    emitter: &'a mut Emitter,
  }

  impl fmt::Write for EmitterWriteAdapter<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
      self.emitter.write_str(s);
      Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
      let mut buf = [0u8; 4];
      let encoded = c.encode_utf8(&mut buf);
      self.emitter.write_str(encoded);
      Ok(())
    }
  }

  let opts = out.options();
  let mut adapter = EmitterWriteAdapter { emitter: out };
  let mut emit_type =
    |out: &mut EmitterWriteAdapter<'_>, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
  emit_expr_with_options(&mut adapter, expr, &mut emit_type, opts)
}

fn unary_operator_text(op: OperatorName) -> Result<&'static str, EmitError> {
  match op {
    OperatorName::Await => Ok("await "),
    OperatorName::BitwiseNot => Ok("~"),
    OperatorName::Delete => Ok("delete "),
    OperatorName::LogicalNot => Ok("!"),
    OperatorName::New => Ok("new "),
    OperatorName::PrefixDecrement => Ok("--"),
    OperatorName::PrefixIncrement => Ok("++"),
    OperatorName::Typeof => Ok("typeof "),
    OperatorName::UnaryNegation => Ok("-"),
    OperatorName::UnaryPlus => Ok("+"),
    OperatorName::Void => Ok("void "),
    OperatorName::Yield => Ok("yield "),
    OperatorName::YieldDelegated => Ok("yield* "),
    _ => Err(EmitError::unsupported(
      "operator not supported in unary emitter",
    )),
  }
}

fn binary_operator_text(op: OperatorName) -> Result<&'static str, EmitError> {
  match op {
    OperatorName::Addition => Ok("+"),
    OperatorName::Subtraction => Ok("-"),
    OperatorName::Multiplication => Ok("*"),
    OperatorName::Division => Ok("/"),
    OperatorName::Remainder => Ok("%"),
    OperatorName::Exponentiation => Ok("**"),
    OperatorName::LessThan => Ok("<"),
    OperatorName::LessThanOrEqual => Ok("<="),
    OperatorName::GreaterThan => Ok(">"),
    OperatorName::GreaterThanOrEqual => Ok(">="),
    OperatorName::Equality => Ok("=="),
    OperatorName::Inequality => Ok("!="),
    OperatorName::StrictEquality => Ok("==="),
    OperatorName::StrictInequality => Ok("!=="),
    OperatorName::BitwiseAnd => Ok("&"),
    OperatorName::BitwiseOr => Ok("|"),
    OperatorName::BitwiseXor => Ok("^"),
    OperatorName::BitwiseLeftShift => Ok("<<"),
    OperatorName::BitwiseRightShift => Ok(">>"),
    OperatorName::BitwiseUnsignedRightShift => Ok(">>>"),
    OperatorName::LogicalAnd => Ok("&&"),
    OperatorName::LogicalOr => Ok("||"),
    OperatorName::NullishCoalescing => Ok("??"),
    OperatorName::In => Ok("in"),
    OperatorName::Instanceof => Ok("instanceof"),
    OperatorName::Comma => Ok(","),
    OperatorName::Assignment => Ok("="),
    OperatorName::AssignmentAddition => Ok("+="),
    OperatorName::AssignmentBitwiseAnd => Ok("&="),
    OperatorName::AssignmentBitwiseLeftShift => Ok("<<="),
    OperatorName::AssignmentBitwiseOr => Ok("|="),
    OperatorName::AssignmentBitwiseRightShift => Ok(">>="),
    OperatorName::AssignmentBitwiseUnsignedRightShift => Ok(">>>="),
    OperatorName::AssignmentBitwiseXor => Ok("^="),
    OperatorName::AssignmentDivision => Ok("/="),
    OperatorName::AssignmentExponentiation => Ok("**="),
    OperatorName::AssignmentLogicalAnd => Ok("&&="),
    OperatorName::AssignmentLogicalOr => Ok("||="),
    OperatorName::AssignmentMultiplication => Ok("*="),
    OperatorName::AssignmentNullishCoalescing => Ok("??="),
    OperatorName::AssignmentRemainder => Ok("%="),
    OperatorName::AssignmentSubtraction => Ok("-="),
    // Operators that should be handled in dedicated branches instead of generic binary printing.
    OperatorName::Call
    | OperatorName::ComputedMemberAccess
    | OperatorName::Conditional
    | OperatorName::ConditionalAlternate
    | OperatorName::MemberAccess
    | OperatorName::OptionalChainingCall
    | OperatorName::OptionalChainingComputedMemberAccess
    | OperatorName::OptionalChainingMemberAccess
    | OperatorName::Await
    | OperatorName::BitwiseNot
    | OperatorName::Delete
    | OperatorName::LogicalNot
    | OperatorName::New
    | OperatorName::PrefixDecrement
    | OperatorName::PrefixIncrement
    | OperatorName::Typeof
    | OperatorName::UnaryNegation
    | OperatorName::UnaryPlus
    | OperatorName::Void
    | OperatorName::Yield
    | OperatorName::YieldDelegated
    | OperatorName::PostfixDecrement
    | OperatorName::PostfixIncrement => Err(EmitError::unsupported(
      "operator not supported in binary emitter",
    )),
  }
}

fn is_comma_expression(expr: &Expr) -> bool {
  matches!(expr, Expr::Binary(binary) if binary.stx.operator == OperatorName::Comma)
}

fn expr_starts_with_brace(expr: &Node<Expr>) -> bool {
  match expr.stx.as_ref() {
    Expr::LitObj(_) | Expr::ObjPat(_) => true,
    Expr::Binary(binary) => expr_starts_with_brace(&binary.stx.left),
    Expr::Call(call) => expr_starts_with_brace(&call.stx.callee),
    Expr::Member(member) => expr_starts_with_brace(&member.stx.left),
    Expr::ComputedMember(member) => expr_starts_with_brace(&member.stx.object),
    Expr::TaggedTemplate(tagged) => expr_starts_with_brace(&tagged.stx.function),
    Expr::NonNullAssertion(expr) => expr_starts_with_brace(&expr.stx.expression),
    Expr::TypeAssertion(assertion) => expr_starts_with_brace(&assertion.stx.expression),
    Expr::SatisfiesExpr(satisfies) => expr_starts_with_brace(&satisfies.stx.expression),
    Expr::UnaryPostfix(unary) => expr_starts_with_brace(&unary.stx.argument),
    Expr::Cond(cond) => expr_starts_with_brace(&cond.stx.test),
    _ => false,
  }
}

fn is_nullish(expr: &Node<Expr>) -> bool {
  matches!(
    expr.stx.as_ref(),
    Expr::Binary(binary) if binary.stx.operator == OperatorName::NullishCoalescing
  )
}

fn is_logical_and_or(expr: &Node<Expr>) -> bool {
  matches!(
    expr.stx.as_ref(),
    Expr::Binary(binary)
      if binary.stx.operator == OperatorName::LogicalAnd
        || binary.stx.operator == OperatorName::LogicalOr
  )
}

fn requires_trailing_dot(rendered: &str) -> bool {
  let mut bytes = rendered.as_bytes();
  if bytes.starts_with(b"-") {
    bytes = &bytes[1..];
  }
  bytes.iter().all(|b| b.is_ascii_digit())
}

#[cfg(test)]
mod tests {
  use super::*;
  use parse_js::ast::expr::lit::LitNumExpr;
  use parse_js::ast::expr::NonNullAssertionExpr;
  use parse_js::ast::expr::SatisfiesExpr;
  use parse_js::ast::expr::TypeAssertionExpr;
  use parse_js::ast::type_expr::{TypeEntityName, TypeReference};
  use parse_js::loc::Loc;
  use parse_js::num::JsNumber;

  fn node<T: derive_visitor::Drive + derive_visitor::DriveMut>(stx: T) -> Node<T> {
    Node::new(Loc(0, 0), stx)
  }

  fn type_ref(name: &str) -> Node<TypeExpr> {
    node(TypeExpr::TypeReference(node(TypeReference {
      name: TypeEntityName::Identifier(name.to_string()),
      type_arguments: None,
    })))
  }

  fn id(name: &str) -> Node<Expr> {
    node(Expr::Id(node(IdExpr {
      name: name.to_string(),
    })))
  }

  fn binary_add(left: Node<Expr>, right: Node<Expr>) -> Node<Expr> {
    node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Addition,
      left,
      right,
    })))
  }

  fn lit_num(value: f64) -> Node<Expr> {
    node(Expr::LitNum(node(LitNumExpr {
      value: JsNumber(value),
    })))
  }

  fn member(left: Node<Expr>, right: &str, optional_chaining: bool) -> Node<Expr> {
    node(Expr::Member(node(MemberExpr {
      optional_chaining,
      left,
      right: right.to_string(),
    })))
  }

  fn assert_emit(expr: Node<Expr>, expected: &str) {
    let mut out = String::new();
    let mut emit_type = |out: &mut String, ty: &Node<TypeExpr>| match ty.stx.as_ref() {
      TypeExpr::TypeReference(reference) => match &reference.stx.name {
        TypeEntityName::Identifier(name) => {
          out.push_str(name);
          Ok(())
        }
        _ => Err(fmt::Error),
      },
      _ => Err(fmt::Error),
    };

    emit_expr(&mut out, &expr, &mut emit_type).unwrap();
    assert_eq!(out, expected);
  }

  #[test]
  fn emits_member_after_integer_literal_with_extra_dot() {
    assert_emit(member(lit_num(1.0), "toString", false), "1..toString");
  }

  #[test]
  fn emits_member_after_decimal_literal_without_extra_dot() {
    assert_emit(member(lit_num(1.2), "toString", false), "1.2.toString");
  }

  #[test]
  fn emits_optional_chaining_member_after_integer_literal_without_extra_dot() {
    assert_emit(member(lit_num(1.0), "toString", true), "1?.toString");
  }

  #[test]
  fn emits_type_assertion_const() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(id("x")),
      type_annotation: None,
      const_assertion: true,
    });
    let expr = node(Expr::TypeAssertion(assertion));

    assert_emit(expr, "x as const");
  }

  #[test]
  fn emits_type_assertion_type() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(id("x")),
      type_annotation: Some(type_ref("T")),
      const_assertion: false,
    });
    let expr = node(Expr::TypeAssertion(assertion));

    assert_emit(expr, "x as T");
  }

  #[test]
  fn emits_satisfies_expression() {
    let satisfies = node(SatisfiesExpr {
      expression: Box::new(id("x")),
      type_annotation: type_ref("T"),
    });
    let expr = node(Expr::SatisfiesExpr(satisfies));

    assert_emit(expr, "x satisfies T");
  }

  #[test]
  fn wraps_type_assertion_operand_when_needed() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(binary_add(id("a"), id("b"))),
      type_annotation: Some(type_ref("T")),
      const_assertion: false,
    });
    let expr = node(Expr::TypeAssertion(assertion));

    assert_emit(expr, "(a + b) as T");
  }

  #[test]
  fn emits_non_null_with_parentheses_for_low_precedence_operand() {
    let non_null = node(NonNullAssertionExpr {
      expression: Box::new(binary_add(id("a"), id("b"))),
    });
    let expr = node(Expr::NonNullAssertion(non_null));

    let mut out = String::new();
    let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
    emit_expr(&mut out, &expr, &mut emit_type).unwrap();
    assert_eq!(out, "(a + b)!");
  }

  #[test]
  fn type_assertion_inside_call_argument() {
    let arg = node(CallArg {
      spread: false,
      value: node(Expr::TypeAssertion(node(TypeAssertionExpr {
        expression: Box::new(id("x")),
        type_annotation: Some(type_ref("T")),
        const_assertion: false,
      }))),
    });
    let call = node(Expr::Call(node(CallExpr {
      optional_chaining: false,
      callee: id("f"),
      arguments: vec![arg],
    })));

    assert_emit(call, "f(x as T)");
  }

  #[test]
  fn type_assertion_operand_in_binary_respects_grouping() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(binary_add(id("a"), id("b"))),
      type_annotation: Some(type_ref("T")),
      const_assertion: false,
    });
    let outer = node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Addition,
      left: node(Expr::TypeAssertion(assertion)),
      right: id("c"),
    })));

    assert_emit(outer, "(a + b) as T + c");
  }
}
