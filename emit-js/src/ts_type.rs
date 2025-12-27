use crate::{EmitMode, EmitOptions, EmitResult, Emitter};
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::ImportExpr;
use parse_js::ast::node::Node;
use parse_js::ast::ts_stmt::InterfaceDecl;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::ast::type_expr::*;
use std::fmt;

/// Precedence levels for TypeScript type expressions. Higher variants bind more tightly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum TypePrec {
  ArrowOrConditional,
  Union,
  Intersection,
  Unary,
  Postfix,
  Primary,
}

/// Emit a TypeScript type expression using an [`Emitter`].
pub fn emit_ts_type(em: &mut Emitter, expr: &Node<TypeExpr>) -> EmitResult {
  TypeEmitter::new(em).emit_type_expr(expr)
}

/// Convenience helper returning the emitted representation as a [`String`].
pub fn ts_type_to_string(expr: &Node<TypeExpr>, mode: EmitMode) -> String {
  let mut em = Emitter::new(EmitOptions::from(mode));
  emit_ts_type(&mut em, expr).expect("type emission should not fail");
  String::from_utf8(em.into_bytes()).expect("Emitter output is UTF-8")
}

/// Compatibility wrapper emitting with canonical formatting into a [`fmt::Write`].
pub fn emit_type_expr<W: fmt::Write>(out: &mut W, expr: &Node<TypeExpr>) -> fmt::Result {
  out.write_str(&ts_type_to_string(expr, EmitMode::Canonical))
}

pub fn emit_type_alias_decl<W: fmt::Write>(out: &mut W, decl: &TypeAliasDecl) -> fmt::Result {
  write_with_emitter(out, EmitMode::Canonical, |em| em.emit_type_alias_decl(decl))
}

pub fn emit_type_members<W: fmt::Write>(out: &mut W, members: &[Node<TypeMember>]) -> fmt::Result {
  write_with_emitter(out, EmitMode::Canonical, |em| em.emit_type_members(members))
}

pub fn emit_interface_decl<W: fmt::Write>(out: &mut W, decl: &InterfaceDecl) -> fmt::Result {
  write_with_emitter(out, EmitMode::Canonical, |em| em.emit_interface_decl(decl))
}

pub(crate) fn emit_type_parameters(out: &mut String, params: Option<&[Node<TypeParameter>]>) {
  let mut emitter = Emitter::new(EmitOptions::canonical());
  {
    let mut ty_emitter = TypeEmitter::new(&mut emitter);
    ty_emitter
      .emit_type_parameters(params)
      .expect("type parameter emission should not fail");
  }
  out.push_str(&String::from_utf8(emitter.into_bytes()).expect("Emitter output is UTF-8"));
}

fn write_with_emitter<W: fmt::Write>(
  out: &mut W,
  mode: EmitMode,
  mut f: impl FnMut(&mut TypeEmitter<'_>) -> EmitResult,
) -> fmt::Result {
  let mut emitter = Emitter::new(EmitOptions::from(mode));
  {
    let mut ty_emitter = TypeEmitter::new(&mut emitter);
    f(&mut ty_emitter).map_err(|_| fmt::Error)?;
  }
  out.write_str(&String::from_utf8(emitter.into_bytes()).expect("Emitter output is UTF-8"))
}

struct TypeEmitter<'a> {
  em: &'a mut Emitter,
}

impl<'a> TypeEmitter<'a> {
  fn new(em: &'a mut Emitter) -> Self {
    TypeEmitter { em }
  }

  fn is_canonical(&self) -> bool {
    !self.em.minify()
  }

  fn space(&mut self) {
    if self.is_canonical() {
      self.em.write_space();
    }
  }

  fn emit_type_expr(&mut self, expr: &Node<TypeExpr>) -> EmitResult {
    self.emit_type_expr_with_prec(expr, TypePrec::ArrowOrConditional)
  }

  fn emit_type_alias_decl(&mut self, decl: &TypeAliasDecl) -> EmitResult {
    if decl.export {
      self.em.write_keyword("export");
      self.space();
    }
    if decl.declare {
      self.em.write_keyword("declare");
      self.space();
    }
    self.em.write_keyword("type");
    self.space();
    self.em.write_identifier(&decl.name);
    self.emit_type_parameters(decl.type_parameters.as_deref())?;
    self.space();
    self.em.write_punct("=");
    self.space();
    self.emit_type_expr(&decl.type_expr)?;
    self.em.write_punct(";");
    Ok(())
  }

  fn emit_interface_decl(&mut self, decl: &InterfaceDecl) -> EmitResult {
    if decl.export {
      self.em.write_keyword("export");
      self.space();
    }
    if decl.declare {
      self.em.write_keyword("declare");
      self.space();
    }
    self.em.write_keyword("interface");
    self.space();
    self.em.write_identifier(&decl.name);
    self.emit_type_parameters(decl.type_parameters.as_deref())?;
    if !decl.extends.is_empty() {
      self.space();
      self.em.write_keyword("extends");
      self.space();
      for (i, ty) in decl.extends.iter().enumerate() {
        if i > 0 {
          self.em.write_punct(",");
          self.space();
        }
        self.emit_type_expr_with_prec(ty, TypePrec::ArrowOrConditional)?;
      }
    }
    self.space();
    self.em.write_punct("{");
    self.emit_type_members(&decl.members)?;
    self.em.write_punct("}");
    Ok(())
  }

  fn emit_type_members(&mut self, members: &[Node<TypeMember>]) -> EmitResult {
    for (i, member) in members.iter().enumerate() {
      if i > 0 && self.is_canonical() {
        self.em.write_space();
      }
      self.emit_type_member(member)?;
      self.em.write_punct(";");
    }
    Ok(())
  }

  fn emit_type_expr_with_prec(
    &mut self,
    expr: &Node<TypeExpr>,
    parent_prec: TypePrec,
  ) -> EmitResult {
    if let TypeExpr::ParenthesizedType(inner) = expr.stx.as_ref() {
      self.em.write_punct("(");
      self.emit_type_expr_with_prec(&inner.stx.type_expr, TypePrec::ArrowOrConditional)?;
      self.em.write_punct(")");
      return Ok(());
    }

    let self_prec = type_prec(expr.stx.as_ref());
    let needs_paren = self_prec < parent_prec;

    if needs_paren {
      self.em.write_punct("(");
    }
    self.emit_type_expr_no_paren(expr)?;
    if needs_paren {
      self.em.write_punct(")");
    }

    Ok(())
  }

  fn emit_type_expr_no_paren(&mut self, expr: &Node<TypeExpr>) -> EmitResult {
    match expr.stx.as_ref() {
      TypeExpr::Any(_) => self.em.write_keyword("any"),
      TypeExpr::Unknown(_) => self.em.write_keyword("unknown"),
      TypeExpr::Never(_) => self.em.write_keyword("never"),
      TypeExpr::Void(_) => self.em.write_keyword("void"),
      TypeExpr::String(_) => self.em.write_keyword("string"),
      TypeExpr::Number(_) => self.em.write_keyword("number"),
      TypeExpr::Boolean(_) => self.em.write_keyword("boolean"),
      TypeExpr::BigInt(_) => self.em.write_keyword("bigint"),
      TypeExpr::Symbol(_) => self.em.write_keyword("symbol"),
      TypeExpr::UniqueSymbol(_) => {
        self.em.write_keyword("unique");
        self.space();
        self.em.write_keyword("symbol");
      }
      TypeExpr::Object(_) => self.em.write_keyword("object"),
      TypeExpr::Null(_) => self.em.write_keyword("null"),
      TypeExpr::Undefined(_) => self.em.write_keyword("undefined"),

      TypeExpr::TypeReference(reference) => self.emit_type_reference(reference)?,
      TypeExpr::LiteralType(lit) => self.emit_type_literal(lit)?,
      TypeExpr::ArrayType(array) => self.emit_array_type(array)?,
      TypeExpr::TupleType(tuple) => self.emit_tuple_type(tuple)?,
      TypeExpr::UnionType(union) => self.emit_union_type(union)?,
      TypeExpr::IntersectionType(intersection) => self.emit_intersection_type(intersection)?,
      TypeExpr::FunctionType(func) => self.emit_function_type(func)?,
      TypeExpr::ConstructorType(cons) => self.emit_constructor_type(cons)?,
      TypeExpr::ObjectType(obj) => self.emit_object_type(obj)?,
      TypeExpr::TypeQuery(query) => self.emit_type_query(query)?,
      TypeExpr::KeyOfType(keyof) => self.emit_keyof(keyof)?,
      TypeExpr::IndexedAccessType(indexed) => self.emit_indexed_access(indexed)?,
      TypeExpr::ConditionalType(cond) => self.emit_conditional_type(cond)?,
      TypeExpr::InferType(infer_ty) => self.emit_infer(infer_ty)?,
      TypeExpr::MappedType(mapped) => self.emit_mapped_type_expr(mapped)?,
      TypeExpr::TemplateLiteralType(template) => self.emit_template_literal(template)?,
      TypeExpr::TypePredicate(pred) => self.emit_type_predicate(pred)?,
      TypeExpr::ThisType(_) => self.em.write_keyword("this"),
      TypeExpr::ImportType(import_type) => self.emit_import_type(import_type)?,

      TypeExpr::ParenthesizedType(_) => unreachable!("handled earlier"),
    }
    Ok(())
  }

  fn emit_type_reference(&mut self, reference: &Node<TypeReference>) -> EmitResult {
    let reference = reference.stx.as_ref();
    self.emit_type_entity_name(&reference.name)?;
    self.emit_type_arguments(reference.type_arguments.as_deref())
  }

  fn emit_type_literal(&mut self, lit: &Node<TypeLiteral>) -> EmitResult {
    match lit.stx.as_ref() {
      TypeLiteral::String(value) => self.emit_string_literal(value),
      TypeLiteral::Number(value) => self.em.write_number(value),
      TypeLiteral::BigInt(value) => self.em.write_bigint(value),
      TypeLiteral::Boolean(value) => self.em.write_keyword(if *value { "true" } else { "false" }),
      TypeLiteral::Null => self.em.write_keyword("null"),
    }
    Ok(())
  }

  fn emit_array_type(&mut self, array: &Node<TypeArray>) -> EmitResult {
    let array = array.stx.as_ref();
    if array.readonly {
      self.em.write_keyword("readonly");
      self.space();
    }
    self.emit_type_expr_with_prec(&array.element_type, TypePrec::Postfix)?;
    self.em.write_punct("[]");
    Ok(())
  }

  fn emit_tuple_type(&mut self, tuple: &Node<TypeTuple>) -> EmitResult {
    let tuple = tuple.stx.as_ref();
    if tuple.readonly {
      self.em.write_keyword("readonly");
      self.space();
    }
    self.em.write_punct("[");
    for (i, elem) in tuple.elements.iter().enumerate() {
      if i > 0 {
        self.em.write_punct(",");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_tuple_element(elem)?;
    }
    self.em.write_punct("]");
    Ok(())
  }

  fn emit_tuple_element(&mut self, elem: &Node<TypeTupleElement>) -> EmitResult {
    let TypeTupleElement {
      label,
      optional,
      rest,
      type_expr,
    } = elem.stx.as_ref();

    if *rest {
      self.em.write_punct("...");
    }

    match label {
      Some(name) => {
        self.em.write_identifier(name);
        if *optional {
          self.em.write_punct("?");
        }
        self.em.write_punct(":");
        self.space();
        self.emit_type_expr_with_prec(type_expr, TypePrec::ArrowOrConditional)?;
      }
      None => {
        self.emit_type_expr_with_prec(type_expr, TypePrec::ArrowOrConditional)?;
        if *optional {
          self.em.write_punct("?");
        }
      }
    }

    Ok(())
  }

  fn emit_union_type(&mut self, union: &Node<TypeUnion>) -> EmitResult {
    for (i, ty) in union.stx.types.iter().enumerate() {
      if i > 0 {
        if self.is_canonical() {
          self.em.write_space();
        }
        self.em.write_punct("|");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_type_expr_with_prec(ty, TypePrec::Union)?;
    }
    Ok(())
  }

  fn emit_intersection_type(&mut self, intersection: &Node<TypeIntersection>) -> EmitResult {
    for (i, ty) in intersection.stx.types.iter().enumerate() {
      if i > 0 {
        if self.is_canonical() {
          self.em.write_space();
        }
        self.em.write_punct("&");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_type_expr_with_prec(ty, TypePrec::Intersection)?;
    }
    Ok(())
  }

  fn emit_function_type(&mut self, func: &Node<TypeFunction>) -> EmitResult {
    let func = func.stx.as_ref();
    self.emit_type_parameters(func.type_parameters.as_deref())?;
    self.em.write_punct("(");
    for (i, param) in func.parameters.iter().enumerate() {
      if i > 0 {
        self.em.write_punct(",");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_function_param(param)?;
    }
    self.em.write_punct(")");
    self.space();
    self.em.write_punct("=>");
    self.space();
    self.emit_type_expr_with_prec(&func.return_type, TypePrec::ArrowOrConditional)
  }

  fn emit_constructor_type(&mut self, cons: &Node<TypeConstructor>) -> EmitResult {
    let cons = cons.stx.as_ref();
    self.em.write_keyword("new");
    self.space();
    self.emit_type_parameters(cons.type_parameters.as_deref())?;
    self.em.write_punct("(");
    for (i, param) in cons.parameters.iter().enumerate() {
      if i > 0 {
        self.em.write_punct(",");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_function_param(param)?;
    }
    self.em.write_punct(")");
    self.space();
    self.em.write_punct("=>");
    self.space();
    self.emit_type_expr_with_prec(&cons.return_type, TypePrec::ArrowOrConditional)
  }

  fn emit_function_param(&mut self, param: &Node<TypeFunctionParameter>) -> EmitResult {
    let TypeFunctionParameter {
      name,
      optional,
      rest,
      type_expr,
    } = param.stx.as_ref();

    if *rest {
      self.em.write_punct("...");
    }

    if let Some(name) = name {
      self.em.write_identifier(name);
      if *optional {
        self.em.write_punct("?");
      }
      self.em.write_punct(":");
      self.space();
      self.emit_type_expr_with_prec(type_expr, TypePrec::ArrowOrConditional)?;
    } else {
      self.emit_type_expr_with_prec(type_expr, TypePrec::ArrowOrConditional)?;
      if *optional {
        self.em.write_punct("?");
      }
    }

    Ok(())
  }

  fn emit_object_type(&mut self, obj: &Node<TypeObjectLiteral>) -> EmitResult {
    let obj = obj.stx.as_ref();
    self.em.write_punct("{");
    self.emit_type_members(&obj.members)?;
    self.em.write_punct("}");
    Ok(())
  }

  fn emit_type_member(&mut self, member: &Node<TypeMember>) -> EmitResult {
    match member.stx.as_ref() {
      TypeMember::Property(prop) => self.emit_property_signature(prop),
      TypeMember::Method(method) => self.emit_method_signature(method),
      TypeMember::Constructor(cons) => self.emit_construct_signature(cons),
      TypeMember::CallSignature(call) => self.emit_call_signature(call),
      TypeMember::IndexSignature(index) => self.emit_index_signature(index),
      TypeMember::GetAccessor(get) => self.emit_get_accessor(get),
      TypeMember::SetAccessor(set) => self.emit_set_accessor(set),
      TypeMember::MappedProperty(mapped) => self.emit_mapped_signature(mapped.stx.as_ref()),
    }
  }

  fn emit_property_signature(&mut self, prop: &Node<TypePropertySignature>) -> EmitResult {
    let prop = prop.stx.as_ref();
    if prop.readonly {
      self.em.write_keyword("readonly");
      self.space();
    }
    self.emit_property_key(&prop.key)?;
    if prop.optional {
      self.em.write_punct("?");
    }
    if let Some(ty) = &prop.type_annotation {
      self.em.write_punct(":");
      self.space();
      self.emit_type_expr_with_prec(ty, TypePrec::ArrowOrConditional)?;
    }
    Ok(())
  }

  fn emit_method_signature(&mut self, method: &Node<TypeMethodSignature>) -> EmitResult {
    let method = method.stx.as_ref();
    self.emit_property_key(&method.key)?;
    if method.optional {
      self.em.write_punct("?");
    }
    self.emit_type_parameters(method.type_parameters.as_deref())?;
    self.em.write_punct("(");
    for (i, param) in method.parameters.iter().enumerate() {
      if i > 0 {
        self.em.write_punct(",");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_function_param(param)?;
    }
    self.em.write_punct(")");
    if let Some(ret) = &method.return_type {
      self.em.write_punct(":");
      self.space();
      self.emit_type_expr_with_prec(ret, TypePrec::ArrowOrConditional)?;
    }
    Ok(())
  }

  fn emit_construct_signature(&mut self, cons: &Node<TypeConstructSignature>) -> EmitResult {
    let cons = cons.stx.as_ref();
    self.em.write_keyword("new");
    self.space();
    self.emit_type_parameters(cons.type_parameters.as_deref())?;
    self.em.write_punct("(");
    for (i, param) in cons.parameters.iter().enumerate() {
      if i > 0 {
        self.em.write_punct(",");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_function_param(param)?;
    }
    self.em.write_punct(")");
    if let Some(ret) = &cons.return_type {
      self.em.write_punct(":");
      self.space();
      self.emit_type_expr_with_prec(ret, TypePrec::ArrowOrConditional)?;
    }
    Ok(())
  }

  fn emit_call_signature(&mut self, call: &Node<TypeCallSignature>) -> EmitResult {
    let call = call.stx.as_ref();
    self.emit_type_parameters(call.type_parameters.as_deref())?;
    self.em.write_punct("(");
    for (i, param) in call.parameters.iter().enumerate() {
      if i > 0 {
        self.em.write_punct(",");
        if self.is_canonical() {
          self.em.write_space();
        }
      }
      self.emit_function_param(param)?;
    }
    self.em.write_punct(")");
    if let Some(ret) = &call.return_type {
      self.em.write_punct(":");
      self.space();
      self.emit_type_expr_with_prec(ret, TypePrec::ArrowOrConditional)?;
    }
    Ok(())
  }

  fn emit_index_signature(&mut self, index: &Node<TypeIndexSignature>) -> EmitResult {
    let index = index.stx.as_ref();
    if index.readonly {
      self.em.write_keyword("readonly");
      self.space();
    }
    self.em.write_punct("[");
    self.em.write_identifier(&index.parameter_name);
    self.em.write_punct(":");
    self.space();
    self.emit_type_expr_with_prec(&index.parameter_type, TypePrec::ArrowOrConditional)?;
    self.em.write_punct("]");
    self.em.write_punct(":");
    self.space();
    self.emit_type_expr_with_prec(&index.type_annotation, TypePrec::ArrowOrConditional)
  }

  fn emit_get_accessor(&mut self, get: &Node<TypeGetAccessor>) -> EmitResult {
    let get = get.stx.as_ref();
    self.em.write_keyword("get");
    self.space();
    self.emit_property_key(&get.key)?;
    self.em.write_punct("(");
    self.em.write_punct(")");
    self.em.write_punct(":");
    self.space();
    if let Some(ret) = &get.return_type {
      self.emit_type_expr_with_prec(ret, TypePrec::ArrowOrConditional)?;
    } else {
      self.em.write_keyword("void");
    }
    Ok(())
  }

  fn emit_set_accessor(&mut self, set: &Node<TypeSetAccessor>) -> EmitResult {
    let set = set.stx.as_ref();
    self.em.write_keyword("set");
    self.space();
    self.emit_property_key(&set.key)?;
    self.em.write_punct("(");
    self.emit_function_param(&set.parameter)?;
    self.em.write_punct(")");
    Ok(())
  }

  fn emit_property_key(&mut self, key: &TypePropertyKey) -> EmitResult {
    match key {
      TypePropertyKey::Identifier(name) => self.em.write_identifier(name),
      TypePropertyKey::String(value) => self.emit_string_literal(value),
      TypePropertyKey::Number(value) => self.em.write_number(value),
      TypePropertyKey::Computed(expr) => {
        self.em.write_punct("[");
        self.emit_expr(expr)?;
        self.em.write_punct("]");
      }
    }
    Ok(())
  }

  fn emit_type_parameters(&mut self, params: Option<&[Node<TypeParameter>]>) -> EmitResult {
    if let Some(params) = params {
      if params.is_empty() {
        return Ok(());
      }
      self.em.write_punct("<");
      for (i, param) in params.iter().enumerate() {
        if i > 0 {
          self.em.write_punct(",");
          if self.is_canonical() {
            self.em.write_space();
          }
        }
        self.emit_type_parameter(param)?;
      }
      self.em.write_punct(">");
    }
    Ok(())
  }

  fn emit_type_parameter(&mut self, param: &Node<TypeParameter>) -> EmitResult {
    let TypeParameter {
      const_,
      variance,
      name,
      constraint,
      default,
    } = param.stx.as_ref();

    if *const_ {
      self.em.write_keyword("const");
      self.space();
    }
    if let Some(variance) = variance {
      match variance {
        Variance::In => {
          self.em.write_keyword("in");
          self.space();
        }
        Variance::Out => {
          self.em.write_keyword("out");
          self.space();
        }
        Variance::InOut => {
          self.em.write_keyword("in");
          self.space();
          self.em.write_keyword("out");
          self.space();
        }
      }
    }
    self.em.write_identifier(name);
    if let Some(constraint) = constraint {
      self.space();
      self.em.write_keyword("extends");
      self.space();
      self.emit_type_expr_with_prec(constraint, TypePrec::ArrowOrConditional)?;
    }
    if let Some(default) = default {
      self.space();
      self.em.write_punct("=");
      self.space();
      self.emit_type_expr_with_prec(default, TypePrec::ArrowOrConditional)?;
    }
    Ok(())
  }

  fn emit_type_query(&mut self, query: &Node<TypeQuery>) -> EmitResult {
    let query = query.stx.as_ref();
    self.em.write_keyword("typeof");
    self.space();
    self.emit_type_entity_name(&query.expr_name)
  }

  fn emit_keyof(&mut self, keyof: &Node<TypeKeyOf>) -> EmitResult {
    let keyof = keyof.stx.as_ref();
    self.em.write_keyword("keyof");
    self.space();
    self.emit_type_expr_with_prec(&keyof.type_expr, TypePrec::Unary)
  }

  fn emit_indexed_access(&mut self, indexed: &Node<TypeIndexedAccess>) -> EmitResult {
    let indexed = indexed.stx.as_ref();
    self.emit_type_expr_with_prec(&indexed.object_type, TypePrec::Postfix)?;
    self.em.write_punct("[");
    self.emit_type_expr_with_prec(&indexed.index_type, TypePrec::ArrowOrConditional)?;
    self.em.write_punct("]");
    Ok(())
  }

  fn emit_conditional_type(&mut self, cond: &Node<TypeConditional>) -> EmitResult {
    let cond = cond.stx.as_ref();
    self.emit_type_expr_with_prec(&cond.check_type, TypePrec::Union)?;
    self.space();
    self.em.write_keyword("extends");
    self.space();
    self.emit_type_expr_with_prec(&cond.extends_type, TypePrec::Union)?;
    self.space();
    self.em.write_punct("?");
    if self.is_canonical() {
      self.em.write_space();
    }
    self.emit_type_expr_with_prec(&cond.true_type, TypePrec::ArrowOrConditional)?;
    self.space();
    self.em.write_punct(":");
    self.space();
    self.emit_type_expr_with_prec(&cond.false_type, TypePrec::ArrowOrConditional)
  }

  fn emit_infer(&mut self, infer_ty: &Node<TypeInfer>) -> EmitResult {
    let infer_ty = infer_ty.stx.as_ref();
    self.em.write_keyword("infer");
    self.space();
    self.em.write_identifier(&infer_ty.type_parameter);
    if let Some(constraint) = &infer_ty.constraint {
      self.space();
      self.em.write_keyword("extends");
      self.space();
      self.emit_type_expr_with_prec(constraint, TypePrec::ArrowOrConditional)?;
    }
    Ok(())
  }

  fn emit_mapped_type_expr(&mut self, mapped: &Node<TypeMapped>) -> EmitResult {
    self.em.write_punct("{");
    if self.is_canonical() {
      self.em.write_space();
    }
    self.emit_mapped_signature(mapped.stx.as_ref())?;
    if self.is_canonical() {
      self.em.write_space();
    }
    self.em.write_punct("}");
    Ok(())
  }

  fn emit_mapped_signature(&mut self, mapped: &TypeMapped) -> EmitResult {
    if let Some(modifier) = mapped.readonly_modifier {
      self.emit_mapped_modifier(modifier, "readonly", true);
    }
    self.em.write_punct("[");
    self.em.write_identifier(&mapped.type_parameter);
    self.space();
    self.em.write_keyword("in");
    self.space();
    self.emit_type_expr_with_prec(&mapped.constraint, TypePrec::ArrowOrConditional)?;
    if let Some(name_type) = &mapped.name_type {
      self.space();
      self.em.write_keyword("as");
      self.space();
      self.emit_type_expr_with_prec(name_type, TypePrec::ArrowOrConditional)?;
    }
    self.em.write_punct("]");
    if let Some(modifier) = mapped.optional_modifier {
      self.emit_mapped_modifier(modifier, "?", false);
    }
    self.em.write_punct(":");
    self.space();
    self.emit_type_expr_with_prec(&mapped.type_expr, TypePrec::ArrowOrConditional)
  }

  fn emit_mapped_modifier(
    &mut self,
    modifier: MappedTypeModifier,
    token: &str,
    trailing_space: bool,
  ) {
    match modifier {
      MappedTypeModifier::Plus => self.em.write_punct("+"),
      MappedTypeModifier::Minus => self.em.write_punct("-"),
      MappedTypeModifier::None => {}
    }
    if token.chars().all(|c| c.is_alphanumeric() || c == '_') {
      self.em.write_keyword(token);
    } else {
      self.em.write_punct(token);
    }
    if trailing_space && self.is_canonical() {
      self.em.write_space();
    }
  }

  fn emit_template_literal(&mut self, template: &Node<TypeTemplateLiteral>) -> EmitResult {
    let template = template.stx.as_ref();
    self.em.write_str(&template.head);
    for span in &template.spans {
      self.emit_type_expr_with_prec(&span.stx.type_expr, TypePrec::ArrowOrConditional)?;
      self.em.write_punct("}");
      self.em.write_str(&span.stx.literal);
    }
    Ok(())
  }

  fn emit_type_predicate(&mut self, pred: &Node<TypePredicate>) -> EmitResult {
    let pred = pred.stx.as_ref();
    if pred.asserts {
      self.em.write_keyword("asserts");
      self.space();
    }
    self.em.write_identifier(&pred.parameter_name);
    if let Some(ann) = &pred.type_annotation {
      self.space();
      self.em.write_keyword("is");
      self.space();
      self.emit_type_expr_with_prec(ann, TypePrec::ArrowOrConditional)?;
    }
    Ok(())
  }

  fn emit_import_type(&mut self, import: &Node<TypeImport>) -> EmitResult {
    let import = import.stx.as_ref();
    self.em.write_keyword("import");
    self.em.write_punct("(");
    self.emit_string_literal(&import.module_specifier);
    self.em.write_punct(")");
    if let Some(qualifier) = &import.qualifier {
      self.em.write_punct(".");
      self.emit_type_entity_name(qualifier)?;
    }
    self.emit_type_arguments(import.type_arguments.as_deref())
  }

  fn emit_type_entity_name(&mut self, name: &TypeEntityName) -> EmitResult {
    match name {
      TypeEntityName::Identifier(id) => self.em.write_identifier(id),
      TypeEntityName::Qualified(q) => {
        self.emit_type_entity_name(&q.left)?;
        self.em.write_punct(".");
        self.em.write_identifier(&q.right);
      }
      TypeEntityName::Import(import) => self.emit_import_entity(import)?,
    }
    Ok(())
  }

  fn emit_import_entity(&mut self, import: &Node<ImportExpr>) -> EmitResult {
    let import_expr = import.stx.as_ref();
    self.em.write_keyword("import");
    self.em.write_punct("(");
    self.emit_expr(&import_expr.module)?;
    if let Some(attrs) = &import_expr.attributes {
      self.em.write_punct(",");
      if self.is_canonical() {
        self.em.write_space();
      }
      self.emit_expr(attrs)?;
    }
    self.em.write_punct(")");
    Ok(())
  }

  fn emit_type_arguments(&mut self, args: Option<&[Node<TypeExpr>]>) -> EmitResult {
    if let Some(args) = args {
      if args.is_empty() {
        return Ok(());
      }
      self.em.write_punct("<");
      for (i, arg) in args.iter().enumerate() {
        if i > 0 {
          self.em.write_punct(",");
          if self.is_canonical() {
            self.em.write_space();
          }
        }
        self.emit_type_expr_with_prec(arg, TypePrec::ArrowOrConditional)?;
      }
      self.em.write_punct(">");
    }
    Ok(())
  }

  fn emit_expr(&mut self, expr: &Node<Expr>) -> EmitResult {
    match expr.stx.as_ref() {
      Expr::Id(id) => self.em.write_identifier(&id.stx.name),
      Expr::LitStr(lit) => self.emit_string_literal(&lit.stx.value),
      Expr::LitNum(lit) => self.em.write_number(&lit.stx.value.to_string()),
      Expr::LitBool(lit) => self
        .em
        .write_keyword(if lit.stx.value { "true" } else { "false" }),
      Expr::LitNull(_) => self.em.write_keyword("null"),
      Expr::LitBigInt(lit) => self.em.write_bigint(&lit.stx.value),
      Expr::This(_) => self.em.write_keyword("this"),
      Expr::Member(member) => {
        let member = member.stx.as_ref();
        self.emit_expr(&member.left)?;
        if member.optional_chaining {
          self.em.write_punct("?.");
        } else {
          self.em.write_punct(".");
        }
        self.em.write_identifier(&member.right);
      }
      Expr::ComputedMember(member) => {
        let member = member.stx.as_ref();
        self.emit_expr(&member.object)?;
        if member.optional_chaining {
          self.em.write_punct("?.");
        }
        self.em.write_punct("[");
        self.emit_expr(&member.member)?;
        self.em.write_punct("]");
      }
      Expr::Import(import) => self.emit_import_entity(import)?,
      _ => {
        self.em.write_keyword("undefined");
      }
    }
    Ok(())
  }

  fn emit_string_literal(&mut self, value: &str) {
    self.em.write_string_literal(value);
  }
}

fn type_prec(expr: &TypeExpr) -> TypePrec {
  match expr {
    TypeExpr::ConditionalType(_) | TypeExpr::FunctionType(_) | TypeExpr::ConstructorType(_) => {
      TypePrec::ArrowOrConditional
    }
    TypeExpr::UnionType(_) => TypePrec::Union,
    TypeExpr::IntersectionType(_) => TypePrec::Intersection,
    TypeExpr::KeyOfType(_) | TypeExpr::TypeQuery(_) | TypeExpr::InferType(_) => TypePrec::Unary,
    TypeExpr::ArrayType(_) | TypeExpr::IndexedAccessType(_) => TypePrec::Postfix,
    // Everything else is treated as a primary expression.
    _ => TypePrec::Primary,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use parse_js::loc::Loc;

  fn loc() -> Loc {
    Loc(0, 0)
  }

  fn type_ref(name: &str) -> Node<TypeExpr> {
    Node::new(
      loc(),
      TypeExpr::TypeReference(Node::new(
        loc(),
        TypeReference {
          name: TypeEntityName::Identifier(name.to_string()),
          type_arguments: None,
        },
      )),
    )
  }

  fn union(types: Vec<Node<TypeExpr>>) -> Node<TypeExpr> {
    Node::new(
      loc(),
      TypeExpr::UnionType(Node::new(loc(), TypeUnion { types })),
    )
  }

  fn array_of(elem: Node<TypeExpr>) -> Node<TypeExpr> {
    Node::new(
      loc(),
      TypeExpr::ArrayType(Node::new(
        loc(),
        TypeArray {
          readonly: false,
          element_type: Box::new(elem),
        },
      )),
    )
  }

  fn fn_type(ret: Node<TypeExpr>) -> Node<TypeExpr> {
    Node::new(
      loc(),
      TypeExpr::FunctionType(Node::new(
        loc(),
        TypeFunction {
          type_parameters: None,
          parameters: Vec::new(),
          return_type: Box::new(ret),
        },
      )),
    )
  }

  fn conditional(check: Node<TypeExpr>, extends_ty: Node<TypeExpr>) -> Node<TypeExpr> {
    Node::new(
      loc(),
      TypeExpr::ConditionalType(Node::new(
        loc(),
        TypeConditional {
          check_type: Box::new(check),
          extends_type: Box::new(extends_ty),
          true_type: Box::new(type_ref("X")),
          false_type: Box::new(type_ref("Y")),
        },
      )),
    )
  }

  #[test]
  fn array_and_index_parentheses() {
    let ty = array_of(union(vec![type_ref("A"), type_ref("B")]));
    assert_eq!(ts_type_to_string(&ty, EmitMode::Canonical), "(A | B)[]");
    assert_eq!(ts_type_to_string(&ty, EmitMode::Minified), "(A|B)[]");

    let idx = Node::new(
      loc(),
      TypeExpr::IndexedAccessType(Node::new(
        loc(),
        TypeIndexedAccess {
          object_type: Box::new(union(vec![type_ref("A"), type_ref("B")])),
          index_type: Box::new(type_ref("K")),
        },
      )),
    );
    assert_eq!(ts_type_to_string(&idx, EmitMode::Canonical), "(A | B)[K]");

    let fn_array = array_of(fn_type(type_ref("T")));
    assert_eq!(
      ts_type_to_string(&fn_array, EmitMode::Canonical),
      "(() => T)[]"
    );
  }

  #[test]
  fn conditional_operands_parenthesized_like_ts() {
    let cond = conditional(fn_type(type_ref("T")), type_ref("U"));
    assert_eq!(
      ts_type_to_string(&cond, EmitMode::Canonical),
      "(() => T) extends U ? X : Y"
    );

    let cond_extends = conditional(type_ref("T"), fn_type(type_ref("U")));
    assert_eq!(
      ts_type_to_string(&cond_extends, EmitMode::Canonical),
      "T extends (() => U) ? X : Y"
    );
  }

  #[test]
  fn unary_operator_parentheses() {
    let union_ty = union(vec![type_ref("A"), type_ref("B")]);
    let keyof_union = Node::new(
      loc(),
      TypeExpr::KeyOfType(Node::new(
        loc(),
        TypeKeyOf {
          type_expr: Box::new(union_ty),
        },
      )),
    );
    assert_eq!(
      ts_type_to_string(&keyof_union, EmitMode::Canonical),
      "keyof (A | B)"
    );
    assert_eq!(
      ts_type_to_string(&keyof_union, EmitMode::Minified),
      "keyof(A|B)"
    );

    let keyof_simple = Node::new(
      loc(),
      TypeExpr::KeyOfType(Node::new(
        loc(),
        TypeKeyOf {
          type_expr: Box::new(type_ref("A")),
        },
      )),
    );
    assert_eq!(
      ts_type_to_string(&keyof_simple, EmitMode::Canonical),
      "keyof A"
    );
  }

  #[test]
  fn preserves_parenthesized_node() {
    let paren = Node::new(
      loc(),
      TypeExpr::ParenthesizedType(Node::new(
        loc(),
        TypeParenthesized {
          type_expr: Box::new(union(vec![type_ref("A"), type_ref("B")])),
        },
      )),
    );
    assert_eq!(ts_type_to_string(&paren, EmitMode::Canonical), "(A | B)");
  }
}
