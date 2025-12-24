use parse_js::ast::expr::Expr;
use parse_js::ast::expr::ImportExpr;
use parse_js::ast::node::Node;
use parse_js::ast::ts_stmt::InterfaceDecl;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::ast::type_expr::*;
use std::fmt::Write;

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

/// Emit a TypeScript type expression into the provided buffer.
pub fn emit_ts_type(out: &mut String, expr: &Node<TypeExpr>) {
  emit_type_expr_with_prec(out, expr, TypePrec::ArrowOrConditional);
}

pub fn emit_type_expr_to_string(expr: &Node<TypeExpr>) -> String {
  let mut out = String::new();
  emit_ts_type(&mut out, expr);
  out
}

/// Convenience helper returning the emitted representation as a [`String`].
pub fn ts_type_to_string(expr: &Node<TypeExpr>) -> String {
  emit_type_expr_to_string(expr)
}

pub fn emit_type_expr<W: std::fmt::Write>(out: &mut W, expr: &Node<TypeExpr>) -> std::fmt::Result {
  out.write_str(&emit_type_expr_to_string(expr))
}

pub fn emit_type_alias_decl<W: std::fmt::Write>(
  out: &mut W,
  decl: &TypeAliasDecl,
) -> std::fmt::Result {
  if decl.export {
    out.write_str("export ")?;
  }
  if decl.declare {
    out.write_str("declare ")?;
  }
  out.write_str("type ")?;
  out.write_str(&decl.name)?;

  let mut type_parameters = String::new();
  emit_type_parameters(&mut type_parameters, decl.type_parameters.as_deref());
  out.write_str(&type_parameters)?;

  out.write_str(" = ")?;
  emit_type_expr(out, &decl.type_expr)?;
  out.write_char(';')
}

pub fn emit_interface_decl<W: std::fmt::Write>(
  out: &mut W,
  decl: &InterfaceDecl,
) -> std::fmt::Result {
  out.write_str(&interface_decl_to_string(decl))
}

fn interface_decl_to_string(decl: &InterfaceDecl) -> String {
  let mut out = String::new();

  if decl.export {
    out.push_str("export ");
  }
  if decl.declare {
    out.push_str("declare ");
  }

  out.push_str("interface ");
  out.push_str(&decl.name);
  emit_type_parameters(&mut out, decl.type_parameters.as_deref());

  if !decl.extends.is_empty() {
    out.push_str(" extends ");
    for (i, ty) in decl.extends.iter().enumerate() {
      if i > 0 {
        out.push_str(", ");
      }
      emit_type_expr_with_prec(&mut out, ty, TypePrec::ArrowOrConditional);
    }
  }

  out.push(' ');
  out.push('{');
  for (i, member) in decl.members.iter().enumerate() {
    if i > 0 {
      out.push(' ');
    }
    emit_type_member(&mut out, member);
    out.push(';');
  }
  out.push('}');

  out
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

fn emit_type_expr_with_prec(out: &mut String, expr: &Node<TypeExpr>, parent_prec: TypePrec) {
  if let TypeExpr::ParenthesizedType(inner) = expr.stx.as_ref() {
    // Preserve explicit parentheses exactly once.
    out.push('(');
    emit_type_expr_with_prec(
      out,
      &inner.stx.as_ref().type_expr,
      TypePrec::ArrowOrConditional,
    );
    out.push(')');
    return;
  }

  let self_prec = type_prec(expr.stx.as_ref());
  let needs_paren = self_prec < parent_prec;

  if needs_paren {
    out.push('(');
  }

  emit_type_expr_no_paren(out, expr);

  if needs_paren {
    out.push(')');
  }
}

fn emit_type_expr_no_paren(out: &mut String, expr: &Node<TypeExpr>) {
  match expr.stx.as_ref() {
    TypeExpr::Any(_) => out.push_str("any"),
    TypeExpr::Unknown(_) => out.push_str("unknown"),
    TypeExpr::Never(_) => out.push_str("never"),
    TypeExpr::Void(_) => out.push_str("void"),
    TypeExpr::String(_) => out.push_str("string"),
    TypeExpr::Number(_) => out.push_str("number"),
    TypeExpr::Boolean(_) => out.push_str("boolean"),
    TypeExpr::BigInt(_) => out.push_str("bigint"),
    TypeExpr::Symbol(_) => out.push_str("symbol"),
    TypeExpr::UniqueSymbol(_) => out.push_str("unique symbol"),
    TypeExpr::Object(_) => out.push_str("object"),
    TypeExpr::Null(_) => out.push_str("null"),
    TypeExpr::Undefined(_) => out.push_str("undefined"),

    TypeExpr::TypeReference(reference) => emit_type_reference(out, reference),
    TypeExpr::LiteralType(lit) => emit_type_literal(out, lit),
    TypeExpr::ArrayType(array) => emit_array_type(out, array),
    TypeExpr::TupleType(tuple) => emit_tuple_type(out, tuple),
    TypeExpr::UnionType(union) => emit_union_type(out, union),
    TypeExpr::IntersectionType(intersection) => emit_intersection_type(out, intersection),
    TypeExpr::FunctionType(func) => emit_function_type(out, func),
    TypeExpr::ConstructorType(cons) => emit_constructor_type(out, cons),
    TypeExpr::ObjectType(obj) => emit_object_type(out, obj),
    TypeExpr::TypeQuery(query) => emit_type_query(out, query),
    TypeExpr::KeyOfType(keyof) => emit_keyof(out, keyof),
    TypeExpr::IndexedAccessType(indexed) => emit_indexed_access(out, indexed),
    TypeExpr::ConditionalType(cond) => emit_conditional_type(out, cond),
    TypeExpr::InferType(infer_ty) => emit_infer(out, infer_ty),
    TypeExpr::MappedType(mapped) => emit_mapped_type_expr(out, mapped),
    TypeExpr::TemplateLiteralType(template) => emit_template_literal(out, template),
    TypeExpr::TypePredicate(pred) => emit_type_predicate(out, pred),
    TypeExpr::ThisType(_) => out.push_str("this"),
    TypeExpr::ImportType(import_type) => emit_import_type(out, import_type),

    TypeExpr::ParenthesizedType(_) => unreachable!("handled earlier"),
  }
}

fn emit_type_reference(out: &mut String, reference: &Node<TypeReference>) {
  let reference = reference.stx.as_ref();
  emit_type_entity_name(out, &reference.name);
  emit_type_arguments(out, reference.type_arguments.as_deref());
}

fn emit_type_literal(out: &mut String, lit: &Node<TypeLiteral>) {
  match lit.stx.as_ref() {
    TypeLiteral::String(value) => {
      emit_string_literal(out, value);
    }
    TypeLiteral::Number(value) | TypeLiteral::BigInt(value) => out.push_str(value),
    TypeLiteral::Boolean(value) => out.push_str(if *value { "true" } else { "false" }),
    TypeLiteral::Null => out.push_str("null"),
  }
}

fn emit_array_type(out: &mut String, array: &Node<TypeArray>) {
  let array = array.stx.as_ref();
  if array.readonly {
    out.push_str("readonly ");
  }
  emit_type_expr_with_prec(out, &array.element_type, TypePrec::Postfix);
  out.push_str("[]");
}

fn emit_tuple_type(out: &mut String, tuple: &Node<TypeTuple>) {
  let tuple = tuple.stx.as_ref();
  if tuple.readonly {
    out.push_str("readonly ");
  }
  out.push('[');
  for (i, elem) in tuple.elements.iter().enumerate() {
    if i > 0 {
      out.push_str(", ");
    }
    emit_tuple_element(out, elem);
  }
  out.push(']');
}

fn emit_tuple_element(out: &mut String, elem: &Node<TypeTupleElement>) {
  let TypeTupleElement {
    label,
    optional,
    rest,
    type_expr,
  } = elem.stx.as_ref();

  if *rest {
    out.push_str("...");
  }

  match label {
    Some(name) => {
      out.push_str(name);
      if *optional {
        out.push('?');
      }
      out.push_str(": ");
      emit_type_expr_with_prec(out, type_expr, TypePrec::ArrowOrConditional);
    }
    None => {
      emit_type_expr_with_prec(out, type_expr, TypePrec::ArrowOrConditional);
      if *optional {
        out.push('?');
      }
    }
  }
}

fn emit_union_type(out: &mut String, union: &Node<TypeUnion>) {
  for (i, ty) in union.stx.types.iter().enumerate() {
    if i > 0 {
      out.push_str(" | ");
    }
    emit_type_expr_with_prec(out, ty, TypePrec::Union);
  }
}

fn emit_intersection_type(out: &mut String, intersection: &Node<TypeIntersection>) {
  for (i, ty) in intersection.stx.types.iter().enumerate() {
    if i > 0 {
      out.push_str(" & ");
    }
    emit_type_expr_with_prec(out, ty, TypePrec::Intersection);
  }
}

fn emit_function_type(out: &mut String, func: &Node<TypeFunction>) {
  let func = func.stx.as_ref();
  emit_type_parameters(out, func.type_parameters.as_deref());
  out.push('(');
  for (i, param) in func.parameters.iter().enumerate() {
    if i > 0 {
      out.push_str(", ");
    }
    emit_function_param(out, param);
  }
  out.push(')');
  out.push_str(" => ");
  emit_type_expr_with_prec(out, &func.return_type, TypePrec::ArrowOrConditional);
}

fn emit_constructor_type(out: &mut String, cons: &Node<TypeConstructor>) {
  let cons = cons.stx.as_ref();
  out.push_str("new ");
  emit_type_parameters(out, cons.type_parameters.as_deref());
  out.push('(');
  for (i, param) in cons.parameters.iter().enumerate() {
    if i > 0 {
      out.push_str(", ");
    }
    emit_function_param(out, param);
  }
  out.push(')');
  out.push_str(" => ");
  emit_type_expr_with_prec(out, &cons.return_type, TypePrec::ArrowOrConditional);
}

fn emit_function_param(out: &mut String, param: &Node<TypeFunctionParameter>) {
  let TypeFunctionParameter {
    name,
    optional,
    rest,
    type_expr,
  } = param.stx.as_ref();

  if *rest {
    out.push_str("...");
  }

  if let Some(name) = name {
    out.push_str(name);
    if *optional {
      out.push('?');
    }
    out.push_str(": ");
    emit_type_expr_with_prec(out, type_expr, TypePrec::ArrowOrConditional);
  } else {
    emit_type_expr_with_prec(out, type_expr, TypePrec::ArrowOrConditional);
    if *optional {
      out.push('?');
    }
  }
}

fn emit_object_type(out: &mut String, obj: &Node<TypeObjectLiteral>) {
  let obj = obj.stx.as_ref();
  out.push('{');
  for (i, member) in obj.members.iter().enumerate() {
    if i > 0 {
      out.push(' ');
    }
    emit_type_member(out, member);
    out.push(';');
  }
  out.push('}');
}

fn emit_type_member(out: &mut String, member: &Node<TypeMember>) {
  match member.stx.as_ref() {
    TypeMember::Property(prop) => emit_property_signature(out, prop),
    TypeMember::Method(method) => emit_method_signature(out, method),
    TypeMember::Constructor(cons) => emit_construct_signature(out, cons),
    TypeMember::CallSignature(call) => emit_call_signature(out, call),
    TypeMember::IndexSignature(index) => emit_index_signature(out, index),
    TypeMember::GetAccessor(get) => emit_get_accessor(out, get),
    TypeMember::SetAccessor(set) => emit_set_accessor(out, set),
    TypeMember::MappedProperty(mapped) => emit_mapped_signature(out, mapped.stx.as_ref()),
  }
}

fn emit_property_signature(out: &mut String, prop: &Node<TypePropertySignature>) {
  let prop = prop.stx.as_ref();
  if prop.readonly {
    out.push_str("readonly ");
  }
  emit_property_key(out, &prop.key);
  if prop.optional {
    out.push('?');
  }
  if let Some(ty) = &prop.type_annotation {
    out.push_str(": ");
    emit_type_expr_with_prec(out, ty, TypePrec::ArrowOrConditional);
  }
}

fn emit_method_signature(out: &mut String, method: &Node<TypeMethodSignature>) {
  let method = method.stx.as_ref();
  emit_property_key(out, &method.key);
  if method.optional {
    out.push('?');
  }
  emit_type_parameters(out, method.type_parameters.as_deref());
  out.push('(');
  for (i, param) in method.parameters.iter().enumerate() {
    if i > 0 {
      out.push_str(", ");
    }
    emit_function_param(out, param);
  }
  out.push(')');
  if let Some(ret) = &method.return_type {
    out.push_str(": ");
    emit_type_expr_with_prec(out, ret, TypePrec::ArrowOrConditional);
  }
}

fn emit_construct_signature(out: &mut String, cons: &Node<TypeConstructSignature>) {
  let cons = cons.stx.as_ref();
  out.push_str("new ");
  emit_type_parameters(out, cons.type_parameters.as_deref());
  out.push('(');
  for (i, param) in cons.parameters.iter().enumerate() {
    if i > 0 {
      out.push_str(", ");
    }
    emit_function_param(out, param);
  }
  out.push(')');
  if let Some(ret) = &cons.return_type {
    out.push_str(": ");
    emit_type_expr_with_prec(out, ret, TypePrec::ArrowOrConditional);
  }
}

fn emit_call_signature(out: &mut String, call: &Node<TypeCallSignature>) {
  let call = call.stx.as_ref();
  emit_type_parameters(out, call.type_parameters.as_deref());
  out.push('(');
  for (i, param) in call.parameters.iter().enumerate() {
    if i > 0 {
      out.push_str(", ");
    }
    emit_function_param(out, param);
  }
  out.push(')');
  if let Some(ret) = &call.return_type {
    out.push_str(": ");
    emit_type_expr_with_prec(out, ret, TypePrec::ArrowOrConditional);
  }
}

fn emit_index_signature(out: &mut String, index: &Node<TypeIndexSignature>) {
  let index = index.stx.as_ref();
  if index.readonly {
    out.push_str("readonly ");
  }
  out.push('[');
  out.push_str(&index.parameter_name);
  out.push_str(": ");
  emit_type_expr_with_prec(out, &index.parameter_type, TypePrec::ArrowOrConditional);
  out.push(']');
  out.push_str(": ");
  emit_type_expr_with_prec(out, &index.type_annotation, TypePrec::ArrowOrConditional);
}

fn emit_get_accessor(out: &mut String, get: &Node<TypeGetAccessor>) {
  let get = get.stx.as_ref();
  out.push_str("get ");
  emit_property_key(out, &get.key);
  out.push_str("(): ");
  if let Some(ret) = &get.return_type {
    emit_type_expr_with_prec(out, ret, TypePrec::ArrowOrConditional);
  } else {
    out.push_str("void");
  }
}

fn emit_set_accessor(out: &mut String, set: &Node<TypeSetAccessor>) {
  let set = set.stx.as_ref();
  out.push_str("set ");
  emit_property_key(out, &set.key);
  out.push('(');
  emit_function_param(out, &set.parameter);
  out.push(')');
}

fn emit_property_key(out: &mut String, key: &TypePropertyKey) {
  match key {
    TypePropertyKey::Identifier(name) => out.push_str(name),
    TypePropertyKey::String(value) => {
      emit_string_literal(out, value);
    }
    TypePropertyKey::Number(value) => out.push_str(value),
    TypePropertyKey::Computed(expr) => {
      out.push('[');
      emit_expr(out, expr);
      out.push(']');
    }
  }
}

fn emit_type_parameters(out: &mut String, params: Option<&[Node<TypeParameter>]>) {
  if let Some(params) = params {
    if params.is_empty() {
      return;
    }
    out.push('<');
    for (i, param) in params.iter().enumerate() {
      if i > 0 {
        out.push_str(", ");
      }
      emit_type_parameter(out, param);
    }
    out.push('>');
  }
}

fn emit_type_parameter(out: &mut String, param: &Node<TypeParameter>) {
  let TypeParameter {
    const_,
    variance,
    name,
    constraint,
    default,
  } = param.stx.as_ref();

  if *const_ {
    out.push_str("const ");
  }
  if let Some(variance) = variance {
    match variance {
      Variance::In => out.push_str("in "),
      Variance::Out => out.push_str("out "),
      Variance::InOut => out.push_str("in out "),
    }
  }
  out.push_str(name);
  if let Some(constraint) = constraint {
    out.push_str(" extends ");
    emit_type_expr_with_prec(out, constraint, TypePrec::ArrowOrConditional);
  }
  if let Some(default) = default {
    out.push_str(" = ");
    emit_type_expr_with_prec(out, default, TypePrec::ArrowOrConditional);
  }
}

fn emit_type_query(out: &mut String, query: &Node<TypeQuery>) {
  let query = query.stx.as_ref();
  out.push_str("typeof ");
  emit_type_entity_name(out, &query.expr_name);
}

fn emit_keyof(out: &mut String, keyof: &Node<TypeKeyOf>) {
  let keyof = keyof.stx.as_ref();
  out.push_str("keyof ");
  emit_type_expr_with_prec(out, &keyof.type_expr, TypePrec::Unary);
}

fn emit_indexed_access(out: &mut String, indexed: &Node<TypeIndexedAccess>) {
  let indexed = indexed.stx.as_ref();
  emit_type_expr_with_prec(out, &indexed.object_type, TypePrec::Postfix);
  out.push('[');
  emit_type_expr_with_prec(out, &indexed.index_type, TypePrec::ArrowOrConditional);
  out.push(']');
}

fn emit_conditional_type(out: &mut String, cond: &Node<TypeConditional>) {
  let cond = cond.stx.as_ref();
  emit_type_expr_with_prec(out, &cond.check_type, TypePrec::Union);
  out.push_str(" extends ");
  emit_type_expr_with_prec(out, &cond.extends_type, TypePrec::Union);
  out.push_str(" ? ");
  emit_type_expr_with_prec(out, &cond.true_type, TypePrec::ArrowOrConditional);
  out.push_str(" : ");
  emit_type_expr_with_prec(out, &cond.false_type, TypePrec::ArrowOrConditional);
}

fn emit_infer(out: &mut String, infer_ty: &Node<TypeInfer>) {
  let infer_ty = infer_ty.stx.as_ref();
  out.push_str("infer ");
  out.push_str(&infer_ty.type_parameter);
  if let Some(constraint) = &infer_ty.constraint {
    out.push_str(" extends ");
    emit_type_expr_with_prec(out, constraint, TypePrec::ArrowOrConditional);
  }
}

fn emit_mapped_type_expr(out: &mut String, mapped: &Node<TypeMapped>) {
  out.push('{');
  out.push(' ');
  emit_mapped_signature(out, mapped.stx.as_ref());
  out.push(' ');
  out.push('}');
}

fn emit_mapped_signature(out: &mut String, mapped: &TypeMapped) {
  if let Some(modifier) = mapped.readonly_modifier {
    emit_mapped_modifier(out, modifier, "readonly ");
  }
  out.push('[');
  out.push_str(&mapped.type_parameter);
  out.push_str(" in ");
  emit_type_expr_with_prec(out, &mapped.constraint, TypePrec::ArrowOrConditional);
  if let Some(name_type) = &mapped.name_type {
    out.push_str(" as ");
    emit_type_expr_with_prec(out, name_type, TypePrec::ArrowOrConditional);
  }
  out.push(']');
  if let Some(modifier) = mapped.optional_modifier {
    emit_mapped_modifier(out, modifier, "?");
  }
  out.push_str(": ");
  emit_type_expr_with_prec(out, &mapped.type_expr, TypePrec::ArrowOrConditional);
}

fn emit_mapped_modifier(out: &mut String, modifier: MappedTypeModifier, token: &str) {
  match modifier {
    MappedTypeModifier::Plus => out.push('+'),
    MappedTypeModifier::Minus => out.push('-'),
    MappedTypeModifier::None => {}
  }
  out.push_str(token);
}

fn emit_template_literal(out: &mut String, template: &Node<TypeTemplateLiteral>) {
  let template = template.stx.as_ref();
  out.push('`');
  out.push_str(&template.head);
  for span in &template.spans {
    out.push_str("${");
    emit_type_expr_with_prec(out, &span.stx.type_expr, TypePrec::ArrowOrConditional);
    out.push('}');
    out.push_str(&span.stx.literal);
  }
  out.push('`');
}

fn emit_type_predicate(out: &mut String, pred: &Node<TypePredicate>) {
  let pred = pred.stx.as_ref();
  if pred.asserts {
    out.push_str("asserts ");
  }
  out.push_str(&pred.parameter_name);
  if let Some(ann) = &pred.type_annotation {
    out.push_str(" is ");
    emit_type_expr_with_prec(out, ann, TypePrec::ArrowOrConditional);
  }
}

fn emit_import_type(out: &mut String, import: &Node<TypeImport>) {
  let import = import.stx.as_ref();
  out.push_str("import(");
  emit_string_literal(out, &import.module_specifier);
  out.push(')');
  if let Some(qualifier) = &import.qualifier {
    out.push('.');
    emit_type_entity_name(out, qualifier);
  }
  emit_type_arguments(out, import.type_arguments.as_deref());
}

fn emit_type_entity_name(out: &mut String, name: &TypeEntityName) {
  match name {
    TypeEntityName::Identifier(id) => out.push_str(id),
    TypeEntityName::Qualified(q) => {
      emit_type_entity_name(out, &q.left);
      out.push('.');
      out.push_str(&q.right);
    }
    TypeEntityName::Import(import) => emit_import_entity(out, import),
  }
}

fn emit_import_entity(out: &mut String, import: &Node<ImportExpr>) {
  let import_expr = import.stx.as_ref();
  out.push_str("import(");
  emit_expr(out, &import_expr.module);
  if let Some(attrs) = &import_expr.attributes {
    out.push_str(", ");
    emit_expr(out, attrs);
  }
  out.push(')');
}

fn emit_type_arguments(out: &mut String, args: Option<&[Node<TypeExpr>]>) {
  if let Some(args) = args {
    if args.is_empty() {
      return;
    }
    out.push('<');
    for (i, arg) in args.iter().enumerate() {
      if i > 0 {
        out.push_str(", ");
      }
      emit_type_expr_with_prec(out, arg, TypePrec::ArrowOrConditional);
    }
    out.push('>');
  }
}

fn emit_expr(out: &mut String, expr: &Node<Expr>) {
  match expr.stx.as_ref() {
    Expr::Id(id) => out.push_str(&id.stx.name),
    Expr::LitStr(lit) => {
      emit_string_literal(out, &lit.stx.value);
    }
    Expr::LitNum(lit) => {
      write!(out, "{}", lit.stx.value).unwrap();
    }
    Expr::LitBool(lit) => out.push_str(if lit.stx.value { "true" } else { "false" }),
    Expr::LitNull(_) => out.push_str("null"),
    Expr::LitBigInt(lit) => out.push_str(&lit.stx.value),
    Expr::This(_) => out.push_str("this"),
    Expr::Member(member) => {
      let member = member.stx.as_ref();
      emit_expr(out, &member.left);
      if member.optional_chaining {
        out.push_str("?.");
      } else {
        out.push('.');
      }
      out.push_str(&member.right);
    }
    Expr::ComputedMember(member) => {
      let member = member.stx.as_ref();
      emit_expr(out, &member.object);
      if member.optional_chaining {
        out.push_str("?.");
      }
      out.push('[');
      emit_expr(out, &member.member);
      out.push(']');
    }
    _ => out.push_str("undefined"),
  }
}

fn emit_string_literal(out: &mut String, value: &str) {
  let mut buf = Vec::new();
  crate::emit_string_literal_double_quoted(&mut buf, value);
  out.push_str(std::str::from_utf8(&buf).expect("string literal escape output is UTF-8"));
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
    assert_eq!(ts_type_to_string(&ty), "(A | B)[]");

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
    assert_eq!(ts_type_to_string(&idx), "(A | B)[K]");

    let fn_array = array_of(fn_type(type_ref("T")));
    assert_eq!(ts_type_to_string(&fn_array), "(() => T)[]");
  }

  #[test]
  fn conditional_operands_parenthesized_like_ts() {
    let cond = conditional(fn_type(type_ref("T")), type_ref("U"));
    assert_eq!(ts_type_to_string(&cond), "(() => T) extends U ? X : Y");

    let cond_extends = conditional(type_ref("T"), fn_type(type_ref("U")));
    assert_eq!(
      ts_type_to_string(&cond_extends),
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
    assert_eq!(ts_type_to_string(&keyof_union), "keyof (A | B)");

    let keyof_simple = Node::new(
      loc(),
      TypeExpr::KeyOfType(Node::new(
        loc(),
        TypeKeyOf {
          type_expr: Box::new(type_ref("A")),
        },
      )),
    );
    assert_eq!(ts_type_to_string(&keyof_simple), "keyof A");
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
    assert_eq!(ts_type_to_string(&paren), "(A | B)");
  }
}
