use crate::ids::StableHasher;
use derive_visitor::{Drive, DriveMut};
use parse_js::ast::class_or_object::{
  ClassIndexSignature, ClassMember, ClassOrObjGetter, ClassOrObjKey, ClassOrObjMemberDirectKey,
  ClassOrObjMethod, ClassOrObjSetter, ClassOrObjVal, ClassStaticBlock, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::jsx::{
  JsxAttr, JsxAttrVal, JsxElem, JsxElemChild, JsxElemName, JsxExprContainer, JsxMemberExpr,
  JsxName, JsxSpreadAttr, JsxText,
};
use parse_js::ast::expr::lit::{
  LitArrElem, LitArrExpr, LitBigIntExpr, LitBoolExpr, LitNullExpr, LitNumExpr, LitObjExpr,
  LitRegexExpr, LitStrExpr, LitTemplateExpr, LitTemplatePart,
};
use parse_js::ast::expr::pat::{
  ArrPat, ArrPatElem, ClassOrFuncName, IdPat, ObjPat, ObjPatProp, Pat,
};
use parse_js::ast::expr::{
  ArrowFuncExpr, BinaryExpr, CallArg, CallExpr, ClassExpr, ComputedMemberExpr, CondExpr, Decorator,
  Expr, FuncExpr, IdExpr, ImportExpr, ImportMeta, InstantiationExpr, MemberExpr, NewTarget,
  NonNullAssertionExpr, SatisfiesExpr, SuperExpr, TaggedTemplateExpr, ThisExpr, TypeAssertionExpr,
  UnaryExpr, UnaryPostfixExpr,
};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{Accessibility, ParamDecl};
use parse_js::ast::stmt::Stmt;
use parse_js::operator::OperatorName;
use parse_js::token::TT;

// Domain separator for computed key fingerprints.
const EXPR_FINGERPRINT_DOMAIN: u64 = 0x65787072_66696e67; // "exprfing"

pub(crate) fn stable_expr_fingerprint(expr: &Node<Expr>) -> u64 {
  let mut hasher = StableHasher::new();
  hasher.write_u64(EXPR_FINGERPRINT_DOMAIN);
  hash_expr_node(&mut hasher, expr);
  hasher.finish()
}

#[inline]
fn hash_expr_node(hasher: &mut StableHasher, expr: &Node<Expr>) {
  hash_expr(hasher, &expr.stx);
}

#[inline]
fn hash_expr(hasher: &mut StableHasher, expr: &Expr) {
  match expr {
    Expr::ArrowFunc(node) => {
      hasher.write_u64(0);
      hash_arrow_func_expr(hasher, &node.stx);
    }
    Expr::Binary(node) => {
      hasher.write_u64(1);
      hash_binary_expr(hasher, &node.stx);
    }
    Expr::Call(node) => {
      hasher.write_u64(2);
      hash_call_expr(hasher, &node.stx);
    }
    Expr::Class(node) => {
      hasher.write_u64(3);
      hash_class_expr(hasher, &node.stx);
    }
    Expr::ComputedMember(node) => {
      hasher.write_u64(4);
      hash_computed_member_expr(hasher, &node.stx);
    }
    Expr::Cond(node) => {
      hasher.write_u64(5);
      hash_cond_expr(hasher, &node.stx);
    }
    Expr::Func(node) => {
      hasher.write_u64(6);
      hash_func_expr(hasher, &node.stx);
    }
    Expr::Id(node) => {
      hasher.write_u64(7);
      hash_id_expr(hasher, &node.stx);
    }
    Expr::Import(node) => {
      hasher.write_u64(8);
      hash_import_expr(hasher, &node.stx);
    }
    Expr::ImportMeta(node) => {
      hasher.write_u64(9);
      hash_import_meta(hasher, &node.stx);
    }
    Expr::Member(node) => {
      hasher.write_u64(10);
      hash_member_expr(hasher, &node.stx);
    }
    Expr::NewTarget(node) => {
      hasher.write_u64(11);
      hash_new_target(hasher, &node.stx);
    }
    Expr::Super(node) => {
      hasher.write_u64(12);
      hash_super_expr(hasher, &node.stx);
    }
    Expr::TaggedTemplate(node) => {
      hasher.write_u64(13);
      hash_tagged_template_expr(hasher, &node.stx);
    }
    Expr::This(node) => {
      hasher.write_u64(14);
      hash_this_expr(hasher, &node.stx);
    }
    Expr::Unary(node) => {
      hasher.write_u64(15);
      hash_unary_expr(hasher, &node.stx);
    }
    Expr::UnaryPostfix(node) => {
      hasher.write_u64(16);
      hash_unary_postfix_expr(hasher, &node.stx);
    }

    // JSX.
    Expr::JsxElem(node) => {
      hasher.write_u64(17);
      hash_jsx_elem(hasher, &node.stx);
    }
    Expr::JsxExprContainer(node) => {
      hasher.write_u64(18);
      hash_jsx_expr_container(hasher, &node.stx);
    }
    Expr::JsxMember(node) => {
      hasher.write_u64(19);
      hash_jsx_member_expr(hasher, &node.stx);
    }
    Expr::JsxName(node) => {
      hasher.write_u64(20);
      hash_jsx_name(hasher, &node.stx);
    }
    Expr::JsxSpreadAttr(node) => {
      hasher.write_u64(21);
      hash_jsx_spread_attr(hasher, &node.stx);
    }
    Expr::JsxText(node) => {
      hasher.write_u64(22);
      hash_jsx_text(hasher, &node.stx);
    }

    // Literals.
    Expr::LitArr(node) => {
      hasher.write_u64(23);
      hash_lit_arr_expr(hasher, &node.stx);
    }
    Expr::LitBigInt(node) => {
      hasher.write_u64(24);
      hash_lit_bigint_expr(hasher, &node.stx);
    }
    Expr::LitBool(node) => {
      hasher.write_u64(25);
      hash_lit_bool_expr(hasher, &node.stx);
    }
    Expr::LitNull(node) => {
      hasher.write_u64(26);
      hash_lit_null_expr(hasher, &node.stx);
    }
    Expr::LitNum(node) => {
      hasher.write_u64(27);
      hash_lit_num_expr(hasher, &node.stx);
    }
    Expr::LitObj(node) => {
      hasher.write_u64(28);
      hash_lit_obj_expr(hasher, &node.stx);
    }
    Expr::LitRegex(node) => {
      hasher.write_u64(29);
      hash_lit_regex_expr(hasher, &node.stx);
    }
    Expr::LitStr(node) => {
      hasher.write_u64(30);
      hash_lit_str_expr(hasher, &node.stx);
    }
    Expr::LitTemplate(node) => {
      hasher.write_u64(31);
      hash_lit_template_expr(hasher, &node.stx);
    }

    // Patterns.
    Expr::ArrPat(node) => {
      hasher.write_u64(32);
      hash_arr_pat(hasher, &node.stx);
    }
    Expr::IdPat(node) => {
      hasher.write_u64(33);
      hash_id_pat(hasher, &node.stx);
    }
    Expr::ObjPat(node) => {
      hasher.write_u64(34);
      hash_obj_pat(hasher, &node.stx);
    }

    // TypeScript expressions.
    Expr::Instantiation(node) => {
      hasher.write_u64(38);
      hash_instantiation_expr(hasher, &node.stx);
    }
    Expr::TypeAssertion(node) => {
      hasher.write_u64(35);
      hash_type_assertion_expr(hasher, &node.stx);
    }
    Expr::NonNullAssertion(node) => {
      hasher.write_u64(36);
      hash_non_null_assertion_expr(hasher, &node.stx);
    }
    Expr::SatisfiesExpr(node) => {
      hasher.write_u64(37);
      hash_satisfies_expr(hasher, &node.stx);
    }
  }
}

#[inline]
fn hash_arrow_func_expr(hasher: &mut StableHasher, expr: &ArrowFuncExpr) {
  hash_func_node(hasher, &expr.func);
}

#[inline]
fn hash_binary_expr(hasher: &mut StableHasher, expr: &BinaryExpr) {
  hash_operator_name(hasher, expr.operator);
  hash_expr_node(hasher, &expr.left);
  hash_expr_node(hasher, &expr.right);
}

#[inline]
fn hash_call_expr(hasher: &mut StableHasher, expr: &CallExpr) {
  write_bool(hasher, expr.optional_chaining);
  hash_expr_node(hasher, &expr.callee);
  hash_vec(hasher, &expr.arguments, hash_call_arg_node);
}

#[inline]
fn hash_call_arg_node(hasher: &mut StableHasher, arg: &Node<CallArg>) {
  hash_call_arg(hasher, &arg.stx);
}

#[inline]
fn hash_call_arg(hasher: &mut StableHasher, arg: &CallArg) {
  write_bool(hasher, arg.spread);
  hash_expr_node(hasher, &arg.value);
}

#[inline]
fn hash_class_expr(hasher: &mut StableHasher, expr: &ClassExpr) {
  hash_vec(hasher, &expr.decorators, hash_decorator_node);
  hash_option_node(hasher, expr.name.as_ref(), hash_class_or_func_name);

  // TypeScript-only fields intentionally omitted: `type_parameters`, `implements`.
  hash_option_node(hasher, expr.extends.as_ref(), hash_expr);
  hash_vec(hasher, &expr.members, hash_class_member_node);
}

#[inline]
fn hash_class_member_node(hasher: &mut StableHasher, member: &Node<ClassMember>) {
  hash_class_member(hasher, &member.stx);
}

#[inline]
fn hash_class_member(hasher: &mut StableHasher, member: &ClassMember) {
  hash_vec(hasher, &member.decorators, hash_decorator_node);
  hash_class_or_obj_key(hasher, &member.key);
  write_bool(hasher, member.static_);
  write_bool(hasher, member.abstract_);
  write_bool(hasher, member.readonly);
  write_bool(hasher, member.accessor);
  write_bool(hasher, member.optional);
  write_bool(hasher, member.override_);
  write_bool(hasher, member.definite_assignment);
  hash_option(hasher, member.accessibility.as_ref(), hash_accessibility);
  // TypeScript-only field intentionally omitted: `type_annotation`.
  hash_class_or_obj_val(hasher, &member.val);
}

#[inline]
fn hash_accessibility(hasher: &mut StableHasher, acc: &Accessibility) {
  hasher.write_u64(*acc as u64);
}

#[inline]
fn hash_computed_member_expr(hasher: &mut StableHasher, expr: &ComputedMemberExpr) {
  write_bool(hasher, expr.optional_chaining);
  hash_expr_node(hasher, &expr.object);
  hash_expr_node(hasher, &expr.member);
}

#[inline]
fn hash_cond_expr(hasher: &mut StableHasher, expr: &CondExpr) {
  hash_expr_node(hasher, &expr.test);
  hash_expr_node(hasher, &expr.consequent);
  hash_expr_node(hasher, &expr.alternate);
}

#[inline]
fn hash_func_expr(hasher: &mut StableHasher, expr: &FuncExpr) {
  hash_option_node(hasher, expr.name.as_ref(), hash_class_or_func_name);
  hash_func_node(hasher, &expr.func);
}

#[inline]
fn hash_class_or_func_name(hasher: &mut StableHasher, name: &ClassOrFuncName) {
  write_str(hasher, &name.name);
}

#[inline]
fn hash_func_node(hasher: &mut StableHasher, func: &Node<Func>) {
  hash_func(hasher, &func.stx);
}

#[inline]
fn hash_func(hasher: &mut StableHasher, func: &Func) {
  write_bool(hasher, func.arrow);
  write_bool(hasher, func.async_);
  write_bool(hasher, func.generator);

  // TypeScript-only fields intentionally omitted: `type_parameters`, `return_type`.
  hash_vec(hasher, &func.parameters, hash_param_decl_node);

  hash_option(hasher, func.body.as_ref(), hash_func_body);
}

#[inline]
fn hash_param_decl_node(hasher: &mut StableHasher, param: &Node<ParamDecl>) {
  hash_param_decl(hasher, &param.stx);
}

#[inline]
fn hash_param_decl(hasher: &mut StableHasher, param: &ParamDecl) {
  hash_vec(hasher, &param.decorators, hash_decorator_node);
  write_bool(hasher, param.rest);
  write_bool(hasher, param.optional);
  hash_option(hasher, param.accessibility.as_ref(), hash_accessibility);
  write_bool(hasher, param.readonly);

  hash_pat_decl_node(hasher, &param.pattern);

  hash_option_node(hasher, param.default_value.as_ref(), hash_expr);

  // TypeScript-only field intentionally omitted: `type_annotation`.
}

#[inline]
fn hash_func_body(hasher: &mut StableHasher, body: &FuncBody) {
  match body {
    FuncBody::Block(stmts) => {
      hasher.write_u64(0);
      hasher.write_u64(stmts.len() as u64);
      for stmt in stmts {
        hash_stmt_tag(hasher, &stmt.stx);
      }
    }
    FuncBody::Expression(expr) => {
      hasher.write_u64(1);
      hash_expr_node(hasher, expr);
    }
  }
}

#[inline]
fn hash_stmt_tag(hasher: &mut StableHasher, stmt: &Stmt) {
  match stmt {
    Stmt::Block(_) => hasher.write_u64(0),
    Stmt::Break(_) => hasher.write_u64(1),
    Stmt::Continue(_) => hasher.write_u64(2),
    Stmt::Debugger(_) => hasher.write_u64(3),
    Stmt::DoWhile(_) => hasher.write_u64(4),
    Stmt::Empty(_) => hasher.write_u64(5),
    Stmt::ExportDefaultExpr(_) => hasher.write_u64(6),
    Stmt::ExportList(_) => hasher.write_u64(7),
    Stmt::Expr(_) => hasher.write_u64(8),
    Stmt::ForIn(_) => hasher.write_u64(9),
    Stmt::ForOf(_) => hasher.write_u64(10),
    Stmt::ForTriple(_) => hasher.write_u64(11),
    Stmt::If(_) => hasher.write_u64(12),
    Stmt::Import(_) => hasher.write_u64(13),
    Stmt::Label(_) => hasher.write_u64(14),
    Stmt::Return(_) => hasher.write_u64(15),
    Stmt::Switch(_) => hasher.write_u64(16),
    Stmt::Throw(_) => hasher.write_u64(17),
    Stmt::Try(_) => hasher.write_u64(18),
    Stmt::While(_) => hasher.write_u64(19),
    Stmt::With(_) => hasher.write_u64(20),
    Stmt::ClassDecl(_) => hasher.write_u64(21),
    Stmt::FunctionDecl(_) => hasher.write_u64(22),
    Stmt::VarDecl(_) => hasher.write_u64(23),
    Stmt::InterfaceDecl(_) => hasher.write_u64(24),
    Stmt::TypeAliasDecl(_) => hasher.write_u64(25),
    Stmt::EnumDecl(_) => hasher.write_u64(26),
    Stmt::NamespaceDecl(_) => hasher.write_u64(27),
    Stmt::ModuleDecl(_) => hasher.write_u64(28),
    Stmt::GlobalDecl(_) => hasher.write_u64(29),
    Stmt::AmbientVarDecl(_) => hasher.write_u64(30),
    Stmt::AmbientFunctionDecl(_) => hasher.write_u64(31),
    Stmt::AmbientClassDecl(_) => hasher.write_u64(32),
    Stmt::ImportTypeDecl(_) => hasher.write_u64(33),
    Stmt::ExportTypeDecl(_) => hasher.write_u64(34),
    Stmt::ImportEqualsDecl(_) => hasher.write_u64(35),
    Stmt::ExportAssignmentDecl(_) => hasher.write_u64(36),
    Stmt::ExportAsNamespaceDecl(_) => hasher.write_u64(37),
  }
}

#[inline]
fn hash_id_expr(hasher: &mut StableHasher, expr: &IdExpr) {
  write_str(hasher, &expr.name);
}

#[inline]
fn hash_import_expr(hasher: &mut StableHasher, expr: &ImportExpr) {
  hash_expr_node(hasher, &expr.module);
  hash_option_node(hasher, expr.attributes.as_ref(), hash_expr);
}

#[inline]
fn hash_import_meta(_hasher: &mut StableHasher, _expr: &ImportMeta) {}

#[inline]
fn hash_member_expr(hasher: &mut StableHasher, expr: &MemberExpr) {
  write_bool(hasher, expr.optional_chaining);
  hash_expr_node(hasher, &expr.left);
  write_str(hasher, &expr.right);
}

#[inline]
fn hash_new_target(_hasher: &mut StableHasher, _expr: &NewTarget) {}

#[inline]
fn hash_super_expr(_hasher: &mut StableHasher, _expr: &SuperExpr) {}

#[inline]
fn hash_tagged_template_expr(hasher: &mut StableHasher, expr: &TaggedTemplateExpr) {
  hash_expr_node(hasher, &expr.function);
  hash_vec(hasher, &expr.parts, hash_lit_template_part);
}

#[inline]
fn hash_this_expr(_hasher: &mut StableHasher, _expr: &ThisExpr) {}

#[inline]
fn hash_unary_expr(hasher: &mut StableHasher, expr: &UnaryExpr) {
  hash_operator_name(hasher, expr.operator);
  hash_expr_node(hasher, &expr.argument);
}

#[inline]
fn hash_unary_postfix_expr(hasher: &mut StableHasher, expr: &UnaryPostfixExpr) {
  hash_operator_name(hasher, expr.operator);
  hash_expr_node(hasher, &expr.argument);
}

#[inline]
fn hash_operator_name(hasher: &mut StableHasher, op: OperatorName) {
  hasher.write_u64(op as u64);
}

#[inline]
fn hash_jsx_elem(hasher: &mut StableHasher, elem: &JsxElem) {
  hash_option(hasher, elem.name.as_ref(), hash_jsx_elem_name);
  hash_vec(hasher, &elem.attributes, hash_jsx_attr);
  hash_vec(hasher, &elem.children, hash_jsx_elem_child);
}

#[inline]
fn hash_jsx_elem_name(hasher: &mut StableHasher, name: &JsxElemName) {
  match name {
    JsxElemName::Id(id) => {
      hasher.write_u64(0);
      hash_id_expr(hasher, &id.stx);
    }
    JsxElemName::Member(member) => {
      hasher.write_u64(1);
      hash_jsx_member_expr(hasher, &member.stx);
    }
    JsxElemName::Name(name) => {
      hasher.write_u64(2);
      hash_jsx_name(hasher, &name.stx);
    }
  }
}

#[inline]
fn hash_jsx_attr(hasher: &mut StableHasher, attr: &JsxAttr) {
  match attr {
    JsxAttr::Named { name, value } => {
      hasher.write_u64(0);
      hash_jsx_name(hasher, &name.stx);
      hash_option(hasher, value.as_ref(), hash_jsx_attr_val);
    }
    JsxAttr::Spread { value } => {
      hasher.write_u64(1);
      hash_jsx_spread_attr(hasher, &value.stx);
    }
  }
}

#[inline]
fn hash_jsx_attr_val(hasher: &mut StableHasher, value: &JsxAttrVal) {
  match value {
    JsxAttrVal::Expression(expr) => {
      hasher.write_u64(0);
      hash_jsx_expr_container(hasher, &expr.stx);
    }
    JsxAttrVal::Text(text) => {
      hasher.write_u64(1);
      hash_jsx_text(hasher, &text.stx);
    }
    JsxAttrVal::Element(elem) => {
      hasher.write_u64(2);
      hash_jsx_elem(hasher, &elem.stx);
    }
  }
}

#[inline]
fn hash_jsx_elem_child(hasher: &mut StableHasher, child: &JsxElemChild) {
  match child {
    JsxElemChild::Element(elem) => {
      hasher.write_u64(0);
      hash_jsx_elem(hasher, &elem.stx);
    }
    JsxElemChild::Expr(expr) => {
      hasher.write_u64(1);
      hash_jsx_expr_container(hasher, &expr.stx);
    }
    JsxElemChild::Text(text) => {
      hasher.write_u64(2);
      hash_jsx_text(hasher, &text.stx);
    }
  }
}

#[inline]
fn hash_jsx_expr_container(hasher: &mut StableHasher, container: &JsxExprContainer) {
  write_bool(hasher, container.spread);
  hash_expr_node(hasher, &container.value);
}

#[inline]
fn hash_jsx_member_expr(hasher: &mut StableHasher, member: &JsxMemberExpr) {
  hash_id_expr(hasher, &member.base.stx);
  hash_vec(hasher, &member.path, hash_string);
}

#[inline]
fn hash_jsx_name(hasher: &mut StableHasher, name: &JsxName) {
  hash_option(hasher, name.namespace.as_ref(), hash_string);
  write_str(hasher, &name.name);
}

#[inline]
fn hash_jsx_spread_attr(hasher: &mut StableHasher, spread: &JsxSpreadAttr) {
  hash_expr_node(hasher, &spread.value);
}

#[inline]
fn hash_jsx_text(hasher: &mut StableHasher, text: &JsxText) {
  write_str(hasher, &text.value);
}

#[inline]
fn hash_lit_arr_expr(hasher: &mut StableHasher, lit: &LitArrExpr) {
  hash_vec(hasher, &lit.elements, hash_lit_arr_elem);
}

#[inline]
fn hash_lit_arr_elem(hasher: &mut StableHasher, elem: &LitArrElem) {
  match elem {
    LitArrElem::Single(expr) => {
      hasher.write_u64(0);
      hash_expr_node(hasher, expr);
    }
    LitArrElem::Rest(expr) => {
      hasher.write_u64(1);
      hash_expr_node(hasher, expr);
    }
    LitArrElem::Empty => {
      hasher.write_u64(2);
    }
  }
}

#[inline]
fn hash_lit_bigint_expr(hasher: &mut StableHasher, lit: &LitBigIntExpr) {
  write_str(hasher, &lit.value);
}

#[inline]
fn hash_lit_bool_expr(hasher: &mut StableHasher, lit: &LitBoolExpr) {
  write_bool(hasher, lit.value);
}

#[inline]
fn hash_lit_null_expr(_hasher: &mut StableHasher, _lit: &LitNullExpr) {}

#[inline]
fn hash_lit_num_expr(hasher: &mut StableHasher, lit: &LitNumExpr) {
  hasher.write_u64(lit.value.to_bits());
}

#[inline]
fn hash_lit_obj_expr(hasher: &mut StableHasher, lit: &LitObjExpr) {
  hash_vec(hasher, &lit.members, hash_obj_member_node);
}

#[inline]
fn hash_obj_member_node(hasher: &mut StableHasher, member: &Node<ObjMember>) {
  hash_obj_member(hasher, &member.stx);
}

#[inline]
fn hash_obj_member(hasher: &mut StableHasher, member: &ObjMember) {
  hash_obj_member_type(hasher, &member.typ);
}

#[inline]
fn hash_obj_member_type(hasher: &mut StableHasher, typ: &ObjMemberType) {
  match typ {
    ObjMemberType::Valued { key, val } => {
      hasher.write_u64(0);
      hash_class_or_obj_key(hasher, key);
      hash_class_or_obj_val(hasher, val);
    }
    ObjMemberType::Shorthand { id } => {
      hasher.write_u64(1);
      hash_id_expr(hasher, &id.stx);
    }
    ObjMemberType::Rest { val } => {
      hasher.write_u64(2);
      hash_expr_node(hasher, val);
    }
  }
}

#[inline]
fn hash_class_or_obj_key(hasher: &mut StableHasher, key: &ClassOrObjKey) {
  match key {
    ClassOrObjKey::Direct(direct) => {
      hasher.write_u64(0);
      hash_direct_key(hasher, &direct.stx);
    }
    ClassOrObjKey::Computed(expr) => {
      hasher.write_u64(1);
      hash_expr_node(hasher, expr);
    }
  }
}

#[inline]
fn hash_direct_key(hasher: &mut StableHasher, key: &ClassOrObjMemberDirectKey) {
  write_str(hasher, &key.key);
  hash_token_type(hasher, key.tt);
}

#[inline]
fn hash_token_type(hasher: &mut StableHasher, tt: TT) {
  hasher.write_u64(tt as u64);
}

#[inline]
fn hash_class_or_obj_val(hasher: &mut StableHasher, val: &ClassOrObjVal) {
  match val {
    ClassOrObjVal::Getter(get) => {
      hasher.write_u64(0);
      hash_getter(hasher, &get.stx);
    }
    ClassOrObjVal::Setter(set) => {
      hasher.write_u64(1);
      hash_setter(hasher, &set.stx);
    }
    ClassOrObjVal::Method(method) => {
      hasher.write_u64(2);
      hash_method(hasher, &method.stx);
    }
    ClassOrObjVal::Prop(expr) => {
      hasher.write_u64(3);
      hash_option_node(hasher, expr.as_ref(), hash_expr);
    }
    ClassOrObjVal::IndexSignature(sig) => {
      hasher.write_u64(4);
      hash_index_signature(hasher, &sig.stx);
    }
    ClassOrObjVal::StaticBlock(block) => {
      hasher.write_u64(5);
      hash_static_block(hasher, &block.stx);
    }
  }
}

#[inline]
fn hash_getter(hasher: &mut StableHasher, get: &ClassOrObjGetter) {
  hash_func_node(hasher, &get.func);
}

#[inline]
fn hash_setter(hasher: &mut StableHasher, set: &ClassOrObjSetter) {
  hash_func_node(hasher, &set.func);
}

#[inline]
fn hash_method(hasher: &mut StableHasher, method: &ClassOrObjMethod) {
  hash_func_node(hasher, &method.func);
}

#[inline]
fn hash_index_signature(hasher: &mut StableHasher, sig: &ClassIndexSignature) {
  write_str(hasher, &sig.parameter_name);
  // TypeScript-only fields intentionally omitted: `parameter_type`, `type_annotation`.
}

#[inline]
fn hash_static_block(hasher: &mut StableHasher, block: &ClassStaticBlock) {
  hasher.write_u64(block.body.len() as u64);
  for stmt in block.body.iter() {
    hash_stmt_tag(hasher, &stmt.stx);
  }
}

#[inline]
fn hash_lit_regex_expr(hasher: &mut StableHasher, lit: &LitRegexExpr) {
  write_str(hasher, &lit.value);
}

#[inline]
fn hash_lit_str_expr(hasher: &mut StableHasher, lit: &LitStrExpr) {
  write_str(hasher, &lit.value);
}

#[inline]
fn hash_lit_template_expr(hasher: &mut StableHasher, lit: &LitTemplateExpr) {
  hash_vec(hasher, &lit.parts, hash_lit_template_part);
}

#[inline]
fn hash_lit_template_part(hasher: &mut StableHasher, part: &LitTemplatePart) {
  match part {
    LitTemplatePart::Substitution(expr) => {
      hasher.write_u64(0);
      hash_expr_node(hasher, expr);
    }
    LitTemplatePart::String(text) => {
      hasher.write_u64(1);
      write_str(hasher, text);
    }
  }
}

#[inline]
fn hash_arr_pat(hasher: &mut StableHasher, pat: &ArrPat) {
  hasher.write_u64(pat.elements.len() as u64);
  for elem in pat.elements.iter() {
    match elem {
      Some(elem) => {
        hasher.write_u64(1);
        hash_arr_pat_elem(hasher, elem);
      }
      None => hasher.write_u64(0),
    }
  }
  hash_option_node(hasher, pat.rest.as_ref(), hash_pat);
}

#[inline]
fn hash_arr_pat_elem(hasher: &mut StableHasher, elem: &ArrPatElem) {
  hash_pat_node(hasher, &elem.target);
  hash_option_node(hasher, elem.default_value.as_ref(), hash_expr);
}

#[inline]
fn hash_id_pat(hasher: &mut StableHasher, pat: &IdPat) {
  write_str(hasher, &pat.name);
}

#[inline]
fn hash_obj_pat(hasher: &mut StableHasher, pat: &ObjPat) {
  hash_vec(hasher, &pat.properties, hash_obj_pat_prop_node);
  hash_option_node(hasher, pat.rest.as_ref(), hash_pat);
}

#[inline]
fn hash_obj_pat_prop_node(hasher: &mut StableHasher, prop: &Node<ObjPatProp>) {
  hash_obj_pat_prop(hasher, &prop.stx);
}

#[inline]
fn hash_obj_pat_prop(hasher: &mut StableHasher, prop: &ObjPatProp) {
  hash_class_or_obj_key(hasher, &prop.key);
  hash_pat_node(hasher, &prop.target);
  write_bool(hasher, prop.shorthand);
  hash_option_node(hasher, prop.default_value.as_ref(), hash_expr);
}

#[inline]
fn hash_pat_decl_node(hasher: &mut StableHasher, decl: &Node<parse_js::ast::stmt::decl::PatDecl>) {
  hash_pat_node(hasher, &decl.stx.pat);
}

#[inline]
fn hash_pat_node(hasher: &mut StableHasher, pat: &Node<Pat>) {
  hash_pat(hasher, &pat.stx);
}

#[inline]
fn hash_pat(hasher: &mut StableHasher, pat: &Pat) {
  match pat {
    Pat::Arr(arr) => {
      hasher.write_u64(0);
      hash_arr_pat(hasher, &arr.stx);
    }
    Pat::Id(id) => {
      hasher.write_u64(1);
      hash_id_pat(hasher, &id.stx);
    }
    Pat::Obj(obj) => {
      hasher.write_u64(2);
      hash_obj_pat(hasher, &obj.stx);
    }
    Pat::AssignTarget(expr) => {
      hasher.write_u64(3);
      hash_expr_node(hasher, expr);
    }
  }
}

#[inline]
fn hash_instantiation_expr(hasher: &mut StableHasher, expr: &InstantiationExpr) {
  hash_expr_node(hasher, &expr.expression);
  // TypeScript-only field intentionally omitted: `type_arguments`.
  hasher.write_u64(expr.type_arguments.len() as u64);
}

#[inline]
fn hash_type_assertion_expr(hasher: &mut StableHasher, expr: &TypeAssertionExpr) {
  hash_expr_node(hasher, &expr.expression);
  write_bool(hasher, expr.const_assertion);
  // TypeScript-only field intentionally omitted: `type_annotation`.
}

#[inline]
fn hash_non_null_assertion_expr(hasher: &mut StableHasher, expr: &NonNullAssertionExpr) {
  hash_expr_node(hasher, &expr.expression);
}

#[inline]
fn hash_satisfies_expr(hasher: &mut StableHasher, expr: &SatisfiesExpr) {
  hash_expr_node(hasher, &expr.expression);
  // TypeScript-only field intentionally omitted: `type_annotation`.
}

#[inline]
fn hash_decorator_node(hasher: &mut StableHasher, decorator: &Node<Decorator>) {
  hash_decorator(hasher, &decorator.stx);
}

#[inline]
fn hash_decorator(hasher: &mut StableHasher, decorator: &Decorator) {
  hash_expr_node(hasher, &decorator.expression);
}

#[inline]
fn write_bool(hasher: &mut StableHasher, value: bool) {
  hasher.write_u64(u64::from(value));
}

#[inline]
fn write_str(hasher: &mut StableHasher, value: &str) {
  hasher.write_u64(value.len() as u64);
  hasher.write_str(value);
}

#[inline]
fn hash_string(hasher: &mut StableHasher, value: &String) {
  write_str(hasher, value);
}

#[inline]
fn hash_vec<T>(hasher: &mut StableHasher, values: &[T], mut f: impl FnMut(&mut StableHasher, &T)) {
  hasher.write_u64(values.len() as u64);
  for value in values {
    f(hasher, value);
  }
}

#[inline]
fn hash_option<T>(
  hasher: &mut StableHasher,
  value: Option<&T>,
  f: impl FnOnce(&mut StableHasher, &T),
) {
  match value {
    None => hasher.write_u64(0),
    Some(value) => {
      hasher.write_u64(1);
      f(hasher, value);
    }
  }
}

#[inline]
fn hash_option_node<T: Drive + DriveMut>(
  hasher: &mut StableHasher,
  value: Option<&Node<T>>,
  f: impl FnOnce(&mut StableHasher, &T),
) {
  hash_option(hasher, value.map(|node| node.stx.as_ref()), f);
}
