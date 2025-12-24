use emit_js::emit_type_alias_decl;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::ast::type_expr::{TypeEntityName, TypeExpr, TypeParameter, TypeReference, Variance};

#[derive(Debug, PartialEq)]
struct TypeParamSummary {
  const_: bool,
  variance: Option<VarianceSummary>,
  name: String,
  constraint: Option<String>,
  default: Option<String>,
}

#[derive(Debug, PartialEq)]
enum VarianceSummary {
  In,
  Out,
  InOut,
}

#[test]
fn emits_const_type_parameter() {
  check("type Id<const T>=T;", "type Id<const T> = T;");
}

#[test]
fn emits_covariant_type_parameter() {
  check("type Cov<out T>=T;", "type Cov<out T> = T;");
}

#[test]
fn emits_contravariant_type_parameter() {
  check("type Contra<in T>=T;", "type Contra<in T> = T;");
}

#[test]
fn emits_invariant_type_parameter() {
  check("type Inv<in out T>=T;", "type Inv<in out T> = T;");
}

#[test]
fn emits_const_variance_with_constraints_and_defaults() {
  check(
    "type X< const   out T extends   U = V >=T;",
    "type X<const out T extends U = V> = T;",
  );
}

fn check(source: &str, expected: &str) {
  let parsed = parse_js::parse(source).expect("parse source");
  let alias = extract_type_alias(&parsed);

  let emitted = {
    let mut out = String::new();
    emit_type_alias_decl(&mut out, alias.stx.as_ref()).expect("emit type alias");
    out
  };
  assert_eq!(emitted, expected);

  let reparsed = parse_js::parse(&emitted).expect("parse emitted");
  assert_eq!(type_params(&parsed), type_params(&reparsed));
}

fn extract_type_alias(top: &Node<TopLevel>) -> &Node<TypeAliasDecl> {
  let TopLevel { body } = top.stx.as_ref();
  for stmt in body {
    if let Stmt::TypeAliasDecl(alias) = stmt.stx.as_ref() {
      return alias;
    }
  }
  panic!("expected a type alias declaration");
}

fn type_params(top: &Node<TopLevel>) -> Vec<TypeParamSummary> {
  extract_type_alias(top)
    .stx
    .type_parameters
    .as_ref()
    .map(|params| params.iter().map(summarize_type_param).collect())
    .unwrap_or_default()
}

fn summarize_type_param(param: &Node<TypeParameter>) -> TypeParamSummary {
  let param = param.stx.as_ref();
  TypeParamSummary {
    const_: param.const_,
    variance: param.variance.map(VarianceSummary::from),
    name: param.name.clone(),
    constraint: param.constraint.as_ref().map(|c| summarize_type_expr(c)),
    default: param.default.as_ref().map(|d| summarize_type_expr(d)),
  }
}

impl From<Variance> for VarianceSummary {
  fn from(value: Variance) -> Self {
    match value {
      Variance::In => VarianceSummary::In,
      Variance::Out => VarianceSummary::Out,
      Variance::InOut => VarianceSummary::InOut,
    }
  }
}

fn summarize_type_expr(expr: &Node<TypeExpr>) -> String {
  match expr.stx.as_ref() {
    TypeExpr::TypeReference(reference) => summarize_type_reference(reference.stx.as_ref()),
    TypeExpr::Any(_) => "any".to_string(),
    TypeExpr::Unknown(_) => "unknown".to_string(),
    TypeExpr::Never(_) => "never".to_string(),
    TypeExpr::Void(_) => "void".to_string(),
    TypeExpr::String(_) => "string".to_string(),
    TypeExpr::Number(_) => "number".to_string(),
    TypeExpr::Boolean(_) => "boolean".to_string(),
    TypeExpr::BigInt(_) => "bigint".to_string(),
    TypeExpr::Symbol(_) => "symbol".to_string(),
    TypeExpr::UniqueSymbol(_) => "unique symbol".to_string(),
    TypeExpr::Object(_) => "object".to_string(),
    TypeExpr::Null(_) => "null".to_string(),
    TypeExpr::Undefined(_) => "undefined".to_string(),
    _ => panic!("unsupported type expression in summary"),
  }
}

fn summarize_type_reference(reference: &TypeReference) -> String {
  let mut out = summarize_entity_name(&reference.name);
  if let Some(args) = &reference.type_arguments {
    out.push('<');
    for (i, arg) in args.iter().enumerate() {
      if i > 0 {
        out.push(',');
      }
      out.push_str(&summarize_type_expr(arg));
    }
    out.push('>');
  }
  out
}

fn summarize_entity_name(name: &TypeEntityName) -> String {
  match name {
    TypeEntityName::Identifier(name) => name.clone(),
    TypeEntityName::Qualified(q) => format!("{}.{}", summarize_entity_name(&q.left), q.right),
    TypeEntityName::Import(import) => {
      panic!(
        "import type entities are not expected in these tests: {:?}",
        import
      )
    }
  }
}
