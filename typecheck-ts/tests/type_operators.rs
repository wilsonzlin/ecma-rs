use ahash::AHashMap;
use ordered_float::OrderedFloat;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::parse;
use typecheck_ts::check::type_expr::TypeLowerer;
use types_ts_interned::{
  MappedModifier, MappedType, ObjectType, PropData, PropKey, Property, Shape, TemplateChunk,
  TemplateLiteralType, TypeEvaluator, TypeKind, TypeParamId, TypeStore,
};

fn parse_type_alias(source: &str) -> Node<TypeAliasDecl> {
  let ast = parse(source).expect("parse failed");
  for stmt in ast.stx.body.into_iter() {
    match *stmt.stx {
      Stmt::TypeAliasDecl(alias) => return alias,
      _ => {}
    }
  }
  panic!("no type alias in source");
}

#[test]
fn eval_keyof_object_literal() {
  let alias = parse_type_alias("type K = keyof { a: number; b?: string };");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  let evaluated = store.evaluate(ty);
  assert_eq!(store.display(evaluated).to_string(), "\"a\" | \"b\"");
}

#[test]
fn eval_indexed_access_with_union_key() {
  let alias = parse_type_alias("type V = { a: number; b?: string }['a' | 'b'];");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  let evaluated = store.evaluate(ty);
  assert_eq!(
    store.display(evaluated).to_string(),
    "undefined | number | string"
  );
}

#[test]
fn eval_distributive_conditional() {
  let store = TypeStore::new();
  let string_union = store.union(vec![
    store.intern_type(TypeKind::StringLiteral(store.intern_name("x"))),
    store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(1.0))),
  ]);
  let yes = store.intern_type(TypeKind::StringLiteral(store.intern_name("yes")));
  let no = store.intern_type(TypeKind::StringLiteral(store.intern_name("no")));
  let cond = store.intern_type(TypeKind::Conditional {
    check: string_union,
    extends: store.primitive_ids().string,
    true_ty: yes,
    false_ty: no,
    distributive: true,
  });
  let evaluated = store.evaluate(cond);
  assert_eq!(store.display(evaluated).to_string(), "\"no\" | \"yes\"");
}

#[test]
fn eval_mapped_type_over_keyof() {
  let store = TypeStore::new();
  let mut shape = Shape::new();
  let key = store.intern_name("value");
  shape.properties.push(Property {
    key: PropKey::String(key),
    data: PropData {
      ty: store.primitive_ids().number,
      optional: false,
      readonly: false,
      accessibility: None,
    },
  });
  let obj_shape = store.intern_shape(shape);
  let obj = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: obj_shape }),
  ));

  let param = TypeParamId(0);
  let mapped = store.intern_type(TypeKind::Mapped(MappedType {
    param,
    source: store.intern_type(TypeKind::KeyOf(obj)),
    value: store.intern_type(TypeKind::IndexedAccess {
      obj,
      index: store.intern_type(TypeKind::TypeParam(param)),
    }),
    readonly: MappedModifier::Add,
    optional: MappedModifier::Preserve,
    name_type: None,
    as_type: None,
  }));

  let evaluated = store.evaluate(mapped);
  assert_eq!(
    store.display(evaluated).to_string(),
    "{ readonly value: number }"
  );
}

#[test]
fn eval_template_literal_distribution() {
  let store = TypeStore::new();
  let span_ty = store.union(vec![
    store.intern_type(TypeKind::StringLiteral(store.intern_name("x"))),
    store.intern_type(TypeKind::StringLiteral(store.intern_name("y"))),
  ]);
  let tpl = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "id-".to_string(),
    spans: vec![TemplateChunk {
      literal: "".to_string(),
      ty: span_ty,
    }],
  }));
  let evaluated = store.evaluate(tpl);
  assert_eq!(store.display(evaluated).to_string(), "\"id-x\" | \"id-y\"");
}

#[test]
fn mapped_type_from_lib_snippet_instantiates() {
  let alias = parse_type_alias("type Readonly<T> = { readonly [P in keyof T]: T[P] };");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  lowerer.register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]));
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  let t_param = lowerer.type_param_id("T").unwrap();

  let mut shape = Shape::new();
  let key = store.intern_name("value");
  shape.properties.push(Property {
    key: PropKey::String(key),
    data: PropData {
      ty: store.primitive_ids().number,
      optional: false,
      readonly: false,
      accessibility: None,
    },
  });
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let mut env = AHashMap::new();
  env.insert(t_param, obj);
  let mut evaluator = TypeEvaluator::new(store.as_ref());
  let evaluated = evaluator.eval_with_env(ty, &mut env);
  assert_eq!(
    store.display(evaluated).to_string(),
    "{ readonly value: number }"
  );
}
