use ahash::AHashMap;
use hir_js::{lower_from_source, DefKind, DefTypeInfo};
use ordered_float::OrderedFloat;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::TypeAliasDecl;
use parse_js::parse;
use std::collections::HashMap;
use std::sync::Arc;
use typecheck_ts::check::decls::HirDeclLowerer;
use typecheck_ts::check::type_expr::{LoweredPredicate, TypeLowerer, TypeResolver};
use typecheck_ts::Diagnostic;
use types_ts_interned::{
  DefId, ExpandedType, MappedModifier, MappedType, ObjectType, PropData, PropKey, Property, Shape,
  TemplateChunk, TemplateLiteralType, TypeEvaluator, TypeExpander, TypeId, TypeKind, TypeParamId,
  TypeStore,
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

fn parse_type_alias_named(source: &str, name: &str) -> Node<TypeAliasDecl> {
  let ast = parse(source).expect("parse failed");
  for stmt in ast.stx.body.into_iter() {
    if let Stmt::TypeAliasDecl(alias) = *stmt.stx {
      if alias.stx.name == name {
        return alias;
      }
    }
  }
  panic!("no type alias named {}", name);
}

#[derive(Default)]
struct MockResolver {
  symbols: AHashMap<String, DefId>,
  imports: AHashMap<(String, Option<Vec<String>>), DefId>,
}

impl MockResolver {
  fn with_symbol(mut self, name: impl Into<String>, def: DefId) -> Self {
    self.symbols.insert(name.into(), def);
    self
  }

  fn with_import(
    mut self,
    module: impl Into<String>,
    qualifier: Option<Vec<String>>,
    def: DefId,
  ) -> Self {
    self.imports.insert((module.into(), qualifier), def);
    self
  }
}

impl TypeResolver for MockResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    self.symbols.get(&path.join(".")).copied()
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<DefId> {
    self.resolve_type_name(path)
  }

  fn resolve_import_type(&self, module: &str, qualifier: Option<&[String]>) -> Option<DefId> {
    let key = (module.to_string(), qualifier.map(|q| q.to_vec()));
    self.imports.get(&key).copied()
  }
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
fn eval_keyof_union_collects_member_keys() {
  let alias = parse_type_alias("type K = keyof ({ a: number } | { b: string } | { c: boolean });");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  let evaluated = store.evaluate(ty);
  let mut names: Vec<_> = match store.type_kind(evaluated) {
    TypeKind::Union(members) => members
      .into_iter()
      .map(|m| match store.type_kind(m) {
        TypeKind::StringLiteral(id) => store.name(id),
        other => panic!("unexpected member {:?}", other),
      })
      .collect(),
    TypeKind::StringLiteral(id) => vec![store.name(id)],
    other => panic!("unexpected kind {:?}", other),
  };
  names.sort();
  assert_eq!(
    names,
    vec!["a".to_string(), "b".to_string(), "c".to_string()]
  );
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
fn indexed_access_over_union_distributes() {
  let store = TypeStore::new();
  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");

  let left_shape = store.intern_shape(Shape {
    properties: vec![Property {
      key: PropKey::String(name_a),
      data: PropData {
        ty: store.primitive_ids().string,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    }],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });
  let right_shape = store.intern_shape(Shape {
    properties: vec![Property {
      key: PropKey::String(name_b),
      data: PropData {
        ty: store.primitive_ids().number,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    }],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });

  let left = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: left_shape }),
  ));
  let right = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: right_shape }),
  ));
  let union = store.union(vec![left, right]);
  let index = store.intern_type(TypeKind::KeyOf(union));
  let indexed = store.intern_type(TypeKind::IndexedAccess { obj: union, index });
  let evaluated = store.evaluate(indexed);
  let members = match store.type_kind(evaluated) {
    TypeKind::Union(members) => members,
    other => vec![store.intern_type(other)],
  };

  let mut kinds: Vec<_> = members.into_iter().map(|m| store.type_kind(m)).collect();
  kinds.sort_by_key(|k| format!("{:?}", k));
  assert!(kinds.contains(&TypeKind::String));
  assert!(kinds.contains(&TypeKind::Number));
  assert_eq!(kinds.len(), 2);
}

#[test]
fn lowers_this_type() {
  let alias = parse_type_alias("type Self = this;");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  assert!(matches!(store.type_kind(ty), TypeKind::This));
}

#[test]
fn captures_type_predicate_details() {
  let alias = parse_type_alias("type Pred = (value: unknown) => value is string;");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  let TypeKind::Callable { overloads } = store.type_kind(ty) else {
    panic!("expected callable, got {:?}", store.type_kind(ty));
  };
  let sig = store.signature(overloads[0]);
  assert!(matches!(store.type_kind(sig.ret), TypeKind::Boolean));

  let preds: Vec<LoweredPredicate> = lowerer.predicates().to_vec();
  assert_eq!(preds.len(), 1);
  let pred = &preds[0];
  assert_eq!(pred.parameter, "value");
  assert!(!pred.asserts);
  let pred_ty = pred.ty.expect("predicate type");
  assert!(matches!(store.type_kind(pred_ty), TypeKind::String));
}

#[test]
fn lowers_infer_type_binding() {
  let alias =
    parse_type_alias("type Inferred<T> = T extends infer U extends string ? U[] : never;");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  lowerer.register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]));
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);

  let TypeKind::Conditional {
    extends, true_ty, ..
  } = store.type_kind(ty)
  else {
    panic!("expected conditional, got {:?}", store.type_kind(ty));
  };

  let inferred_id = match store.type_kind(extends) {
    TypeKind::Infer { param, constraint } => {
      let Some(bound) = constraint else {
        panic!("expected constraint")
      };
      assert!(matches!(store.type_kind(bound), TypeKind::String));
      param
    }
    other => panic!("expected infer, got {:?}", other),
  };

  let inner = match store.type_kind(true_ty) {
    TypeKind::Array { ty, .. } => ty,
    other => panic!("expected array, got {:?}", other),
  };
  assert_eq!(store.type_kind(inner), TypeKind::TypeParam(inferred_id));
}

#[test]
fn lowers_distributive_conditional_for_naked_param() {
  let alias = parse_type_alias("type Result<T> = T extends string ? true : false;");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  lowerer.register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]));
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  let TypeKind::Conditional { distributive, .. } = store.type_kind(ty) else {
    panic!("expected conditional");
  };
  assert!(distributive);
}

#[test]
fn resolves_type_reference_with_args() {
  let alias = parse_type_alias("type Value = Box<string>;");
  let store = TypeStore::new();
  let resolver = Arc::new(MockResolver::default().with_symbol("Box", DefId(42)));
  let mut lowerer = TypeLowerer::with_resolver(store.clone(), resolver);
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  match store.type_kind(ty) {
    TypeKind::Ref { def, args } => {
      assert_eq!(def, DefId(42));
      assert_eq!(args, vec![store.primitive_ids().string]);
    }
    other => panic!("expected ref, got {:?}", other),
  }
}

#[test]
fn resolves_type_query() {
  let alias = parse_type_alias("type Value = typeof foo;");
  let store = TypeStore::new();
  let resolver = Arc::new(MockResolver::default().with_symbol("foo", DefId(7)));
  let mut lowerer = TypeLowerer::with_resolver(store.clone(), resolver);
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  match store.type_kind(ty) {
    TypeKind::Ref { def, .. } => assert_eq!(def, DefId(7)),
    other => panic!("expected ref, got {:?}", other),
  }
}

#[test]
fn resolves_import_type_with_qualifier() {
  let alias = parse_type_alias(r#"type Value = import("./pkg").Thing<number>;"#);
  let store = TypeStore::new();
  let resolver =
    Arc::new(MockResolver::default().with_import("./pkg", Some(vec!["Thing".into()]), DefId(99)));
  let mut lowerer = TypeLowerer::with_resolver(store.clone(), resolver);
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  assert!(
    lowerer.diagnostics().is_empty(),
    "unexpected diagnostics: {:?}",
    lowerer.diagnostics()
  );
  match store.type_kind(ty) {
    TypeKind::Ref { def, args } => {
      assert_eq!(def, DefId(99));
      assert_eq!(args, vec![store.primitive_ids().number]);
    }
    other => panic!("expected ref, got {:?}", other),
  }
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
      is_method: false,
      origin: None,
      declared_on: None,
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
fn mapped_type_as_clause_is_preserved() {
  let alias = parse_type_alias("type Remap<T> = { [K in keyof T as `${K}_done`]: T[K] };");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  lowerer.register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]));
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  let TypeKind::Mapped(mapped) = store.type_kind(ty) else {
    panic!("expected mapped type, got {:?}", store.type_kind(ty));
  };
  let Some(as_type) = mapped.as_type else {
    panic!("expected as_type to be set");
  };
  assert!(matches!(
    store.type_kind(as_type),
    TypeKind::TemplateLiteral(_)
  ));
}

#[test]
fn mapped_type_over_literal_union_preserves_keys() {
  let alias = parse_type_alias(r#"type Keys = { [K in "a" | "b"]: number };"#);
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);
  assert_eq!(
    store.display(ty).to_string(),
    "{ [K in \"a\" | \"b\"]: number }"
  );
}

#[test]
fn hir_decl_lowering_preserves_mapped_as_clause() {
  let source = "type M<T> = { [K in keyof T as `${K & string}Changed`]: T[K] };";
  let lowered = lower_from_source(source).expect("lowering should succeed");
  let alias = lowered
    .defs
    .iter()
    .find(|def| matches!(def.type_info, Some(DefTypeInfo::TypeAlias { .. })))
    .expect("type alias");

  let store = TypeStore::new();
  let mut diagnostics: Vec<Diagnostic> = Vec::new();
  let mut lowerer = HirDeclLowerer::new(
    store.clone(),
    &lowered.types,
    None,
    HashMap::new(),
    alias.path.module,
    None,
    HashMap::new(),
    &mut diagnostics,
    None,
    None,
    None,
    None,
    None,
  );
  let (ty, _) =
    lowerer.lower_type_info(alias.id, alias.type_info.as_ref().unwrap(), &lowered.names);

  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );

  let TypeKind::Mapped(mapped) = store.type_kind(ty) else {
    panic!("expected mapped type, got {:?}", store.type_kind(ty));
  };
  let Some(as_type) = mapped.as_type else {
    panic!("expected as_type to be populated");
  };
  match store.type_kind(as_type) {
    TypeKind::TemplateLiteral(_) => {}
    other => panic!("expected template literal as_type, got {:?}", other),
  }
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
      is_method: false,
      origin: None,
      declared_on: None,
    },
  });
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let mut env = AHashMap::new();
  env.insert(t_param, obj);

  #[derive(Default)]
  struct NoopExpander;

  impl TypeExpander for NoopExpander {
    fn expand(&self, _store: &TypeStore, _def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
      None
    }
  }

  let expander = NoopExpander::default();
  let mut evaluator = TypeEvaluator::new(store.clone(), &expander);
  let evaluated = evaluator.evaluate_with_bindings(ty, env.iter().map(|(k, v)| (*k, *v)));
  assert_eq!(
    store.display(evaluated).to_string(),
    "{ readonly value: number }"
  );
}

#[test]
fn hir_alias_reference_expands_through_evaluator() {
  let source = r#"
    type Box<T> = T[];
    type Value = Box<string>;
  "#;
  let lowered = lower_from_source(source).expect("lowering should succeed");
  let box_def = lowered
    .defs
    .iter()
    .find(|def| {
      def.path.kind == DefKind::TypeAlias
        && lowered.names.resolve(def.path.name).as_deref() == Some("Box")
    })
    .unwrap()
    .id;

  let box_alias = parse_type_alias_named(source, "Box");
  let value_alias = parse_type_alias_named(source, "Value");
  let store = TypeStore::new();

  let mut box_lowerer = TypeLowerer::new(store.clone());
  let box_params =
    box_lowerer.register_type_params(box_alias.stx.type_parameters.as_deref().unwrap_or(&[]));
  let box_param_ids: Vec<_> = box_params.iter().map(|p| p.id).collect();
  let box_body = box_lowerer.lower_type_expr(&box_alias.stx.type_expr);

  let resolver = Arc::new(MockResolver::default().with_symbol("Box", box_def));
  let mut value_lowerer = TypeLowerer::with_resolver(store.clone(), resolver);
  let value_ty = value_lowerer.lower_type_expr(&value_alias.stx.type_expr);
  let TypeKind::Ref { def, args } = store.type_kind(value_ty) else {
    panic!("expected ref, got {:?}", store.type_kind(value_ty));
  };
  assert_eq!(def, box_def);
  assert_eq!(args, vec![store.primitive_ids().string]);

  struct MapExpander {
    map: AHashMap<DefId, ExpandedType>,
  }

  impl TypeExpander for MapExpander {
    fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
      self.map.get(&def).cloned()
    }
  }

  let expander = MapExpander {
    map: AHashMap::from([(
      box_def,
      ExpandedType {
        params: box_param_ids,
        ty: box_body,
      },
    )]),
  };
  let mut evaluator = TypeEvaluator::new(store.clone(), &expander);
  let expanded = evaluator.evaluate(value_ty);
  assert_eq!(store.display(expanded).to_string(), "string[]");
}

#[test]
fn method_type_params_do_not_leak_and_preserve_outer_bindings() {
  let alias = parse_type_alias("type Outer<T> = { method<U>(x: T, y: U): T };");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let outer_t = lowerer
    .register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]))
    .first()
    .expect("outer type param")
    .id;
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);

  let TypeKind::Object(obj) = store.type_kind(ty) else {
    panic!("expected object, got {:?}", store.type_kind(ty));
  };
  let shape = store.shape(store.object(obj).shape);
  let method = shape
    .properties
    .iter()
    .find(|prop| matches!(prop.key, PropKey::String(name) if store.name(name) == "method"))
    .expect("method property");
  let TypeKind::Callable { overloads } = store.type_kind(method.data.ty) else {
    panic!(
      "expected callable method, got {:?}",
      store.type_kind(method.data.ty)
    );
  };
  assert_eq!(overloads.len(), 1);
  let sig = store.signature(overloads[0]);

  assert_eq!(sig.type_params.len(), 1);
  let inner_u = sig.type_params[0].id;
  assert_ne!(inner_u, outer_t);

  let first_param = sig.params.first().expect("first param");
  assert_eq!(
    store.type_kind(first_param.ty),
    TypeKind::TypeParam(outer_t)
  );

  let second_param = sig.params.get(1).expect("second param");
  assert_eq!(
    store.type_kind(second_param.ty),
    TypeKind::TypeParam(inner_u)
  );

  assert_eq!(store.type_kind(sig.ret), TypeKind::TypeParam(outer_t));
}

#[test]
fn nested_function_type_params_shadow_outer() {
  let alias = parse_type_alias("type X<T> = (fn: <T>(arg: T) => T) => T;");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let outer_t = lowerer
    .register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]))
    .first()
    .expect("outer type param")
    .id;
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);

  let TypeKind::Callable { overloads } = store.type_kind(ty) else {
    panic!("expected callable, got {:?}", store.type_kind(ty));
  };
  let outer_sig = store.signature(overloads[0]);
  assert_eq!(store.type_kind(outer_sig.ret), TypeKind::TypeParam(outer_t));

  let param_ty = outer_sig.params.first().expect("fn param").ty;
  let TypeKind::Callable {
    overloads: inner_overloads,
  } = store.type_kind(param_ty)
  else {
    panic!(
      "expected callable param, got {:?}",
      store.type_kind(param_ty)
    );
  };
  let inner_sig = store.signature(inner_overloads[0]);
  assert_eq!(inner_sig.type_params.len(), 1);
  let inner_t = inner_sig.type_params[0].id;
  assert_ne!(inner_t, outer_t);
  let inner_param_ty = inner_sig.params.first().expect("inner param").ty;
  assert_eq!(
    store.type_kind(inner_param_ty),
    TypeKind::TypeParam(inner_t)
  );
  assert_eq!(store.type_kind(inner_sig.ret), TypeKind::TypeParam(inner_t));
}

#[test]
fn infer_type_params_are_scoped_to_conditional_types() {
  let alias = parse_type_alias("type C<T> = T extends infer U ? U : never;");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let outer_t = lowerer
    .register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]))
    .first()
    .expect("outer type param")
    .id;
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);

  let TypeKind::Conditional {
    extends,
    true_ty,
    false_ty,
    ..
  } = store.type_kind(ty)
  else {
    panic!("expected conditional type");
  };

  let infer_param = match store.type_kind(extends) {
    TypeKind::Infer { param, constraint } => {
      assert!(constraint.is_none());
      param
    }
    other => panic!("expected infer, got {:?}", other),
  };
  assert_eq!(store.type_kind(true_ty), TypeKind::TypeParam(infer_param));
  assert_eq!(store.type_kind(false_ty), TypeKind::Never);

  assert_eq!(lowerer.type_param_id("T"), Some(outer_t));
  assert_eq!(lowerer.type_param_id("U"), None);
}

#[test]
fn infer_type_params_shadow_outer_and_arent_visible_in_false_branch() {
  let alias = parse_type_alias("type S<T> = T extends infer T ? T : T;");
  let store = TypeStore::new();
  let mut lowerer = TypeLowerer::new(store.clone());
  let outer_t = lowerer
    .register_type_params(alias.stx.type_parameters.as_deref().unwrap_or(&[]))
    .first()
    .expect("outer type param")
    .id;
  let ty = lowerer.lower_type_expr(&alias.stx.type_expr);

  let TypeKind::Conditional {
    extends,
    true_ty,
    false_ty,
    ..
  } = store.type_kind(ty)
  else {
    panic!("expected conditional type");
  };

  let infer_param = match store.type_kind(extends) {
    TypeKind::Infer { param, .. } => param,
    other => panic!("expected infer in extends, got {:?}", other),
  };
  assert_ne!(infer_param, outer_t);
  assert_eq!(store.type_kind(true_ty), TypeKind::TypeParam(infer_param));
  assert_eq!(store.type_kind(false_ty), TypeKind::TypeParam(outer_t));
}
