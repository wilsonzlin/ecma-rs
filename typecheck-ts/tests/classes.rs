use typecheck_ts::check::class::*;
use types_ts_interned::{Accessibility, PropKey, TypeKind};

fn number_type(env: &ClassEnv) -> types_ts_interned::TypeId {
  env.store().primitive_ids().number
}

#[test]
fn private_classes_are_nominal() {
  let mut env = ClassEnv::new();
  let num = number_type(&env);
  let field = Field {
    name: "value".to_string(),
    ty: num.into(),
    optional: false,
    readonly: false,
    visibility: Accessibility::Private,
    is_static: false,
  };

  let class_a = env.build_class(ClassDecl {
    name: "A".into(),
    extends: None,
    fields: vec![field.clone()],
    methods: Vec::new(),
    constructor: None,
  });
  let class_b = env.build_class(ClassDecl {
    name: "B".into(),
    extends: None,
    fields: vec![field],
    methods: Vec::new(),
    constructor: None,
  });

  let ctx = env.relate_ctx(types_ts_interned::TypeOptions::default());
  assert!(!ctx.is_assignable(class_a.instance, class_b.instance));
  assert!(!ctx.is_assignable(class_b.instance, class_a.instance));
}

#[test]
fn protected_members_allow_inheritance_compatibility() {
  let mut env = ClassEnv::new();
  let num = number_type(&env);
  let protected = Field {
    name: "id".to_string(),
    ty: num.into(),
    optional: false,
    readonly: false,
    visibility: Accessibility::Protected,
    is_static: false,
  };

  let base = env.build_class(ClassDecl {
    name: "Base".into(),
    extends: None,
    fields: vec![protected.clone()],
    methods: Vec::new(),
    constructor: None,
  });
  let derived = env.build_class(ClassDecl {
    name: "Derived".into(),
    extends: Some(base.clone()),
    fields: Vec::new(),
    methods: Vec::new(),
    constructor: None,
  });
  assert_eq!(derived.super_instance, Some(base.instance));
  assert_eq!(derived.super_static, Some(base.static_type));
  let sibling = env.build_class(ClassDecl {
    name: "Sibling".into(),
    extends: Some(base.clone()),
    fields: Vec::new(),
    methods: Vec::new(),
    constructor: None,
  });

  let ctx = env.relate_ctx(types_ts_interned::TypeOptions::default());

  assert!(ctx.is_assignable(derived.instance, base.instance));
  assert!(ctx.is_assignable(base.instance, derived.instance));
  assert!(ctx.is_assignable(derived.instance, sibling.instance));
  assert!(ctx.is_assignable(sibling.instance, derived.instance));
}

#[test]
fn methods_capture_implicit_this_type() {
  let mut env = ClassEnv::new();
  let method = Method {
    name: "self".to_string(),
    params: Vec::new(),
    ret: TypeExpr::This,
    this_type: None,
    visibility: Accessibility::Public,
    is_static: false,
  };

  let class = env.build_class(ClassDecl {
    name: "Selfish".into(),
    extends: None,
    fields: Vec::new(),
    methods: vec![method],
    constructor: None,
  });

  let store = env.store();
  let method_ty = match store.type_kind(class.instance) {
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      let prop = shape
        .properties
        .iter()
        .find(|p| matches!(p.key, PropKey::String(id) if store.name(id) == "self"))
        .expect("method present");
      store.type_kind(prop.data.ty)
    }
    other => panic!("expected object type, got {other:?}"),
  };

  match method_ty {
    TypeKind::Callable { overloads } => {
      let sig = store.signature(*overloads.first().expect("signature present"));
      assert_eq!(sig.this_param, Some(class.this_type));
      assert_eq!(sig.ret, class.this_type);
    }
    other => panic!("expected function type, got {other:?}"),
  }
}
