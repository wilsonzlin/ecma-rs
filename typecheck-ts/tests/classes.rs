use std::collections::HashMap;
use std::sync::Arc;

use types_ts_interned::{
  Accessibility, DefId, Param, PropData, PropKey, Property, RelateCtx, RelateHooks,
  RelateTypeExpander, Signature, TypeId, TypeKind, TypeOptions, TypeStore,
};

/// Placeholder type expression used when constructing class members.
#[derive(Debug, Clone)]
enum TypeExpr {
  /// Concrete, already-resolved type ID.
  Type(TypeId),
  /// The implicit `this` type of the class.
  This,
}

impl From<TypeId> for TypeExpr {
  fn from(value: TypeId) -> Self {
    TypeExpr::Type(value)
  }
}

/// Declaration of a single class field.
#[derive(Debug, Clone)]
struct Field {
  name: String,
  ty: TypeExpr,
  optional: bool,
  readonly: bool,
  visibility: Accessibility,
  is_static: bool,
}

/// Declaration of a method parameter.
#[derive(Debug, Clone)]
struct MethodParam {
  name: Option<String>,
  ty: TypeExpr,
  optional: bool,
  rest: bool,
}

/// Declaration of a single method.
#[derive(Debug, Clone)]
struct Method {
  name: String,
  params: Vec<MethodParam>,
  ret: TypeExpr,
  this_type: Option<TypeExpr>,
  visibility: Accessibility,
  is_static: bool,
}

/// Optional constructor declaration. The return type is always `this`.
#[derive(Debug, Clone)]
struct Constructor {
  params: Vec<MethodParam>,
}

/// Resulting types for a class declaration.
#[derive(Debug, Clone)]
struct ClassType {
  name: String,
  instance: TypeId,
  static_type: TypeId,
  instance_def: DefId,
  origin: DefId,
  this_type: TypeId,
  super_instance: Option<TypeId>,
  super_static: Option<TypeId>,
}

/// High-level declaration used to build a class type pair.
#[derive(Debug, Clone)]
struct ClassDecl {
  name: String,
  extends: Option<ClassType>,
  fields: Vec<Field>,
  methods: Vec<Method>,
  constructor: Option<Constructor>,
}

impl ClassDecl {
  fn new(name: impl Into<String>) -> Self {
    Self {
      name: name.into(),
      extends: None,
      fields: Vec::new(),
      methods: Vec::new(),
      constructor: None,
    }
  }
}

/// Environment for constructing class types and relating them with nominal visibility rules.
#[derive(Debug)]
struct ClassEnv {
  store: Arc<TypeStore>,
  ref_map: HashMap<DefId, TypeId>,
  next_def: u32,
  next_origin: u32,
}

impl Default for ClassEnv {
  fn default() -> Self {
    Self::new()
  }
}

impl ClassEnv {
  fn new() -> Self {
    Self {
      store: TypeStore::new(),
      ref_map: HashMap::new(),
      next_def: 0,
      next_origin: 1,
    }
  }

  /// Access the underlying type store.
  fn store(&self) -> &Arc<TypeStore> {
    &self.store
  }

  /// Build a relation context that understands class `TypeKind::Ref` expansion and
  /// private/protected nominal compatibility.
  fn relate_ctx(&self, options: TypeOptions) -> RelateCtx<'_> {
    let hooks = class_hooks(self);
    RelateCtx::with_hooks(Arc::clone(&self.store), options, hooks)
  }

  fn alloc_def(&mut self) -> DefId {
    let id = DefId(self.next_def);
    self.next_def += 1;
    id
  }

  fn alloc_origin(&mut self) -> DefId {
    let id = DefId(self.next_origin);
    self.next_origin += 1;
    id
  }

  fn register_ref(&mut self, id: DefId, ty: TypeId) {
    self.ref_map.insert(id, ty);
  }

  fn resolve_type(&self, expr: &TypeExpr, this_ref: DefId) -> TypeId {
    match expr {
      TypeExpr::Type(id) => *id,
      TypeExpr::This => self.store.intern_type(TypeKind::Ref {
        def: this_ref,
        args: Vec::new(),
      }),
    }
  }

  /// Construct instance and static types for a class declaration, handling
  /// inheritance and implicit `this` typing.
  fn build_class(&mut self, decl: ClassDecl) -> ClassType {
    let origin = self.alloc_origin();
    let instance_def = self.alloc_def();
    let mut instance_shape_props: Vec<Property> = Vec::new();
    let mut static_shape_props: Vec<Property> = Vec::new();
    let mut instance_indexers = Vec::new();
    let mut instance_call_sigs = Vec::new();
    let mut instance_construct_sigs = Vec::new();
    let mut static_indexers = Vec::new();
    let mut static_call_sigs = Vec::new();
    let mut static_construct_sigs = Vec::new();

    let super_instance = decl.extends.as_ref().map(|b| b.instance);
    let super_static = decl.extends.as_ref().map(|b| b.static_type);
    if let Some(base) = &decl.extends {
      if let TypeKind::Object(obj) = self.store.type_kind(base.instance) {
        let shape = self.store.shape(self.store.object(obj).shape);
        instance_shape_props.extend(shape.properties.clone());
        instance_indexers.extend(shape.indexers.clone());
        instance_call_sigs.extend(shape.call_signatures.clone());
        instance_construct_sigs.extend(shape.construct_signatures.clone());
      }
      if let TypeKind::Object(obj) = self.store.type_kind(base.static_type) {
        let shape = self.store.shape(self.store.object(obj).shape);
        static_shape_props.extend(shape.properties.clone());
        static_indexers.extend(shape.indexers.clone());
        static_call_sigs.extend(shape.call_signatures.clone());
        static_construct_sigs.extend(shape.construct_signatures.clone());
      }
    }

    for field in decl.fields {
      let target = if field.is_static {
        &mut static_shape_props
      } else {
        &mut instance_shape_props
      };
      let ty = self.resolve_type(&field.ty, instance_def);
      let prop = Property {
        key: PropKey::String(self.store.intern_name(field.name)),
        data: PropData {
          ty,
          optional: field.optional,
          readonly: field.readonly,
          accessibility: Some(field.visibility),
          is_method: false,
          origin: member_origin(field.visibility, origin).map(|id| id.0),
          declared_on: member_origin(field.visibility, origin),
        },
      };
      upsert_property(target, prop);
    }

    for method in decl.methods {
      let target = if method.is_static {
        &mut static_shape_props
      } else {
        &mut instance_shape_props
      };
      let this_type = method
        .this_type
        .or_else(|| (!method.is_static).then_some(TypeExpr::This))
        .map(|ty| self.resolve_type(&ty, instance_def));
      let params: Vec<Param> = method
        .params
        .into_iter()
        .map(|p| Param {
          name: p.name.map(|n| self.store.intern_name(n)),
          ty: self.resolve_type(&p.ty, instance_def),
          optional: p.optional,
          rest: p.rest,
        })
        .collect();
      let ret = self.resolve_type(&method.ret, instance_def);
      let sig = Signature {
        params,
        ret,
        type_params: Vec::new(),
        this_param: this_type,
      };
      let fn_type = self.store.intern_type(TypeKind::Callable {
        overloads: vec![self.store.intern_signature(sig)],
      });
      let prop = Property {
        key: PropKey::String(self.store.intern_name(method.name)),
        data: PropData {
          ty: fn_type,
          optional: false,
          readonly: true,
          accessibility: Some(method.visibility),
          is_method: true,
          origin: member_origin(method.visibility, origin).map(|id| id.0),
          declared_on: member_origin(method.visibility, origin),
        },
      };
      upsert_property(target, prop);
    }

    if let Some(cons) = decl.constructor {
      let params: Vec<Param> = cons
        .params
        .into_iter()
        .map(|p| Param {
          name: p.name.map(|n| self.store.intern_name(n)),
          ty: self.resolve_type(&p.ty, instance_def),
          optional: p.optional,
          rest: p.rest,
        })
        .collect();
      let ctor_sig = Signature {
        params,
        ret: self.store.intern_type(TypeKind::Ref {
          def: instance_def,
          args: Vec::new(),
        }),
        type_params: Vec::new(),
        this_param: None,
      };
      let ctor_sig_id = self.store.intern_signature(ctor_sig);
      static_construct_sigs.push(ctor_sig_id);
      let ctor = self.store.intern_type(TypeKind::Callable {
        overloads: vec![ctor_sig_id],
      });
      let prop = Property {
        key: PropKey::String(self.store.intern_name("constructor")),
        data: PropData {
          ty: ctor,
          optional: false,
          readonly: true,
          accessibility: Some(Accessibility::Public),
          is_method: true,
          origin: None,
          declared_on: None,
        },
      };
      upsert_property(&mut static_shape_props, prop);
    }

    let instance_shape = self.store.intern_shape(types_ts_interned::Shape {
      properties: instance_shape_props,
      call_signatures: instance_call_sigs,
      construct_signatures: instance_construct_sigs,
      indexers: instance_indexers,
    });
    let instance_ty = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(
        types_ts_interned::ObjectType {
          shape: instance_shape,
        },
      )));
    let this_type = self.store.intern_type(TypeKind::Ref {
      def: instance_def,
      args: Vec::new(),
    });
    self.register_ref(instance_def, instance_ty);

    let static_shape = self.store.intern_shape(types_ts_interned::Shape {
      properties: static_shape_props,
      call_signatures: static_call_sigs,
      construct_signatures: static_construct_sigs,
      indexers: static_indexers,
    });
    let static_ty = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(
        types_ts_interned::ObjectType {
          shape: static_shape,
        },
      )));

    ClassType {
      name: decl.name,
      instance: instance_ty,
      static_type: static_ty,
      instance_def,
      origin,
      this_type,
      super_instance,
      super_static,
    }
  }
}

impl RelateTypeExpander for ClassEnv {
  fn expand_ref(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<TypeId> {
    self.ref_map.get(&def).copied()
  }
}

fn class_hooks<'a>(expander: &'a dyn RelateTypeExpander) -> RelateHooks<'a> {
  RelateHooks {
    expander: Some(expander),
    is_same_origin_private_member: Some(&same_origin_private_member),
  }
}

fn same_origin_private_member(a: &Property, b: &Property) -> bool {
  matches!(
    (a.data.declared_on, b.data.declared_on),
    (Some(left), Some(right)) if left == right
  )
}

fn member_origin(visibility: Accessibility, origin: DefId) -> Option<DefId> {
  match visibility {
    Accessibility::Public => None,
    Accessibility::Private | Accessibility::Protected => Some(origin),
  }
}

fn upsert_property(target: &mut Vec<Property>, prop: Property) {
  if let Some(idx) = target.iter().position(|p| p.key == prop.key) {
    target[idx] = prop;
  } else {
    target.push(prop);
  }
}

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

#[test]
fn this_parameter_is_enforced_in_assignability() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let with_this = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(Signature {
      params: Vec::new(),
      ret: prim.number,
      type_params: Vec::new(),
      this_param: Some(prim.string),
    })],
  });
  let without_this = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(Signature {
      params: Vec::new(),
      ret: prim.number,
      type_params: Vec::new(),
      this_param: None,
    })],
  });
  let relate = RelateCtx::new(Arc::clone(&store), store.options());
  assert!(
    !relate.is_assignable(with_this, without_this),
    "missing this parameter should make signatures incompatible"
  );
  assert!(
    !relate.is_assignable(without_this, with_this),
    "adding this parameter should change assignability"
  );
}
