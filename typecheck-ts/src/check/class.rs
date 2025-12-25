use std::collections::HashMap;
use std::sync::Arc;

use types_ts_interned::{
  Accessibility, DefId, Param, PropData, PropKey, Property, RelateCtx, RelateTypeExpander,
  Signature, TypeId, TypeKind, TypeOptions, TypeStore,
};

/// Placeholder type expression used when constructing class members.
#[derive(Debug, Clone)]
pub enum TypeExpr {
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
pub struct Field {
  pub name: String,
  pub ty: TypeExpr,
  pub optional: bool,
  pub readonly: bool,
  pub visibility: Accessibility,
  pub is_static: bool,
}

/// Declaration of a method parameter.
#[derive(Debug, Clone)]
pub struct MethodParam {
  pub name: Option<String>,
  pub ty: TypeExpr,
  pub optional: bool,
  pub rest: bool,
}

/// Declaration of a single method.
#[derive(Debug, Clone)]
pub struct Method {
  pub name: String,
  pub params: Vec<MethodParam>,
  pub ret: TypeExpr,
  pub this_type: Option<TypeExpr>,
  pub visibility: Accessibility,
  pub is_static: bool,
}

/// Optional constructor declaration. The return type is always `this`.
#[derive(Debug, Clone)]
pub struct Constructor {
  pub params: Vec<MethodParam>,
}

/// Resulting types for a class declaration.
#[derive(Debug, Clone)]
pub struct ClassType {
  pub name: String,
  pub instance: TypeId,
  pub static_type: TypeId,
  pub instance_def: DefId,
  pub origin: DefId,
  pub this_type: TypeId,
  pub super_instance: Option<TypeId>,
  pub super_static: Option<TypeId>,
}

/// High-level declaration used to build a class type pair.
#[derive(Debug, Clone)]
pub struct ClassDecl {
  pub name: String,
  pub extends: Option<ClassType>,
  pub fields: Vec<Field>,
  pub methods: Vec<Method>,
  pub constructor: Option<Constructor>,
}

impl ClassDecl {
  pub fn new(name: impl Into<String>) -> Self {
    Self {
      name: name.into(),
      extends: None,
      fields: Vec::new(),
      methods: Vec::new(),
      constructor: None,
    }
  }
}

/// Environment for constructing class types and relating them with nominal
/// visibility rules.
#[derive(Debug)]
pub struct ClassEnv {
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
  pub fn new() -> Self {
    Self {
      store: TypeStore::new(),
      ref_map: HashMap::new(),
      next_def: 0,
      next_origin: 1,
    }
  }

  /// Access the underlying type store.
  pub fn store(&self) -> &Arc<TypeStore> {
    &self.store
  }

  /// Mutable access to the underlying type store.
  pub fn store_mut(&mut self) -> &mut Arc<TypeStore> {
    &mut self.store
  }

  /// Build a relation context that understands class `TypeKind::Ref` expansion and
  /// private/protected nominal compatibility.
  pub fn relate_ctx(&self, options: TypeOptions) -> RelateCtx<'_> {
    let hooks = super::relate_hooks::class_hooks(self);
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
  pub fn build_class(&mut self, decl: ClassDecl) -> ClassType {
    let origin = self.alloc_origin();
    let instance_def = self.alloc_def();
    let mut instance_shape_props: Vec<Property> = Vec::new();
    let mut static_shape_props: Vec<Property> = Vec::new();
    let mut instance_indexers = Vec::new();
    let mut static_indexers = Vec::new();

    let super_instance = decl.extends.as_ref().map(|b| b.instance);
    let super_static = decl.extends.as_ref().map(|b| b.static_type);
    if let Some(base) = &decl.extends {
      if let TypeKind::Object(obj) = self.store.type_kind(base.instance) {
        let shape = self.store.shape(self.store.object(obj).shape);
        instance_shape_props.extend(shape.properties.clone());
        instance_indexers.extend(shape.indexers.clone());
      }
      if let TypeKind::Object(obj) = self.store.type_kind(base.static_type) {
        let shape = self.store.shape(self.store.object(obj).shape);
        static_shape_props.extend(shape.properties.clone());
        static_indexers.extend(shape.indexers.clone());
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
      let ctor = self.store.intern_type(TypeKind::Callable {
        overloads: vec![self.store.intern_signature(ctor_sig)],
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
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
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
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
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
