use std::collections::HashMap;

use crate::check::relate_hooks;
use types_ts::FnParam;
use types_ts::FunctionType;
use types_ts::IndexSignature;
use types_ts::MemberVisibility;
use types_ts::ObjectType;
use types_ts::Property;
use types_ts::RelateCtx;
use types_ts::TypeExpander;
use types_ts::TypeId;
use types_ts::TypeKind;
use types_ts::TypeOptions;
use types_ts::TypeRefId;
use types_ts::TypeStore;

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
  pub visibility: MemberVisibility,
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
  pub visibility: MemberVisibility,
  pub is_static: bool,
}

/// Optional constructor declaration. The return type is always `this`.
#[derive(Debug, Clone)]
pub struct Constructor {
  pub params: Vec<MethodParam>,
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

/// Resulting types for a class declaration.
#[derive(Debug, Clone)]
pub struct ClassType {
  pub name: String,
  pub instance: TypeId,
  pub static_type: TypeId,
  pub instance_ref: TypeRefId,
  pub origin: u32,
  pub this_type: TypeId,
  pub super_instance: Option<TypeId>,
  pub super_static: Option<TypeId>,
}

/// Environment for constructing class types and relating them with nominal
/// visibility rules.
pub struct ClassEnv {
  store: TypeStore,
  ref_map: HashMap<TypeRefId, TypeId>,
  next_ref: u32,
  next_origin: u32,
}

impl std::fmt::Debug for ClassEnv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("ClassEnv")
      .field("ref_map_len", &self.ref_map.len())
      .field("next_ref", &self.next_ref)
      .field("next_origin", &self.next_origin)
      .finish()
  }
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
      next_ref: 0,
      next_origin: 1,
    }
  }

  /// Access the underlying type store.
  pub fn store(&self) -> &TypeStore {
    &self.store
  }

  /// Mutable access to the underlying type store.
  pub fn store_mut(&mut self) -> &mut TypeStore {
    &mut self.store
  }

  /// Build a relation context that understands class `TypeRefId` expansion and
  /// private/protected nominal compatibility.
  pub fn relate_ctx(&self, options: TypeOptions) -> RelateCtx<'_> {
    let hooks = relate_hooks::class_hooks(self);
    RelateCtx::with_hooks(&self.store, options, hooks)
  }

  fn alloc_ref(&mut self) -> TypeRefId {
    let id = TypeRefId(self.next_ref);
    self.next_ref += 1;
    id
  }

  fn alloc_origin(&mut self) -> u32 {
    let id = self.next_origin;
    self.next_origin += 1;
    id
  }

  fn register_ref(&mut self, id: TypeRefId, ty: TypeId) {
    self.ref_map.insert(id, ty);
  }

  fn resolve_type(&mut self, expr: &TypeExpr, this_ref: TypeRefId) -> TypeId {
    match expr {
      TypeExpr::Type(id) => *id,
      TypeExpr::This => self.store.type_ref(this_ref),
    }
  }

  /// Construct instance and static types for a class declaration, handling
  /// inheritance and implicit `this` typing.
  pub fn build_class(&mut self, decl: ClassDecl) -> ClassType {
    let origin = self.alloc_origin();
    let instance_ref = self.alloc_ref();
    let mut instance_props: Vec<Property> = Vec::new();
    let mut static_props: Vec<Property> = Vec::new();
    let mut instance_indexes: Vec<IndexSignature> = Vec::new();
    let mut static_indexes: Vec<IndexSignature> = Vec::new();

    let super_instance = decl.extends.as_ref().map(|b| b.instance);
    let super_static = decl.extends.as_ref().map(|b| b.static_type);
    if let Some(base) = &decl.extends {
      if let TypeKind::Object(obj) = self.store.get(base.instance) {
        instance_props.extend(obj.properties.clone());
        instance_indexes.extend(obj.index_signatures.clone());
      }
      if let TypeKind::Object(obj) = self.store.get(base.static_type) {
        static_props.extend(obj.properties.clone());
        static_indexes.extend(obj.index_signatures.clone());
      }
    }

    for field in decl.fields {
      let target = if field.is_static {
        &mut static_props
      } else {
        &mut instance_props
      };
      let ty = self.resolve_type(&field.ty, instance_ref);
      let prop = Property {
        name: field.name,
        ty,
        optional: field.optional,
        readonly: field.readonly,
        is_method: false,
        visibility: field.visibility,
        origin_id: member_origin(field.visibility, origin),
      };
      upsert_property(target, prop);
    }

    for method in decl.methods {
      let target = if method.is_static {
        &mut static_props
      } else {
        &mut instance_props
      };
      let this_type = method
        .this_type
        .or_else(|| (!method.is_static).then_some(TypeExpr::This))
        .map(|ty| self.resolve_type(&ty, instance_ref));
      let params: Vec<FnParam> = method
        .params
        .into_iter()
        .map(|p| FnParam {
          name: p.name,
          ty: self.resolve_type(&p.ty, instance_ref),
          optional: p.optional,
          rest: p.rest,
        })
        .collect();
      let ret = self.resolve_type(&method.ret, instance_ref);
      let fn_type = self.store.function(FunctionType {
        params,
        ret,
        is_method: !method.is_static,
        this_param: this_type,
      });
      let prop = Property {
        name: method.name,
        ty: fn_type,
        optional: false,
        readonly: true,
        is_method: true,
        visibility: method.visibility,
        origin_id: member_origin(method.visibility, origin),
      };
      upsert_property(target, prop);
    }

    if let Some(cons) = decl.constructor {
      let params: Vec<FnParam> = cons
        .params
        .into_iter()
        .map(|p| FnParam {
          name: p.name,
          ty: self.resolve_type(&p.ty, instance_ref),
          optional: p.optional,
          rest: p.rest,
        })
        .collect();
      let ctor_ret = self.store.type_ref(instance_ref);
      let ctor = self.store.function(FunctionType {
        params,
        ret: ctor_ret,
        is_method: false,
        this_param: None,
      });
      let prop = Property {
        name: "constructor".to_string(),
        ty: ctor,
        optional: false,
        readonly: true,
        is_method: true,
        visibility: MemberVisibility::Public,
        origin_id: None,
      };
      upsert_property(&mut static_props, prop);
    }

    let instance_ty = self.store.object(ObjectType::new(instance_props, instance_indexes));
    let this_type = self.store.type_ref(instance_ref);
    self.register_ref(instance_ref, instance_ty);
    let static_ty = self.store.object(ObjectType::new(static_props, static_indexes));

    ClassType {
      name: decl.name,
      instance: instance_ty,
      static_type: static_ty,
      instance_ref,
      origin,
      this_type,
      super_instance,
      super_static,
    }
  }
}

impl TypeExpander for ClassEnv {
  fn expand_ref(&self, _store: &TypeStore, reference: TypeRefId) -> Option<TypeId> {
    self.ref_map.get(&reference).copied()
  }
}

fn member_origin(visibility: MemberVisibility, origin: u32) -> Option<u32> {
  match visibility {
    MemberVisibility::Public => None,
    MemberVisibility::Private | MemberVisibility::Protected => Some(origin),
  }
}

fn upsert_property(target: &mut Vec<Property>, prop: Property) {
  if let Some(idx) = target.iter().position(|p| p.name == prop.name) {
    target[idx] = prop;
  } else {
    target.push(prop);
  }
}
