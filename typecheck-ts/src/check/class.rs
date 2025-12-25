use std::collections::HashMap;
use std::sync::Arc;

use crate::check::relate_hooks;
use types_ts_interned::{
  Accessibility, DefId, ExpandedType, ObjectType, Param, PropData, PropKey, Property, RelateCtx,
  RelateTypeExpander, Shape, Signature, TypeExpander, TypeId, TypeKind, TypeOptions, TypeStore,
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

/// Visibility of a class member.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemberVisibility {
  Public,
  Private,
  Protected,
}

impl MemberVisibility {
  fn accessibility(self) -> Option<Accessibility> {
    match self {
      MemberVisibility::Public => None,
      MemberVisibility::Private => Some(Accessibility::Private),
      MemberVisibility::Protected => Some(Accessibility::Protected),
    }
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
  pub def_id: DefId,
  pub origin: u32,
  pub this_type: TypeId,
  pub super_instance: Option<TypeId>,
  pub super_static: Option<TypeId>,
}

/// Environment for constructing class types and relating them with nominal
/// visibility rules.
pub struct ClassEnv {
  store: Arc<TypeStore>,
  ref_map: HashMap<DefId, TypeId>,
  next_def: u32,
  next_origin: u32,
}

impl std::fmt::Debug for ClassEnv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("ClassEnv")
      .field("ref_map_len", &self.ref_map.len())
      .field("next_def", &self.next_def)
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
      next_def: 0,
      next_origin: 1,
    }
  }

  /// Access the underlying type store.
  pub fn store(&self) -> &TypeStore {
    self.store.as_ref()
  }

  /// Shared handle to the underlying type store.
  pub fn store_arc(&self) -> Arc<TypeStore> {
    Arc::clone(&self.store)
  }

  /// Build a relation context that understands class `TypeKind::Ref` expansion and
  /// private/protected nominal compatibility.
  pub fn relate_ctx(&self, options: TypeOptions) -> RelateCtx<'_> {
    let hooks = relate_hooks::class_hooks(self);
    RelateCtx::with_hooks(self.store_arc(), options, hooks)
  }

  fn alloc_def(&mut self) -> DefId {
    let id = DefId(self.next_def);
    self.next_def += 1;
    id
  }

  fn alloc_origin(&mut self) -> u32 {
    let id = self.next_origin;
    self.next_origin += 1;
    id
  }

  fn register_ref(&mut self, id: DefId, ty: TypeId) {
    self.ref_map.insert(id, ty);
  }

  fn resolve_type(&self, expr: &TypeExpr, this_ty: TypeId) -> TypeId {
    match expr {
      TypeExpr::Type(id) => *id,
      TypeExpr::This => this_ty,
    }
  }

  fn shape_from_type(&self, ty: TypeId) -> Shape {
    match self.store.type_kind(ty) {
      TypeKind::Object(obj) => {
        let obj = self.store.object(obj);
        self.store.shape(obj.shape)
      }
      _ => Shape::new(),
    }
  }

  /// Construct instance and static types for a class declaration, handling
  /// inheritance and implicit `this` typing.
  pub fn build_class(&mut self, decl: ClassDecl) -> ClassType {
    let origin = decl
      .extends
      .as_ref()
      .map(|base| base.origin)
      .unwrap_or_else(|| self.alloc_origin());
    let def_id = self.alloc_def();
    let this_type = self.store.intern_type(TypeKind::Ref {
      def: def_id,
      args: Vec::new(),
    });

    let super_instance = decl.extends.as_ref().map(|b| b.instance);
    let super_static = decl.extends.as_ref().map(|b| b.static_type);

    let mut instance_shape = decl
      .extends
      .as_ref()
      .map(|base| self.shape_from_type(base.instance))
      .unwrap_or_else(Shape::new);
    let mut static_shape = decl
      .extends
      .as_ref()
      .map(|base| self.shape_from_type(base.static_type))
      .unwrap_or_else(Shape::new);

    for field in decl.fields {
      let target = if field.is_static {
        &mut static_shape
      } else {
        &mut instance_shape
      };
      let ty = self.resolve_type(&field.ty, this_type);
      let prop = Property {
        key: PropKey::String(self.store.intern_name(field.name)),
        data: PropData {
          ty,
          optional: field.optional,
          readonly: field.readonly,
          accessibility: field.visibility.accessibility(),
          is_method: false,
          origin: member_origin(field.visibility, origin),
          declared_on: None,
        },
      };
      upsert_property(&mut target.properties, prop);
    }

    for method in decl.methods {
      let target = if method.is_static {
        &mut static_shape
      } else {
        &mut instance_shape
      };
      let this_param = method
        .this_type
        .or_else(|| (!method.is_static).then_some(TypeExpr::This))
        .map(|ty| self.resolve_type(&ty, this_type));
      let this_for_resolution = this_param.unwrap_or(this_type);
      let params: Vec<Param> = method
        .params
        .into_iter()
        .map(|p| Param {
          name: p.name.map(|n| self.store.intern_name(n)),
          ty: self.resolve_type(&p.ty, this_for_resolution),
          optional: p.optional,
          rest: p.rest,
        })
        .collect();
      let ret = self.resolve_type(&method.ret, this_for_resolution);
      let sig = Signature {
        params,
        ret,
        type_params: Vec::new(),
        this_param,
      };
      let sig_id = self.store.intern_signature(sig);
      let fn_type = self.store.intern_type(TypeKind::Callable {
        overloads: vec![sig_id],
      });
      let prop = Property {
        key: PropKey::String(self.store.intern_name(method.name)),
        data: PropData {
          ty: fn_type,
          optional: false,
          readonly: true,
          accessibility: method.visibility.accessibility(),
          is_method: true,
          origin: member_origin(method.visibility, origin),
          declared_on: None,
        },
      };
      upsert_property(&mut target.properties, prop);
    }

    if let Some(cons) = decl.constructor {
      let params: Vec<Param> = cons
        .params
        .into_iter()
        .map(|p| Param {
          name: p.name.map(|n| self.store.intern_name(n)),
          ty: self.resolve_type(&p.ty, this_type),
          optional: p.optional,
          rest: p.rest,
        })
        .collect();
      let sig = Signature {
        params,
        ret: this_type,
        type_params: Vec::new(),
        this_param: None,
      };
      let sig_id = self.store.intern_signature(sig);
      static_shape.construct_signatures.push(sig_id);
    }

    let instance_ty = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(ObjectType {
        shape: self.store.intern_shape(instance_shape),
      })));
    let static_ty = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(ObjectType {
        shape: self.store.intern_shape(static_shape),
      })));

    self.register_ref(def_id, instance_ty);

    ClassType {
      name: decl.name,
      instance: instance_ty,
      static_type: static_ty,
      def_id,
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

impl TypeExpander for ClassEnv {
  fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
    self.ref_map.get(&def).copied().map(|ty| ExpandedType {
      params: Vec::new(),
      ty,
    })
  }
}

fn member_origin(visibility: MemberVisibility, origin: u32) -> Option<u32> {
  match visibility {
    MemberVisibility::Public => None,
    MemberVisibility::Private | MemberVisibility::Protected => Some(origin),
  }
}

fn upsert_property(target: &mut Vec<Property>, prop: Property) {
  if let Some(idx) = target.iter().position(|p| p.key == prop.key) {
    target[idx] = prop;
  } else {
    target.push(prop);
  }
}
