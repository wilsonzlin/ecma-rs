use std::collections::HashMap;
use std::sync::Arc;

use crate::{codes, FileKey, Host};
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  DefId as HirDefId, DefTypeInfo, TypeArenas, TypeArenasByDef, TypeExprId, TypeExprKind,
  TypeFnParam, TypeMemberId, TypeMemberKind, TypeName, TypeParamId as HirTypeParamId,
  TypeSignature,
};
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use semantic_js::ts::{ModuleRef, Namespace, SymbolOrigin, SymbolOwner, TsProgramSemantics};
use types_ts_interned::{
  DefId, Indexer, MappedModifier, MappedType, ObjectType, Param, PropData, PropKey, Property,
  Shape, Signature, TupleElem, TypeId, TypeKind, TypeParamDecl, TypeParamId, TypeParamVariance,
  TypeStore,
};

/// Lower HIR type expressions and declarations into interned types.
pub struct HirDeclLowerer<'a, 'diag> {
  store: Arc<TypeStore>,
  arenas: &'a TypeArenasByDef,
  current_arenas: Option<&'a TypeArenas>,
  semantics: Option<&'a TsProgramSemantics>,
  defs: HashMap<(FileId, String), DefId>,
  file: FileId,
  file_key: Option<FileKey>,
  local_defs: HashMap<String, HirDefId>,
  diagnostics: &'diag mut Vec<Diagnostic>,
  type_params: HashMap<HirTypeParamId, TypeParamId>,
  type_param_names: HashMap<hir_js::NameId, TypeParamId>,
  def_map: Option<&'a HashMap<DefId, DefId>>,
  def_by_name: Option<&'a HashMap<(FileId, String), DefId>>,
  host: Option<&'a dyn Host>,
  key_to_id: Option<&'a dyn Fn(&FileKey) -> Option<FileId>>,
  module_namespace_defs: Option<&'a HashMap<FileId, DefId>>,
  value_defs: Option<&'a HashMap<DefId, DefId>>,
}

impl<'a, 'diag> HirDeclLowerer<'a, 'diag> {
  pub fn new(
    store: Arc<TypeStore>,
    arenas: &'a TypeArenasByDef,
    semantics: Option<&'a TsProgramSemantics>,
    defs: HashMap<(FileId, String), DefId>,
    file: FileId,
    file_key: Option<FileKey>,
    local_defs: HashMap<String, HirDefId>,
    diagnostics: &'diag mut Vec<Diagnostic>,
    def_map: Option<&'a HashMap<DefId, DefId>>,
    def_by_name: Option<&'a HashMap<(FileId, String), DefId>>,
    host: Option<&'a dyn Host>,
    key_to_id: Option<&'a dyn Fn(&FileKey) -> Option<FileId>>,
    module_namespace_defs: Option<&'a HashMap<FileId, DefId>>,
    value_defs: Option<&'a HashMap<DefId, DefId>>,
  ) -> Self {
    Self {
      store,
      arenas,
      semantics,
      defs,
      file,
      file_key,
      local_defs,
      diagnostics,
      type_params: HashMap::new(),
      type_param_names: HashMap::new(),
      current_arenas: None,
      def_map,
      def_by_name,
      host,
      key_to_id,
      module_namespace_defs,
      value_defs,
    }
  }

  fn arenas(&self) -> &TypeArenas {
    self
      .current_arenas
      .expect("type arenas should be set before lowering")
  }

  pub fn lower_type_info(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> (TypeId, Vec<TypeParamDecl>) {
    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      return (self.store.primitive_ids().unknown, Vec::new());
    };
    let result = match info {
      DefTypeInfo::TypeAlias {
        type_expr,
        type_params,
      } => {
        let params = self.lower_type_param_decls(type_params, names);
        let ty = self.lower_type_expr(*type_expr, names);
        self.validate_variance_annotations(type_params, ty, names);
        (ty, params)
      }
      DefTypeInfo::Interface {
        type_params,
        extends,
        members,
      } => {
        let params = self.lower_type_param_decls(type_params, names);
        let mut shape = Shape::new();

        for member in members.iter() {
          self.lower_member(&mut shape, *member, names);
        }

        let mut types: Vec<TypeId> = Vec::new();
        if !shape.properties.is_empty()
          || !shape.call_signatures.is_empty()
          || !shape.construct_signatures.is_empty()
          || !shape.indexers.is_empty()
        {
          let shape_id = self.store.intern_shape(shape);
          let obj = self.store.intern_object(ObjectType { shape: shape_id });
          types.push(self.store.intern_type(TypeKind::Object(obj)));
        }

        for base in extends.iter() {
          types.push(self.lower_type_expr(*base, names));
        }

        let ty = match types.len() {
          0 => self.store.primitive_ids().any,
          1 => types[0],
          _ => self.store.intersection(types),
        };
        self.validate_variance_annotations(type_params, ty, names);
        (ty, params)
      }
      DefTypeInfo::Class { type_params, .. } => {
        let params = self.lower_type_param_decls(type_params, names);
        let (instance, _value) =
          self.lower_class_instance_and_value(info, names, self.store.primitive_ids().unknown);
        self.validate_variance_annotations(type_params, instance, names);
        (instance, params)
      }
      DefTypeInfo::Enum { .. } => (self.lower_enum_type(info, names), Vec::new()),
      DefTypeInfo::Namespace { .. } => (self.store.primitive_ids().unknown, Vec::new()),
    };
    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = None;
    result
  }

  pub fn lower_class_instance_and_value_types(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> Option<(TypeId, TypeId, Vec<TypeParamDecl>)> {
    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      self.current_arenas = None;
      return None;
    };

    let DefTypeInfo::Class { type_params, .. } = info else {
      self.current_arenas = None;
      return None;
    };
    let params = self.lower_type_param_decls(type_params, names);

    let unknown = self.store.primitive_ids().unknown;
    let (instance, value) = self.lower_class_instance_and_value(info, names, unknown);
    self.validate_variance_annotations(type_params, instance, names);

    self.type_params.clear();
    self.type_param_names.clear();
    self.current_arenas = None;
    Some((instance, value, params))
  }

  pub fn lower_enum_type_and_value(
    &mut self,
    owner: HirDefId,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> Option<(TypeId, TypeId)> {
    self.current_arenas = self.arenas.get(&owner);
    let Some(_) = self.current_arenas else {
      self.current_arenas = None;
      return None;
    };
    let value = self.lower_enum_value(info, names);
    let ty = self.lower_enum_type(info, names);
    self.current_arenas = None;
    Some((ty, value))
  }

  fn lower_enum_type(&mut self, info: &DefTypeInfo, _names: &hir_js::NameInterner) -> TypeId {
    let prim = self.store.primitive_ids();
    let DefTypeInfo::Enum { members } = info else {
      return prim.any;
    };
    let mut has_number = false;
    let mut has_string = false;
    for member in members.iter() {
      match member.value {
        hir_js::EnumMemberValue::Number => has_number = true,
        hir_js::EnumMemberValue::String => has_string = true,
        hir_js::EnumMemberValue::Computed => {
          has_number = true;
          has_string = true;
        }
      }
    }
    match (has_number, has_string) {
      (true, true) => self.store.union(vec![prim.number, prim.string]),
      (true, false) => prim.number,
      (false, true) => prim.string,
      (false, false) => prim.any,
    }
  }

  fn lower_enum_value(&mut self, info: &DefTypeInfo, names: &hir_js::NameInterner) -> TypeId {
    let prim = self.store.primitive_ids();
    let DefTypeInfo::Enum { members } = info else {
      return prim.unknown;
    };
    let mut shape = Shape::new();
    for member in members.iter() {
      let Some(name) = names.resolve(member.name) else {
        continue;
      };
      let key = PropKey::String(self.store.intern_name(name.to_string()));
      let ty = match member.value {
        hir_js::EnumMemberValue::Number => prim.number,
        hir_js::EnumMemberValue::String => prim.string,
        hir_js::EnumMemberValue::Computed => prim.any,
      };
      shape.properties.push(Property {
        key,
        data: PropData {
          ty,
          optional: false,
          readonly: true,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn lower_class_instance_and_value(
    &mut self,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
    unknown: TypeId,
  ) -> (TypeId, TypeId) {
    let DefTypeInfo::Class {
      extends,
      implements,
      members,
      ..
    } = info
    else {
      return (unknown, unknown);
    };

    let mut instance_shape = Shape::new();
    let mut static_shape = Shape::new();
    let mut ctor_signatures: Vec<TypeSignature> = Vec::new();

    for member in members.iter() {
      match &member.kind {
        hir_js::ClassMemberSigKind::Constructor(sig) => {
          ctor_signatures.push(sig.clone());
        }
        hir_js::ClassMemberSigKind::CallSignature(sig) => {
          let lowered = self.lower_signature(sig, names);
          let sig_id = self.store.intern_signature(lowered);
          if member.static_ {
            static_shape.call_signatures.push(sig_id);
          } else {
            instance_shape.call_signatures.push(sig_id);
          }
        }
        hir_js::ClassMemberSigKind::IndexSignature(idx) => {
          let key_type = self.lower_type_expr(idx.parameter_type, names);
          let value_type = self.lower_type_expr(idx.type_annotation, names);
          let indexer = Indexer {
            key_type,
            value_type,
            readonly: idx.readonly,
          };
          if member.static_ {
            static_shape.indexers.push(indexer);
          } else {
            instance_shape.indexers.push(indexer);
          }
        }
        hir_js::ClassMemberSigKind::Field {
          name,
          type_annotation,
        } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let ty = type_annotation
            .map(|t| self.lower_type_expr(t, names))
            .unwrap_or(unknown);
          let accessibility = member.accessibility.map(|a| match a {
            hir_js::ClassMemberAccessibility::Public => types_ts_interned::Accessibility::Public,
            hir_js::ClassMemberAccessibility::Protected => {
              types_ts_interned::Accessibility::Protected
            }
            hir_js::ClassMemberAccessibility::Private => types_ts_interned::Accessibility::Private,
          });
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional,
              readonly: member.readonly,
              accessibility,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
        hir_js::ClassMemberSigKind::Method { name, signature } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let sig = self.lower_signature(signature, names);
          let sig_id = self.store.intern_signature(sig);
          let ty = self.store.intern_type(TypeKind::Callable {
            overloads: vec![sig_id],
          });
          let accessibility = member.accessibility.map(|a| match a {
            hir_js::ClassMemberAccessibility::Public => types_ts_interned::Accessibility::Public,
            hir_js::ClassMemberAccessibility::Protected => {
              types_ts_interned::Accessibility::Protected
            }
            hir_js::ClassMemberAccessibility::Private => types_ts_interned::Accessibility::Private,
          });
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional,
              readonly: member.readonly,
              accessibility,
              is_method: true,
              origin: None,
              declared_on: None,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
        hir_js::ClassMemberSigKind::Getter { name, return_type } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let ty = return_type
            .map(|t| self.lower_type_expr(t, names))
            .unwrap_or(unknown);
          let accessibility = member.accessibility.map(|a| match a {
            hir_js::ClassMemberAccessibility::Public => types_ts_interned::Accessibility::Public,
            hir_js::ClassMemberAccessibility::Protected => {
              types_ts_interned::Accessibility::Protected
            }
            hir_js::ClassMemberAccessibility::Private => types_ts_interned::Accessibility::Private,
          });
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional,
              readonly: true,
              accessibility,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
        hir_js::ClassMemberSigKind::Setter { name, parameter } => {
          let Some(key) = self.prop_key_from_name(name, names) else {
            continue;
          };
          let ty = self.lower_type_expr(parameter.ty, names);
          let accessibility = member.accessibility.map(|a| match a {
            hir_js::ClassMemberAccessibility::Public => types_ts_interned::Accessibility::Public,
            hir_js::ClassMemberAccessibility::Protected => {
              types_ts_interned::Accessibility::Protected
            }
            hir_js::ClassMemberAccessibility::Private => types_ts_interned::Accessibility::Private,
          });
          let prop = Property {
            key,
            data: PropData {
              ty,
              optional: member.optional || parameter.optional,
              readonly: false,
              accessibility,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          };
          if member.static_ {
            static_shape.properties.push(prop);
          } else {
            instance_shape.properties.push(prop);
          }
        }
      }
    }

    let instance_obj = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(ObjectType {
        shape: self.store.intern_shape(instance_shape),
      })));
    let mut instance_parts = vec![instance_obj];
    if let Some(ext) = extends {
      instance_parts.push(self.lower_type_expr(*ext, names));
    }
    for implemented in implements.iter() {
      instance_parts.push(self.lower_type_expr(*implemented, names));
    }
    let instance = if instance_parts.len() == 1 {
      instance_parts[0]
    } else {
      self.store.intersection(instance_parts)
    };

    let mut ctor_sig_ids: Vec<types_ts_interned::SignatureId> = Vec::new();
    for sig in ctor_signatures.iter() {
      let mut lowered = self.lower_signature(sig, names);
      lowered.ret = instance;
      lowered.this_param = None;
      ctor_sig_ids.push(self.store.intern_signature(lowered));
    }
    if ctor_sig_ids.is_empty() {
      let sig = Signature {
        params: Vec::new(),
        ret: instance,
        type_params: Vec::new(),
        this_param: None,
      };
      ctor_sig_ids.push(self.store.intern_signature(sig));
    }
    static_shape.construct_signatures.extend(ctor_sig_ids);

    let value = self
      .store
      .intern_type(TypeKind::Object(self.store.intern_object(ObjectType {
        shape: self.store.intern_shape(static_shape),
      })));

    (instance, value)
  }

  fn prop_key_from_name(
    &mut self,
    name: &hir_js::PropertyName,
    names: &hir_js::NameInterner,
  ) -> Option<PropKey> {
    match name {
      hir_js::PropertyName::Ident(id) => {
        let name = names.resolve(*id)?;
        let interned = self.store.intern_name(name.to_string());
        if name.starts_with("Symbol.") {
          Some(PropKey::Symbol(interned))
        } else {
          Some(PropKey::String(interned))
        }
      }
      hir_js::PropertyName::String(s) => Some(PropKey::String(self.store.intern_name(s.clone()))),
      hir_js::PropertyName::Number(n) => Some(PropKey::Number(n.parse::<i64>().ok()?)),
      hir_js::PropertyName::Symbol(id) => Some(PropKey::Symbol(
        self.store.intern_name(names.resolve(*id)?.to_string()),
      )),
      hir_js::PropertyName::Computed => None,
    }
  }

  fn map_value_def(&self, def: DefId) -> DefId {
    self
      .value_defs
      .and_then(|map| map.get(&def).copied())
      .unwrap_or(def)
  }

  fn lower_type_expr(&mut self, id: TypeExprId, names: &hir_js::NameInterner) -> TypeId {
    let Some(ty) = self.arenas().type_exprs.get(id.0 as usize).cloned() else {
      return self.store.primitive_ids().unknown;
    };
    match ty.kind {
      TypeExprKind::Any => self.store.primitive_ids().any,
      TypeExprKind::Unknown => self.store.primitive_ids().unknown,
      TypeExprKind::Never => self.store.primitive_ids().never,
      TypeExprKind::Void => self.store.primitive_ids().void,
      TypeExprKind::Null => self.store.primitive_ids().null,
      TypeExprKind::Undefined => self.store.primitive_ids().undefined,
      TypeExprKind::Intrinsic => self.store.primitive_ids().unknown,
      TypeExprKind::Object => {
        let shape = Shape::new();
        let shape_id = self.store.intern_shape(shape);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      TypeExprKind::Boolean => self.store.primitive_ids().boolean,
      TypeExprKind::Number => self.store.primitive_ids().number,
      TypeExprKind::String => self.store.primitive_ids().string,
      TypeExprKind::BigInt => self.store.primitive_ids().bigint,
      TypeExprKind::Symbol => self.store.primitive_ids().symbol,
      TypeExprKind::UniqueSymbol => self.store.primitive_ids().unique_symbol,
      TypeExprKind::This => self.store.intern_type(TypeKind::This),
      TypeExprKind::Literal(lit) => match lit {
        hir_js::TypeLiteral::Boolean(b) => self.store.intern_type(TypeKind::BooleanLiteral(b)),
        hir_js::TypeLiteral::Number(n) => {
          let parsed = n.parse::<f64>().unwrap_or(0.0);
          self
            .store
            .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(parsed)))
        }
        hir_js::TypeLiteral::String(s) => {
          let name = self.store.intern_name(s.clone());
          self.store.intern_type(TypeKind::StringLiteral(name))
        }
        hir_js::TypeLiteral::BigInt(n) => {
          let trimmed = n.trim_end_matches('n');
          let value = trimmed.parse::<BigInt>().unwrap_or_default();
          self.store.intern_type(TypeKind::BigIntLiteral(value))
        }
        hir_js::TypeLiteral::Null => self.store.primitive_ids().null,
      },
      TypeExprKind::Array(arr) => {
        let elem = self.lower_type_expr(arr.element, names);
        self.store.intern_type(TypeKind::Array {
          ty: elem,
          readonly: arr.readonly,
        })
      }
      TypeExprKind::Tuple(tuple) => {
        let mut elems = Vec::new();
        for elem in tuple.elements.iter() {
          elems.push(TupleElem {
            ty: self.lower_type_expr(elem.ty, names),
            optional: elem.optional,
            rest: elem.rest,
            readonly: tuple.readonly,
          });
        }
        self.store.intern_type(TypeKind::Tuple(elems))
      }
      TypeExprKind::Union(members) => {
        let lowered = members
          .iter()
          .map(|m| self.lower_type_expr(*m, names))
          .collect();
        self.store.union(lowered)
      }
      TypeExprKind::Intersection(members) => {
        let lowered = members
          .iter()
          .map(|m| self.lower_type_expr(*m, names))
          .collect();
        self.store.intersection(lowered)
      }
      TypeExprKind::Function(func) | TypeExprKind::Constructor(func) => {
        let sig = self.lower_function_type(&func, names);
        let sig_id = self.store.intern_signature(sig);
        self.store.intern_type(TypeKind::Callable {
          overloads: vec![sig_id],
        })
      }
      TypeExprKind::TypeLiteral(obj) => {
        if obj.members.is_empty() {
          self.store.intern_type(TypeKind::EmptyObject)
        } else {
          let mut shape = Shape::new();
          for member in obj.members.iter() {
            self.lower_member(&mut shape, *member, names);
          }
          let shape_id = self.store.intern_shape(shape);
          let obj = self.store.intern_object(ObjectType { shape: shape_id });
          self.store.intern_type(TypeKind::Object(obj))
        }
      }
      TypeExprKind::Parenthesized(inner) => self.lower_type_expr(inner, names),
      TypeExprKind::TypeRef(r) => self.lower_type_ref(&r, names),
      TypeExprKind::TypeQuery(name) => {
        if let TypeName::Import(import) = &name {
          let empty_qualifier = import
            .qualifier
            .as_ref()
            .map(|segments| segments.is_empty())
            .unwrap_or(true);
          if empty_qualifier {
            if let Some(namespace_def) = self.resolve_import_module_namespace(import) {
              return self.store.intern_type(TypeKind::Ref {
                def: self.map_value_def(namespace_def),
                args: Vec::new(),
              });
            }
          } else if let Some(def) = self.resolve_import_typeof_qualifier(import, names) {
            return self.store.intern_type(TypeKind::Ref {
              def: self.map_value_def(def),
              args: Vec::new(),
            });
          }
        }
        if let Some(def) = self.resolve_value_name(&name, names, None) {
          return self.store.intern_type(TypeKind::Ref {
            def: self.map_value_def(def),
            args: Vec::new(),
          });
        }

        let fallback_name = self.type_name_to_string(&name, names);
        if let Some(def) = self.defs.get(&(self.file, fallback_name.clone())) {
          return self.store.intern_type(TypeKind::Ref {
            def: self.map_value_def(*def),
            args: Vec::new(),
          });
        }

        self.diagnostics.push(codes::UNKNOWN_IDENTIFIER.error(
          format!("Cannot find name '{fallback_name}'."),
          Span::new(self.file, TextRange::new(0, 0)),
        ));

        self.store.primitive_ids().unknown
      }
      TypeExprKind::KeyOf(inner) => {
        let ty = self.lower_type_expr(inner, names);
        self.store.intern_type(TypeKind::KeyOf(ty))
      }
      TypeExprKind::IndexedAccess {
        object_type,
        index_type,
      } => {
        let obj = self.lower_type_expr(object_type, names);
        let idx = self.lower_type_expr(index_type, names);
        self
          .store
          .intern_type(TypeKind::IndexedAccess { obj, index: idx })
      }
      TypeExprKind::Conditional(cond) => {
        let distributive = self.is_naked_type_param(cond.check_type);
        let prev_params = self.type_params.clone();
        let prev_names = self.type_param_names.clone();
        let check = self.lower_type_expr(cond.check_type, names);
        let extends = self.lower_type_expr(cond.extends_type, names);
        let true_ty = self.lower_type_expr(cond.true_type, names);
        let false_ty = self.lower_type_expr(cond.false_type, names);
        self.type_params = prev_params;
        self.type_param_names = prev_names;
        self.store.intern_type(TypeKind::Conditional {
          check,
          extends,
          true_ty,
          false_ty,
          distributive,
        })
      }
      TypeExprKind::Mapped(mapped) => self.lower_mapped_type(&mapped, names),
      TypeExprKind::TemplateLiteral(tpl) => {
        let mut spans = Vec::new();
        for span in tpl.spans.iter() {
          spans.push(types_ts_interned::TemplateChunk {
            literal: span.literal.clone(),
            ty: self.lower_type_expr(span.type_expr, names),
          });
        }
        self.store.intern_type(TypeKind::TemplateLiteral(
          types_ts_interned::TemplateLiteralType {
            head: tpl.head,
            spans,
          },
        ))
      }
      TypeExprKind::Infer(param) => self.lower_infer_type(param, names),
      TypeExprKind::TypePredicate(pred) => {
        let asserted = pred
          .type_annotation
          .map(|ty| self.lower_type_expr(ty, names));
        let parameter = names
          .resolve(pred.parameter)
          .map(|n| self.store.intern_name(n.to_string()));
        self.store.intern_type(TypeKind::Predicate {
          parameter,
          asserted,
          asserts: pred.asserts,
        })
      }
      TypeExprKind::Import(import) => self.lower_import_type(&import, names),
    }
  }

  fn lower_mapped_type(
    &mut self,
    mapped: &hir_js::TypeMapped,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    let tp = self.alloc_type_param(mapped.type_param);
    let constraint = self.lower_type_expr(mapped.constraint, names);
    let value = self.lower_type_expr(mapped.value_type, names);
    let name_type = mapped
      .name_type
      .as_ref()
      .map(|n| self.lower_type_expr(*n, names));
    let mapped_kind = MappedType {
      param: tp,
      source: constraint,
      value,
      readonly: self.map_modifier(mapped.readonly),
      optional: self.map_modifier(mapped.optional),
      name_type,
      as_type: name_type,
    };
    let mapped_ty = self.store.intern_type(TypeKind::Mapped(mapped_kind));
    mapped_ty
  }

  fn lower_infer_type(&mut self, id: HirTypeParamId, names: &hir_js::NameInterner) -> TypeId {
    let param = self.alloc_type_param(id);
    let constraint = self
      .arenas()
      .type_params
      .get(id.0 as usize)
      .and_then(|tp| tp.constraint)
      .map(|c| self.lower_type_expr(c, names));
    self
      .store
      .intern_type(TypeKind::Infer { param, constraint })
  }

  fn is_naked_type_param(&self, expr: TypeExprId) -> bool {
    let ty = &self.arenas().type_exprs[expr.0 as usize];
    match &ty.kind {
      TypeExprKind::TypeRef(reference) if reference.type_args.is_empty() => {
        matches!(
          reference.name,
          TypeName::Ident(name) if self.type_param_names.contains_key(&name)
        )
      }
      _ => false,
    }
  }

  fn lower_function_type(
    &mut self,
    func: &hir_js::TypeFunction,
    names: &hir_js::NameInterner,
  ) -> Signature {
    let prev_params = self.type_params.clone();
    let prev_names = self.type_param_names.clone();
    let type_params = self.lower_type_param_decls(&func.type_params, names);
    let (this_param, params) = self.lower_fn_params(&func.params, names);
    let ret = self.lower_type_expr(func.ret, names);
    let sig = Signature {
      params,
      ret,
      type_params,
      this_param,
    };
    self.type_params = prev_params;
    self.type_param_names = prev_names;
    sig
  }

  fn map_modifier(&self, modifier: Option<hir_js::TypeMappedModifier>) -> MappedModifier {
    match modifier {
      None => MappedModifier::Preserve,
      Some(hir_js::TypeMappedModifier::Plus) => MappedModifier::Add,
      Some(hir_js::TypeMappedModifier::Minus) => MappedModifier::Remove,
      Some(hir_js::TypeMappedModifier::None) => MappedModifier::Add,
    }
  }

  fn alloc_type_param(&mut self, id: HirTypeParamId) -> TypeParamId {
    if let Some(existing) = self.type_params.get(&id) {
      return *existing;
    }
    let new_id = TypeParamId(self.type_params.len() as u32);
    self.type_params.insert(id, new_id);
    if let Some(param) = self.arenas().type_params.get(id.0 as usize) {
      self.type_param_names.insert(param.name, new_id);
    }
    new_id
  }

  fn lower_type_param_decls(
    &mut self,
    params: &[HirTypeParamId],
    names: &hir_js::NameInterner,
  ) -> Vec<TypeParamDecl> {
    for tp in params.iter() {
      self.alloc_type_param(*tp);
    }
    params
      .iter()
      .filter_map(|id| {
        let (constraint, default, variance, const_) = {
          let data = self.arenas().type_params.get(id.0 as usize)?;
          (data.constraint, data.default, data.variance, data.const_)
        };
        let mapped = *self.type_params.get(id)?;
        let constraint = constraint.map(|c| self.lower_type_expr(c, names));
        let default = default.map(|d| self.lower_type_expr(d, names));
        let variance = variance.map(|variance| match variance {
          hir_js::TypeVariance::In => TypeParamVariance::In,
          hir_js::TypeVariance::Out => TypeParamVariance::Out,
          hir_js::TypeVariance::InOut => TypeParamVariance::InOut,
        });
        Some(TypeParamDecl {
          id: mapped,
          constraint,
          default,
          variance,
          const_,
        })
      })
      .collect()
  }

  fn validate_variance_annotations(
    &mut self,
    params: &[HirTypeParamId],
    ty: TypeId,
    names: &hir_js::NameInterner,
  ) {
    const OUT: u8 = 1;
    const IN: u8 = 2;

    let mut declared: Vec<(TypeParamId, TypeParamVariance, TextRange, String)> = Vec::new();
    for hir_id in params.iter() {
      let Some(data) = self.arenas().type_params.get(hir_id.0 as usize) else {
        continue;
      };
      let Some(variance) = data.variance else {
        continue;
      };
      let Some(mapped) = self.type_params.get(hir_id).copied() else {
        continue;
      };
      let name = names
        .resolve(data.name)
        .map(|n| n.to_string())
        .unwrap_or_default();
      let mut span = data.span;
      if let (Some(host), Some(file_key)) = (self.host, self.file_key.as_ref()) {
        if let Ok(text) = host.file_text(file_key) {
          let end = span.end as usize;
          if end > 0 && end <= text.len() {
            match text.as_bytes()[end - 1] {
              b'>' | b',' => span.end = span.end.saturating_sub(1),
              _ => {}
            }
          }
        }
      }
      let variance = match variance {
        hir_js::TypeVariance::In => TypeParamVariance::In,
        hir_js::TypeVariance::Out => TypeParamVariance::Out,
        hir_js::TypeVariance::InOut => TypeParamVariance::InOut,
      };
      declared.push((mapped, variance, span, name));
    }
    if declared.is_empty() {
      return;
    }

    let mut usage: HashMap<TypeParamId, u8> = HashMap::new();
    let mut visited: std::collections::HashSet<(TypeId, u8)> = std::collections::HashSet::new();
    self.collect_variance_usage(ty, OUT, &mut usage, &mut visited);

    for (param_id, expected, span, name) in declared {
      let actual = usage.get(&param_id).copied().unwrap_or(0);
      let ok = match expected {
        TypeParamVariance::Out => (actual & IN) == 0,
        TypeParamVariance::In => (actual & OUT) == 0,
        TypeParamVariance::InOut => true,
      };
      if ok {
        continue;
      }
      let expected_str = match expected {
        TypeParamVariance::Out => "out",
        TypeParamVariance::In => "in",
        TypeParamVariance::InOut => "in out",
      };
      let actual_str = match actual {
        0 => "it is never used",
        OUT => "it is only used covariantly",
        IN => "it is only used contravariantly",
        _ => "it is used in both covariant and contravariant positions",
      };
      self
        .diagnostics
        .push(codes::INVALID_VARIANCE_ANNOTATION.error(
          format!("Type parameter '{name}' is declared as '{expected_str}', but {actual_str}."),
          Span::new(self.file, span),
        ));
    }
  }

  fn collect_variance_usage(
    &self,
    ty: TypeId,
    position: u8,
    usage: &mut HashMap<TypeParamId, u8>,
    visited: &mut std::collections::HashSet<(TypeId, u8)>,
  ) {
    const OUT: u8 = 1;
    const IN: u8 = 2;

    if !visited.insert((ty, position)) {
      return;
    }
    match self.store.type_kind(ty) {
      TypeKind::TypeParam(id) => {
        usage
          .entry(id)
          .and_modify(|bits| *bits |= position)
          .or_insert(position);
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for member in members {
          self.collect_variance_usage(member, position, usage, visited);
        }
      }
      TypeKind::Array { ty, .. } => self.collect_variance_usage(ty, position, usage, visited),
      TypeKind::Tuple(elems) => {
        for elem in elems {
          self.collect_variance_usage(elem.ty, position, usage, visited);
        }
      }
      TypeKind::Callable { overloads } => {
        for sig_id in overloads {
          let sig = self.store.signature(sig_id);
          self.collect_signature_variance(&sig, position, usage, visited);
        }
      }
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in shape.properties {
          self.collect_variance_usage(prop.data.ty, position, usage, visited);
        }
        for sig_id in shape.call_signatures {
          let sig = self.store.signature(sig_id);
          self.collect_signature_variance(&sig, position, usage, visited);
        }
        for sig_id in shape.construct_signatures {
          let sig = self.store.signature(sig_id);
          self.collect_signature_variance(&sig, position, usage, visited);
        }
        for idx in shape.indexers {
          let flipped = ((position & OUT) << 1) | ((position & IN) >> 1);
          self.collect_variance_usage(idx.key_type, flipped, usage, visited);
          self.collect_variance_usage(idx.value_type, position, usage, visited);
        }
      }
      TypeKind::Ref { args, .. } => {
        for arg in args {
          self.collect_variance_usage(arg, position, usage, visited);
        }
      }
      TypeKind::Intrinsic { ty, .. } => self.collect_variance_usage(ty, position, usage, visited),
      TypeKind::Infer { constraint, .. } => {
        if let Some(constraint) = constraint {
          self.collect_variance_usage(constraint, position, usage, visited);
        }
      }
      TypeKind::Predicate { asserted, .. } => {
        if let Some(asserted) = asserted {
          self.collect_variance_usage(asserted, position, usage, visited);
        }
      }
      TypeKind::Conditional {
        check,
        extends,
        true_ty,
        false_ty,
        ..
      } => {
        self.collect_variance_usage(check, OUT | IN, usage, visited);
        self.collect_variance_usage(extends, OUT | IN, usage, visited);
        self.collect_variance_usage(true_ty, position, usage, visited);
        self.collect_variance_usage(false_ty, position, usage, visited);
      }
      TypeKind::Mapped(mapped) => {
        self.collect_variance_usage(mapped.source, OUT | IN, usage, visited);
        self.collect_variance_usage(mapped.value, position, usage, visited);
        if let Some(name_type) = mapped.name_type {
          self.collect_variance_usage(name_type, OUT | IN, usage, visited);
        }
        if let Some(as_type) = mapped.as_type {
          self.collect_variance_usage(as_type, OUT | IN, usage, visited);
        }
      }
      TypeKind::IndexedAccess { obj, index } => {
        self.collect_variance_usage(obj, OUT | IN, usage, visited);
        self.collect_variance_usage(index, OUT | IN, usage, visited);
      }
      TypeKind::KeyOf(inner) => self.collect_variance_usage(inner, OUT | IN, usage, visited),
      TypeKind::EmptyObject
      | TypeKind::Any
      | TypeKind::Unknown
      | TypeKind::Never
      | TypeKind::Void
      | TypeKind::Null
      | TypeKind::Undefined
      | TypeKind::Boolean
      | TypeKind::Number
      | TypeKind::String
      | TypeKind::BigInt
      | TypeKind::Symbol
      | TypeKind::UniqueSymbol
      | TypeKind::BooleanLiteral(_)
      | TypeKind::NumberLiteral(_)
      | TypeKind::StringLiteral(_)
      | TypeKind::BigIntLiteral(_)
      | TypeKind::This
      | TypeKind::TemplateLiteral(_) => {}
    }
  }

  fn collect_signature_variance(
    &self,
    sig: &Signature,
    position: u8,
    usage: &mut HashMap<TypeParamId, u8>,
    visited: &mut std::collections::HashSet<(TypeId, u8)>,
  ) {
    const OUT: u8 = 1;
    const IN: u8 = 2;

    let flipped = ((position & OUT) << 1) | ((position & IN) >> 1);
    if let Some(this) = sig.this_param {
      self.collect_variance_usage(this, flipped, usage, visited);
    }
    for param in sig.params.iter() {
      self.collect_variance_usage(param.ty, flipped, usage, visited);
    }
    self.collect_variance_usage(sig.ret, position, usage, visited);
  }

  fn type_name_to_string(&self, name: &hir_js::TypeName, names: &hir_js::NameInterner) -> String {
    match name {
      TypeName::Ident(id) => names.resolve(*id).unwrap_or_default().to_string(),
      TypeName::Qualified(path) => path
        .last()
        .and_then(|id| names.resolve(*id))
        .unwrap_or_default()
        .to_string(),
      TypeName::Import(import) => import
        .qualifier
        .as_ref()
        .and_then(|q| q.last())
        .and_then(|id| names.resolve(*id))
        .unwrap_or_default()
        .to_string(),
      TypeName::ImportExpr => String::new(),
    }
  }

  fn lower_signature(&mut self, sig: &TypeSignature, names: &hir_js::NameInterner) -> Signature {
    let prev_params = self.type_params.clone();
    let prev_names = self.type_param_names.clone();
    let type_params = self.lower_type_param_decls(&sig.type_params, names);
    let (this_param, sig_params) = self.lower_fn_params(&sig.params, names);
    let ret = sig
      .return_type
      .map(|r| self.lower_type_expr(r, names))
      .unwrap_or(self.store.primitive_ids().any);
    let sig = Signature {
      params: sig_params,
      ret,
      type_params,
      this_param,
    };
    self.type_params = prev_params;
    self.type_param_names = prev_names;
    sig
  }

  fn lower_fn_params(
    &mut self,
    params: &[TypeFnParam],
    names: &hir_js::NameInterner,
  ) -> (Option<TypeId>, Vec<Param>) {
    let mut lowered = Vec::new();
    let mut this_param = None;
    for param in params.iter() {
      let name = param.name.and_then(|n| names.resolve(n));
      if matches!(name.as_deref(), Some("this")) && this_param.is_none() {
        this_param = Some(self.lower_type_expr(param.ty, names));
        continue;
      }
      lowered.push(self.lower_fn_param(param, names));
    }
    (this_param, lowered)
  }

  fn lower_fn_param(&mut self, param: &TypeFnParam, names: &hir_js::NameInterner) -> Param {
    Param {
      name: param
        .name
        .and_then(|n| names.resolve(n))
        .map(|n| self.store.intern_name(n.to_string())),
      ty: self.lower_type_expr(param.ty, names),
      optional: param.optional,
      rest: param.rest,
    }
  }

  fn lower_member(
    &mut self,
    shape: &mut Shape,
    member: TypeMemberId,
    names: &hir_js::NameInterner,
  ) {
    let Some(member) = self.arenas().type_members.get(member.0 as usize).cloned() else {
      return;
    };
    match member.kind {
      TypeMemberKind::Property(prop) => {
        if let Some((key, data)) = self.lower_property(&prop, names) {
          shape.properties.push(Property { key, data });
        }
      }
      TypeMemberKind::Method(method) => {
        if let Some((key, ty)) = self.lower_method(&method, names) {
          shape.properties.push(Property {
            key,
            data: PropData {
              ty,
              optional: method.optional,
              readonly: false,
              accessibility: None,
              is_method: true,
              origin: None,
              declared_on: None,
            },
          });
        }
      }
      TypeMemberKind::Constructor(cons) => {
        let sig = self.lower_signature(&cons, names);
        let sig_id = self.store.intern_signature(sig);
        shape.construct_signatures.push(sig_id);
      }
      TypeMemberKind::CallSignature(call) => {
        let sig = self.lower_signature(&call, names);
        let sig_id = self.store.intern_signature(sig);
        shape.call_signatures.push(sig_id);
      }
      TypeMemberKind::IndexSignature(idx) => {
        let key_type = self.lower_type_expr(idx.parameter_type, names);
        let value_type = self.lower_type_expr(idx.type_annotation, names);
        shape.indexers.push(Indexer {
          key_type,
          value_type,
          readonly: idx.readonly,
        });
      }
      TypeMemberKind::Getter(getter) => {
        if let Some((key, mut data)) = self.lower_property(
          &hir_js::TypePropertySignature {
            readonly: true,
            optional: false,
            name: getter.name,
            type_annotation: getter.return_type,
          },
          names,
        ) {
          data.readonly = true;
          shape.properties.push(Property { key, data });
        }
      }
      TypeMemberKind::Setter(setter) => {
        if let Some((key, mut data)) = self.lower_property(
          &hir_js::TypePropertySignature {
            readonly: false,
            optional: setter.parameter.optional,
            name: setter.name,
            type_annotation: Some(setter.parameter.ty),
          },
          names,
        ) {
          data.readonly = false;
          shape.properties.push(Property { key, data });
        }
      }
      TypeMemberKind::Mapped(mapped) => {
        let key_type = self.lower_type_expr(mapped.constraint, names);
        let value_type = self.lower_type_expr(mapped.value_type, names);
        shape.indexers.push(Indexer {
          key_type,
          value_type,
          readonly: matches!(
            mapped.readonly,
            Some(hir_js::TypeMappedModifier::Plus) | Some(hir_js::TypeMappedModifier::None)
          ),
        });
      }
    }
  }

  fn lower_property(
    &mut self,
    prop: &hir_js::TypePropertySignature,
    names: &hir_js::NameInterner,
  ) -> Option<(PropKey, PropData)> {
    let trace = std::env::var("TRACE_TYPEOF").is_ok();
    let key = self.prop_key_from_name(&prop.name, names)?;
    let ty = prop
      .type_annotation
      .map(|t| self.lower_type_expr(t, names))
      .unwrap_or(self.store.primitive_ids().unknown);
    if trace {
      if let PropKey::String(name_id) = &key {
        let name = self.store.name(*name_id);
        if name == "document" {
          eprintln!(
            "[lower_property] file {:?} prop {} has_annotation={}",
            self.file,
            name,
            prop.type_annotation.is_some()
          );
        }
      }
    }
    Some((
      key,
      PropData {
        ty,
        optional: prop.optional,
        readonly: prop.readonly,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    ))
  }

  fn lower_method(
    &mut self,
    method: &hir_js::TypeMethodSignature,
    names: &hir_js::NameInterner,
  ) -> Option<(PropKey, TypeId)> {
    let key = self.prop_key_from_name(&method.name, names)?;
    let prev_params = self.type_params.clone();
    let prev_names = self.type_param_names.clone();
    let type_params = self.lower_type_param_decls(&method.type_params, names);
    let (this_param, params) = self.lower_fn_params(&method.params, names);
    let sig = Signature {
      params,
      ret: method
        .return_type
        .map(|t| self.lower_type_expr(t, names))
        .unwrap_or(self.store.primitive_ids().unknown),
      type_params,
      this_param,
    };
    let sig_id = self.store.intern_signature(sig);
    self.type_params = prev_params;
    self.type_param_names = prev_names;
    Some((
      key,
      self.store.intern_type(TypeKind::Callable {
        overloads: vec![sig_id],
      }),
    ))
  }

  fn lower_type_ref(
    &mut self,
    reference: &hir_js::TypeRef,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    let args: Vec<_> = reference
      .type_args
      .iter()
      .map(|a| self.lower_type_expr(*a, names))
      .collect();

    // Type parameter reference.
    if let TypeName::Ident(name_id) = &reference.name {
      if let Some(tp) = self.type_param_names.get(name_id) {
        return self.store.intern_type(TypeKind::TypeParam(*tp));
      }
    }

    // TypeScript `intrinsic` marker used by lib declarations (e.g. `type Uppercase<S extends string> = intrinsic;`).
    // Treat it as an opaque type during lowering so that we can detect and
    // replace intrinsic aliases later without emitting an "unknown identifier"
    // diagnostic for the marker itself.
    if reference.type_args.is_empty() {
      if let TypeName::Ident(name_id) = &reference.name {
        if names.resolve(*name_id) == Some("intrinsic") {
          return self.store.primitive_ids().unknown;
        }
      }
    }

    if let Some(resolved) = self.resolve_type_name(&reference.name, names, None) {
      return self.store.intern_type(TypeKind::Ref {
        def: resolved,
        args,
      });
    }

    let name = self.type_name_to_string(&reference.name, names);

    if let Some(def) = self
      .defs
      .iter()
      .find(|((_, def_name), _)| def_name == &name)
      .map(|(_, def)| *def)
      .or_else(|| {
        self.def_by_name.and_then(|map| {
          map
            .iter()
            .find(|((_, def_name), _)| def_name == &name)
            .map(|(_, def)| *def)
        })
      })
    {
      return self.store.intern_type(TypeKind::Ref { def, args });
    }

    self.diagnostics.push(codes::UNKNOWN_IDENTIFIER.error(
      format!("Cannot find name '{name}'."),
      Span::new(self.file, TextRange::new(0, 0)),
    ));

    self.store.primitive_ids().unknown
  }

  fn lower_import_type(
    &mut self,
    import: &hir_js::TypeImport,
    names: &hir_js::NameInterner,
  ) -> TypeId {
    let Some(host) = self.host else {
      return self.store.primitive_ids().unknown;
    };

    let Some(from_key) = self.file_key.as_ref() else {
      return self.store.primitive_ids().unknown;
    };
    let Some(target_key) = host.resolve(from_key, &import.module) else {
      return self.store.primitive_ids().unknown;
    };
    let Some(target_file) = self.key_to_id.and_then(|resolver| resolver(&target_key)) else {
      return self.store.primitive_ids().unknown;
    };

    let args: Vec<_> = import
      .type_args
      .iter()
      .map(|a| self.lower_type_expr(*a, names))
      .collect();

    let qualifier_name = import.qualifier.as_ref().and_then(|q| match q {
      TypeName::Ident(id) => names.resolve(*id),
      TypeName::Qualified(path) => path.last().and_then(|id| names.resolve(*id)),
      TypeName::Import(inner) => inner
        .qualifier
        .as_ref()
        .and_then(|segments| segments.last())
        .and_then(|id| names.resolve(*id)),
      TypeName::ImportExpr => None,
    });

    if let Some(name) = qualifier_name.map(|n| n.to_string()) {
      if let Some(def) = self
        .def_by_name
        .and_then(|map| map.get(&(target_file, name.clone())).copied())
        .or_else(|| self.defs.get(&(target_file, name.clone())).copied())
      {
        return self.store.intern_type(TypeKind::Ref {
          def,
          args: args.clone(),
        });
      }
    }

    self.store.primitive_ids().unknown
  }

  fn resolve_type_name(
    &self,
    name: &hir_js::TypeName,
    names: &hir_js::NameInterner,
    file_override: Option<FileId>,
  ) -> Option<DefId> {
    self.resolve_in_namespace(name, names, file_override, Namespace::TYPE)
  }

  fn resolve_value_name(
    &self,
    name: &hir_js::TypeName,
    names: &hir_js::NameInterner,
    file_override: Option<FileId>,
  ) -> Option<DefId> {
    self.resolve_in_namespace(name, names, file_override, Namespace::VALUE)
  }

  fn resolve_in_namespace(
    &self,
    name: &hir_js::TypeName,
    names: &hir_js::NameInterner,
    file_override: Option<FileId>,
    ns: Namespace,
  ) -> Option<DefId> {
    match name {
      TypeName::Ident(id) => {
        let resolved = names.resolve(*id)?.to_string();
        self.resolve_named_in_namespace(&resolved, file_override.unwrap_or(self.file), ns)
      }
      TypeName::Qualified(path) => self
        .resolve_qualified_in_namespace(path, names, file_override.unwrap_or(self.file), ns)
        .or_else(|| {
          path
            .last()
            .and_then(|id| names.resolve(*id))
            .and_then(|resolved| {
              self.resolve_named_in_namespace(
                &resolved.to_string(),
                file_override.unwrap_or(self.file),
                ns,
              )
            })
        }),
      TypeName::Import(import) => import.module.as_ref().and_then(|module| {
        let name = import
          .qualifier
          .as_ref()
          .and_then(|segments| segments.last())
          .and_then(|id| names.resolve(*id))
          .map(|s| s.to_string())?;
        let from_key = self.file_key.as_ref()?;
        let target_key = self.host.and_then(|h| h.resolve(from_key, module))?;
        let target_file = self.key_to_id.and_then(|resolver| resolver(&target_key))?;
        self.resolve_named_in_namespace(&name, target_file, ns)
      }),
      TypeName::ImportExpr => None,
    }
  }

  fn resolve_import_module_namespace(&self, import: &hir_js::hir::TypeImportName) -> Option<DefId> {
    let module = import.module.as_ref()?;
    let from_key = self.file_key.as_ref()?;
    let host = self.host?;
    let target_key = host.resolve(from_key, module)?;
    let target_file = self.key_to_id.and_then(|resolver| resolver(&target_key))?;
    self
      .module_namespace_defs
      .and_then(|defs| defs.get(&target_file).copied())
  }

  fn resolve_import_typeof_qualifier(
    &self,
    import: &hir_js::hir::TypeImportName,
    names: &hir_js::NameInterner,
  ) -> Option<DefId> {
    let sem = self.semantics?;
    let module = import.module.as_ref()?;
    let qualifier_ids = import.qualifier.as_ref()?;
    if qualifier_ids.is_empty() {
      return None;
    }
    let from_key = self.file_key.as_ref()?;
    let host = self.host?;
    let target_key = host.resolve(from_key, module)?;
    let mut current_file = self.key_to_id.and_then(|resolver| resolver(&target_key))?;

    let mut segments = Vec::with_capacity(qualifier_ids.len());
    for id in qualifier_ids.iter() {
      segments.push(names.resolve(*id)?.to_string());
    }

    for (idx, segment) in segments.iter().enumerate() {
      let is_last = idx + 1 == segments.len();
      let ns = if is_last {
        Namespace::VALUE
      } else {
        Namespace::NAMESPACE
      };
      let symbol = sem.resolve_export(current_file, segment, ns)?;
      if is_last {
        if let Some(def) = self.def_for_symbol_in_namespace(sem, symbol, Namespace::VALUE) {
          return Some(def);
        }
        if let SymbolOrigin::Import { from, imported } = &sem.symbols().symbol(symbol).origin {
          if imported == "*" {
            if let ModuleRef::File(from_file) = from {
              return self
                .module_namespace_defs
                .and_then(|defs| defs.get(from_file).copied());
            }
          }
        }
        return None;
      }
      current_file = self.symbol_target_file(sem, symbol)?;
    }
    None
  }

  fn resolve_named_in_namespace(&self, name: &str, file: FileId, ns: Namespace) -> Option<DefId> {
    let trace = std::env::var("TRACE_TYPEOF").is_ok() && (name == "document" || name == "window");
    if trace {
      eprintln!(
        "[resolve_named_in_namespace] file {:?} name {} ns {:?}",
        file, name, ns
      );
    }
    if file == self.file {
      if let Some(local) = self.local_defs.get(name).copied() {
        if trace {
          eprintln!("[resolve_named_in_namespace] local def {:?}", local);
        }
        return self
          .def_map
          .and_then(|map| map.get(&local).copied())
          .or_else(|| {
            self
              .def_by_name
              .and_then(|map| map.get(&(self.file, name.to_string())).copied())
          })
          .or(Some(local));
      }
    }

    if let Some(def) = self.defs.get(&(file, name.to_string())) {
      if trace {
        eprintln!(
          "[resolve_named_in_namespace] defs map hit {:?} -> {:?}",
          (file, name),
          def
        );
      }
      return Some(*def);
    }

    if let Some(def) = self
      .def_by_name
      .and_then(|map| map.get(&(file, name.to_string())).copied())
    {
      if trace {
        eprintln!(
          "[resolve_named_in_namespace] def_by_name hit {:?} -> {:?}",
          (file, name),
          def
        );
      }
      return Some(def);
    }

    // Fallback to any known definition with the same name across files. This
    // allows unqualified references to resolve to ambient/global declarations
    // provided by libraries even when they originate from a different file.
    let mut candidates: Vec<_> = self
      .defs
      .iter()
      .filter_map(|((_, def_name), def)| (def_name == name).then_some(*def))
      .collect();
    candidates.sort_by_key(|d| d.0);
    if let Some(def) = candidates.first() {
      return Some(*def);
    }

    if let Some(sem) = self.semantics {
      let order = if ns == Namespace::VALUE {
        [Namespace::VALUE, Namespace::NAMESPACE, Namespace::TYPE]
      } else {
        [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE]
      };
      if let Some(symbol) = self.resolve_symbol_in_module_ns(sem, file, name, &order) {
        if let Some(decl) = sem.symbol_decls(symbol, ns).first().or_else(|| {
          order
            .iter()
            .filter_map(|candidate| sem.symbol_decls(symbol, *candidate).first())
            .next()
        }) {
          let decl_data = sem.symbols().decl(*decl);
          let target = DefId(decl_data.def_id.0);
          if trace {
            eprintln!(
              "[resolve_named_in_namespace] symbol decl hit {:?} -> {:?}",
              (file, name),
              target
            );
          }
          return self
            .def_map
            .and_then(|map| map.get(&target).copied())
            .or_else(|| {
              self.def_by_name.and_then(|map| {
                map
                  .get(&(FileId(decl_data.file.0), decl_data.name.clone()))
                  .copied()
              })
            })
            .or(Some(target));
        }
      }
      if let Some((_, group)) = sem
        .global_symbols()
        .iter()
        .find(|(global_name, _)| *global_name == name)
      {
        if let Some(symbol) = group.symbol_for(ns, sem.symbols()) {
          if let Some(def) = self.def_for_symbol(sem, symbol) {
            if trace {
              eprintln!(
                "[resolve_named_in_namespace] global symbol {:?} -> {:?}",
                name, def
              );
            }
            return Some(def);
          }
        }
      }
    }

    None
  }

  fn resolve_qualified_in_namespace(
    &self,
    path: &[hir_js::NameId],
    names: &hir_js::NameInterner,
    file: FileId,
    ns: Namespace,
  ) -> Option<DefId> {
    let sem = self.semantics?;
    let mut segments = Vec::new();
    for id in path.iter() {
      let Some(name) = names.resolve(*id) else {
        return None;
      };
      segments.push(name.to_string());
    }
    if segments.is_empty() {
      return None;
    }

    let order = if ns == Namespace::VALUE {
      [Namespace::VALUE, Namespace::NAMESPACE, Namespace::TYPE]
    } else {
      [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE]
    };
    let mut symbol = self.resolve_symbol_in_module_ns(sem, file, &segments[0], &order)?;
    let mut current_file = self.symbol_target_file(sem, symbol).unwrap_or(file);
    for segment in segments.iter().skip(1) {
      symbol = self.resolve_symbol_export(sem, current_file, segment, &order)?;
      current_file = self.symbol_target_file(sem, symbol).unwrap_or(current_file);
    }

    let def = self.def_for_symbol(sem, symbol);
    def
  }

  fn resolve_symbol_in_module_ns(
    &self,
    sem: &TsProgramSemantics,
    file: FileId,
    name: &str,
    order: &[Namespace],
  ) -> Option<semantic_js::ts::SymbolId> {
    for ns in order {
      if let Some(sym) = sem.resolve_in_module(file, name, *ns) {
        return Some(sym);
      }
    }
    None
  }

  fn resolve_symbol_export(
    &self,
    sem: &TsProgramSemantics,
    file: FileId,
    name: &str,
    order: &[Namespace],
  ) -> Option<semantic_js::ts::SymbolId> {
    for ns in order {
      if let Some(sym) = sem.resolve_export(file, name, *ns) {
        return Some(sym);
      }
    }
    None
  }

  fn symbol_target_file(
    &self,
    sem: &TsProgramSemantics,
    symbol: semantic_js::ts::SymbolId,
  ) -> Option<FileId> {
    let sym = sem.symbols().symbol(symbol);
    match &sym.origin {
      SymbolOrigin::Import { from, .. } => match from {
        ModuleRef::File(from) => Some(*from),
        _ => None,
      },
      _ => match &sym.owner {
        SymbolOwner::Module(file) => Some(*file),
        _ => None,
      },
    }
  }

  fn def_for_symbol(
    &self,
    sem: &TsProgramSemantics,
    symbol: semantic_js::ts::SymbolId,
  ) -> Option<DefId> {
    for ns in [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE] {
      if let Some(def) = self.def_for_symbol_in_namespace(sem, symbol, ns) {
        return Some(def);
      }
    }
    None
  }

  fn def_for_symbol_in_namespace(
    &self,
    sem: &TsProgramSemantics,
    symbol: semantic_js::ts::SymbolId,
    ns: Namespace,
  ) -> Option<DefId> {
    let decl = sem.symbol_decls(symbol, ns).first()?;
    let decl_data = sem.symbols().decl(*decl);
    let def = DefId(decl_data.def_id.0);
    self
      .def_map
      .and_then(|map| map.get(&def).copied())
      .or_else(|| {
        self
          .def_by_name
          .and_then(|map| map.get(&(decl_data.file, decl_data.name.clone())).copied())
      })
      .or(Some(def))
  }
}

impl<'a, 'diag> std::fmt::Debug for HirDeclLowerer<'a, 'diag> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("HirDeclLowerer")
      .field("file", &self.file)
      .finish_non_exhaustive()
  }
}
