use std::collections::HashMap;
use std::sync::Arc;

use crate::{codes, FileKey, Host};
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  DefId as HirDefId, DefTypeInfo, TypeArenas, TypeExprId, TypeExprKind, TypeFnParam, TypeMemberId,
  TypeMemberKind, TypeName, TypeParamId as HirTypeParamId, TypeSignature,
};
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use semantic_js::ts::{ImportSource, Namespace, SymbolOrigin, SymbolOwner, TsProgramSemantics};
use types_ts_interned::{
  DefId, Indexer, MappedModifier, MappedType, ObjectType, Param, PropData, PropKey, Property,
  Shape, Signature, TupleElem, TypeId, TypeKind, TypeParamId, TypeStore,
};

/// Lower HIR type expressions and declarations into interned types.
pub struct HirDeclLowerer<'a, 'diag> {
  store: Arc<TypeStore>,
  arenas: &'a TypeArenas,
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
}

impl<'a, 'diag> HirDeclLowerer<'a, 'diag> {
  pub fn new(
    store: Arc<TypeStore>,
    arenas: &'a TypeArenas,
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
      def_map,
      def_by_name,
      host,
      key_to_id,
    }
  }

  pub fn lower_type_info(
    &mut self,
    info: &DefTypeInfo,
    names: &hir_js::NameInterner,
  ) -> (TypeId, Vec<TypeParamId>) {
    match info {
      DefTypeInfo::TypeAlias {
        type_expr,
        type_params,
      } => {
        self.register_type_params(type_params);
        let params = self.collect_type_params(type_params);
        let ty = self.lower_type_expr(*type_expr, names);
        self.type_params.clear();
        self.type_param_names.clear();
        (ty, params)
      }
      DefTypeInfo::Interface {
        type_params,
        extends,
        members,
      } => {
        self.register_type_params(type_params);
        let params = self.collect_type_params(type_params);
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
        self.type_params.clear();
        self.type_param_names.clear();
        (ty, params)
      }
      DefTypeInfo::Class { type_params, .. } => {
        self.register_type_params(type_params);
        let params = self.collect_type_params(type_params);
        self.type_params.clear();
        self.type_param_names.clear();
        (self.store.primitive_ids().unknown, params)
      }
      DefTypeInfo::Enum { .. } => (self.store.primitive_ids().any, Vec::new()),
      DefTypeInfo::Namespace { .. } => (self.store.primitive_ids().unknown, Vec::new()),
    }
  }

  fn register_type_params(&mut self, params: &[HirTypeParamId]) {
    for tp in params.iter() {
      let id = TypeParamId(self.type_params.len() as u32);
      self.type_params.insert(*tp, id);
      if let Some(param) = self.arenas.type_params.get(tp.0 as usize) {
        self.type_param_names.insert(param.name, id);
      }
    }
  }

  fn lower_type_expr(&mut self, id: TypeExprId, names: &hir_js::NameInterner) -> TypeId {
    let ty = &self.arenas.type_exprs[id.0 as usize];
    match &ty.kind {
      TypeExprKind::Any => self.store.primitive_ids().any,
      TypeExprKind::Unknown => self.store.primitive_ids().unknown,
      TypeExprKind::Never => self.store.primitive_ids().never,
      TypeExprKind::Void => self.store.primitive_ids().void,
      TypeExprKind::Null => self.store.primitive_ids().null,
      TypeExprKind::Undefined => self.store.primitive_ids().undefined,
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
        hir_js::TypeLiteral::Boolean(b) => self.store.intern_type(TypeKind::BooleanLiteral(*b)),
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
        let sig = self.lower_function_type(func, names);
        let sig_id = self.store.intern_signature(sig);
        self.store.intern_type(TypeKind::Callable {
          overloads: vec![sig_id],
        })
      }
      TypeExprKind::TypeLiteral(obj) => {
        let mut shape = Shape::new();
        for member in obj.members.iter() {
          self.lower_member(&mut shape, *member, names);
        }
        let shape_id = self.store.intern_shape(shape);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      TypeExprKind::Parenthesized(inner) => self.lower_type_expr(*inner, names),
      TypeExprKind::TypeRef(r) => self.lower_type_ref(r, names),
      TypeExprKind::TypeQuery(name) => {
        let reference = hir_js::TypeRef {
          name: name.clone(),
          type_args: Vec::new(),
        };
        self.lower_type_ref(&reference, names)
      }
      TypeExprKind::KeyOf(inner) => {
        let ty = self.lower_type_expr(*inner, names);
        self.store.intern_type(TypeKind::KeyOf(ty))
      }
      TypeExprKind::IndexedAccess {
        object_type,
        index_type,
      } => {
        let obj = self.lower_type_expr(*object_type, names);
        let idx = self.lower_type_expr(*index_type, names);
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
      TypeExprKind::Mapped(mapped) => self.lower_mapped_type(mapped, names),
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
            head: tpl.head.clone(),
            spans,
          },
        ))
      }
      TypeExprKind::Infer(param) => self.lower_infer_type(*param, names),
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
      TypeExprKind::Import(import) => self.lower_import_type(import, names),
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
    let as_type = mapped
      .name_type
      .as_ref()
      .map(|n| self.lower_type_expr(*n, names));
    self.store.intern_type(TypeKind::Mapped(MappedType {
      param: tp,
      source: constraint,
      value,
      readonly: self.map_modifier(mapped.readonly),
      optional: self.map_modifier(mapped.optional),
      name_type: None,
      as_type,
    }))
  }

  fn lower_infer_type(&mut self, id: HirTypeParamId, names: &hir_js::NameInterner) -> TypeId {
    let param = self.alloc_type_param(id);
    let constraint = self
      .arenas
      .type_params
      .get(id.0 as usize)
      .and_then(|tp| tp.constraint)
      .map(|c| self.lower_type_expr(c, names));
    self
      .store
      .intern_type(TypeKind::Infer { param, constraint })
  }

  fn is_naked_type_param(&self, expr: TypeExprId) -> bool {
    let ty = &self.arenas.type_exprs[expr.0 as usize];
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
    let (this_param, params) = self.lower_fn_params(&func.params, names);
    let mut type_params = Vec::new();
    for tp in func.type_params.iter() {
      type_params.push(self.alloc_type_param(*tp));
    }
    Signature {
      params,
      ret: self.lower_type_expr(func.ret, names),
      type_params,
      this_param,
    }
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
    if let Some(param) = self.arenas.type_params.get(id.0 as usize) {
      self.type_param_names.insert(param.name, new_id);
    }
    new_id
  }

  fn collect_type_params(&self, params: &[HirTypeParamId]) -> Vec<TypeParamId> {
    params
      .iter()
      .filter_map(|id| self.type_params.get(id).copied())
      .collect()
  }

  fn lower_signature(&mut self, sig: &TypeSignature, names: &hir_js::NameInterner) -> Signature {
    let (this_param, sig_params) = self.lower_fn_params(&sig.params, names);
    let ret = sig
      .return_type
      .map(|r| self.lower_type_expr(r, names))
      .unwrap_or(self.store.primitive_ids().any);
    let mut type_params = Vec::new();
    for tp in sig.type_params.iter() {
      type_params.push(self.alloc_type_param(*tp));
    }
    Signature {
      params: sig_params,
      ret,
      type_params,
      this_param,
    }
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
    let member = &self.arenas.type_members[member.0 as usize];
    match &member.kind {
      TypeMemberKind::Property(prop) => {
        if let Some((key, data)) = self.lower_property(prop, names) {
          shape.properties.push(Property { key, data });
        }
      }
      TypeMemberKind::Method(method) => {
        if let Some((key, ty)) = self.lower_method(method, names) {
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
        let sig = self.lower_signature(cons, names);
        let sig_id = self.store.intern_signature(sig);
        shape.construct_signatures.push(sig_id);
      }
      TypeMemberKind::CallSignature(call) => {
        let sig = self.lower_signature(call, names);
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
            name: getter.name.clone(),
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
            name: setter.name.clone(),
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
    let key = match &prop.name {
      hir_js::PropertyName::Ident(id) => {
        PropKey::String(self.store.intern_name(names.resolve(*id)?.to_string()))
      }
      hir_js::PropertyName::String(s) => PropKey::String(self.store.intern_name(s.clone())),
      hir_js::PropertyName::Number(n) => {
        let parsed = n.parse::<i64>().ok()?;
        PropKey::Number(parsed)
      }
      hir_js::PropertyName::Computed => return None,
    };
    let ty = prop
      .type_annotation
      .map(|t| self.lower_type_expr(t, names))
      .unwrap_or(self.store.primitive_ids().unknown);
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
    let key = match &method.name {
      hir_js::PropertyName::Ident(id) => {
        PropKey::String(self.store.intern_name(names.resolve(*id)?.to_string()))
      }
      hir_js::PropertyName::String(s) => PropKey::String(self.store.intern_name(s.clone())),
      hir_js::PropertyName::Number(n) => {
        let parsed = n.parse::<i64>().ok()?;
        PropKey::Number(parsed)
      }
      hir_js::PropertyName::Computed => return None,
    };
    let (this_param, params) = self.lower_fn_params(&method.params, names);
    let sig = Signature {
      params,
      ret: method
        .return_type
        .map(|t| self.lower_type_expr(t, names))
        .unwrap_or(self.store.primitive_ids().unknown),
      type_params: method
        .type_params
        .iter()
        .map(|tp| self.alloc_type_param(*tp))
        .collect(),
      this_param,
    };
    let sig_id = self.store.intern_signature(sig);
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
    // Type parameter reference.
    if let TypeName::Ident(name_id) = &reference.name {
      if let Some(tp) = self.type_param_names.get(name_id) {
        return self.store.intern_type(TypeKind::TypeParam(*tp));
      }
    }

    if let Some(resolved) = self.resolve_type_name(&reference.name, names, None) {
      let args: Vec<_> = reference
        .type_args
        .iter()
        .map(|a| self.lower_type_expr(*a, names))
        .collect();
      return self.store.intern_type(TypeKind::Ref {
        def: resolved,
        args,
      });
    }

    let name = match &reference.name {
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
    };

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
    match name {
      TypeName::Ident(id) => {
        let resolved = names.resolve(*id)?.to_string();
        self.resolve_named_type(&resolved, file_override.unwrap_or(self.file))
      }
      TypeName::Qualified(path) => self
        .resolve_qualified_type(path, names, file_override.unwrap_or(self.file))
        .or_else(|| {
          path
            .last()
            .and_then(|id| names.resolve(*id))
            .and_then(|resolved| {
              self.resolve_named_type(&resolved.to_string(), file_override.unwrap_or(self.file))
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
        self.resolve_named_type(&name, target_file)
      }),
      TypeName::ImportExpr => None,
    }
  }

  fn resolve_named_type(&self, name: &str, file: FileId) -> Option<DefId> {
    if file == self.file {
      if let Some(local) = self.local_defs.get(name).copied() {
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
      return Some(*def);
    }

    if let Some(def) = self
      .def_by_name
      .and_then(|map| map.get(&(file, name.to_string())).copied())
    {
      return Some(def);
    }

    if let Some(sem) = self.semantics {
      if let Some(symbol) = sem.resolve_in_module(file, name, Namespace::TYPE) {
        if let Some(decl) = sem.symbol_decls(symbol, Namespace::TYPE).first() {
          let decl_data = sem.symbols().decl(*decl);
          let target = DefId(decl_data.def_id.0);
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
        if let Some(symbol) = group.symbol_for(Namespace::TYPE, sem.symbols()) {
          if let Some(def) = self.def_for_symbol(sem, symbol) {
            return Some(def);
          }
        }
      }
    }

    None
  }

  fn resolve_qualified_type(
    &self,
    path: &[hir_js::NameId],
    names: &hir_js::NameInterner,
    file: FileId,
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

    let mut symbol = self.resolve_symbol_in_module(sem, file, &segments[0])?;
    let mut current_file = self.symbol_target_file(sem, symbol).unwrap_or(file);
    for segment in segments.iter().skip(1) {
      symbol = self.resolve_symbol_export(sem, current_file, segment)?;
      current_file = self.symbol_target_file(sem, symbol).unwrap_or(current_file);
    }

    self.def_for_symbol(sem, symbol)
  }

  fn resolve_symbol_in_module(
    &self,
    sem: &TsProgramSemantics,
    file: FileId,
    name: &str,
  ) -> Option<semantic_js::ts::SymbolId> {
    for ns in [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE] {
      if let Some(sym) = sem.resolve_in_module(file, name, ns) {
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
  ) -> Option<semantic_js::ts::SymbolId> {
    for ns in [Namespace::TYPE, Namespace::NAMESPACE, Namespace::VALUE] {
      if let Some(sym) = sem.resolve_export(file, name, ns) {
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
      SymbolOrigin::Import { source, .. } => match source {
        ImportSource::File(from) => Some(*from),
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
      if let Some(decl) = sem.symbol_decls(symbol, ns).first() {
        let decl_data = sem.symbols().decl(*decl);
        let def = DefId(decl_data.def_id.0);
        return self
          .def_map
          .and_then(|map| map.get(&def).copied())
          .or_else(|| {
            self
              .def_by_name
              .and_then(|map| map.get(&(decl_data.file, decl_data.name.clone())).copied())
          })
          .or(Some(def));
      }
    }
    None
  }
}

impl<'a, 'diag> std::fmt::Debug for HirDeclLowerer<'a, 'diag> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("HirDeclLowerer")
      .field("file", &self.file)
      .finish_non_exhaustive()
  }
}
