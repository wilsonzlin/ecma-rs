use crate::codes;
use ahash::AHashMap;
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::{
  MappedTypeModifier, TypeArray, TypeConditional, TypeConstructor, TypeEntityName, TypeExpr,
  TypeFunction, TypeFunctionParameter, TypeIndexedAccess, TypeInfer, TypeIntersection, TypeKeyOf,
  TypeLiteral, TypeMapped, TypeMember, TypeMethodSignature, TypeObjectLiteral, TypeParameter,
  TypePredicate, TypePropertyKey, TypePropertySignature, TypeTemplateLiteral, TypeTuple,
  TypeTupleElement, TypeUnion,
};
use parse_js::loc::Loc;
use std::fmt;
use std::sync::Arc;
use types_ts_interned::{
  DefId, Indexer, MappedModifier, MappedType, ObjectType, Param, PropData, PropKey, Property,
  Shape, Signature, TemplateChunk, TemplateLiteralType, TupleElem, TypeId, TypeKind, TypeParamDecl,
  TypeParamId, TypeStore,
};

/// Resolves entity names in type positions to canonical [`DefId`]s.
pub trait TypeResolver: Send + Sync {
  /// Resolve a type name (e.g. `["Promise"]` or `["ns", "Type"]`) to a
  /// definition identifier.
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId>;

  /// Resolve a `typeof` query. By default this delegates to [`resolve_type_name`].
  fn resolve_typeof(&self, path: &[String]) -> Option<DefId> {
    self.resolve_type_name(path)
  }

  /// Resolve an `import()` type with an optional qualifier path inside the
  /// imported module namespace.
  fn resolve_import_type(&self, _module: &str, _qualifier: Option<&[String]>) -> Option<DefId> {
    None
  }
}

/// Captured lowering information for a type predicate. The lowered type for the
/// predicate itself is `boolean`, but the richer predicate is preserved for
/// downstream narrowing.
#[derive(Debug, Clone)]
pub struct LoweredPredicate {
  pub span: Span,
  pub asserts: bool,
  pub parameter: String,
  pub ty: Option<TypeId>,
}

/// Lowers `parse-js` [`TypeExpr`] nodes into interned type representations.
pub struct TypeLowerer {
  store: Arc<TypeStore>,
  type_param_scopes: Vec<AHashMap<String, TypeParamId>>,
  next_type_param: u32,
  resolver: Option<Arc<dyn TypeResolver>>,
  file: Option<FileId>,
  diagnostics: Vec<Diagnostic>,
  predicates: Vec<LoweredPredicate>,
}

impl fmt::Debug for TypeLowerer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("TypeLowerer")
      .field("type_param_scopes", &self.type_param_scopes)
      .field("next_type_param", &self.next_type_param)
      .field("diagnostics", &self.diagnostics)
      .field("predicates", &self.predicates)
      .finish()
  }
}

impl TypeLowerer {
  pub fn new(store: Arc<TypeStore>) -> Self {
    Self {
      store,
      type_param_scopes: vec![AHashMap::new()],
      next_type_param: 0,
      resolver: None,
      file: None,
      diagnostics: Vec::new(),
      predicates: Vec::new(),
    }
  }

  /// Create a new lowerer configured with a resolver for type references.
  pub fn with_resolver(store: Arc<TypeStore>, resolver: Arc<dyn TypeResolver>) -> Self {
    let mut lowerer = Self::new(store);
    lowerer.resolver = Some(resolver);
    lowerer
  }

  /// Associate a file id with this lowerer for diagnostics and predicate spans.
  pub fn set_file(&mut self, file: FileId) {
    self.file = Some(file);
  }

  /// Set or clear the resolver used to resolve named type references.
  pub fn set_resolver(&mut self, resolver: Option<Arc<dyn TypeResolver>>) {
    self.resolver = resolver;
  }

  /// Diagnostics emitted while lowering. These capture unsupported or unresolved
  /// constructs that could not be represented precisely.
  pub fn diagnostics(&self) -> &[Diagnostic] {
    &self.diagnostics
  }

  /// Take ownership of accumulated diagnostics.
  pub fn take_diagnostics(&mut self) -> Vec<Diagnostic> {
    let mut diagnostics = std::mem::take(&mut self.diagnostics);
    codes::normalize_diagnostics(&mut diagnostics);
    diagnostics
  }

  /// Captured type predicates lowered so far.
  pub fn predicates(&self) -> &[LoweredPredicate] {
    &self.predicates
  }

  pub fn store(&self) -> Arc<TypeStore> {
    self.store.clone()
  }

  pub fn type_param_id(&self, name: &str) -> Option<TypeParamId> {
    self.lookup_type_param(name)
  }

  pub fn register_type_params(&mut self, params: &[Node<TypeParameter>]) -> Vec<TypeParamDecl> {
    let mut ids = Vec::new();
    for param in params.iter() {
      ids.push(self.alloc_type_param(param.stx.name.clone()));
    }
    params
      .iter()
      .zip(ids.iter())
      .map(|(param, id)| TypeParamDecl {
        id: *id,
        constraint: param
          .stx
          .constraint
          .as_ref()
          .map(|c| self.lower_type_expr(c)),
        default: param.stx.default.as_ref().map(|d| self.lower_type_expr(d)),
      })
      .collect()
  }

  fn alloc_type_param(&mut self, name: String) -> TypeParamId {
    let id = TypeParamId(self.next_type_param);
    self.next_type_param += 1;
    self
      .type_param_scopes
      .last_mut()
      .expect("type parameter scope stack should not be empty")
      .insert(name, id);
    id
  }

  pub(crate) fn push_type_param_scope(&mut self) {
    self.type_param_scopes.push(AHashMap::new());
  }

  pub(crate) fn pop_type_param_scope(&mut self) {
    self
      .type_param_scopes
      .pop()
      .expect("type parameter scope stack underflow");
  }

  fn lookup_type_param(&self, name: &str) -> Option<TypeParamId> {
    for scope in self.type_param_scopes.iter().rev() {
      if let Some(id) = scope.get(name) {
        return Some(*id);
      }
    }
    None
  }

  pub fn lower_type_expr(&mut self, expr: &Node<TypeExpr>) -> TypeId {
    match expr.stx.as_ref() {
      TypeExpr::Any(_) => self.store.primitive_ids().any,
      TypeExpr::Unknown(_) => self.store.primitive_ids().unknown,
      TypeExpr::Never(_) => self.store.primitive_ids().never,
      TypeExpr::Void(_) => self.store.primitive_ids().void,
      TypeExpr::String(_) => self.store.primitive_ids().string,
      TypeExpr::Number(_) => self.store.primitive_ids().number,
      TypeExpr::Boolean(_) => self.store.primitive_ids().boolean,
      TypeExpr::Null(_) => self.store.primitive_ids().null,
      TypeExpr::Undefined(_) => self.store.primitive_ids().undefined,
      TypeExpr::BigInt(_) => self.store.primitive_ids().bigint,
      TypeExpr::Symbol(_) => self.store.primitive_ids().symbol,
      TypeExpr::UniqueSymbol(_) => self.store.primitive_ids().unique_symbol,
      TypeExpr::ThisType(_) => self.store.intern_type(TypeKind::This),
      TypeExpr::Object(_) => {
        let shape = self.store.intern_shape(Shape::new());
        let obj = self.store.intern_object(ObjectType { shape });
        self.store.intern_type(TypeKind::Object(obj))
      }
      TypeExpr::TypeReference(reference) => self.lower_type_reference(reference),
      TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
        TypeLiteral::String(value) => {
          let name = self.store.intern_name(value.clone());
          self.store.intern_type(TypeKind::StringLiteral(name))
        }
        TypeLiteral::Number(value) => {
          let parsed = value.parse::<f64>().unwrap_or(0.0);
          self
            .store
            .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(parsed)))
        }
        TypeLiteral::Boolean(value) => self.store.intern_type(TypeKind::BooleanLiteral(*value)),
        TypeLiteral::BigInt(value) => {
          let trimmed = value.trim_end_matches('n');
          let parsed = trimmed
            .parse::<BigInt>()
            .unwrap_or_else(|_| BigInt::from(0u8));
          self.store.intern_type(TypeKind::BigIntLiteral(parsed))
        }
        TypeLiteral::Null => self.store.primitive_ids().null,
      },
      TypeExpr::ArrayType(arr) => {
        let TypeArray {
          element_type,
          readonly,
        } = arr.stx.as_ref();
        let elem = self.lower_type_expr(element_type);
        self.store.intern_type(TypeKind::Array {
          ty: elem,
          readonly: *readonly,
        })
      }
      TypeExpr::TupleType(tuple) => self.lower_tuple_type(tuple),
      TypeExpr::UnionType(union) => {
        let TypeUnion { types } = union.stx.as_ref();
        let members = types.iter().map(|t| self.lower_type_expr(t)).collect();
        self.store.union(members)
      }
      TypeExpr::IntersectionType(intersection) => {
        let TypeIntersection { types } = intersection.stx.as_ref();
        let members = types.iter().map(|t| self.lower_type_expr(t)).collect();
        self.store.intersection(members)
      }
      TypeExpr::FunctionType(func) => self.lower_function_type(func),
      TypeExpr::ConstructorType(cons) => self.lower_constructor_type(cons),
      TypeExpr::ObjectType(obj) => self.lower_object_type(obj),
      TypeExpr::ParenthesizedType(inner) => self.lower_type_expr(&inner.stx.type_expr),
      TypeExpr::KeyOfType(keyof) => {
        let TypeKeyOf { type_expr } = keyof.stx.as_ref();
        let inner = self.lower_type_expr(type_expr);
        self.store.intern_type(TypeKind::KeyOf(inner))
      }
      TypeExpr::IndexedAccessType(indexed) => {
        let TypeIndexedAccess {
          object_type,
          index_type,
        } = indexed.stx.as_ref();
        let obj = self.lower_type_expr(object_type);
        let index = self.lower_type_expr(index_type);
        self
          .store
          .intern_type(TypeKind::IndexedAccess { obj, index })
      }
      TypeExpr::ConditionalType(cond) => self.lower_conditional_type(cond),
      TypeExpr::MappedType(mapped) => self.lower_mapped_type(mapped),
      TypeExpr::TemplateLiteralType(tpl) => self.lower_template_literal(tpl),
      TypeExpr::TypePredicate(pred) => self.lower_type_predicate(pred),
      TypeExpr::TypeQuery(query) => self.lower_type_query(query),
      TypeExpr::ImportType(import) => self.lower_import_type(import),
      TypeExpr::InferType(infer) => self.lower_infer_type(infer),
    }
  }

  fn lower_tuple_type(&mut self, tuple: &Node<TypeTuple>) -> TypeId {
    let mut elems = Vec::new();
    for elem in tuple.stx.elements.iter() {
      let TypeTupleElement {
        label: _,
        optional,
        rest,
        type_expr,
      } = elem.stx.as_ref();
      elems.push(TupleElem {
        ty: self.lower_type_expr(type_expr),
        optional: *optional,
        rest: *rest,
        readonly: tuple.stx.readonly,
      });
    }
    self.store.intern_type(TypeKind::Tuple(elems))
  }

  fn lower_function_type(&mut self, func: &Node<TypeFunction>) -> TypeId {
    let sig = self.lower_member_signature(
      &func.stx.type_parameters,
      &func.stx.parameters,
      Some(func.stx.return_type.as_ref()),
    );
    self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig],
    })
  }

  fn lower_constructor_type(&mut self, cons: &Node<TypeConstructor>) -> TypeId {
    let sig = self.lower_member_signature(
      &cons.stx.type_parameters,
      &cons.stx.parameters,
      Some(cons.stx.return_type.as_ref()),
    );
    self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig],
    })
  }

  fn lower_params(
    &mut self,
    params: &[Node<TypeFunctionParameter>],
  ) -> (Option<TypeId>, Vec<Param>) {
    let mut lowered = Vec::new();
    let mut this_param = None;
    for p in params.iter() {
      if matches!(p.stx.name.as_deref(), Some("this")) && this_param.is_none() {
        this_param = Some(self.lower_type_expr(&p.stx.type_expr));
        continue;
      }
      lowered.push(Param {
        name: p
          .stx
          .name
          .as_ref()
          .map(|n| self.store.intern_name(n.clone())),
        ty: self.lower_type_expr(&p.stx.type_expr),
        optional: p.stx.optional,
        rest: p.stx.rest,
      });
    }
    (this_param, lowered)
  }

  fn lower_member_signature(
    &mut self,
    type_params: &Option<Vec<Node<TypeParameter>>>,
    params: &[Node<TypeFunctionParameter>],
    return_type: Option<&Node<TypeExpr>>,
  ) -> types_ts_interned::SignatureId {
    self.push_type_param_scope();
    let type_params = type_params
      .as_ref()
      .map(|params| self.register_type_params(params))
      .unwrap_or_default();
    let (this_param, params) = self.lower_params(params);
    let ret = return_type
      .map(|t| self.lower_type_expr(t))
      .unwrap_or(self.store.primitive_ids().unknown);
    let sig = Signature {
      params,
      ret,
      type_params,
      this_param,
    };
    self.pop_type_param_scope();
    self.store.intern_signature(sig)
  }

  pub(crate) fn lower_type_members(&mut self, members: &[Node<TypeMember>]) -> Shape {
    let mut shape = Shape::new();

    for member in members.iter() {
      match member.stx.as_ref() {
        TypeMember::Property(prop) => {
          if let Some((key, data)) = self.lower_property(prop) {
            shape.properties.push(Property { key, data });
          }
        }
        TypeMember::Method(method) => {
          if let Some((key, sig)) = self.lower_method(method) {
            shape.properties.push(Property {
              key,
              data: PropData {
                ty: sig,
                optional: method.stx.optional,
                readonly: false,
                accessibility: None,
                is_method: true,
                origin: None,
                declared_on: None,
              },
            });
          }
        }
        TypeMember::Constructor(cons) => {
          let sig = self.lower_member_signature(
            &cons.stx.type_parameters,
            &cons.stx.parameters,
            cons.stx.return_type.as_ref(),
          );
          shape.construct_signatures.push(sig);
        }
        TypeMember::CallSignature(call) => {
          let sig = self.lower_member_signature(
            &call.stx.type_parameters,
            &call.stx.parameters,
            call.stx.return_type.as_ref(),
          );
          shape.call_signatures.push(sig);
        }
        TypeMember::IndexSignature(idx) => {
          shape.indexers.push(Indexer {
            key_type: self.lower_type_expr(&idx.stx.parameter_type),
            value_type: self.lower_type_expr(&idx.stx.type_annotation),
            readonly: idx.stx.readonly,
          });
        }
        TypeMember::GetAccessor(get) => {
          if let Some(key) = self.lower_type_member_key(&get.stx.key) {
            let ty = get
              .stx
              .return_type
              .as_ref()
              .map(|t| self.lower_type_expr(t))
              .unwrap_or(self.store.primitive_ids().unknown);
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
        }
        TypeMember::SetAccessor(set) => {
          if let Some(key) = self.lower_type_member_key(&set.stx.key) {
            shape.properties.push(Property {
              key,
              data: PropData {
                ty: self.lower_type_expr(&set.stx.parameter.stx.type_expr),
                optional: set.stx.parameter.stx.optional,
                readonly: false,
                accessibility: None,
                is_method: false,
                origin: None,
                declared_on: None,
              },
            });
          }
        }
        TypeMember::MappedProperty(_) => {}
      }
    }

    shape
  }

  fn lower_object_type(&mut self, obj: &Node<TypeObjectLiteral>) -> TypeId {
    let shape = self.lower_type_members(&obj.stx.members);
    let shape = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn lower_type_member_key(&self, key: &TypePropertyKey) -> Option<PropKey> {
    match key {
      TypePropertyKey::Identifier(id) | TypePropertyKey::String(id) => {
        Some(PropKey::String(self.store.intern_name(id.clone())))
      }
      TypePropertyKey::Number(num) => {
        let parsed = num.parse::<i64>().ok()?;
        Some(PropKey::Number(parsed))
      }
      TypePropertyKey::Computed(_) => None,
    }
  }

  fn lower_property(&mut self, prop: &Node<TypePropertySignature>) -> Option<(PropKey, PropData)> {
    let key = match self.lower_type_member_key(&prop.stx.key) {
      Some(key) => key,
      None => return None,
    };
    let ty = prop
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.lower_type_expr(t))
      .unwrap_or(self.store.primitive_ids().unknown);
    let data = PropData {
      ty,
      optional: prop.stx.optional,
      readonly: prop.stx.readonly,
      accessibility: None,
      is_method: false,
      origin: None,
      declared_on: None,
    };
    Some((key, data))
  }

  fn lower_method(&mut self, method: &Node<TypeMethodSignature>) -> Option<(PropKey, TypeId)> {
    let key = match self.lower_type_member_key(&method.stx.key) {
      Some(key) => key,
      None => return None,
    };

    let sig = self.lower_member_signature(
      &method.stx.type_parameters,
      &method.stx.parameters,
      method.stx.return_type.as_ref(),
    );
    Some((
      key,
      self.store.intern_type(TypeKind::Callable {
        overloads: vec![sig],
      }),
    ))
  }

  fn lower_conditional_type(&mut self, cond: &Node<TypeConditional>) -> TypeId {
    let TypeConditional {
      check_type,
      extends_type,
      true_type,
      false_type,
    } = cond.stx.as_ref();

    let distributive = self.is_naked_type_param(check_type);
    self.push_type_param_scope();
    let check = self.lower_type_expr(check_type);
    let extends = self.lower_type_expr(extends_type);
    let true_ty = self.lower_type_expr(true_type);
    self.pop_type_param_scope();
    let false_ty = self.lower_type_expr(false_type);
    self.store.intern_type(TypeKind::Conditional {
      check,
      extends,
      true_ty,
      false_ty,
      distributive,
    })
  }

  fn is_naked_type_param(&self, expr: &Node<TypeExpr>) -> bool {
    match expr.stx.as_ref() {
      TypeExpr::TypeReference(reference) if reference.stx.type_arguments.is_none() => {
        matches!(
          reference.stx.name,
          TypeEntityName::Identifier(ref name) if self.lookup_type_param(name).is_some()
        )
      }
      _ => false,
    }
  }

  fn lower_mapped_type(&mut self, mapped: &Node<TypeMapped>) -> TypeId {
    let TypeMapped {
      readonly_modifier,
      type_parameter,
      constraint,
      name_type,
      optional_modifier,
      type_expr,
    } = mapped.stx.as_ref();

    self.push_type_param_scope();
    let param_id = self.alloc_type_param(type_parameter.clone());

    let source = self.lower_type_expr(constraint);
    let value = self.lower_type_expr(type_expr);
    let remap = name_type.as_ref().map(|n| self.lower_type_expr(n));

    let result = self.store.intern_type(TypeKind::Mapped(MappedType {
      param: param_id,
      source,
      value,
      readonly: map_mapped_modifier(readonly_modifier),
      optional: map_mapped_modifier(optional_modifier),
      name_type: remap,
      as_type: remap,
    }));

    self.pop_type_param_scope();
    result
  }

  fn lower_template_literal(&mut self, tpl: &Node<TypeTemplateLiteral>) -> TypeId {
    let head = tpl.stx.head.clone();
    let spans = tpl
      .stx
      .spans
      .iter()
      .map(|span| TemplateChunk {
        literal: span.stx.literal.clone(),
        ty: self.lower_type_expr(&span.stx.type_expr),
      })
      .collect::<Vec<_>>();
    self
      .store
      .intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
        head,
        spans,
      }))
  }

  fn lower_type_reference(
    &mut self,
    reference: &Node<parse_js::ast::type_expr::TypeReference>,
  ) -> TypeId {
    let type_args = self.lower_type_arguments(&reference.stx.type_arguments);
    match &reference.stx.name {
      TypeEntityName::Identifier(name) => {
        if let Some(id) = self.lookup_type_param(name) {
          if !type_args.is_empty() {
            self.push_diag(
              reference.loc,
              &codes::UNRESOLVED_TYPE_REFERENCE,
              format!("type parameter '{}' cannot accept type arguments", name),
            );
          }
          return self.store.intern_type(TypeKind::TypeParam(id));
        }
        let path = vec![name.clone()];
        if let Some(resolved) = self.resolve_to_ref(&path, type_args.clone(), false) {
          return resolved;
        }
        self.push_diag(
          reference.loc,
          &codes::UNRESOLVED_TYPE_REFERENCE,
          format!("unresolved type '{}'", name),
        );
        self.store.primitive_ids().unknown
      }
      TypeEntityName::Qualified(_) => {
        let Some(path) = entity_name_segments(&reference.stx.name) else {
          self.push_diag(
            reference.loc,
            &codes::UNSUPPORTED_QUALIFIED_NAME,
            "unsupported qualified type reference",
          );
          return self.store.primitive_ids().unknown;
        };
        if let Some(resolved) = self.resolve_to_ref(&path, type_args, false) {
          return resolved;
        }
        self.push_diag(
          reference.loc,
          &codes::UNSUPPORTED_QUALIFIED_NAME,
          format!("unresolved qualified type '{}'", path.join(".")),
        );
        self.store.primitive_ids().unknown
      }
      TypeEntityName::Import(_) => {
        self.push_diag(
          reference.loc,
          &codes::UNRESOLVED_TYPE_REFERENCE,
          "import expressions in type references are not supported",
        );
        self.store.primitive_ids().unknown
      }
    }
  }

  fn lower_type_query(&mut self, query: &Node<parse_js::ast::type_expr::TypeQuery>) -> TypeId {
    let Some(path) = entity_name_segments(&query.stx.expr_name) else {
      self.push_diag(
        query.loc,
        &codes::UNRESOLVED_TYPE_QUERY,
        "unsupported typeof query target",
      );
      return self.store.primitive_ids().unknown;
    };
    if let Some(resolved) = self.resolve_to_ref(&path, Vec::new(), true) {
      return resolved;
    }
    self.push_diag(
      query.loc,
      &codes::UNRESOLVED_TYPE_QUERY,
      format!("cannot resolve typeof {}", path.join(".")),
    );
    self.store.primitive_ids().unknown
  }

  fn lower_import_type(&mut self, import: &Node<parse_js::ast::type_expr::TypeImport>) -> TypeId {
    let qualifier = import
      .stx
      .qualifier
      .as_ref()
      .and_then(|name| entity_name_segments(name));
    let type_args = self.lower_type_arguments(&import.stx.type_arguments);
    if let Some(resolver) = &self.resolver {
      if let Some(def) =
        resolver.resolve_import_type(&import.stx.module_specifier, qualifier.as_deref())
      {
        return self.store.intern_type(TypeKind::Ref {
          def,
          args: type_args,
        });
      }
    }
    let mut message = format!(
      "unable to resolve import(\"{}\") type",
      import.stx.module_specifier
    );
    if let Some(path) = qualifier.as_ref() {
      message.push_str(&format!(" for {}", path.join(".")));
    }
    self.push_diag(import.loc, &codes::UNRESOLVED_IMPORT_TYPE, message);
    self.store.primitive_ids().unknown
  }

  fn lower_infer_type(&mut self, infer: &Node<TypeInfer>) -> TypeId {
    let id = self
      .type_param_scopes
      .last()
      .and_then(|scope| scope.get(&infer.stx.type_parameter).copied())
      .unwrap_or_else(|| self.alloc_type_param(infer.stx.type_parameter.clone()));
    let constraint = infer
      .stx
      .constraint
      .as_ref()
      .map(|c| self.lower_type_expr(c));
    self.store.intern_type(TypeKind::Infer {
      param: id,
      constraint,
    })
  }

  fn lower_type_predicate(&mut self, pred: &Node<TypePredicate>) -> TypeId {
    let asserted = pred
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.lower_type_expr(t));
    let span = self.span_for(pred.loc);
    self.predicates.push(LoweredPredicate {
      span,
      asserts: pred.stx.asserts,
      parameter: pred.stx.parameter_name.clone(),
      ty: asserted,
    });
    let parameter = if pred.stx.parameter_name.is_empty() {
      None
    } else {
      Some(self.store.intern_name(pred.stx.parameter_name.clone()))
    };
    self.store.intern_type(TypeKind::Predicate {
      parameter,
      asserted,
      asserts: pred.stx.asserts,
    })
  }

  fn lower_type_arguments(&mut self, args: &Option<Vec<Node<TypeExpr>>>) -> Vec<TypeId> {
    args
      .as_ref()
      .map(|args| args.iter().map(|arg| self.lower_type_expr(arg)).collect())
      .unwrap_or_default()
  }

  fn resolve_to_ref(
    &mut self,
    path: &[String],
    args: Vec<TypeId>,
    for_typeof: bool,
  ) -> Option<TypeId> {
    let Some(resolver) = &self.resolver else {
      return None;
    };
    let resolved = if for_typeof {
      resolver.resolve_typeof(path)
    } else {
      resolver.resolve_type_name(path)
    };
    resolved.map(|def| {
      self.store.intern_type(TypeKind::Ref {
        def,
        args: args.clone(),
      })
    })
  }

  fn span_for(&self, loc: Loc) -> Span {
    let file = self.file.unwrap_or(FileId(0));
    let start = loc.0.min(u32::MAX as usize) as u32;
    let end = loc.1.min(u32::MAX as usize) as u32;
    Span {
      file,
      range: TextRange::new(start, end),
    }
  }

  fn push_diag(&mut self, loc: Loc, code: &codes::Code, message: impl Into<String>) {
    let span = self.span_for(loc);
    self.diagnostics.push(code.error(message, span));
  }
}

fn map_mapped_modifier(modifier: &Option<MappedTypeModifier>) -> MappedModifier {
  match modifier {
    Some(MappedTypeModifier::Plus) | Some(MappedTypeModifier::None) => MappedModifier::Add,
    Some(MappedTypeModifier::Minus) => MappedModifier::Remove,
    None => MappedModifier::Preserve,
  }
}

fn entity_name_segments(name: &TypeEntityName) -> Option<Vec<String>> {
  match name {
    TypeEntityName::Identifier(id) => Some(vec![id.clone()]),
    TypeEntityName::Qualified(qualified) => {
      let mut parts = entity_name_segments(&qualified.left)?;
      parts.push(qualified.right.clone());
      Some(parts)
    }
    TypeEntityName::Import(_) => None,
  }
}
