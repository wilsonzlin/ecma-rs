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
  DefId, MappedModifier, MappedType, ObjectType, Param, PropData, PropKey, Property, Shape,
  Signature, TemplateChunk, TemplateLiteralType, TupleElem, TypeId, TypeKind, TypeParamId,
  TypeStore,
};

const CODE_UNRESOLVED_TYPE_REF: &str = "TC2008";
const CODE_UNSUPPORTED_QUALIFIED_NAME: &str = "TC2009";
const CODE_UNRESOLVED_IMPORT_TYPE: &str = "TC2010";
const CODE_UNRESOLVED_TYPE_QUERY: &str = "TC2011";

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
  type_params: AHashMap<String, TypeParamId>,
  next_type_param: u32,
  resolver: Option<Arc<dyn TypeResolver>>,
  file: Option<FileId>,
  diagnostics: Vec<Diagnostic>,
  predicates: Vec<LoweredPredicate>,
}

impl fmt::Debug for TypeLowerer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("TypeLowerer")
      .field("type_params", &self.type_params)
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
      type_params: AHashMap::new(),
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
    std::mem::take(&mut self.diagnostics)
  }

  /// Captured type predicates lowered so far.
  pub fn predicates(&self) -> &[LoweredPredicate] {
    &self.predicates
  }

  pub fn store(&self) -> Arc<TypeStore> {
    self.store.clone()
  }

  pub fn type_param_id(&self, name: &str) -> Option<TypeParamId> {
    self.type_params.get(name).copied()
  }

  pub fn register_type_params(&mut self, params: &[Node<TypeParameter>]) -> Vec<TypeParamId> {
    let mut ids = Vec::new();
    for param in params.iter() {
      ids.push(self.alloc_type_param(param.stx.name.clone()));
    }
    ids
  }

  fn alloc_type_param(&mut self, name: String) -> TypeParamId {
    let id = TypeParamId(self.next_type_param);
    self.next_type_param += 1;
    self.type_params.insert(name, id);
    id
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
    let snapshot = self.type_params.clone();
    let mut type_param_ids = Vec::new();
    if let Some(params) = func.stx.type_parameters.as_ref() {
      type_param_ids = self.register_type_params(params);
    }
    let sig = Signature {
      params: self.lower_params(&func.stx.parameters),
      ret: self.lower_type_expr(&func.stx.return_type),
      type_params: type_param_ids,
      this_param: None,
    };
    self.type_params = snapshot;
    let sig_id = self.store.intern_signature(sig);
    self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    })
  }

  fn lower_constructor_type(&mut self, cons: &Node<TypeConstructor>) -> TypeId {
    let snapshot = self.type_params.clone();
    let mut type_param_ids = Vec::new();
    if let Some(params) = cons.stx.type_parameters.as_ref() {
      type_param_ids = self.register_type_params(params);
    }
    let sig = Signature {
      params: self.lower_params(&cons.stx.parameters),
      ret: self.lower_type_expr(&cons.stx.return_type),
      type_params: type_param_ids,
      this_param: None,
    };
    self.type_params = snapshot;
    let sig_id = self.store.intern_signature(sig);
    self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    })
  }

  fn lower_params(&mut self, params: &[Node<TypeFunctionParameter>]) -> Vec<Param> {
    params
      .iter()
      .map(|p| Param {
        name: p
          .stx
          .name
          .as_ref()
          .map(|n| self.store.intern_name(n.clone())),
        ty: self.lower_type_expr(&p.stx.type_expr),
        optional: p.stx.optional,
        rest: p.stx.rest,
      })
      .collect()
  }

  fn lower_object_type(&mut self, obj: &Node<TypeObjectLiteral>) -> TypeId {
    let mut shape = Shape::new();

    for member in obj.stx.members.iter() {
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
                declared_on: None,
              },
            });
          }
        }
        TypeMember::Constructor(cons) => {
          let sig = Signature {
            params: self.lower_params(&cons.stx.parameters),
            ret: cons
              .stx
              .return_type
              .as_ref()
              .map(|t| self.lower_type_expr(t))
              .unwrap_or(self.store.primitive_ids().unknown),
            type_params: Vec::new(),
            this_param: None,
          };
          let sig_id = self.store.intern_signature(sig);
          shape.construct_signatures.push(sig_id);
        }
        TypeMember::CallSignature(call) => {
          let mut type_param_ids = Vec::new();
          if let Some(params) = call.stx.type_parameters.as_ref() {
            type_param_ids = self.register_type_params(params);
          }
          let sig = Signature {
            params: self.lower_params(&call.stx.parameters),
            ret: call
              .stx
              .return_type
              .as_ref()
              .map(|t| self.lower_type_expr(t))
              .unwrap_or(self.store.primitive_ids().unknown),
            type_params: type_param_ids,
            this_param: None,
          };
          let sig_id = self.store.intern_signature(sig);
          shape.call_signatures.push(sig_id);
        }
        TypeMember::IndexSignature(idx) => {
          shape.indexers.push(types_ts_interned::Indexer {
            key_type: self.lower_type_expr(&idx.stx.parameter_type),
            value_type: self.lower_type_expr(&idx.stx.type_annotation),
            readonly: idx.stx.readonly,
          });
        }
        _ => {}
      }
    }

    let shape = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape });
    self.store.intern_type(TypeKind::Object(obj))
  }

  fn lower_property(&mut self, prop: &Node<TypePropertySignature>) -> Option<(PropKey, PropData)> {
    let key = match &prop.stx.key {
      TypePropertyKey::Identifier(id) | TypePropertyKey::String(id) => {
        PropKey::String(self.store.intern_name(id.clone()))
      }
      TypePropertyKey::Number(num) => {
        let parsed = num.parse::<i64>().ok()?;
        PropKey::Number(parsed)
      }
      TypePropertyKey::Computed(_) => return None,
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
      declared_on: None,
    };
    Some((key, data))
  }

  fn lower_method(&mut self, method: &Node<TypeMethodSignature>) -> Option<(PropKey, TypeId)> {
    let key = match &method.stx.key {
      TypePropertyKey::Identifier(id) | TypePropertyKey::String(id) => {
        PropKey::String(self.store.intern_name(id.clone()))
      }
      TypePropertyKey::Number(num) => {
        let parsed = num.parse::<i64>().ok()?;
        PropKey::Number(parsed)
      }
      TypePropertyKey::Computed(_) => return None,
    };

    let mut type_param_ids = Vec::new();
    if let Some(params) = method.stx.type_parameters.as_ref() {
      type_param_ids = self.register_type_params(params);
    }
    let sig = Signature {
      params: self.lower_params(&method.stx.parameters),
      ret: method
        .stx
        .return_type
        .as_ref()
        .map(|t| self.lower_type_expr(t))
        .unwrap_or(self.store.primitive_ids().unknown),
      type_params: type_param_ids,
      this_param: None,
    };
    let sig_id = self.store.intern_signature(sig);
    Some((
      key,
      self.store.intern_type(TypeKind::Callable {
        overloads: vec![sig_id],
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

    let prev_params = self.type_params.clone();
    let prev_next_param = self.next_type_param;
    let distributive = self.is_naked_type_param(check_type);
    let check = self.lower_type_expr(check_type);
    let extends = self.lower_type_expr(extends_type);
    let true_ty = self.lower_type_expr(true_type);
    let false_ty = self.lower_type_expr(false_type);
    self.type_params = prev_params;
    self.next_type_param = prev_next_param;
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
          TypeEntityName::Identifier(ref name) if self.type_params.contains_key(name)
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

    let prev = self.type_params.clone();
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

    self.type_params = prev;
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
        if let Some(id) = self.type_params.get(name).copied() {
          if !type_args.is_empty() {
            self.push_diag(
              reference.loc,
              CODE_UNRESOLVED_TYPE_REF,
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
          CODE_UNRESOLVED_TYPE_REF,
          format!("unresolved type '{}'", name),
        );
        self.store.primitive_ids().unknown
      }
      TypeEntityName::Qualified(_) => {
        let Some(path) = entity_name_segments(&reference.stx.name) else {
          self.push_diag(
            reference.loc,
            CODE_UNSUPPORTED_QUALIFIED_NAME,
            "unsupported qualified type reference",
          );
          return self.store.primitive_ids().unknown;
        };
        if let Some(resolved) = self.resolve_to_ref(&path, type_args, false) {
          return resolved;
        }
        self.push_diag(
          reference.loc,
          CODE_UNSUPPORTED_QUALIFIED_NAME,
          format!("unresolved qualified type '{}'", path.join(".")),
        );
        self.store.primitive_ids().unknown
      }
      TypeEntityName::Import(_) => {
        self.push_diag(
          reference.loc,
          CODE_UNRESOLVED_TYPE_REF,
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
        CODE_UNRESOLVED_TYPE_QUERY,
        "unsupported typeof query target",
      );
      return self.store.primitive_ids().unknown;
    };
    if let Some(resolved) = self.resolve_to_ref(&path, Vec::new(), true) {
      return resolved;
    }
    self.push_diag(
      query.loc,
      CODE_UNRESOLVED_TYPE_QUERY,
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
    self.push_diag(import.loc, CODE_UNRESOLVED_IMPORT_TYPE, message);
    self.store.primitive_ids().unknown
  }

  fn lower_infer_type(&mut self, infer: &Node<TypeInfer>) -> TypeId {
    let id = match self.type_params.get(&infer.stx.type_parameter) {
      Some(id) => *id,
      None => self.alloc_type_param(infer.stx.type_parameter.clone()),
    };
    // TODO: Track infer constraints once the type representation supports it.
    self.store.intern_type(TypeKind::Infer(id))
  }

  fn lower_type_predicate(&mut self, pred: &Node<TypePredicate>) -> TypeId {
    let ty = pred
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.lower_type_expr(t));
    let span = self.span_for(pred.loc);
    self.predicates.push(LoweredPredicate {
      span,
      asserts: pred.stx.asserts,
      parameter: pred.stx.parameter_name.clone(),
      ty,
    });
    self.store.primitive_ids().boolean
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

  fn push_diag(&mut self, loc: Loc, code: &'static str, message: impl Into<String>) {
    let span = self.span_for(loc);
    self
      .diagnostics
      .push(Diagnostic::error(code, message, span));
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
