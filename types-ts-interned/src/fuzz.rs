use std::sync::Arc;

use crate::{
  Indexer, MappedModifier, MappedType, ObjectType, Param, PropData, PropKey, Property, RelateCtx,
  Shape, Signature, TemplateChunk, TemplateLiteralType, TupleElem, TypeEvaluator, TypeExpander,
  TypeId, TypeKind, TypeParamId, TypeStore,
};
use hir_js::DefId;
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use serde::Deserialize;

#[derive(Debug, Deserialize, Clone)]
pub struct SerializedTypeGraph {
  #[serde(default)]
  pub roots: Vec<usize>,
  #[serde(default)]
  pub nodes: Vec<SerializedType>,
}

#[derive(Debug, Deserialize, Clone)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum SerializedType {
  Any,
  Unknown,
  Never,
  Void,
  Null,
  Undefined,
  Boolean,
  Number,
  String,
  BigInt,
  Symbol,
  UniqueSymbol,
  BooleanLiteral {
    value: bool,
  },
  NumberLiteral {
    value: f64,
  },
  StringLiteral {
    value: String,
  },
  BigIntLiteral {
    value: i64,
  },
  This,
  Infer {
    id: u32,
    #[serde(default)]
    constraint: Option<usize>,
  },
  Tuple {
    elements: Vec<SerializedTupleElem>,
  },
  Array {
    ty: usize,
    #[serde(default)]
    readonly: bool,
  },
  Union {
    members: Vec<usize>,
  },
  Intersection {
    members: Vec<usize>,
  },
  Object {
    properties: Vec<SerializedProp>,
    #[serde(default)]
    indexers: Vec<SerializedIndexer>,
  },
  Callable {
    params: Vec<SerializedParam>,
    ret: usize,
  },
  Ref {
    def: u32,
    #[serde(default)]
    args: Vec<usize>,
  },
  TypeParam {
    id: u32,
  },
  Conditional {
    check: usize,
    extends: usize,
    true_ty: usize,
    false_ty: usize,
    #[serde(default)]
    distributive: bool,
  },
  Mapped {
    param: u32,
    source: usize,
    value: usize,
    #[serde(default)]
    readonly: Option<SerializedModifier>,
    #[serde(default)]
    optional: Option<SerializedModifier>,
    #[serde(default)]
    name_type: Option<usize>,
    #[serde(default)]
    as_type: Option<usize>,
  },
  TemplateLiteral {
    head: String,
    spans: Vec<SerializedTemplateSpan>,
  },
  IndexedAccess {
    obj: usize,
    index: usize,
  },
  KeyOf {
    ty: usize,
  },
}

#[derive(Debug, Deserialize, Clone)]
struct SerializedTupleElem {
  ty: usize,
  #[serde(default)]
  optional: bool,
  #[serde(default)]
  rest: bool,
  #[serde(default)]
  readonly: bool,
}

#[derive(Debug, Deserialize, Clone)]
struct SerializedParam {
  #[serde(default)]
  name: Option<String>,
  ty: usize,
  #[serde(default)]
  optional: bool,
  #[serde(default)]
  rest: bool,
}

#[derive(Debug, Deserialize, Clone)]
struct SerializedTemplateSpan {
  ty: usize,
  #[serde(default)]
  literal: String,
}

#[derive(Debug, Deserialize, Clone)]
struct SerializedProp {
  name: String,
  ty: usize,
  #[serde(default)]
  optional: bool,
  #[serde(default)]
  readonly: bool,
}

#[derive(Debug, Deserialize, Clone)]
struct SerializedIndexer {
  key: usize,
  value: usize,
  #[serde(default)]
  readonly: bool,
}

#[derive(Debug, Deserialize, Clone, Copy)]
#[serde(rename_all = "snake_case")]
enum SerializedModifier {
  Add,
  Remove,
  Preserve,
}

fn modifier_value(modifier: Option<SerializedModifier>) -> MappedModifier {
  match modifier.unwrap_or(SerializedModifier::Preserve) {
    SerializedModifier::Add => MappedModifier::Add,
    SerializedModifier::Remove => MappedModifier::Remove,
    SerializedModifier::Preserve => MappedModifier::Preserve,
  }
}

fn resolve_index(
  graph: &SerializedTypeGraph,
  store: &Arc<TypeStore>,
  cache: &mut [Option<TypeId>],
  visiting: &mut [bool],
  idx: usize,
  depth: usize,
) -> TypeId {
  if idx >= graph.nodes.len() || depth > 64 {
    return store.primitive_ids().unknown;
  }
  if let Some(existing) = cache[idx] {
    return existing;
  }
  if visiting[idx] {
    return store.primitive_ids().never;
  }
  visiting[idx] = true;
  let node = graph.nodes[idx].clone();
  let ty = match node {
    SerializedType::Any => store.primitive_ids().any,
    SerializedType::Unknown => store.primitive_ids().unknown,
    SerializedType::Never => store.primitive_ids().never,
    SerializedType::Void => store.primitive_ids().void,
    SerializedType::Null => store.primitive_ids().null,
    SerializedType::Undefined => store.primitive_ids().undefined,
    SerializedType::Boolean => store.primitive_ids().boolean,
    SerializedType::Number => store.primitive_ids().number,
    SerializedType::String => store.primitive_ids().string,
    SerializedType::BigInt => store.primitive_ids().bigint,
    SerializedType::Symbol => store.primitive_ids().symbol,
    SerializedType::UniqueSymbol => store.primitive_ids().unique_symbol,
    SerializedType::BooleanLiteral { value } => store.intern_type(TypeKind::BooleanLiteral(value)),
    SerializedType::NumberLiteral { value } => {
      store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(value)))
    }
    SerializedType::StringLiteral { value } => {
      store.intern_type(TypeKind::StringLiteral(store.intern_name(value.as_str())))
    }
    SerializedType::BigIntLiteral { value } => {
      store.intern_type(TypeKind::BigIntLiteral(BigInt::from(value)))
    }
    SerializedType::This => store.intern_type(TypeKind::This),
    SerializedType::Infer { id, constraint } => store.intern_type(TypeKind::Infer {
      param: TypeParamId(id),
      constraint: constraint
        .map(|idx| resolve_index(graph, store, cache, visiting, idx, depth + 1)),
    }),
    SerializedType::Tuple { elements } => {
      let elems = elements
        .iter()
        .map(|elem| TupleElem {
          ty: resolve_index(graph, store, cache, visiting, elem.ty, depth + 1),
          optional: elem.optional,
          rest: elem.rest,
          readonly: elem.readonly,
        })
        .collect();
      store.intern_type(TypeKind::Tuple(elems))
    }
    SerializedType::Array { ty, readonly } => store.intern_type(TypeKind::Array {
      ty: resolve_index(graph, store, cache, visiting, ty, depth + 1),
      readonly,
    }),
    SerializedType::Union { members } => {
      let members: Vec<_> = members
        .iter()
        .map(|member| resolve_index(graph, store, cache, visiting, *member, depth + 1))
        .collect();
      store.union(members)
    }
    SerializedType::Intersection { members } => {
      let members: Vec<_> = members
        .iter()
        .map(|member| resolve_index(graph, store, cache, visiting, *member, depth + 1))
        .collect();
      store.intersection(members)
    }
    SerializedType::Object {
      properties,
      indexers,
    } => {
      let mut shape = Shape::new();
      for prop in properties.iter() {
        shape.properties.push(Property {
          key: PropKey::String(store.intern_name(&prop.name)),
          data: PropData {
            ty: resolve_index(graph, store, cache, visiting, prop.ty, depth + 1),
            optional: prop.optional,
            readonly: prop.readonly,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      for idx in indexers.iter() {
        shape.indexers.push(Indexer {
          key_type: resolve_index(graph, store, cache, visiting, idx.key, depth + 1),
          value_type: resolve_index(graph, store, cache, visiting, idx.value, depth + 1),
          readonly: idx.readonly,
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(ObjectType { shape: shape_id });
      store.intern_type(TypeKind::Object(obj_id))
    }
    SerializedType::Callable { params, ret } => {
      let params: Vec<_> = params
        .iter()
        .map(|param| Param {
          name: param.name.as_ref().map(|name| store.intern_name(name)),
          ty: resolve_index(graph, store, cache, visiting, param.ty, depth + 1),
          optional: param.optional,
          rest: param.rest,
        })
        .collect();
      let ret = resolve_index(graph, store, cache, visiting, ret, depth + 1);
      let sig = store.intern_signature(Signature::new(params, ret));
      store.intern_type(TypeKind::Callable {
        overloads: vec![sig],
      })
    }
    SerializedType::Ref { def, args } => {
      let args: Vec<_> = args
        .iter()
        .map(|arg| resolve_index(graph, store, cache, visiting, *arg, depth + 1))
        .collect();
      store.intern_type(TypeKind::Ref {
        def: DefId(def),
        args,
      })
    }
    SerializedType::TypeParam { id } => store.intern_type(TypeKind::TypeParam(TypeParamId(id))),
    SerializedType::Conditional {
      check,
      extends,
      true_ty,
      false_ty,
      distributive,
    } => store.intern_type(TypeKind::Conditional {
      check: resolve_index(graph, store, cache, visiting, check, depth + 1),
      extends: resolve_index(graph, store, cache, visiting, extends, depth + 1),
      true_ty: resolve_index(graph, store, cache, visiting, true_ty, depth + 1),
      false_ty: resolve_index(graph, store, cache, visiting, false_ty, depth + 1),
      distributive,
    }),
    SerializedType::Mapped {
      param,
      source,
      value,
      readonly,
      optional,
      name_type,
      as_type,
    } => store.intern_type(TypeKind::Mapped(MappedType {
      param: TypeParamId(param),
      source: resolve_index(graph, store, cache, visiting, source, depth + 1),
      value: resolve_index(graph, store, cache, visiting, value, depth + 1),
      readonly: modifier_value(readonly),
      optional: modifier_value(optional),
      name_type: name_type.map(|idx| resolve_index(graph, store, cache, visiting, idx, depth + 1)),
      as_type: as_type.map(|idx| resolve_index(graph, store, cache, visiting, idx, depth + 1)),
    })),
    SerializedType::TemplateLiteral { head, spans } => {
      let spans: Vec<_> = spans
        .iter()
        .map(|span| TemplateChunk {
          literal: span.literal.clone(),
          ty: resolve_index(graph, store, cache, visiting, span.ty, depth + 1),
        })
        .collect();
      store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
        head: head.clone(),
        spans,
      }))
    }
    SerializedType::IndexedAccess { obj, index } => store.intern_type(TypeKind::IndexedAccess {
      obj: resolve_index(graph, store, cache, visiting, obj, depth + 1),
      index: resolve_index(graph, store, cache, visiting, index, depth + 1),
    }),
    SerializedType::KeyOf { ty } => store.intern_type(TypeKind::KeyOf(resolve_index(
      graph,
      store,
      cache,
      visiting,
      ty,
      depth + 1,
    ))),
  };
  visiting[idx] = false;
  cache[idx] = Some(ty);
  ty
}

fn build_types(graph: &SerializedTypeGraph, store: &Arc<TypeStore>) -> Vec<TypeId> {
  if graph.nodes.is_empty() {
    return Vec::new();
  }
  let mut cache = vec![None; graph.nodes.len()];
  let mut visiting = vec![false; graph.nodes.len()];
  for idx in 0..graph.nodes.len() {
    let _ = resolve_index(graph, store, &mut cache, &mut visiting, idx, 0);
  }
  cache
    .into_iter()
    .map(|ty| ty.unwrap_or_else(|| store.primitive_ids().unknown))
    .collect()
}

fn roots_from_graph(graph: &SerializedTypeGraph, built: &[TypeId]) -> Vec<TypeId> {
  if graph.roots.is_empty() {
    return built.to_vec();
  }
  graph
    .roots
    .iter()
    .filter_map(|idx| built.get(*idx).copied())
    .collect()
}

#[derive(Debug, Clone)]
struct GraphExpander {
  nodes: Arc<Vec<TypeId>>,
}

impl GraphExpander {
  fn new(nodes: Vec<TypeId>) -> Self {
    Self {
      nodes: Arc::new(nodes),
    }
  }
}

impl TypeExpander for GraphExpander {
  fn expand(
    &self,
    _store: &TypeStore,
    def: DefId,
    _args: &[TypeId],
  ) -> Option<crate::ExpandedType> {
    self
      .nodes
      .get(def.0 as usize)
      .copied()
      .map(|ty| crate::ExpandedType {
        params: Vec::new(),
        ty,
      })
  }
}

/// Fuzz entry point that deserializes random `TypeKind` graphs and ensures core
/// operations terminate without panicking. Use `--features types-ts-interned/fuzzing`
/// when wiring this up to `cargo fuzz`.
#[cfg(feature = "fuzzing")]
#[doc(hidden)]
pub fn fuzz_type_graph(data: &[u8]) {
  let source = String::from_utf8_lossy(data);
  let Ok(graph) = serde_json::from_str::<SerializedTypeGraph>(&source) else {
    return;
  };
  let store = TypeStore::new();
  let built = build_types(&graph, &store);
  if built.is_empty() {
    return;
  }

  let roots = roots_from_graph(&graph, &built);
  let expander = GraphExpander::new(built.clone());
  for ty in roots.iter().copied().take(16) {
    let mut evaluator = TypeEvaluator::new(store.clone(), &expander)
      .with_depth_limit(128)
      .with_step_limit(50_000);
    let _ = evaluator.evaluate(ty);
    let _ = store.evaluate(ty);
  }

  let ctx = RelateCtx::new(store.clone(), store.options()).with_step_limit(50_000);
  for pair in roots.windows(2) {
    let _ = ctx.is_assignable(pair[0], pair[1]);
    let _ = ctx.is_assignable(pair[1], pair[0]);
  }
}
