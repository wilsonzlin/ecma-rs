use std::sync::Arc;

use diagnostics::{FileId, Span, TextRange};
use typecheck_ts::check::expr::resolve_call;
use typecheck_ts::check::infer::TypeParamDecl;
use types_ts_interned::{Param, RelateCtx, Signature, TypeId, TypeKind, TypeOptions, TypeStore};

fn span() -> Span {
  Span::new(FileId(0), TextRange::new(0, 0))
}

fn param(name: &str, ty: TypeId, store: &Arc<TypeStore>) -> Param {
  Param {
    name: Some(store.intern_name(name)),
    ty,
    optional: false,
    rest: false,
  }
}

#[test]
fn selects_literal_overload() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(&store, TypeOptions::default());

  let click = store.intern_type(TypeKind::StringLiteral(store.intern_name("click")));
  let dom_ret = store.intern_type(TypeKind::StringLiteral(store.intern_name("dom")));
  let fallback_ret = store.intern_type(TypeKind::StringLiteral(store.intern_name("fallback")));

  let handler_sig = Signature {
    params: vec![param("ev", primitives.number, &store)],
    ret: primitives.void,
    type_params: Vec::new(),
    this_param: None,
  };
  let handler = store.intern_type(TypeKind::Callable {
    overloads: vec![store.intern_signature(handler_sig)],
  });

  let literal_sig = Signature {
    params: vec![param("type", click, &store), param("handler", handler, &store)],
    ret: dom_ret,
    type_params: Vec::new(),
    this_param: None,
  };
  let literal_id = store.intern_signature(literal_sig);

  let wide_sig = Signature {
    params: vec![param("type", primitives.string, &store), param("handler", handler, &store)],
    ret: fallback_ret,
    type_params: Vec::new(),
    this_param: None,
  };
  let wide_id = store.intern_signature(wide_sig);

  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![literal_id, wide_id],
  });

  let resolution = resolve_call(
    &store,
    &relate,
    callable,
    &[click, handler],
    &[],
    span(),
  );

  assert!(resolution.diagnostics.is_empty());
  assert_eq!(resolution.signature, Some(literal_id));
  assert_eq!(resolution.return_type, dom_ret);
}

#[test]
fn infers_generic_return_type() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(&store, TypeOptions::default());

  let t_param = types_ts_interned::TypeParamId(0);
  let t_type = store.intern_type(TypeKind::TypeParam(t_param));
  let sig = Signature {
    params: vec![param("value", t_type, &store)],
    ret: t_type,
    type_params: vec![t_param],
    this_param: None,
  };
  let sig_id = store.intern_signature(sig);
  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  });

  let decls = vec![TypeParamDecl::new(t_param)];
  let resolution = resolve_call(
    &store,
    &relate,
    callable,
    &[primitives.number],
    &decls,
    span(),
  );

  assert!(resolution.diagnostics.is_empty());
  assert!(resolution.signature.is_some());
  assert_eq!(resolution.return_type, primitives.number);
}

#[test]
fn reports_no_matching_overload_with_reasons() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(&store, TypeOptions::default());

  let sig = Signature {
    params: vec![param("value", primitives.number, &store)],
    ret: primitives.number,
    type_params: Vec::new(),
    this_param: None,
  };
  let sig_id = store.intern_signature(sig);
  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  });

  let resolution = resolve_call(
    &store,
    &relate,
    callable,
    &[primitives.string],
    &[],
    span(),
  );

  assert!(resolution.signature.is_none());
  assert_eq!(resolution.return_type, primitives.unknown);
  assert_eq!(resolution.diagnostics.len(), 1);
  let diag = &resolution.diagnostics[0];
  assert_eq!(diag.code.as_str(), "TC2000");
  assert_eq!(diag.notes.len(), 1);
  assert!(
    diag.notes[0].contains("argument 1"),
    "unexpected note: {}",
    diag.notes[0]
  );
}

#[test]
fn reports_ambiguous_call() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let relate = RelateCtx::new(&store, TypeOptions::default());

  let sig_a = Signature {
    params: vec![param("value", primitives.string, &store)],
    ret: primitives.number,
    type_params: Vec::new(),
    this_param: None,
  };
  let sig_a_id = store.intern_signature(sig_a);
  let sig_b = Signature {
    params: vec![param("value", primitives.string, &store)],
    ret: primitives.boolean,
    type_params: Vec::new(),
    this_param: None,
  };
  let sig_b_id = store.intern_signature(sig_b);

  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_a_id, sig_b_id],
  });

  let resolution = resolve_call(
    &store,
    &relate,
    callable,
    &[primitives.string],
    &[],
    span(),
  );

  assert!(resolution.signature.is_none());
  assert_eq!(resolution.return_type, primitives.unknown);
  assert_eq!(resolution.diagnostics.len(), 1);
  let diag = &resolution.diagnostics[0];
  assert_eq!(diag.code.as_str(), "TC2001");
  assert_eq!(diag.notes.len(), 2);
}
