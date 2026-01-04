use std::sync::Arc;

use typecheck_ts::check::instantiate::InstantiationCache;
use typecheck_ts::{codes, FileId, FileKey, MemoryHost, Program};
use types_ts_interned::{
  Param, RelateCtx, Signature, TypeKind, TypeOptions, TypeParamDecl, TypeParamId, TypeStore,
};

fn run_single_file(source: &str) -> (Program, FileId, Vec<diagnostics::Diagnostic>) {
  let mut host = MemoryHost::new();
  let file = FileKey::new("input.ts");
  host.insert(file.clone(), source);
  let program = Program::new(host, vec![file]);
  let file_id = program.file_id(&FileKey::new("input.ts")).unwrap();
  let diagnostics = program.check();
  (program, file_id, diagnostics)
}

#[test]
fn unresolved_type_param_treated_conservatively() {
  const SOURCE: &str = "function make<T>(): T;\nconst x = make();\n// property access should not trigger overload mismatch\nx.toFixed();\n";
  let (program, file_id, diagnostics) = run_single_file(SOURCE);

  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code == codes::NO_OVERLOAD.as_str()),
    "call to `make` should not fail overload resolution: {diagnostics:?}"
  );
  let call_offset = SOURCE.find("make()").expect("call present") as u32;
  // Query inside the `()` so `type_at` resolves the call expression rather than the callee symbol.
  let call_offset = call_offset + "make".len() as u32;
  let call_type = program
    .type_at(file_id, call_offset)
    .expect("type_at available");
  let call_type_str = program.display_type(call_type).to_string();
  assert!(
    call_type_str.contains("unknown"),
    "unresolved generic call should produce an unknown-like result, got {call_type_str}"
  );
}

#[test]
fn conflicting_type_arguments_still_error() {
  let store = Arc::new(TypeStore::new());
  let primitives = store.primitive_ids();
  let tp = TypeParamId(0);
  let param_ty = store.intern_type(TypeKind::TypeParam(tp));
  let sig = Signature {
    params: vec![
      Param {
        name: None,
        ty: param_ty,
        optional: false,
        rest: false,
      },
      Param {
        name: None,
        ty: param_ty,
        optional: false,
        rest: false,
      },
    ],
    ret: param_ty,
    type_params: vec![TypeParamDecl::new(tp)],
    this_param: None,
  };
  let sig_id = store.intern_signature(sig);
  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  });
  let relate = RelateCtx::new(Arc::clone(&store), TypeOptions::default());
  let span = diagnostics::Span {
    file: FileId(0),
    range: diagnostics::TextRange::new(0, 0),
  };
  let instantiation = InstantiationCache::default();
  let resolution = typecheck_ts::check::overload::resolve_overloads(
    &store,
    &relate,
    &instantiation,
    callable,
    &[primitives.number, primitives.string],
    None,
    None,
    None,
    span,
    None,
  );

  assert!(
    resolution.diagnostics.is_empty(),
    "generic inference should accept heterogeneous arguments by inferring a union, got diagnostics: {:?}",
    resolution
      .diagnostics
      .iter()
      .map(|d| d.message.clone())
      .collect::<Vec<_>>()
  );
  match store.type_kind(resolution.return_type) {
    TypeKind::Union(members) => {
      assert!(
        members.contains(&primitives.number) && members.contains(&primitives.string),
        "expected inferred type param to include both number and string, got {:?}",
        members
          .iter()
          .map(|ty| format!("{:?}", store.type_kind(*ty)))
          .collect::<Vec<_>>()
      );
    }
    other => panic!("expected union return type, got {other:?}"),
  }
}
