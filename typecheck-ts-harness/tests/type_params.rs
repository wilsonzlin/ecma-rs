use std::sync::Arc;

use typecheck_ts::check::instantiate::InstantiationCache;
use typecheck_ts::check::overload::CallArgType;
use typecheck_ts::lib_support::{CompilerOptions, LibName};
use typecheck_ts::{codes, FileId, FileKey, MemoryHost, Program};
use types_ts_interned::{
  Param, RelateCtx, Signature, TypeKind, TypeOptions, TypeParamDecl, TypeParamId, TypeStore,
};

fn run_single_file(source: &str) -> (Program, FileId, Vec<diagnostics::Diagnostic>) {
  let mut host = MemoryHost::with_options(CompilerOptions {
    libs: vec![LibName::parse("es5").expect("es5 lib")],
    ..CompilerOptions::default()
  });
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
fn conflicting_primitive_type_arguments_reject() {
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
    &[
      CallArgType::new(primitives.number),
      CallArgType::new(primitives.string),
    ],
    None,
    None,
    None,
    span,
    None,
  );

  // tsc: `f<T>(a: T, b: T)` with unrelated primitives does NOT union the
  // candidates — the first wins and the second argument is rejected
  // (oracle: `f(1, "s")` → TS2345 '"s"' not assignable to parameter of type
  // '1'). The direct overload API therefore rejects the call; the
  // program-level checker emits TS2345 on the offending argument.
  assert!(
    !resolution.diagnostics.is_empty(),
    "conflicting primitives must reject (tsc first-candidate-wins), got no diagnostics"
  );
}

#[test]
fn homogeneous_type_arguments_infer_shared_type() {
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
    &[
      CallArgType::new(primitives.number),
      CallArgType::new(primitives.number),
    ],
    None,
    None,
    None,
    span,
    None,
  );

  assert!(
    resolution.diagnostics.is_empty(),
    "homogeneous args must infer cleanly: {:?}",
    resolution
      .diagnostics
      .iter()
      .map(|d| d.message.clone())
      .collect::<Vec<_>>()
  );
  assert_eq!(
    store.canon(resolution.return_type),
    primitives.number,
    "T should infer number for (number, number)"
  );
}
