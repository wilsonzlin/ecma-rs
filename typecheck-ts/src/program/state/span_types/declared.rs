use super::*;
use parse_js::ast::type_expr::TypeParameter;

impl ProgramState {
  pub(in super::super) fn declared_type_for_span(
    &mut self,
    file: FileId,
    target: TextRange,
  ) -> Option<TypeId> {
    fn walk_namespace(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      target: TextRange,
    ) -> Option<TypeId> {
      match body {
        NamespaceBody::Block(stmts) => walk(state, file, stmts, target),
        NamespaceBody::Namespace(inner) => walk_namespace(state, file, &inner.stx.body, target),
      }
    }

    fn walk(
      state: &mut ProgramState,
      file: FileId,
      stmts: &[Node<Stmt>],
      target: TextRange,
    ) -> Option<TypeId> {
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::AmbientVarDecl(var) => {
            let span = loc_to_span(file, stmt.loc).range;
            if span == target {
              if let Some(ann) = var.stx.type_annotation.as_ref() {
                return Some(state.lower_interned_type_expr(file, None, ann));
              }
            }
          }
          Stmt::VarDecl(var) => {
            // Most definitions use the binding pattern span, but some def IDs
            // (notably for local variables) may be keyed by a wider span (e.g.
            // the declarator span). Prefer the exact pattern match first, then
            // fall back to a single unambiguous declarator whose span contains
            // the target.
            for decl in var.stx.declarators.iter() {
              let pat_span = loc_to_span(file, decl.pattern.stx.pat.loc).range;
              if pat_span == target {
                if let Some(ann) = decl.type_annotation.as_ref() {
                  return Some(state.lower_interned_type_expr(file, None, ann));
                }
              }
            }

            let mut matching_decl = None;
            for decl in var.stx.declarators.iter() {
              let pat_span = loc_to_span(file, decl.pattern.stx.pat.loc).range;
              let end = decl
                .initializer
                .as_ref()
                .map(|init| loc_to_span(file, init.loc).range.end)
                .or_else(|| {
                  decl
                    .type_annotation
                    .as_ref()
                    .map(|ann| loc_to_span(file, ann.loc).range.end)
                })
                .unwrap_or(pat_span.end);
              let decl_span = TextRange::new(pat_span.start, end);
              // Some defs may be keyed by a span that covers the full declarator
              // (or even the full statement). Prefer matching those wider spans,
              // but avoid matching arbitrary sub-spans inside the pattern (e.g.
              // bindings within destructuring patterns).
              let matches = decl_span == target
                || (target.start <= decl_span.start && target.end >= decl_span.end)
                || (target.start == decl_span.start && target.end <= decl_span.end)
                || (target.start <= pat_span.start && target.end >= pat_span.end);
              if matches {
                if matching_decl.is_some() {
                  matching_decl = None;
                  break;
                }
                matching_decl = Some(decl);
              }
            }

            if let Some(decl) = matching_decl {
              if let Some(ann) = decl.type_annotation.as_ref() {
                return Some(state.lower_interned_type_expr(file, None, ann));
              }
            }
          }
          Stmt::Block(block) => {
            if let Some(ty) = walk(state, file, &block.stx.body, target) {
              return Some(ty);
            }
          }
          Stmt::NamespaceDecl(ns) => {
            if let Some(ty) = walk_namespace(state, file, &ns.stx.body, target) {
              return Some(ty);
            }
          }
          Stmt::ModuleDecl(module) => {
            if let Some(body) = &module.stx.body {
              if let Some(ty) = walk(state, file, body, target) {
                return Some(ty);
              }
            }
          }
          Stmt::GlobalDecl(global) => {
            if let Some(ty) = walk(state, file, &global.stx.body, target) {
              return Some(ty);
            }
          }
          _ => {}
        }
      }
      None
    }

    let ast = match self.asts.get(&file) {
      Some(ast) => ast.clone(),
      None => return None,
    };
    walk(self, file, &ast.stx.body, target)
  }

  fn lower_interned_type_expr(
    &mut self,
    file: FileId,
    type_params: Option<&[Node<TypeParameter>]>,
    expr: &Node<TypeExpr>,
  ) -> TypeId {
    let Some(store) = self.interned_store.clone() else {
      return self.type_from_type_expr(expr);
    };

    let prev_file = self.current_file;
    self.current_file = Some(file);

    let mut binding_defs = HashMap::new();
    if let Some(state) = self.files.get(&file) {
      for (name, binding) in state.bindings.iter() {
        if let Some(def) = binding.def {
          binding_defs.insert(name.clone(), def);
        }
      }
    }
    let resolver = self.build_type_resolver(&binding_defs);
    let mut lowerer = TypeLowerer::new(Arc::clone(&store));
    lowerer.set_file(file);
    lowerer.set_resolver(resolver);
    if let Some(params) = type_params {
      lowerer.register_type_params(params);
    }
    let ty = store.canon(lowerer.lower_type_expr(expr));
    self.diagnostics.extend(lowerer.take_diagnostics());

    self.current_file = prev_file;
    ty
  }

  pub(in super::super) fn type_alias_type_for_span(
    &mut self,
    file: FileId,
    target: TextRange,
    name: &str,
  ) -> Option<TypeId> {
    fn walk_namespace(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      target: TextRange,
      name: &str,
    ) -> Option<TypeId> {
      match body {
        NamespaceBody::Block(stmts) => walk(state, file, stmts, target, name),
        NamespaceBody::Namespace(inner) => {
          walk_namespace(state, file, &inner.stx.body, target, name)
        }
      }
    }

    fn walk(
      state: &mut ProgramState,
      file: FileId,
      stmts: &[Node<Stmt>],
      target: TextRange,
      name: &str,
    ) -> Option<TypeId> {
      for stmt in stmts {
        match stmt.stx.as_ref() {
          Stmt::TypeAliasDecl(alias) => {
            let span = loc_to_span(file, stmt.loc).range;
            if span == target || alias.stx.name == name {
              let ty = state.lower_interned_type_expr(
                file,
                alias.stx.type_parameters.as_deref(),
                &alias.stx.type_expr,
              );
              return Some(ty);
            }
          }
          Stmt::Block(block) => {
            if let Some(ty) = walk(state, file, &block.stx.body, target, name) {
              return Some(ty);
            }
          }
          Stmt::NamespaceDecl(ns) => {
            if let Some(ty) = walk_namespace(state, file, &ns.stx.body, target, name) {
              return Some(ty);
            }
          }
          Stmt::GlobalDecl(global) => {
            if let Some(ty) = walk(state, file, &global.stx.body, target, name) {
              return Some(ty);
            }
          }
          _ => {}
        }
      }
      None
    }

    let ast = match self.asts.get(&file) {
      Some(ast) => ast.clone(),
      None => return None,
    };
    walk(self, file, &ast.stx.body, target, name)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::lib_support::{CompilerOptions, LibManager};
  use crate::profile::QueryStatsCollector;
  use crate::MemoryHost;
  use std::sync::atomic::AtomicBool;
  use std::sync::Arc;

  #[test]
  fn type_alias_span_lowering_registers_type_params() {
    let opts = CompilerOptions {
      no_default_lib: true,
      ..Default::default()
    };
    let mut host = MemoryHost::with_options(opts);
    let file_key = FileKey::new("entry.ts");
    host.insert(file_key.clone(), Arc::<str>::from("type Foo<T> = T;"));

    let host: Arc<dyn Host> = Arc::new(host);
    let cancelled = Arc::new(AtomicBool::new(false));
    let lib_manager = Arc::new(LibManager::new());
    let query_stats = QueryStatsCollector::default();

    let mut state = ProgramState::new(
      Arc::clone(&host),
      lib_manager,
      query_stats,
      Arc::clone(&cancelled),
    );
    let file_id = state.intern_file_key(file_key.clone(), FileOrigin::Source);
    state
      .ensure_analyzed_result(&host, std::slice::from_ref(&file_key))
      .expect("analysis should succeed");

    let foo_def = state
      .def_data
      .iter()
      .find_map(|(def, data)| {
        (data.file == file_id && data.name == "Foo" && matches!(data.kind, DefKind::TypeAlias(_)))
          .then_some(*def)
      })
      .expect("Foo def should be recorded");

    // Create an interned store without running the full decl-type lowering pass
    // so `type_of_def` hits the span-based fallback.
    let store = tti::TypeStore::with_options((&state.compiler_options).into());
    state.interned_store = Some(Arc::clone(&store));
    state.interned_def_types.clear();
    state.def_types.remove(&foo_def);

    let ty = ProgramState::type_of_def(&mut state, foo_def).expect("type_of_def should succeed");
    assert!(
      store.contains_type_id(ty),
      "expected type alias to lower into interned store"
    );
    match store.type_kind(store.canon(ty)) {
      tti::TypeKind::TypeParam(param) => {
        assert_eq!(param, tti::TypeParamId(0));
      }
      other => panic!("expected Foo<T> to lower to its type parameter, got {other:?}"),
    }
  }
}
