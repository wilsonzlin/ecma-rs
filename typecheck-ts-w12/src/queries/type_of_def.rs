use crate::diagnostics::Diagnostic;
use crate::types::TypeLowerer;
use crate::DefId;
use crate::DefKind;
use crate::Program;
use crate::Span;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::ts_stmt::AmbientFunctionDecl;
use types_ts::ClassType;
use types_ts::FunctionType;
use types_ts::ObjectType;
use types_ts::TypeId;
use types_ts::TypeKind;

impl Program {
  pub fn type_of_def(&self, def_id: DefId) -> TypeId {
    let globals = self.global_symbols();
    let mut store = self.type_store_mut();
    let Some(bound) = self.bind(def_id.file_id) else {
      return store.unknown();
    };
    let Some(def) = bound.get_def(def_id) else {
      return store.unknown();
    };
    let Some(hir) = self.hir(def_id.file_id) else {
      return store.unknown();
    };

    let mut lowerer = TypeLowerer::new(self, &mut store, &globals, def_id.file_id);

    match def.kind {
      DefKind::TypeAlias => {
        self.type_of_type_alias(hir.ast.stx.body.get(def.source_stmt_index()), &mut lowerer)
      }
      DefKind::Interface => {
        self.type_of_interface(hir.ast.stx.body.get(def.source_stmt_index()), &mut lowerer)
      }
      DefKind::Enum => {
        self.type_of_enum(hir.ast.stx.body.get(def.source_stmt_index()), &mut lowerer)
      }
      DefKind::Class => self.type_of_class(
        def,
        hir.ast.stx.body.get(def.source_stmt_index()),
        &mut lowerer,
      ),
      DefKind::Function => {
        self.type_of_function(hir.ast.stx.body.get(def.source_stmt_index()), &mut lowerer)
      }
      DefKind::FunctionSignature => {
        self.type_of_function_signature(hir.ast.stx.body.get(def.source_stmt_index()), &mut lowerer)
      }
      DefKind::Var | DefKind::Let | DefKind::Const => self.type_of_var(
        def,
        hir.ast.stx.body.get(def.source_stmt_index()),
        &mut lowerer,
      ),
    }
  }

  fn type_of_type_alias(&self, stmt: Option<&Node<Stmt>>, lowerer: &mut TypeLowerer) -> TypeId {
    let Some(stmt) = stmt else {
      return lowerer.store.unknown();
    };
    if let Stmt::TypeAliasDecl(alias) = &*stmt.stx {
      lowerer.lower_type_expr(&alias.stx.type_expr)
    } else {
      lowerer.store.unknown()
    }
  }

  fn type_of_interface(&self, stmt: Option<&Node<Stmt>>, lowerer: &mut TypeLowerer) -> TypeId {
    let Some(stmt) = stmt else {
      return lowerer.store.unknown();
    };
    if let Stmt::InterfaceDecl(interface) = &*stmt.stx {
      lowerer.lower_object_members(&interface.stx.members)
    } else {
      lowerer.store.unknown()
    }
  }

  fn type_of_enum(&self, stmt: Option<&Node<Stmt>>, lowerer: &mut TypeLowerer) -> TypeId {
    let Some(stmt) = stmt else {
      return lowerer.store.unknown();
    };
    if let Stmt::EnumDecl(enum_decl) = &*stmt.stx {
      lowerer.lower_enum(enum_decl)
    } else {
      lowerer.store.unknown()
    }
  }

  fn type_of_class(
    &self,
    def: &semantic_js::DefInfo,
    stmt: Option<&Node<Stmt>>,
    lowerer: &mut TypeLowerer,
  ) -> TypeId {
    let Some(stmt) = stmt else {
      return lowerer.store.unknown();
    };
    match &*stmt.stx {
      Stmt::ClassDecl(class_decl) => {
        let (instance, static_side) = lowerer.lower_class_members(&class_decl.stx.members);
        lowerer.store.intern(TypeKind::Class(ClassType {
          name: def.name.clone(),
          instance,
          static_side,
        }))
      }
      Stmt::AmbientClassDecl(class_decl) => {
        let instance = lowerer.lower_object_members(&class_decl.stx.members);
        let static_side = lowerer.store.intern(TypeKind::Object(ObjectType::new()));
        lowerer.store.intern(TypeKind::Class(ClassType {
          name: def.name.clone(),
          instance,
          static_side,
        }))
      }
      _ => lowerer.store.unknown(),
    }
  }

  fn type_of_function(&self, stmt: Option<&Node<Stmt>>, lowerer: &mut TypeLowerer) -> TypeId {
    let Some(stmt) = stmt else {
      return lowerer.store.unknown();
    };
    match &*stmt.stx {
      Stmt::FunctionDecl(func_decl) => {
        let func = lowerer.lower_function_from_func(&func_decl.stx.function.stx);
        lowerer.store.intern(TypeKind::Function(func))
      }
      _ => lowerer.store.unknown(),
    }
  }

  fn type_of_function_signature(
    &self,
    stmt: Option<&Node<Stmt>>,
    lowerer: &mut TypeLowerer,
  ) -> TypeId {
    let Some(stmt) = stmt else {
      return lowerer.store.unknown();
    };
    match &*stmt.stx {
      Stmt::FunctionDecl(func_decl) => {
        let func = lowerer.lower_function_from_func(&func_decl.stx.function.stx);
        lowerer.store.intern(TypeKind::Function(func))
      }
      Stmt::AmbientFunctionDecl(func_decl) => {
        let func = lowerer.lower_ambient_function(func_decl);
        lowerer.store.intern(TypeKind::Function(func))
      }
      _ => lowerer.store.unknown(),
    }
  }

  fn type_of_var(
    &self,
    def: &semantic_js::DefInfo,
    stmt: Option<&Node<Stmt>>,
    lowerer: &mut TypeLowerer,
  ) -> TypeId {
    let Some(stmt) = stmt else {
      return lowerer.store.unknown();
    };
    match &*stmt.stx {
      Stmt::VarDecl(var_decl) => {
        let Some(decl_idx) = def.var_decl_index() else {
          return lowerer.store.unknown();
        };
        if let Some(declarator) = var_decl.stx.declarators.get(decl_idx) {
          if let Some(annotation) = &declarator.type_annotation {
            return lowerer.lower_type_expr(annotation);
          }
        }
        self.missing_annotation(def, lowerer)
      }
      Stmt::AmbientVarDecl(var_decl) => {
        if let Some(annotation) = &var_decl.stx.type_annotation {
          lowerer.lower_type_expr(annotation)
        } else {
          self.missing_annotation(def, lowerer)
        }
      }
      _ => lowerer.store.unknown(),
    }
  }

  fn missing_annotation(&self, def: &semantic_js::DefInfo, lowerer: &mut TypeLowerer) -> TypeId {
    let span = Span::new(def.id.file_id, def.span);
    if self.options.no_implicit_any {
      self.push_diagnostic(Diagnostic::missing_annotation("TC1003", &def.name, span));
      lowerer.store.unknown()
    } else {
      lowerer.store.any()
    }
  }
}

trait SourceExt {
  fn source_stmt_index(&self) -> usize;
  fn var_decl_index(&self) -> Option<usize> {
    None
  }
}

impl SourceExt for semantic_js::DefInfo {
  fn source_stmt_index(&self) -> usize {
    match self.source {
      semantic_js::DefSource::Stmt(idx) => idx,
      semantic_js::DefSource::VarDecl { stmt, .. } => stmt,
    }
  }

  fn var_decl_index(&self) -> Option<usize> {
    match self.source {
      semantic_js::DefSource::VarDecl { decl, .. } => Some(decl),
      _ => None,
    }
  }
}

impl TypeLowerer<'_> {
  fn lower_ambient_function(&mut self, func: &Node<AmbientFunctionDecl>) -> FunctionType {
    let type_params = func
      .stx
      .type_parameters
      .as_ref()
      .map(|params| params.iter().map(|p| p.stx.name.clone()).collect())
      .unwrap_or_default();
    let params = func
      .stx
      .parameters
      .iter()
      .map(|param| types_ts::FnParam {
        name: Some(param.stx.name.clone()),
        ty: param
          .stx
          .type_annotation
          .as_ref()
          .map(|t| self.lower_type_expr(t))
          .unwrap_or_else(|| self.store.unknown()),
        optional: param.stx.optional,
        rest: param.stx.rest,
      })
      .collect();
    let ret = func
      .stx
      .return_type
      .as_ref()
      .map(|t| self.lower_type_expr(t))
      .unwrap_or_else(|| self.store.void());
    FunctionType {
      type_params,
      params,
      ret,
    }
  }
}
