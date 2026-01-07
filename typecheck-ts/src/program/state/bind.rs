use super::*;

impl ProgramState {
  fn queue_type_imports_in_stmt(
    &mut self,
    file: FileId,
    stmt: &Node<Stmt>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::ClassDecl(class) => {
        if let Some(params) = class.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
        for member in class.stx.members.iter() {
          self.queue_type_imports_in_class_member(file, member, host, queue);
        }
      }
      Stmt::AmbientClassDecl(class) => {
        if let Some(ext) = class.stx.extends.as_ref() {
          self.queue_type_imports_in_type_expr(file, ext, host, queue);
        }
        for implements in class.stx.implements.iter() {
          self.queue_type_imports_in_type_expr(file, implements, host, queue);
        }
        if let Some(params) = class.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
        for member in class.stx.members.iter() {
          self.queue_type_imports_in_type_member(file, member, host, queue);
        }
      }
      Stmt::TypeAliasDecl(alias) => {
        self.queue_type_imports_in_type_expr(file, &alias.stx.type_expr, host, queue);
      }
      Stmt::FunctionDecl(func) => {
        for param in func.stx.function.stx.parameters.iter() {
          if let Some(ann) = param.stx.type_annotation.as_ref() {
            self.queue_type_imports_in_type_expr(file, ann, host, queue);
          }
        }
        if let Some(ret) = func.stx.function.stx.return_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, ret, host, queue);
        }
        if let Some(body) = func.stx.function.stx.body.as_ref() {
          if let parse_js::ast::func::FuncBody::Block(block) = body {
            for stmt in block.iter() {
              self.queue_type_imports_in_stmt(file, stmt, host, queue);
            }
          }
        }
      }
      Stmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter() {
          if let Some(ann) = decl.type_annotation.as_ref() {
            self.queue_type_imports_in_type_expr(file, ann, host, queue);
          }
        }
      }
      Stmt::Block(block) => {
        for stmt in block.stx.body.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      Stmt::NamespaceDecl(ns) => {
        self.queue_type_imports_in_namespace_body(file, &ns.stx.body, host, queue);
      }
      Stmt::ModuleDecl(module) => {
        if let Some(body) = &module.stx.body {
          for stmt in body.iter() {
            self.queue_type_imports_in_stmt(file, stmt, host, queue);
          }
        }
      }
      Stmt::GlobalDecl(global) => {
        for stmt in global.stx.body.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      _ => {}
    }
  }

  fn queue_type_imports_in_class_member(
    &mut self,
    file: FileId,
    member: &Node<ClassMember>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    if let Some(ann) = member.stx.type_annotation.as_ref() {
      self.queue_type_imports_in_type_expr(file, ann, host, queue);
    }
    match &member.stx.val {
      ClassOrObjVal::Getter(getter) => {
        self.queue_type_imports_in_func(file, &getter.stx.func.stx, host, queue);
      }
      ClassOrObjVal::Setter(setter) => {
        self.queue_type_imports_in_func(file, &setter.stx.func.stx, host, queue);
      }
      ClassOrObjVal::Method(method) => {
        self.queue_type_imports_in_func(file, &method.stx.func.stx, host, queue);
      }
      ClassOrObjVal::IndexSignature(idx) => {
        self.queue_type_imports_in_type_expr(file, &idx.stx.parameter_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &idx.stx.type_annotation, host, queue);
      }
      ClassOrObjVal::StaticBlock(block) => {
        for stmt in block.stx.body.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      ClassOrObjVal::Prop(_) => {}
    }
  }

  fn queue_type_imports_in_func(
    &mut self,
    file: FileId,
    func: &Func,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    for param in func.parameters.iter() {
      if let Some(ann) = param.stx.type_annotation.as_ref() {
        self.queue_type_imports_in_type_expr(file, ann, host, queue);
      }
    }
    if let Some(ret) = func.return_type.as_ref() {
      self.queue_type_imports_in_type_expr(file, ret, host, queue);
    }
    if let Some(params) = func.type_parameters.as_ref() {
      for tp in params.iter() {
        if let Some(constraint) = tp.stx.constraint.as_ref() {
          self.queue_type_imports_in_type_expr(file, constraint, host, queue);
        }
        if let Some(default) = tp.stx.default.as_ref() {
          self.queue_type_imports_in_type_expr(file, default, host, queue);
        }
      }
    }
    if let Some(body) = func.body.as_ref() {
      if let parse_js::ast::func::FuncBody::Block(block) = body {
        for stmt in block.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
    }
  }

  fn queue_type_imports_in_namespace_body(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match body {
      NamespaceBody::Block(stmts) => {
        for stmt in stmts.iter() {
          self.queue_type_imports_in_stmt(file, stmt, host, queue);
        }
      }
      NamespaceBody::Namespace(inner) => {
        self.queue_type_imports_in_namespace_body(file, &inner.stx.body, host, queue)
      }
    }
  }

  pub(super) fn queue_type_imports_in_ast(
    &mut self,
    file: FileId,
    ast: &Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    type TypeImportNode = Node<parse_js::ast::type_expr::TypeImport>;
    type TypeQueryNode = Node<parse_js::ast::type_expr::TypeQuery>;

    #[derive(derive_visitor::Visitor)]
    #[visitor(TypeImportNode(enter), TypeQueryNode(enter))]
    struct TypeImportCollector<'a> {
      state: &'a mut ProgramState,
      file: FileId,
      host: &'a Arc<dyn Host>,
      queue: &'a mut VecDeque<FileId>,
    }

    impl<'a> TypeImportCollector<'a> {
      fn enter_type_import_node(&mut self, node: &TypeImportNode) {
        if let Some(target) =
          self
            .state
            .record_module_resolution(self.file, &node.stx.module_specifier, self.host)
        {
          self.queue.push_back(target);
        }
      }

      fn enter_type_query_node(&mut self, node: &TypeQueryNode) {
        self.state.queue_type_imports_in_entity_name(
          self.file,
          &node.stx.expr_name,
          self.host,
          self.queue,
        );
      }
    }

    let mut collector = TypeImportCollector {
      state: self,
      file,
      host,
      queue,
    };
    derive_visitor::Drive::drive(ast, &mut collector);
  }

  fn queue_type_imports_in_type_expr(
    &mut self,
    file: FileId,
    expr: &Node<TypeExpr>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match expr.stx.as_ref() {
      TypeExpr::ImportType(import) => {
        if let Some(target) =
          self.record_module_resolution(file, &import.stx.module_specifier, host)
        {
          queue.push_back(target);
        }
        if let Some(args) = import.stx.type_arguments.as_ref() {
          for arg in args {
            self.queue_type_imports_in_type_expr(file, arg, host, queue);
          }
        }
        if let Some(qualifier) = import.stx.qualifier.as_ref() {
          self.queue_type_imports_in_entity_name(file, qualifier, host, queue);
        }
      }
      TypeExpr::ArrayType(arr) => {
        self.queue_type_imports_in_type_expr(file, &arr.stx.element_type, host, queue);
      }
      TypeExpr::TupleType(tuple) => {
        for elem in tuple.stx.elements.iter() {
          self.queue_type_imports_in_type_expr(file, &elem.stx.type_expr, host, queue);
        }
      }
      TypeExpr::UnionType(union) => {
        for ty in union.stx.types.iter() {
          self.queue_type_imports_in_type_expr(file, ty, host, queue);
        }
      }
      TypeExpr::IntersectionType(intersection) => {
        for ty in intersection.stx.types.iter() {
          self.queue_type_imports_in_type_expr(file, ty, host, queue);
        }
      }
      TypeExpr::FunctionType(func) => {
        for param in func.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        self.queue_type_imports_in_type_expr(file, &func.stx.return_type, host, queue);
        if let Some(params) = func.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
      }
      TypeExpr::ConstructorType(cons) => {
        for param in cons.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        self.queue_type_imports_in_type_expr(file, &cons.stx.return_type, host, queue);
        if let Some(params) = cons.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
      }
      TypeExpr::ObjectType(obj) => {
        for member in obj.stx.members.iter() {
          self.queue_type_imports_in_type_member(file, member, host, queue);
        }
      }
      TypeExpr::ParenthesizedType(inner) => {
        self.queue_type_imports_in_type_expr(file, &inner.stx.type_expr, host, queue);
      }
      TypeExpr::KeyOfType(keyof) => {
        self.queue_type_imports_in_type_expr(file, &keyof.stx.type_expr, host, queue);
      }
      TypeExpr::IndexedAccessType(indexed) => {
        self.queue_type_imports_in_type_expr(file, &indexed.stx.object_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &indexed.stx.index_type, host, queue);
      }
      TypeExpr::ConditionalType(cond) => {
        self.queue_type_imports_in_type_expr(file, &cond.stx.check_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.extends_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.true_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &cond.stx.false_type, host, queue);
      }
      TypeExpr::MappedType(mapped) => {
        self.queue_type_imports_in_type_expr(file, &mapped.stx.constraint, host, queue);
        self.queue_type_imports_in_type_expr(file, &mapped.stx.type_expr, host, queue);
        if let Some(name_type) = mapped.stx.name_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, name_type, host, queue);
        }
      }
      TypeExpr::TemplateLiteralType(tpl) => {
        for span in tpl.stx.spans.iter() {
          self.queue_type_imports_in_type_expr(file, &span.stx.type_expr, host, queue);
        }
      }
      TypeExpr::TypePredicate(pred) => {
        if let Some(ann) = pred.stx.type_annotation.as_ref() {
          self.queue_type_imports_in_type_expr(file, ann, host, queue);
        }
      }
      TypeExpr::InferType(infer) => {
        if let Some(constraint) = infer.stx.constraint.as_ref() {
          self.queue_type_imports_in_type_expr(file, constraint, host, queue);
        }
      }
      TypeExpr::TypeReference(reference) => {
        if let Some(args) = reference.stx.type_arguments.as_ref() {
          for arg in args {
            self.queue_type_imports_in_type_expr(file, arg, host, queue);
          }
        }
      }
      TypeExpr::TypeQuery(query) => {
        self.queue_type_imports_in_entity_name(file, &query.stx.expr_name, host, queue);
      }
      _ => {}
    }
  }

  fn queue_type_imports_in_type_member(
    &mut self,
    file: FileId,
    member: &Node<TypeMember>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match member.stx.as_ref() {
      TypeMember::Property(prop) => {
        if let Some(ann) = prop.stx.type_annotation.as_ref() {
          self.queue_type_imports_in_type_expr(file, ann, host, queue);
        }
      }
      TypeMember::Method(method) => {
        for param in method.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        if let Some(ret) = method.stx.return_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, ret, host, queue);
        }
        if let Some(params) = method.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
      }
      TypeMember::Constructor(cons) => {
        for param in cons.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        if let Some(ret) = cons.stx.return_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, ret, host, queue);
        }
        if let Some(params) = cons.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
      }
      TypeMember::CallSignature(call) => {
        for param in call.stx.parameters.iter() {
          self.queue_type_imports_in_type_expr(file, &param.stx.type_expr, host, queue);
        }
        if let Some(ret) = call.stx.return_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, ret, host, queue);
        }
        if let Some(params) = call.stx.type_parameters.as_ref() {
          for tp in params.iter() {
            if let Some(constraint) = tp.stx.constraint.as_ref() {
              self.queue_type_imports_in_type_expr(file, constraint, host, queue);
            }
            if let Some(default) = tp.stx.default.as_ref() {
              self.queue_type_imports_in_type_expr(file, default, host, queue);
            }
          }
        }
      }
      TypeMember::IndexSignature(idx) => {
        self.queue_type_imports_in_type_expr(file, &idx.stx.parameter_type, host, queue);
        self.queue_type_imports_in_type_expr(file, &idx.stx.type_annotation, host, queue);
      }
      TypeMember::GetAccessor(get) => {
        if let Some(ret) = get.stx.return_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, ret, host, queue);
        }
      }
      TypeMember::SetAccessor(set) => {
        self.queue_type_imports_in_type_expr(file, &set.stx.parameter.stx.type_expr, host, queue);
      }
      TypeMember::MappedProperty(mapped) => {
        self.queue_type_imports_in_type_expr(file, &mapped.stx.constraint, host, queue);
        self.queue_type_imports_in_type_expr(file, &mapped.stx.type_expr, host, queue);
        if let Some(name_type) = mapped.stx.name_type.as_ref() {
          self.queue_type_imports_in_type_expr(file, name_type, host, queue);
        }
      }
    }
  }

  fn queue_type_imports_in_entity_name(
    &mut self,
    file: FileId,
    name: &TypeEntityName,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) {
    match name {
      TypeEntityName::Qualified(qualified) => {
        self.queue_type_imports_in_entity_name(file, &qualified.left, host, queue);
      }
      TypeEntityName::Import(import) => {
        if let Expr::LitStr(spec) = import.stx.module.stx.as_ref() {
          if let Some(target) = self.record_module_resolution(file, &spec.stx.value, host) {
            queue.push_back(target);
          }
        }
      }
      _ => {}
    }
  }

  pub(super) fn bind_file(
    &mut self,
    file: FileId,
    ast: &Node<TopLevel>,
    host: &Arc<dyn Host>,
    queue: &mut VecDeque<FileId>,
  ) -> sem_ts::HirFile {
    let file_kind = *self.file_kinds.get(&file).unwrap_or(&FileKind::Ts);
    let has_module_syntax = ast.stx.body.iter().any(|stmt| match stmt.stx.as_ref() {
      Stmt::Import(_)
      | Stmt::ExportList(_)
      | Stmt::ExportDefaultExpr(_)
      | Stmt::ExportAssignmentDecl(_)
      | Stmt::ExportAsNamespaceDecl(_)
      | Stmt::ImportTypeDecl(_)
      | Stmt::ExportTypeDecl(_) => true,
      Stmt::ImportEqualsDecl(import_equals) => match &import_equals.stx.rhs {
        ImportEqualsRhs::Require { .. } => true,
        ImportEqualsRhs::EntityName { .. } => import_equals.stx.export,
      },
      Stmt::VarDecl(var) => var.stx.export,
      Stmt::FunctionDecl(func) => func.stx.export,
      Stmt::ClassDecl(class) => class.stx.export,
      Stmt::InterfaceDecl(interface) => interface.stx.export,
      Stmt::TypeAliasDecl(alias) => alias.stx.export,
      Stmt::EnumDecl(en) => en.stx.export,
      Stmt::NamespaceDecl(ns) => ns.stx.export,
      Stmt::ModuleDecl(module) => module.stx.export,
      Stmt::AmbientVarDecl(av) => av.stx.export,
      Stmt::AmbientFunctionDecl(af) => af.stx.export,
      Stmt::AmbientClassDecl(ac) => ac.stx.export,
      _ => false,
    });
    let mut sem_builder = SemHirBuilder::new(file, sem_file_kind(file_kind));
    let mut defs = Vec::new();
    let mut exports: ExportMap = BTreeMap::new();
    let mut bindings: HashMap<String, SymbolBinding> = HashMap::new();
    let mut reexports = Vec::new();
    let mut export_all = Vec::new();

    for stmt in ast.stx.body.iter() {
      self.queue_type_imports_in_stmt(file, stmt, host, queue);
      match stmt.stx.as_ref() {
        Stmt::VarDecl(var) => {
          let new_defs = self.handle_var_decl(file, var.stx.as_ref(), &mut sem_builder);
          for (def_id, binding, export_name) in new_defs {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::FunctionDecl(func) => {
          let span = loc_to_span(file, stmt.loc);
          if let Some((def_id, binding, export_name)) =
            self.handle_function_decl(file, span.range, func.stx.as_ref(), &mut sem_builder)
          {
            defs.push(def_id);
            let (binding_name, binding_value) = binding;
            bindings.insert(binding_name.clone(), binding_value.clone());
            if let Some(name) = export_name {
              exports.insert(
                name,
                ExportEntry {
                  symbol: binding_value.symbol,
                  def: Some(def_id),
                  type_id: binding_value.type_id,
                },
              );
            }
          }
        }
        Stmt::InterfaceDecl(interface) => {
          let span = loc_to_span(file, stmt.loc);
          let name = interface.stx.name.clone();
          let mut object = self.object_type_from_members(&interface.stx.members);
          for base in interface.stx.extends.iter() {
            let base_ty = self.type_from_type_expr(base);
            if let TypeKind::Object(base_obj) = self.type_store.kind(base_ty).clone() {
              object = self.merge_object_types(object, base_obj);
            }
          }
          let mut typ = self.type_store.object(object);
          let existing_interface = bindings
            .get(&name)
            .and_then(|b| b.def)
            .and_then(|id| self.def_data.get(&id).map(|d| (id, d.clone())))
            .and_then(|(id, data)| match data.kind {
              DefKind::Interface(existing) => Some((id, data.symbol, existing.typ)),
              _ => None,
            });
          let (def_id, symbol) =
            if let Some((existing_id, symbol, existing_ty)) = existing_interface {
              typ = match (
                self.type_store.kind(existing_ty).clone(),
                self.type_store.kind(typ).clone(),
              ) {
                (TypeKind::Object(existing_obj), TypeKind::Object(obj)) => {
                  let merged = self.merge_object_types(existing_obj, obj);
                  self.type_store.object(merged)
                }
                _ => self.type_store.union(vec![existing_ty, typ], &self.builtin),
              };
              if let Some(def) = self.def_data.get_mut(&existing_id) {
                def.kind = DefKind::Interface(InterfaceData { typ });
                def.export = def.export || interface.stx.export;
              }
              (existing_id, symbol)
            } else {
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: name.clone(),
                  file,
                  span: span.range,
                  symbol,
                  export: interface.stx.export,
                  kind: DefKind::Interface(InterfaceData { typ }),
                },
              );
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
              sem_builder.add_decl(
                def_id,
                name.clone(),
                sem_ts::DeclKind::Interface,
                if interface.stx.export {
                  sem_ts::Exported::Named
                } else {
                  sem_ts::Exported::No
                },
                span.range,
              );
              (def_id, symbol)
            };

          bindings
            .entry(name.clone())
            .and_modify(|binding| {
              binding.symbol = symbol;
              binding.def = Some(def_id);
              binding.type_id = Some(typ);
            })
            .or_insert(SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(typ),
            });

          if interface.stx.export {
            let entry = exports.entry(name.clone()).or_insert(ExportEntry {
              symbol,
              def: Some(def_id),
              type_id: Some(typ),
            });
            entry.symbol = symbol;
            entry.def = Some(def_id);
            entry.type_id = Some(typ);
          }

          self.def_types.insert(def_id, typ);
          self.record_symbol(file, span.range, symbol);
        }
        Stmt::TypeAliasDecl(alias) => {
          let span = loc_to_span(file, stmt.loc);
          let name = alias.stx.name.clone();
          let ty = self.type_from_type_expr(&alias.stx.type_expr);
          if let TypeExpr::TypeReference(reference) = alias.stx.type_expr.stx.as_ref() {
            if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
              if let Some(binding) = bindings.get(type_name) {
                self.record_symbol(
                  file,
                  loc_to_span(file, alias.stx.type_expr.loc).range,
                  binding.symbol,
                );
              }
            }
          }
          let def_id = self.alloc_def();
          let symbol = self.alloc_symbol();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: alias.stx.export,
              kind: DefKind::TypeAlias(TypeAliasData { typ: ty }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.def_types.insert(def_id, ty);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: Some(ty),
            },
          );
          defs.push(def_id);
          self.record_symbol(file, span.range, symbol);
          sem_builder.add_decl(
            def_id,
            name.clone(),
            sem_ts::DeclKind::TypeAlias,
            if alias.stx.export {
              sem_ts::Exported::Named
            } else {
              sem_ts::Exported::No
            },
            span.range,
          );
          if alias.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: Some(ty),
              },
            );
          }
        }
        Stmt::NamespaceDecl(ns) => {
          let span = loc_to_span(file, stmt.loc);
          let name = ns.stx.name.clone();
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: ns.stx.export,
              kind: DefKind::Namespace(NamespaceData {
                body: None,
                value_type: None,
                type_type: None,
                declare: ns.stx.declare,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          self.bind_namespace_member_defs(file, &ns.stx.body, sem_builder.file_kind, &mut defs);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if ns.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
          }
        }
        Stmt::ModuleDecl(module) => {
          if let parse_js::ast::ts_stmt::ModuleName::String(specifier) = &module.stx.name {
            if has_module_syntax {
              // `declare module "x" { ... }` can act as an external module augmentation
              // when the containing file is itself a module. Record the host mapping
              // so `semantic-js` can resolve the augmentation target and merge it
              // into the module's exports.
              if let Some(target) = self.record_module_resolution(file, specifier, host) {
                queue.push_back(target);
              }
            }
            self.bind_ambient_module(file, module, &mut sem_builder, &mut defs);
          }
          let span = loc_to_span(file, stmt.loc);
          let name = match &module.stx.name {
            parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.clone(),
            parse_js::ast::ts_stmt::ModuleName::String(s) => s.clone(),
          };
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: module.stx.export,
              kind: DefKind::Module(ModuleData {
                body: None,
                value_type: None,
                type_type: None,
                declare: module.stx.declare,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          self.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          bindings.insert(
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          if module.stx.export {
            exports.insert(
              name.clone(),
              ExportEntry {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
          }
        }
        Stmt::ExportDefaultExpr(node) => {
          let span = loc_to_span(file, node.loc);
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: "default".to_string(),
              file,
              span: span.range,
              symbol,
              export: true,
              kind: DefKind::Var(VarData {
                typ: None,
                init: None,
                body: MISSING_BODY,
                mode: VarDeclMode::Const,
              }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          defs.push(def_id);
          sem_builder.add_decl(
            def_id,
            "default".to_string(),
            sem_ts::DeclKind::Var,
            sem_ts::Exported::Default,
            span.range,
          );
          bindings.insert(
            "default".to_string(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
          exports.insert(
            "default".to_string(),
            ExportEntry {
              symbol,
              def: Some(def_id),
              type_id: None,
            },
          );
        }
        Stmt::ExportList(export_list) => {
          let resolved = export_list
            .stx
            .from
            .as_ref()
            .and_then(|module| self.record_module_resolution(file, module, host));
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          match &export_list.stx.names {
            ExportNames::Specific(names) => {
              for name in names {
                let exportable = name.stx.exportable.as_str().to_string();
                let alias = name.stx.alias.stx.name.clone();
                let exported_as = if alias == exportable {
                  None
                } else {
                  Some(alias.clone())
                };
                let is_type_only = export_list.stx.type_only || name.stx.type_only;
                sem_builder.add_named_export(
                  export_list.stx.from.clone(),
                  export_list
                    .stx
                    .from
                    .as_ref()
                    .map(|_| loc_to_span(file, stmt.loc).range),
                  vec![sem_ts::ExportSpecifier {
                    local: exportable.clone(),
                    exported: exported_as.clone(),
                    local_span: loc_to_span(file, name.loc).range,
                    exported_span: exported_as
                      .as_ref()
                      .map(|_| loc_to_span(file, name.stx.alias.loc).range),
                  }],
                  is_type_only,
                );

                if let Some(target) = resolved {
                  reexports.push(Reexport {
                    from: target,
                    original: exportable.clone(),
                    alias: alias.clone(),
                    type_only: is_type_only,
                    span: loc_to_span(file, name.loc).range,
                  });
                }

                if export_list.stx.from.is_none() && !is_type_only {
                  let mapped = bindings.get(&exportable);
                  if let Some(binding) = mapped {
                    exports.insert(
                      alias.clone(),
                      ExportEntry {
                        symbol: binding.symbol,
                        def: binding.def,
                        type_id: binding.type_id,
                      },
                    );
                  } else {
                    self.diagnostics.push(codes::UNKNOWN_EXPORT.error(
                      format!("unknown export {exportable}"),
                      loc_to_span(file, name.loc),
                    ));
                  }
                }
              }
            }
            ExportNames::All(alias) => {
              if let Some(spec) = export_list.stx.from.clone() {
                if alias.is_none() {
                  if let Some(target) = resolved {
                    export_all.push(ExportAll {
                      from: target,
                      type_only: export_list.stx.type_only,
                    });
                  }
                }
                let alias = alias
                  .as_ref()
                  .map(|alias| (alias.stx.name.clone(), loc_to_span(file, alias.loc).range));
                sem_builder.add_export_all(
                  spec,
                  loc_to_span(file, stmt.loc).range,
                  export_list.stx.type_only,
                  alias,
                );
              }
            }
          }
        }
        Stmt::Import(import_stmt) => {
          let module = import_stmt.stx.module.clone();
          let resolved = self.record_module_resolution(file, &module, host);
          if let Some(target) = resolved {
            queue.push_back(target);
          }
          let import_target =
            resolved
              .map(ImportTarget::File)
              .unwrap_or_else(|| ImportTarget::Unresolved {
                specifier: module.clone(),
              });
          let mut import_default = None;
          let mut import_namespace = None;
          let mut import_named = Vec::new();
          if let Some(default_pat) = import_stmt.stx.default.as_ref() {
            let alias_name = match &default_pat.stx.pat.stx.as_ref() {
              Pat::Id(id) => id.stx.name.clone(),
              _ => {
                self
                  .diagnostics
                  .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                    "unsupported import pattern",
                    loc_to_span(file, default_pat.loc),
                  ));
                continue;
              }
            };
            import_default = Some(sem_ts::ImportDefault {
              local: alias_name.clone(),
              local_span: loc_to_span(file, default_pat.loc).range,
              is_type_only: import_stmt.stx.type_only,
            });
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: alias_name.clone(),
                file,
                span: loc_to_span(file, default_pat.loc).range,
                symbol,
                export: false,
                kind: DefKind::Import(ImportData {
                  target: import_target.clone(),
                  original: "default".to_string(),
                }),
              },
            );
            defs.push(def_id);
            bindings.insert(
              alias_name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            self.record_symbol(file, loc_to_span(file, default_pat.loc).range, symbol);
          }
          match import_stmt.stx.names {
            Some(ImportNames::Specific(ref list)) => {
              for entry in list {
                let name = entry.stx.importable.as_str().to_string();
                let alias_pat = &entry.stx.alias;
                let alias_name = match &alias_pat.stx.pat.stx.as_ref() {
                  Pat::Id(id) => id.stx.name.clone(),
                  _ => {
                    self
                      .diagnostics
                      .push(codes::UNSUPPORTED_IMPORT_PATTERN.error(
                        "unsupported import pattern",
                        loc_to_span(file, alias_pat.loc),
                      ));
                    continue;
                  }
                };
                let is_type_only = import_stmt.stx.type_only || entry.stx.type_only;
                import_named.push(sem_ts::ImportNamed {
                  imported: name.clone(),
                  local: alias_name.clone(),
                  is_type_only,
                  imported_span: loc_to_span(file, entry.loc).range,
                  local_span: loc_to_span(file, alias_pat.loc).range,
                });
                let symbol = self.alloc_symbol();
                let def_id = self.alloc_def();
                self.def_data.insert(
                  def_id,
                  DefData {
                    name: alias_name.clone(),
                    file,
                    span: loc_to_span(file, alias_pat.loc).range,
                    symbol,
                    export: false,
                    kind: DefKind::Import(ImportData {
                      target: import_target.clone(),
                      original: name.clone(),
                    }),
                  },
                );
                self.record_def_symbol(def_id, symbol);
                defs.push(def_id);
                bindings.insert(
                  alias_name.clone(),
                  SymbolBinding {
                    symbol,
                    def: Some(def_id),
                    type_id: None,
                  },
                );
                self.record_symbol(file, loc_to_span(file, alias_pat.loc).range, symbol);
              }
            }
            Some(ImportNames::All(ref pat)) => {
              let alias_name = match &pat.stx.pat.stx.as_ref() {
                Pat::Id(id) => id.stx.name.clone(),
                _ => {
                  self.diagnostics.push(
                    codes::UNSUPPORTED_IMPORT_PATTERN
                      .error("unsupported import pattern", loc_to_span(file, pat.loc)),
                  );
                  continue;
                }
              };
              import_namespace = Some(sem_ts::ImportNamespace {
                local: alias_name.clone(),
                local_span: loc_to_span(file, pat.loc).range,
                is_type_only: import_stmt.stx.type_only,
              });
              let symbol = self.alloc_symbol();
              let def_id = self.alloc_def();
              self.def_data.insert(
                def_id,
                DefData {
                  name: alias_name.clone(),
                  file,
                  span: loc_to_span(file, pat.loc).range,
                  symbol,
                  export: false,
                  kind: DefKind::Import(ImportData {
                    target: import_target.clone(),
                    original: "*".to_string(),
                  }),
                },
              );
              self.record_def_symbol(def_id, symbol);
              defs.push(def_id);
              bindings.insert(
                alias_name.clone(),
                SymbolBinding {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
              self.record_symbol(file, loc_to_span(file, pat.loc).range, symbol);
            }
            None => {}
          }
          sem_builder.add_import(sem_ts::Import {
            specifier: module,
            specifier_span: loc_to_span(file, stmt.loc).range,
            default: import_default,
            namespace: import_namespace,
            named: import_named,
            is_type_only: import_stmt.stx.type_only,
          });
        }
        Stmt::ImportEqualsDecl(import_equals) => match &import_equals.stx.rhs {
          ImportEqualsRhs::Require { module } => {
            let resolved = self.record_module_resolution(file, module, host);
            if let Some(target) = resolved {
              queue.push_back(target);
            }
            let import_target =
              resolved
                .map(ImportTarget::File)
                .unwrap_or_else(|| ImportTarget::Unresolved {
                  specifier: module.clone(),
                });
            let span = loc_to_span(file, stmt.loc).range;
            self
              .import_assignment_requires
              .push(ImportAssignmentRequireRecord {
                file,
                span,
                target: import_target.clone(),
              });
            let name = import_equals.stx.name.clone();
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span,
                symbol,
                export: import_equals.stx.export,
                kind: DefKind::Import(ImportData {
                  target: import_target.clone(),
                  original: "*".to_string(),
                }),
              },
            );
            self.record_def_symbol(def_id, symbol);
            defs.push(def_id);
            bindings.insert(
              name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            self.record_symbol(file, span, symbol);
            if import_equals.stx.export {
              exports.insert(
                name.clone(),
                ExportEntry {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
            }
            sem_builder.add_import_equals(sem_ts::ImportEquals {
              local: name,
              local_span: span,
              target: sem_ts::ImportEqualsTarget::Require {
                specifier: module.clone(),
                specifier_span: span,
              },
              is_exported: import_equals.stx.export,
            });
          }
          ImportEqualsRhs::EntityName { path } => {
            let span = loc_to_span(file, stmt.loc).range;
            let name = import_equals.stx.name.clone();
            let symbol = self.alloc_symbol();
            let def_id = self.alloc_def();
            self.def_data.insert(
              def_id,
              DefData {
                name: name.clone(),
                file,
                span,
                symbol,
                export: import_equals.stx.export,
                kind: DefKind::ImportAlias(ImportAliasData { path: path.clone() }),
              },
            );
            self.record_def_symbol(def_id, symbol);
            defs.push(def_id);
            bindings.insert(
              name.clone(),
              SymbolBinding {
                symbol,
                def: Some(def_id),
                type_id: None,
              },
            );
            self.record_symbol(file, span, symbol);
            if import_equals.stx.export {
              exports.insert(
                name.clone(),
                ExportEntry {
                  symbol,
                  def: Some(def_id),
                  type_id: None,
                },
              );
            }
            sem_builder.add_import_equals(sem_ts::ImportEquals {
              local: name,
              local_span: span,
              target: sem_ts::ImportEqualsTarget::EntityName {
                path: path.clone(),
                span,
              },
              is_exported: import_equals.stx.export,
            });
          }
        },
        Stmt::Expr(_) | Stmt::If(_) | Stmt::Block(_) | Stmt::While(_) => {}
        _ => {}
      }
    }

    self.files.insert(
      file,
      FileState {
        defs,
        exports,
        bindings,
        top_body: None,
        reexports,
        export_all,
      },
    );
    sem_builder.finish()
  }

  fn bind_namespace_member_defs(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    file_kind: sem_ts::FileKind,
    defs: &mut Vec<DefId>,
  ) {
    fn bind_body(
      state: &mut ProgramState,
      file: FileId,
      body: &NamespaceBody,
      defs: &mut Vec<DefId>,
      builder: &mut SemHirBuilder,
    ) {
      match body {
        NamespaceBody::Block(stmts) => {
          for stmt in stmts.iter() {
            match stmt.stx.as_ref() {
              Stmt::VarDecl(var) => {
                let new_defs = state.handle_var_decl(file, var.stx.as_ref(), builder);
                for (def_id, _binding, _export_name) in new_defs {
                  defs.push(def_id);
                }
              }
              Stmt::FunctionDecl(func) => {
                let span = loc_to_span(file, stmt.loc);
                if let Some((def_id, _binding, _export_name)) =
                  state.handle_function_decl(file, span.range, func.stx.as_ref(), builder)
                {
                  defs.push(def_id);
                }
              }
              Stmt::NamespaceDecl(ns) => {
                let span = loc_to_span(file, stmt.loc);
                let name = ns.stx.name.clone();
                let symbol = state.alloc_symbol();
                let def_id = state.alloc_def();
                state.def_data.insert(
                  def_id,
                  DefData {
                    name: name.clone(),
                    file,
                    span: span.range,
                    symbol,
                    export: ns.stx.export,
                    kind: DefKind::Namespace(NamespaceData {
                      body: None,
                      value_type: None,
                      type_type: None,
                      declare: ns.stx.declare,
                    }),
                  },
                );
                state.record_def_symbol(def_id, symbol);
                state.record_symbol(file, span.range, symbol);
                defs.push(def_id);
                bind_body(state, file, &ns.stx.body, defs, builder);
              }
              _ => {}
            }
          }
        }
        NamespaceBody::Namespace(inner) => {
          let span = loc_to_span(file, inner.loc);
          let name = inner.stx.name.clone();
          let symbol = state.alloc_symbol();
          let def_id = state.alloc_def();
          state.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: inner.stx.export,
              kind: DefKind::Namespace(NamespaceData {
                body: None,
                value_type: None,
                type_type: None,
                declare: inner.stx.declare,
              }),
            },
          );
          state.record_def_symbol(def_id, symbol);
          state.record_symbol(file, span.range, symbol);
          defs.push(def_id);
          bind_body(state, file, &inner.stx.body, defs, builder);
        }
      }
    }

    let mut dummy_builder = SemHirBuilder::new(file, file_kind);
    bind_body(self, file, body, defs, &mut dummy_builder);
  }

  fn bind_ambient_module(
    &mut self,
    file: FileId,
    module: &Node<parse_js::ast::ts_stmt::ModuleDecl>,
    builder: &mut SemHirBuilder,
    defs: &mut Vec<DefId>,
  ) {
    let Some(body) = module.stx.body.as_ref() else {
      return;
    };
    let name_span = loc_to_span(file, module.loc).range;
    let name = match &module.stx.name {
      parse_js::ast::ts_stmt::ModuleName::Identifier(id) => id.clone(),
      parse_js::ast::ts_stmt::ModuleName::String(specifier) => specifier.clone(),
    };
    let mut module_builder = SemHirBuilder::new_ambient(file, builder.file_kind);
    let mut bindings = HashMap::new();
    for stmt in body.iter() {
      self.bind_ambient_stmt(file, stmt, &mut module_builder, &mut bindings, defs);
    }
    builder.add_ambient_module(module_builder.into_ambient(name, name_span));
  }

  fn bind_ambient_stmt(
    &mut self,
    file: FileId,
    stmt: &Node<Stmt>,
    builder: &mut SemHirBuilder,
    bindings: &mut HashMap<String, SymbolBinding>,
    defs: &mut Vec<DefId>,
  ) {
    match stmt.stx.as_ref() {
      Stmt::AmbientVarDecl(var) => {
        let span = loc_to_span(file, stmt.loc);
        let name = var.stx.name.clone();
        let typ = var
          .stx
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(t));
        let symbol = self.alloc_symbol();
        let def_id = self.alloc_def();
        self.record_symbol(file, span.range, symbol);
        self.def_data.insert(
          def_id,
          DefData {
            name: name.clone(),
            file,
            span: span.range,
            symbol,
            export: var.stx.export,
            kind: DefKind::Var(VarData {
              typ,
              init: None,
              body: MISSING_BODY,
              mode: VarDeclMode::Var,
            }),
          },
        );
        self.record_def_symbol(def_id, symbol);
        defs.push(def_id);
        bindings.insert(
          name.clone(),
          SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: typ,
          },
        );
        builder.add_decl(
          def_id,
          name,
          sem_ts::DeclKind::Var,
          if var.stx.export {
            sem_ts::Exported::Named
          } else {
            sem_ts::Exported::No
          },
          span.range,
        );
      }
      Stmt::VarDecl(var) => {
        let new_defs = self.handle_var_decl(file, var.stx.as_ref(), builder);
        for (def_id, binding, _export_name) in new_defs {
          defs.push(def_id);
          let (name, value) = binding;
          bindings.insert(name, value);
        }
      }
      Stmt::FunctionDecl(func) => {
        let span = loc_to_span(file, stmt.loc);
        if let Some((def_id, binding, _export_name)) =
          self.handle_function_decl(file, span.range, func.stx.as_ref(), builder)
        {
          defs.push(def_id);
          let (name, value) = binding;
          bindings.insert(name, value);
        }
      }
      Stmt::InterfaceDecl(interface) => {
        let span = loc_to_span(file, stmt.loc);
        let name = interface.stx.name.clone();
        let mut object = self.object_type_from_members(&interface.stx.members);
        for base in interface.stx.extends.iter() {
          let base_ty = self.type_from_type_expr(base);
          if let TypeKind::Object(base_obj) = self.type_store.kind(base_ty).clone() {
            object = self.merge_object_types(object, base_obj);
          }
        }
        let mut typ = self.type_store.object(object);
        let existing_interface = bindings
          .get(&name)
          .and_then(|b| b.def)
          .and_then(|id| self.def_data.get(&id).map(|d| (id, d.clone())))
          .and_then(|(id, data)| match data.kind {
            DefKind::Interface(existing) => Some((id, data.symbol, existing.typ)),
            _ => None,
          });
        let (def_id, symbol) = if let Some((existing_id, symbol, existing_ty)) = existing_interface
        {
          typ = match (
            self.type_store.kind(existing_ty).clone(),
            self.type_store.kind(typ).clone(),
          ) {
            (TypeKind::Object(existing_obj), TypeKind::Object(obj)) => {
              let merged = self.merge_object_types(existing_obj, obj);
              self.type_store.object(merged)
            }
            _ => self.type_store.union(vec![existing_ty, typ], &self.builtin),
          };
          if let Some(def) = self.def_data.get_mut(&existing_id) {
            def.kind = DefKind::Interface(InterfaceData { typ });
            def.export = def.export || interface.stx.export;
          }
          (existing_id, symbol)
        } else {
          let symbol = self.alloc_symbol();
          let def_id = self.alloc_def();
          self.def_data.insert(
            def_id,
            DefData {
              name: name.clone(),
              file,
              span: span.range,
              symbol,
              export: interface.stx.export,
              kind: DefKind::Interface(InterfaceData { typ }),
            },
          );
          self.record_def_symbol(def_id, symbol);
          defs.push(def_id);
          builder.add_decl(
            def_id,
            name.clone(),
            sem_ts::DeclKind::Interface,
            if interface.stx.export {
              sem_ts::Exported::Named
            } else {
              sem_ts::Exported::No
            },
            span.range,
          );
          (def_id, symbol)
        };

        bindings
          .entry(name.clone())
          .and_modify(|binding| {
            binding.symbol = symbol;
            binding.def = Some(def_id);
            binding.type_id = Some(typ);
          })
          .or_insert(SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: Some(typ),
          });

        self.def_types.insert(def_id, typ);
        self.record_symbol(file, span.range, symbol);
      }
      Stmt::TypeAliasDecl(alias) => {
        let span = loc_to_span(file, stmt.loc);
        let name = alias.stx.name.clone();
        let mut ty = self.type_from_type_expr(&alias.stx.type_expr);
        if ty == self.builtin.unknown {
          ty = self.type_store.literal_string(name.clone());
        }
        if let TypeExpr::TypeReference(reference) = alias.stx.type_expr.stx.as_ref() {
          if let TypeEntityName::Identifier(type_name) = &reference.stx.name {
            if let Some(binding) = bindings.get(type_name) {
              self.record_symbol(
                file,
                loc_to_span(file, alias.stx.type_expr.loc).range,
                binding.symbol,
              );
            }
          }
        }
        let def_id = self.alloc_def();
        let symbol = self.alloc_symbol();
        self.def_data.insert(
          def_id,
          DefData {
            name: name.clone(),
            file,
            span: span.range,
            symbol,
            export: alias.stx.export,
            kind: DefKind::TypeAlias(TypeAliasData { typ: ty }),
          },
        );
        self.record_def_symbol(def_id, symbol);
        self.def_types.insert(def_id, ty);
        bindings.insert(
          name.clone(),
          SymbolBinding {
            symbol,
            def: Some(def_id),
            type_id: Some(ty),
          },
        );
        defs.push(def_id);
        self.record_symbol(file, span.range, symbol);
        builder.add_decl(
          def_id,
          name.clone(),
          sem_ts::DeclKind::TypeAlias,
          if alias.stx.export {
            sem_ts::Exported::Named
          } else {
            sem_ts::Exported::No
          },
          span.range,
        );
      }
      Stmt::NamespaceDecl(ns) => {
        self.bind_ambient_namespace_body(file, &ns.stx.body, builder, bindings, defs);
      }
      Stmt::ModuleDecl(module) => {
        if matches!(
          module.stx.name,
          parse_js::ast::ts_stmt::ModuleName::String(_)
        ) {
          self.bind_ambient_module(file, module, builder, defs);
        }
      }
      _ => {}
    }
  }

  fn bind_ambient_namespace_body(
    &mut self,
    file: FileId,
    body: &NamespaceBody,
    builder: &mut SemHirBuilder,
    bindings: &mut HashMap<String, SymbolBinding>,
    defs: &mut Vec<DefId>,
  ) {
    match body {
      NamespaceBody::Block(stmts) => {
        for stmt in stmts.iter() {
          self.bind_ambient_stmt(file, stmt, builder, bindings, defs);
        }
      }
      NamespaceBody::Namespace(inner) => {
        self.bind_ambient_namespace_body(file, &inner.stx.body, builder, bindings, defs)
      }
    }
  }

  fn handle_var_decl(
    &mut self,
    file: FileId,
    var: &VarDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Vec<(DefId, (String, SymbolBinding), Option<String>)> {
    fn collect_bound_names(
      state: &mut ProgramState,
      file: FileId,
      pat: &Node<Pat>,
      out: &mut Vec<(String, TextRange)>,
    ) {
      match pat.stx.as_ref() {
        Pat::Id(id) => {
          out.push((id.stx.name.clone(), loc_to_span(file, id.loc).range));
        }
        Pat::Arr(arr) => {
          for elem in arr.stx.elements.iter() {
            let Some(elem) = elem.as_ref() else {
              continue;
            };
            collect_bound_names(state, file, &elem.target, out);
          }
          if let Some(rest) = arr.stx.rest.as_ref() {
            collect_bound_names(state, file, rest, out);
          }
        }
        Pat::Obj(obj) => {
          for prop in obj.stx.properties.iter() {
            collect_bound_names(state, file, &prop.stx.target, out);
          }
          if let Some(rest) = obj.stx.rest.as_ref() {
            collect_bound_names(state, file, rest, out);
          }
        }
        Pat::AssignTarget(_) => {
          state.diagnostics.push(
            codes::UNSUPPORTED_PATTERN.error("unsupported pattern", loc_to_span(file, pat.loc)),
          );
        }
      }
    }

    let mut defs = Vec::new();
    for declarator in var.declarators.iter() {
      let pat = &declarator.pattern;
      let type_ann = match pat.stx.pat.stx.as_ref() {
        Pat::Id(_) => declarator
          .type_annotation
          .as_ref()
          .map(|t| self.type_from_type_expr(t)),
        _ => None,
      };
      let mut names = Vec::new();
      collect_bound_names(self, file, &pat.stx.pat, &mut names);
      for (name, def_span) in names {
        let symbol = self.alloc_symbol();
        let def_id = self.alloc_def();
        self.record_symbol(file, def_span, symbol);
        self.def_data.insert(
          def_id,
          DefData {
            name: name.clone(),
            file,
            span: def_span,
            symbol,
            export: var.export,
            kind: DefKind::Var(VarData {
              typ: type_ann,
              init: None,
              body: MISSING_BODY,
              mode: var.mode,
            }),
          },
        );
        self.record_def_symbol(def_id, symbol);
        defs.push((
          def_id,
          (
            name.clone(),
            SymbolBinding {
              symbol,
              def: Some(def_id),
              type_id: type_ann,
            },
          ),
          if var.export { Some(name.clone()) } else { None },
        ));
        sem_builder.add_decl(
          def_id,
          name.clone(),
          sem_ts::DeclKind::Var,
          if var.export {
            sem_ts::Exported::Named
          } else {
            sem_ts::Exported::No
          },
          def_span,
        );
      }
    }
    defs
  }

  fn handle_function_decl(
    &mut self,
    file: FileId,
    span: TextRange,
    func: &FuncDecl,
    sem_builder: &mut SemHirBuilder,
  ) -> Option<(DefId, (String, SymbolBinding), Option<String>)> {
    let name_node = func.name.as_ref()?;
    let name = name_node.stx.name.clone();
    let symbol = self.alloc_symbol();
    self.record_symbol(file, loc_to_span(file, name_node.loc).range, symbol);
    let def_id = self.alloc_def();
    let func_data = self.lower_function(file, func.function.stx.as_ref(), def_id);
    self.def_data.insert(
      def_id,
      DefData {
        name: name.clone(),
        file,
        span,
        symbol,
        export: func.export || func.export_default,
        kind: DefKind::Function(func_data),
      },
    );
    self.record_def_symbol(def_id, symbol);
    sem_builder.add_decl(
      def_id,
      name.clone(),
      sem_ts::DeclKind::Function,
      if func.export_default {
        sem_ts::Exported::Default
      } else if func.export {
        sem_ts::Exported::Named
      } else {
        sem_ts::Exported::No
      },
      loc_to_span(file, name_node.loc).range,
    );
    let binding = (
      name.clone(),
      SymbolBinding {
        symbol,
        def: Some(def_id),
        type_id: None,
      },
    );
    let export_name = if func.export_default {
      Some("default".to_string())
    } else if func.export {
      Some(name.clone())
    } else {
      None
    };
    Some((def_id, binding, export_name))
  }

  fn lower_function(&mut self, file: FileId, func: &Func, _def: DefId) -> FuncData {
    let mut params = Vec::new();
    for (idx, param) in func.parameters.iter().enumerate() {
      params.push(self.lower_param(file, param, idx));
    }
    let return_ann = func
      .return_type
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    FuncData {
      params,
      return_ann,
      body: None,
    }
  }

  fn lower_param(&mut self, file: FileId, param: &Node<ParamDecl>, index: usize) -> ParamData {
    let (name, symbol, record_symbol) = match param.stx.pattern.stx.pat.stx.as_ref() {
      Pat::Id(id) => (id.stx.name.clone(), self.alloc_symbol(), true),
      _ => (format!("<pattern{index}>"), self.alloc_symbol(), false),
    };
    let typ = param
      .stx
      .type_annotation
      .as_ref()
      .map(|t| self.type_from_type_expr(t));
    if record_symbol {
      self.record_symbol(file, loc_to_span(file, param.stx.pattern.loc).range, symbol);
    }
    ParamData {
      name,
      typ,
      symbol,
      pat: None,
    }
  }
}
