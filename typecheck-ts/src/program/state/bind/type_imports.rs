use super::*;

impl ProgramState {
  pub(super) fn queue_type_imports_in_stmt(
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

  pub(in super::super) fn queue_type_imports_in_ast(
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
}
