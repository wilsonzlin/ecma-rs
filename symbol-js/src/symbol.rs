use ahash::HashMap;
use ahash::HashMapExt;
use parking_lot::RwLock;
use serde::Serialize;
use core::ptr;
use std::collections::hash_map::Entry;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::Write;
use std::hash::Hash;
use std::ops::Deref;
use std::ops::DerefMut;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
use std::sync::Arc;

pub type Identifier = String;

// We don't store the associated Scope anymore as we want to allow easy moving of symbols between scopes (the parse-js parser doesn't do this, but library consumers might), which allows for easy migration of usages without having to rename every one of them. Since we don't have anything else to store, we can't use a reference due to potential zero-sized allocation issues, so we just use a unique sequence number instead.
// To attach additional custom state to a Symbol, use a HashMap. We prefer this instead of adding an extra generic state field on Symbol, as that would require propagating the generic type everywhere.
// Cloning means to cheaply clone the reference to this unique symbol, not create a duplicate symbol. This is useful for sharing a reference to a symbol, including uses in data structures like HashMap.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize)]
pub struct Symbol(u64);

impl Symbol {
  /// It's not recommended to use this unless you know what you're doing; symbol IDs are opaque, ephemeral, and non-deterministic.
  pub fn raw_id(&self) -> u64 {
    self.0
  }

  /// It's not recommended to use this unless you know what you're doing; symbol IDs are opaque, ephemeral, and non-deterministic.
  pub fn from_raw_id(id: u64) -> Symbol {
    Symbol(id)
  }
}

// TODO We can probably avoid using a Arc, but this would require refs and lifetimes (possibly not 'a but an additional one) everywhere. Investigate if performance becomes costly.
#[derive(Clone)]
pub struct SymbolGenerator(Arc<AtomicU64>);

impl SymbolGenerator {
  pub fn new() -> SymbolGenerator {
    SymbolGenerator(Arc::new(AtomicU64::new(0)))
  }

  pub fn next(&self) -> Symbol {
    Symbol(self.0.fetch_add(1, Ordering::Relaxed))
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ScopeType {
  Global,
  Module,
  // Closure with `this` (property initialisers have access to it) but not `arguments`. See examples/es6-class.md.
  Class,
  // Functions with `this` and `arguments`.
  NonArrowFunction,
  // Functions with neither `this` nor `arguments`.
  // NOTE: Arrow function class properties are not on the prototype and simply have access to the class's `this` like other initialisers; it doesn't have a special `this` binding and inherits it like any other arrow function. See examples/es6-class.md.
  ArrowFunction,
  Block,
}

impl ScopeType {
  pub fn is_closure(&self) -> bool {
    match self {
      ScopeType::Module => true,
      ScopeType::NonArrowFunction => true,
      ScopeType::ArrowFunction => true,
      _ => false,
    }
  }

  pub fn is_closure_or_class(&self) -> bool {
    match self {
      ScopeType::Class => true,
      t => t.is_closure(),
    }
  }

  pub fn is_closure_or_global(&self) -> bool {
    match self {
      ScopeType::Global => true,
      t => t.is_closure(),
    }
  }

  pub fn is_closure_or_block(&self) -> bool {
    match self {
      ScopeType::Block => true,
      t => t.is_closure(),
    }
  }
}

pub struct ScopeData {
  symbol_generator: SymbolGenerator,
  symbols: HashMap<Identifier, Symbol>,
  // For deterministic outputs, and to give each Symbol an ID.
  symbol_declaration_order: Vec<Identifier>,
  // Does not exist for top-level.
  parent: Option<Scope>,
  // Not used by the parser, but useful for some library consumers, as there's currently no other way to iterate all scopes.
  children: Vec<Scope>,
  typ: ScopeType,
}

impl ScopeData {
  pub fn parent(&self) -> Option<&Scope> {
    self.parent.as_ref()
  }

  pub fn typ(&self) -> ScopeType {
    self.typ
  }

  pub fn add_symbol(&mut self, identifier: Identifier) {
    match self.symbols.entry(identifier.clone()) {
      Entry::Occupied(_) => {
        // Do not replace existing entry, as it has associated index in symbol_declaration_order.
        // TODO Investigate raising an error; however, many production codebases redeclare `var`.
      }
      Entry::Vacant(e) => {
        e.insert(self.symbol_generator.next());
        self.symbol_declaration_order.push(identifier.clone());
      }
    };
  }

  pub fn add_symbol_if_not_global(&mut self, identifier: Identifier) {
    if self.typ != ScopeType::Global {
      self.add_symbol(identifier);
    };
  }

  pub fn get_symbol(&self, identifier: &str) -> Option<Symbol> {
    self.symbols.get(identifier).cloned()
  }

  pub fn symbol_count(&self) -> usize {
    self.symbols.len()
  }

  pub fn symbol_names(&self) -> &Vec<String> {
    &self.symbol_declaration_order
  }

  pub fn children(&self) -> &Vec<Scope> {
    &self.children
  }
}

// We have downstream uses across threads, so use Arc<RwLock<>> instead of Rc<RefCell<>>.
#[derive(Clone)]
pub struct Scope(Arc<RwLock<ScopeData>>);

impl Scope {
  pub fn new(symbol_generator: SymbolGenerator, parent: Option<Scope>, typ: ScopeType) -> Scope {
    let scope = Scope(Arc::new(RwLock::new(ScopeData {
      symbol_generator,
      symbols: HashMap::new(),
      symbol_declaration_order: Vec::new(),
      parent: parent.clone(),
      children: Vec::new(),
      typ,
    })));
    if let Some(parent) = parent {
      parent.0.write().children.push(scope.clone());
    };
    scope
  }

  pub fn data(&self) -> impl Deref<Target = ScopeData> + '_ {
    self.0.read()
  }

  pub fn data_mut(&self) -> impl DerefMut<Target = ScopeData> + '_ {
    self.0.write()
  }

  pub fn create_child_scope(&self, typ: ScopeType) -> Scope {
    // Scope::new will also acquire ref, so we cannot do this inline.
    let symbol_generator = self.0.read().symbol_generator.clone();
    Scope::new(symbol_generator, Some(self.clone()), typ)
  }

  /// Returns the closest self-or-ancestor scope that matches the provided predicate. If no such match is found, None is returned.
  pub fn find_nearest_scope<F: Fn(ScopeType) -> bool>(&self, pred: F) -> Option<Scope> {
    let cur = self.0.read();
    if pred(cur.typ) {
      Some(self.clone())
    } else if let Some(parent) = &cur.parent {
      parent.find_nearest_scope(pred)
    } else {
      None
    }
  }

  /// Returns the most distant self-or-ancestor scope that matches the provided predicate. If no such match is found, None is returned.
  pub fn find_furthest_scope<F: Fn(ScopeType) -> bool>(&self, pred: F) -> Option<Scope> {
    let mut latest_match = None;
    let mut cur = self.clone();
    loop {
      if !pred(cur.0.read().typ) {
        break;
      };
      latest_match = Some(cur.clone());
      let Some(parent) = cur.0.read().parent.clone() else {
        break;
      };
      cur = parent;
    }
    latest_match
  }

  /// Returns the matching symbol and associated nearest scope that contains the provided identifier. Once a scope is reached that matches the provided predicate, the search stops *after* looking in that scope. If no such match is found, None is returned.
  pub fn find_symbol_up_to_with_scope(
    &self,
    identifier: Identifier,
    scope_pred: impl Fn(ScopeType) -> bool,
  ) -> Option<(Scope, Symbol)> {
    let cur = self.0.read();
    match cur.symbols.get(&identifier) {
      Some(symbol) => Some((self.clone(), symbol.clone())),
      None => {
        if scope_pred(cur.typ) {
          None
        } else {
          match &cur.parent {
            Some(parent) => parent.find_symbol_up_to_with_scope(identifier, scope_pred),
            None => None,
          }
        }
      }
    }
  }

  /// Returns the matching symbol in the nearest scope for the provided identifier. Once a scope is reached that matches the provided predicate, the search stops *after* looking in that scope. If no such match is found, None is returned.
  pub fn find_symbol_up_to<'b>(
    &self,
    identifier: Identifier,
    scope_pred: impl Fn(ScopeType) -> bool,
  ) -> Option<Symbol> {
    self
      .find_symbol_up_to_with_scope(identifier, scope_pred)
      .map(|(_, symbol)| symbol)
  }

  /// Returns the matching symbol in the nearest scope for the provided identifier. Once a scope is reached that matches the provided type, the search stops *after* looking in that scope. If no such match is found, None is returned.
  pub fn find_symbol_up_to_nearest_scope_of_type<'b>(
    &self,
    identifier: Identifier,
    scope_type: ScopeType,
  ) -> Option<Symbol> {
    self.find_symbol_up_to(identifier, |t| t == scope_type)
  }

  /// Returns the matching symbol in the nearest scope for the provided identifier. If no such match is found, None is returned.
  pub fn find_symbol(&self, identifier: Identifier) -> Option<Symbol> {
    self.find_symbol_up_to(identifier, |_| false)
  }

  pub fn debug_indented(&self, out: &mut impl fmt::Write, indent: usize) -> fmt::Result {
    let cur = self.0.read();
    write!(out, "{}", "  ".repeat(indent))?;
    write!(out, "{:?}: {}\n", cur.typ, cur.symbol_declaration_order.join(", "))?;
    for child in cur.children.iter() {
      child.debug_indented(out, indent + 1)?;
    };
    Ok(())
  }
}

// Equality means referring to the same unique scope. Useful for HashMap.
impl PartialEq for Scope {
  fn eq(&self, other: &Self) -> bool {
    ptr::eq(self.0.data_ptr(), other.0.data_ptr())
  }
}

impl Eq for Scope {}

impl Hash for Scope {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    ptr::hash(self.0.data_ptr(), state);
  }
}

impl Debug for Scope {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    f.write_str("\nScope:\n")?;
    self.debug_indented(f, 1)
  }
}
