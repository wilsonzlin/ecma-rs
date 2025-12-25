use crate::il::inst::{Arg, Inst, InstTyp};
use crate::symbol::semantics::SymbolId;
use crate::Program;
use ahash::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForeignBinding {
  pub symbol: SymbolId,
  pub ident: String,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ForeignBindings {
  bindings: Vec<ForeignBinding>,
  map: HashMap<SymbolId, String>,
}

impl ForeignBindings {
  pub fn is_empty(&self) -> bool {
    self.bindings.is_empty()
  }

  pub fn len(&self) -> usize {
    self.bindings.len()
  }

  pub fn iter(&self) -> impl Iterator<Item = &ForeignBinding> {
    self.bindings.iter()
  }

  pub fn name_for(&self, symbol: SymbolId) -> Option<&str> {
    self.map.get(&symbol).map(|s| s.as_str())
  }
}

fn visit_insts(program: &Program, mut f: impl FnMut(&Inst)) {
  for (_, insts) in program.top_level.body.bblocks.all() {
    for inst in insts {
      f(inst);
    }
  }
  for func in &program.functions {
    for (_, insts) in func.body.bblocks.all() {
      for inst in insts {
        f(inst);
      }
    }
  }
}

fn collect_reserved_names(program: &Program) -> HashSet<String> {
  let mut reserved = HashSet::default();
  visit_insts(program, |inst| {
    match inst.t {
      InstTyp::UnknownLoad | InstTyp::UnknownStore => {
        reserved.insert(inst.unknown.clone());
      }
      _ => {}
    }
    for arg in inst.args.iter() {
      if let Arg::Builtin(path) = arg {
        if let Some(root) = path.split('.').next() {
          reserved.insert(root.to_string());
        }
      }
    }
  });
  reserved
}

fn collect_foreign_symbols(program: &Program) -> Vec<SymbolId> {
  let mut symbols = HashSet::default();
  visit_insts(program, |inst| match inst.t {
    InstTyp::ForeignLoad | InstTyp::ForeignStore => {
      symbols.insert(inst.foreign);
    }
    _ => {}
  });
  let mut symbols = symbols.into_iter().collect::<Vec<_>>();
  symbols.sort_by_key(|s| s.raw_id());
  symbols
}

fn generate_names(count: usize, reserved: &HashSet<String>) -> (String, Vec<String>) {
  if count == 0 {
    return ("".to_string(), Vec::new());
  }
  let mut prefix = "__f".to_string();
  loop {
    let names = (0..count)
      .map(|i| format!("{prefix}{i}"))
      .collect::<Vec<_>>();
    if names.iter().all(|n| !reserved.contains(n)) {
      return (prefix, names);
    }
    if prefix == "__f" {
      prefix = "__ecma_f".to_string();
    } else {
      prefix.push('_');
    }
  }
}

/// Collect all foreign symbols in the program and assign deterministic names for decompilation.
///
/// All names used by unknown loads/stores and builtin roots are treated as reserved; generated
/// identifiers will avoid colliding with them by falling back to a longer prefix when necessary.
pub fn collect_foreign_bindings(program: &Program) -> ForeignBindings {
  let symbols = collect_foreign_symbols(program);
  let reserved = collect_reserved_names(program);
  let (_, names) = generate_names(symbols.len(), &reserved);

  let mut bindings = Vec::with_capacity(symbols.len());
  let mut map = HashMap::default();
  for (symbol, ident) in symbols.into_iter().zip(names.into_iter()) {
    map.insert(symbol, ident.clone());
    bindings.push(ForeignBinding { symbol, ident });
  }

  ForeignBindings { bindings, map }
}
