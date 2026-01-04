#[path = "common/mod.rs"]
mod common;
use common::compile_source;
use diagnostics::FileId;
use optimize_js::il::inst::InstTyp;
use optimize_js::symbol::semantics::{JsSymbols, ScopeId, SymbolId};
use optimize_js::symbol::var_analysis::VarAnalysis;
use optimize_js::Program;
use optimize_js::ProgramFunction;
use optimize_js::TopLevelMode;
use parse_js::parse;
use std::collections::HashMap;
use std::collections::HashSet;

fn collect_symbol_names(symbols: &JsSymbols) -> HashMap<SymbolId, String> {
  fn walk(map: &mut HashMap<SymbolId, String>, symbols: &JsSymbols, scope: ScopeId) {
    for (id, name) in symbols.symbols_in_scope(scope) {
      map.insert(id, name);
    }
    for child in symbols.children(scope) {
      walk(map, symbols, child);
    }
  }

  let mut map = HashMap::new();
  walk(&mut map, symbols, symbols.top_scope());
  map
}

fn compile_with_symbols(
  source: &str,
  mode: TopLevelMode,
) -> (Program, VarAnalysis, HashMap<SymbolId, String>) {
  let mut node = parse(source).expect("parse source");
  let (symbols, _diagnostics) = JsSymbols::bind(&mut node, mode, FileId(0));
  let names = collect_symbol_names(&symbols);
  let analysis = VarAnalysis::analyze(&mut node, &symbols);
  let program = compile_source(source, mode, false);
  (program, analysis, names)
}

fn flatten_insts(func: &ProgramFunction) -> Vec<&optimize_js::il::inst::Inst> {
  let mut blocks: Vec<_> = func.body.bblocks.all().collect();
  blocks.sort_by_key(|(label, _)| *label);
  blocks
    .into_iter()
    .flat_map(|(_, insts)| insts.iter())
    .collect()
}

fn foreign_names(func: &ProgramFunction, names: &HashMap<SymbolId, String>) -> Vec<String> {
  flatten_insts(func)
    .into_iter()
    .filter(|inst| matches!(inst.t, InstTyp::ForeignLoad | InstTyp::ForeignStore))
    .map(|inst| {
      names
        .get(&inst.foreign)
        .cloned()
        .unwrap_or_else(|| format!("#{}", inst.foreign.raw_id()))
    })
    .collect()
}

fn unknown_names(func: &ProgramFunction) -> Vec<String> {
  flatten_insts(func)
    .into_iter()
    .filter(|inst| matches!(inst.t, InstTyp::UnknownLoad | InstTyp::UnknownStore))
    .map(|inst| inst.unknown.clone())
    .collect()
}

fn find_symbol<'a>(names: &'a HashMap<SymbolId, String>, target: &str) -> SymbolId {
  *names
    .iter()
    .find(|(_, name)| name.as_str() == target)
    .map(|(sym, _)| sym)
    .expect("symbol exists")
}

#[test]
fn captured_variables_lower_to_foreign_everywhere() {
  let source = r#"
    (() => {
      let captured = 0;
      let only_local = 10;
      const inner = () => {
        captured = captured + 1;
        captured + 0;
      };
      captured = captured + 2;
      inner();
      only_local = only_local + 0;
    })();
  "#;

  let (program, analysis, names) = compile_with_symbols(source, TopLevelMode::Module);

  let captured_sym = find_symbol(&names, "captured");
  let only_local_sym = find_symbol(&names, "only_local");

  assert!(analysis.foreign.contains(&captured_sym));
  assert!(!analysis.foreign.contains(&only_local_sym));
  assert!(unknown_names(&program.top_level).is_empty());

  // IIFE arrow function is Fn0, its nested inner arrow is Fn1.
  assert!(program.functions.len() >= 2);
  let outer = &program.functions[0];
  let inner = &program.functions[1];

  let outer_foreign = foreign_names(outer, &names);
  let inner_foreign = foreign_names(inner, &names);

  assert!(
    !outer_foreign.is_empty() && outer_foreign.iter().all(|n| n == "captured"),
    "outer body should use foreign ops for captured vars",
  );
  assert!(
    !inner_foreign.is_empty() && inner_foreign.iter().all(|n| n == "captured"),
    "inner body should use foreign ops for captured vars",
  );

  assert!(
    !outer_foreign.iter().any(|n| n == "only_local")
      && !inner_foreign.iter().any(|n| n == "only_local"),
    "locals that are not captured should stay local",
  );
  assert!(unknown_names(outer).is_empty());
  assert!(unknown_names(inner).is_empty());
}

#[test]
fn global_top_level_symbols_are_unknown_but_block_locals_bind() {
  let source = r#"
    var g = 1;
    let l = 2;
    const c = 3;
    {
      let block_scoped = g + l + c;
      block_scoped = block_scoped + 1;
    }
    g = g + l + c;
  "#;

  let (program, analysis, names) = compile_with_symbols(source, TopLevelMode::Global);

  let unknowns: HashSet<_> = unknown_names(&program.top_level).into_iter().collect();

  assert!(unknowns.contains("g"));
  assert!(unknowns.contains("l"));
  assert!(unknowns.contains("c"));
  assert!(
    !unknowns.contains("block_scoped"),
    "block-local bindings in global mode should still be resolved",
  );

  assert!(foreign_names(&program.top_level, &names).is_empty());
  assert!(analysis.foreign.is_empty());
}
