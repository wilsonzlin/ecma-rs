use serde::Serialize;

#[derive(Clone, Copy, Debug, Serialize)]
pub enum FixtureKind {
  Ts,
  Tsx,
}

#[derive(Clone, Debug, Serialize)]
pub struct Fixture {
  pub name: &'static str,
  pub source: &'static str,
  pub kind: FixtureKind,
}

#[derive(Clone, Debug, Serialize)]
pub struct ModuleGraphFixture {
  pub name: &'static str,
  pub files: &'static [Fixture],
}

pub fn all_fixtures() -> &'static [Fixture] {
  const CONTROL_FLOW: Fixture = Fixture {
    name: "control_flow",
    source: include_str!("../fixtures/control_flow.ts"),
    kind: FixtureKind::Ts,
  };

  const UNION_INTERSECTION: Fixture = Fixture {
    name: "unions",
    source: include_str!("../fixtures/unions.ts"),
    kind: FixtureKind::Ts,
  };

  const GENERICS: Fixture = Fixture {
    name: "generics",
    source: include_str!("../fixtures/generics.ts"),
    kind: FixtureKind::Ts,
  };

  const COMPONENT_TSX: Fixture = Fixture {
    name: "component_tsx",
    source: include_str!("../fixtures/component.tsx"),
    kind: FixtureKind::Tsx,
  };

  &[CONTROL_FLOW, UNION_INTERSECTION, GENERICS, COMPONENT_TSX]
}

pub fn module_graph_fixtures() -> &'static [ModuleGraphFixture] {
  const MODULE_ENTRY: Fixture = Fixture {
    name: "index.ts",
    source: include_str!("../fixtures/module_entry.ts"),
    kind: FixtureKind::Ts,
  };

  const MODULE_A: Fixture = Fixture {
    name: "module_a.ts",
    source: include_str!("../fixtures/module_a.ts"),
    kind: FixtureKind::Ts,
  };

  const MODULE_B: Fixture = Fixture {
    name: "module_b.ts",
    source: include_str!("../fixtures/module_b.ts"),
    kind: FixtureKind::Ts,
  };

  const SIMPLE_MODULE_GRAPH: ModuleGraphFixture = ModuleGraphFixture {
    name: "three_file_graph",
    files: &[MODULE_ENTRY, MODULE_A, MODULE_B],
  };

  &[SIMPLE_MODULE_GRAPH]
}
