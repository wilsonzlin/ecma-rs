use serde::Serialize;

#[derive(Clone, Copy, Debug, Serialize)]
pub enum FixtureKind {
  Ts,
  Tsx,
  Dts,
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

  const ADVANCED_TYPES: Fixture = Fixture {
    name: "advanced_types",
    source: include_str!("../fixtures/advanced_types.ts"),
    kind: FixtureKind::Ts,
  };

  &[
    CONTROL_FLOW,
    UNION_INTERSECTION,
    GENERICS,
    ADVANCED_TYPES,
    COMPONENT_TSX,
  ]
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

  const PROJECT_INDEX: Fixture = Fixture {
    name: "project_index.ts",
    source: include_str!("../fixtures/project_index.ts"),
    kind: FixtureKind::Ts,
  };

  const PROJECT_NUMBERS: Fixture = Fixture {
    name: "project_numbers.ts",
    source: include_str!("../fixtures/project_numbers.ts"),
    kind: FixtureKind::Ts,
  };

  const PROJECT_TEXT: Fixture = Fixture {
    name: "project_text.ts",
    source: include_str!("../fixtures/project_text.ts"),
    kind: FixtureKind::Ts,
  };

  const SIMPLE_MODULE_GRAPH: ModuleGraphFixture = ModuleGraphFixture {
    name: "three_file_graph",
    files: &[MODULE_ENTRY, MODULE_A, MODULE_B],
  };

  const SMALL_PROJECT: ModuleGraphFixture = ModuleGraphFixture {
    name: "small_project",
    files: &[PROJECT_INDEX, PROJECT_NUMBERS, PROJECT_TEXT],
  };

  const REAL_WORLD_MINI_INDEX: Fixture = Fixture {
    name: "real_world/mini_project/src/index.ts",
    source: include_str!("../fixtures/real_world/mini_project/src/index.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_MINI_TYPES: Fixture = Fixture {
    name: "real_world/mini_project/src/types.ts",
    source: include_str!("../fixtures/real_world/mini_project/src/types.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_MINI_RESULT: Fixture = Fixture {
    name: "real_world/mini_project/src/utils/result.ts",
    source: include_str!("../fixtures/real_world/mini_project/src/utils/result.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_MINI_ARRAY: Fixture = Fixture {
    name: "real_world/mini_project/src/utils/array.ts",
    source: include_str!("../fixtures/real_world/mini_project/src/utils/array.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_MINI_CLIENT: Fixture = Fixture {
    name: "real_world/mini_project/src/api/client.ts",
    source: include_str!("../fixtures/real_world/mini_project/src/api/client.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_MINI_TODOS: Fixture = Fixture {
    name: "real_world/mini_project/src/api/todos.ts",
    source: include_str!("../fixtures/real_world/mini_project/src/api/todos.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_MINI_STORE: Fixture = Fixture {
    name: "real_world/mini_project/src/state/store.ts",
    source: include_str!("../fixtures/real_world/mini_project/src/state/store.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_MINI_PROJECT: ModuleGraphFixture = ModuleGraphFixture {
    name: "real_world/mini_project",
    files: &[
      REAL_WORLD_MINI_INDEX,
      REAL_WORLD_MINI_TYPES,
      REAL_WORLD_MINI_RESULT,
      REAL_WORLD_MINI_ARRAY,
      REAL_WORLD_MINI_CLIENT,
      REAL_WORLD_MINI_TODOS,
      REAL_WORLD_MINI_STORE,
    ],
  };

  const REAL_WORLD_REACT_APP: Fixture = Fixture {
    name: "real_world/react_types/app.ts",
    source: include_str!("../fixtures/real_world/react_types/app.ts"),
    kind: FixtureKind::Ts,
  };
  const REAL_WORLD_REACT_DTS: Fixture = Fixture {
    name: "real_world/react_types/react.d.ts",
    source: include_str!("../fixtures/real_world/react_types/react.d.ts"),
    kind: FixtureKind::Dts,
  };
  const REAL_WORLD_REACT_TYPES: ModuleGraphFixture = ModuleGraphFixture {
    name: "real_world/react_types",
    files: &[REAL_WORLD_REACT_APP, REAL_WORLD_REACT_DTS],
  };

  &[
    SIMPLE_MODULE_GRAPH,
    SMALL_PROJECT,
    REAL_WORLD_MINI_PROJECT,
    REAL_WORLD_REACT_TYPES,
  ]
}
