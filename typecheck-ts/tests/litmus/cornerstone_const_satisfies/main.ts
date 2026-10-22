// Cornerstone: const contexts & `satisfies`
// (wiki/theory/compiler-theory.md § The TypeScript cornerstones)
//
// `satisfies` checks assignability but preserves the expression's inferred type.
// `as const` keeps literal/readonly shape.

const mode = "on" as const;
// expect-def-type: mode = "on"

const cfg = { mode: "on" as const } satisfies { mode: "on" | "off" };
// expect-def-type: cfg = { mode: "on" }

const bad = { mode: "maybe" } satisfies { mode: "on" | "off" };
// expect-diagnostic: TS2322 "mode: \"maybe\""
