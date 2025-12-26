const tagged = { tag: "a" } satisfies { tag: "a" | "b" };
// expect-def-type: tagged = { tag: "a" }

const palette = ["red", "green"] satisfies ("red" | "green")[];
// expect-def-type: palette = ("green" | "red")[]

const config = { mode: "on" as const } satisfies { mode: "on" | "off" };
// expect-def-type: config = { mode: "on" }
