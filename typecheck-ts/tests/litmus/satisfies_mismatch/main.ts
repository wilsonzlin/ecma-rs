const bad = { tag: "c" } satisfies { tag: "a" | "b" };
// expect-diagnostic: TC0007 "tag: \"c\""
