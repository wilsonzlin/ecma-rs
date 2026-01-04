const bad = { tag: "c" } satisfies { tag: "a" | "b" };
// expect-diagnostic: TS2322 "tag: \"c\""
