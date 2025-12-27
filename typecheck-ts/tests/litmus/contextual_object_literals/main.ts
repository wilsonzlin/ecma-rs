type Tag = { tag: "a" | "b" };

const ok: Tag = { tag: "a" };
// expect-def-type: ok = Tag

const bad: Tag = { tag: "c" };
// expect-diagnostic: TC0007 "tag: \"c\""

const extra: Tag = { tag: "a", extra: 1 };
// expect-diagnostic: TC0006 "extra: 1"
