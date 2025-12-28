type Tag = { tag: "a" | "b" };

const ok: Tag = { tag: "a" };
// expect-def-type: ok = Tag

const xs: ("a" | "b")[] = ["a", "b"];
// expect-def-type: xs = ("a" | "b")[]

const f: (x: number) => number = x => x + 1;
// expect-expr-type: "x + 1" = number

let g: (x: number) => number;
g = x => x + 1;
// expect-expr-type: "x + 1" = number
