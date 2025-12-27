const xs: ("a" | "b")[] = ["a", "b"];
// expect-def-type: xs = ("a" | "b")[]

const ys: number[] = [1, 2, 3];
// expect-def-type: ys = number[]

const bad: ("a" | "b")[] = ["a", "c"];
// expect-diagnostic: TC0007 "\"c\""
