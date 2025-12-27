declare function map<T, U>(items: T[], f: (item: T) => U): U[];

const out = map([1, 2], x => x + 1);
// expect-def-type: out = number[]
// expect-expr-type: "x + 1" = number

const bad = map([1, 2], x => x());
// expect-diagnostic: TC2000 "x()"
