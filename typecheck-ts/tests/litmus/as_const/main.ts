const tuple = [1, 2, 3] as const;
// expect-def-type: tuple = readonly [1, 2, 3]

const nested = { coords: [1, 2] as const, label: { name: "point" } } as const;
// expect-def-type: nested = { readonly coords: readonly [1, 2]; readonly label: { readonly name: "point" } }

const readonlyTuple: readonly [true, false] = [true, false] as const;
// expect-def-type: readonlyTuple = readonly [true, false]
