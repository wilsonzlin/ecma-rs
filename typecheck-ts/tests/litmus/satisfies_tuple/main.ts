type RGB = [number, number, number];

const ok = [255, 0, 0] satisfies RGB;
// expect-def-type: ok = [number, number, number]

const arr = [255, 0, 0];
// expect-def-type: arr = number[]

const bad: RGB = arr;
// expect-diagnostic: TC0007 "bad:"
