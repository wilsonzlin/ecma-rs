function collect<T>(...args: T[]) {
  return args;
}

export const collected = collect(1 as number, "x" as string);

function makeTuple<T extends any[]>(...args: T) {
  return args;
}

export const tuple = makeTuple(1 as number, "x" as string);

const arr: number[] = [1, 2];
export const fromArray = makeTuple(...arr);

const tup: [number, string] = [1, "x"];
export const fromTuple = makeTuple(...tup);

declare function pair<T, U>(a: T, b: U): { a: T; b: U };
export const paired = pair(...tup);
